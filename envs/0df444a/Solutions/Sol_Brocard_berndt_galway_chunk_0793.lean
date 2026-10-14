-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0793
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:50:15.025586+00:00
-- url     : https://prove2.me/submissions/fcc575e0-4edc-4d18-8531-022a5a3abee9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 142446043 ≤ n < 142625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 142447293 1250 142446043 142446071
    0xb1807020a03140415030504020f01080106080a020702040b06030a0f051005030309090c0d0204080714040605010503010306020304050a060c030207051c0512070909021209061806010b0c0109050a030f110102070510 93
    0x255085400301c4e00b00d401700c1c000754070741507809036000754002c898800f4800080d80c01101c0c031800900030308000075010000b01349003072a00e801a1030711038401000428213504c941d0105d1000c1d04200c5400c103a050300c4051200c903d0f0303042c0c0309041d0000025400303200c22508100c00300c0d5882c451185040e01580160002a2040d00141c0540b48031041f054000e5550750b030b40e610312666071040350260b03040c8a000903080156a262910a002c101c4506843d0603040d40e186803200b030000c1d0402071050703881c0e02907030040900143c010302c9021094119618016141d000d2801c2c00d51401400c1000103601d11006140301000e95000026034902010104400503140e49448017220a0703041640320b41c14030742c000b08a00c0078440e00c0b2940079110301600c03812200c450740c4580840c2400c5020080d00c41654201303800502c202ca03000001810440c2440001089100c0782e40d503414580040300c0c8082c1e00082a01070f45003096a4012100c0f41176840c400d000b5401d080c039580358981c481400c03e05610646a03988030424481c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 142448543 1250 142447293 142447297
    0x60e18071208040e01060203280e030a0b10051806040c09030b041203270602030a0b060c060109050f09100c0e1807080c0f04050607170c010b1807020a0314 68
    0x4400c00e0101e492a920702d030000c22600140502c5484860200021035190300c00030554988101c00801c076480351002c11840c0300204103060490b010810b0070340c0f03480290b80f030800203081894800c3d4800c80040ca400d001c0346003514115008580304000030b01c029954182d51400c1d85401100485000510451186090340d8110090780028a10042e110404c8103101000304400100c00c95a20103000124510200041c1c00c21100e020b04a03480a41c1050300109040d039025550081e04c003034000038603114282c0082c080c0d4001303900e072034140d900000040c0401d80c12805040d802500303951101d00d007428191040c40e26150201e00b140fa200755902404000540302d1451041d8866025081001031241040709030320306941100c03040d011070304420100d40b861503c02d080710740c00b508034203032141454141000c02103140d101c40c0e001c1d5114005031507001c01c0d5000c048001d100020b00e248c000101060600b003840300395801c1002204501c030b0500b0030024016004a41ccc0c0111079898a44071442c52aa80d040314528 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 142449793 1250 142448543 142448549
    0x20703290a0b03010b0a0806130305040504110c0f0303071b03090b1c0c0206161b060e0303010f050409020604060323090f0708070b041e0812030103110301060e1807 72
    0x41000c00c0a00c00008016805568400d4054009005030042c500500010201da44100d050552010001400d0070541110129010b803292030250310305544c500019007174900141801e0240340c0000341c41c0004620801501b020064907602550a42ca46200c016142501003080d9a43c85482c480b40702041500c1602860041e044445000d6104c0c40d40000800180c00600343c9224038918212001003001d0000070310f144525040c5c0004210003c00d6a01102c010140c1d818440100c0c40f40d0f0007400004859000d01c203272204420005503140d40c0342501d6610101c1c81588071074002d91420201c840075031560000c64081e0340450802040304180f0340840c1030051141800c20324131b604020b0900050a00c080b59858503001c0700002c4510458541034441d440d40c0e501d2040c1000036604100801c0203040c112464074507144503074006030155550312022403c207038aa0345104e4910500100510800042d9009014004c000390000c101031420300e00301c000444805041840d00c43ca61442d40005040304200361409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 142451043 1250 142449793 142449863
    0x110705040f0203180a120c030c0b07031b08070207090b13050412020106090b031b12070b1c0903022d07080606091f0b0304211e0201020406020703 64
    0x15903070081c41d1800003500107940010340d0031248801c02c1c44110700083e1300300b1015080410007118414402094030310b140511011014414401c84030b43c0820305042040e4440c100740e450200300f00c50448285da503880c00100105c01400009002c2c06100b0354001200800d84051110001d5030074076080c00a1007a10314000030314085030038442008204990b1139807000107401c0a8000707202040c0c46031031039425500c04054003509a4442d4039098800050307c001c554180b07d000e400000e040340407082950810310740e0340107030120100009203d48184921064070b4584a988001000341408966000351664001d03035a910501e050560458400d800d121240c5a081c0100c40403517004968400189480c0c00f800c031242031081a42d10001090100c1e1080f40a041340c28031150162000d0030004442c41c5500090001d6400018402000d440d0f0869405084410b940e540c44030641d0024103005c5c00c0f014070082c4982021a40140b0040202540004050007a82d0b803000510501400072090220030040542800070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 142452293 1250 142451043 142451051
    0x50c0d02030901060e1b0f0d09050a06020406020706051c0506040b03070909020f0906060307050a03020706020403030c050609030f0901050304080c01020301120b150f010302160c14010210060506070311070504 91
    0x1190aa05500c00c608441c032540c02ca09441d030751003504920304000711208041e8003004108011f58144071000030300035038444490000702039403c0d031075403031419001090450f40750758006800c0c80b1070790701082010010260340c07a00500d000750a142e50700d002c49860a5908000362071700c0205003140d03501d40104900c05006003c41340640d980304100d10142804201c03c1c1d0162414800450050a02d150b084d03102c0d040c0030788a10b05d1074554007411100d50b030080f1049400c043c2e09014038030002d0118002000214040d5442c214548000d00f411070812201401d80d5403580d0080101e010070045040030b440c280e1009080c800d40700da0322414030a069114900300ca14071544008008907006403001940b1014500403038070b40c4910381d0350804401000000741e40041d0301005440d409681e5610940042c542d0030040240390700700340b01c0c0d9900c21842e0f1805400c1406268504030b040c80455904000400010050786400d000480c60038010800314401c100004e0304100180424484250342041000d00829010300104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 142453543 1250 142452293 142452301
    0x907020102041d060607080a090302090a0b09130302100c0e0a1707090b0a050405070c05010606020309010e0307140f030a0512040311010e090c090a08030f0a030506100909050c0d0203 80
    0xa000754058043c800040760b521550a200c0c04688a03110722883d1301a011524001498460301501d4000943d10010000b5113140840140c0307072070341654040c09159101080340c01440c401c000303002100070046004500060443c00101e0b900065036403011114503000241e00304021800c4405008a1403032507008003440d50000342003042c03942408034142220080d00c01094656050005480c0426862036206182002c20b101c603103441d40c0640d0700500542441d130201030f1255a5142510059408500540c00c082400112542c100d402803c003c103085018100d16800c281040601ca102c8038145070255600c0313110926151030400c0005950303070300f01e03045403070103050700100000d25070013030000311414901441107001c035500401c00d000f43c1e030100402c11801e99503401a04030540d000000540d5203c0340801c4001a010400e100030003c08d00720803421036031442880c80140c195907024080074003540e5042d00780b425869006411400384d03281c00c02c0104aa441c2c81d40c04102e035018241e030741c0c5d283c503100100340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 142454793 1250 142453543 142453547
    0x309030903061014090f070302031003060e0a05010b0105210402060705060f041b1d060301060f0b0318190303050705250201021005010b0a0509060c07030c18060b0f0705010b0907 78
    0x450444071000e6082481c484503406002c8007800a645800c0142d0b003800101f00101c0c0260065607100303170311008400c101543e07a02c1d6101603d103c2d0341108255000b048c9803005000081c056414018028203040d45007814101c820208048000c40c40258407190760081801c640d2104111040290032900b1074410307040500e1580c3c0754600a0310120307003ca0740048000705540d42d40c1c0450046417025a60f511307288902d8011800d900d40700030f0145030326540c2c0d44c401003140301c0b00184000c003801c10104070036268501220550803c01c3d000040043c154056090f03081d8690000c9078030308600fa4940340110b0305032900c1c00705440c1c501495200c120080d48180f8580309400807400e1808086000368212014208031800f480205d0314203001c1d101c017402c010440380135070500490041c0344882000c2c003864a0a41d21913030103420065950003c50f509009980208550080c00c0c09040c04e101548000300600303480c1a101442c2c0c0e100c2c0c6040181003c01c0400c0702d030240a03080d03210001c1e0360380180c41c260451a00380c01c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 142456043 1250 142454793 142454821
    0x617060f150901050915060a09050108091b010f120609090203011d0607140f03070206010807080d020714060c01050f190b06040b070c1a0a0305061008010308030903090306 75
    0x24034185018014002486100c4120070310248200103440300116908002c140486548001c11310700c0007901b98801c402d46921031130024002603051760354000149080ca00010a074040c0944003030201d5008551600703034180100b81a01e6902c109080c0f0344040e100001007520610604828680703058540100016110342c113170064440b2038403c07002003018400d02800b0b03444156a090b400c100b5640150300040d8924018240c00d4440300030f80c40801d04150040c07003500a00e900c111004401600b00c03030010040030004125540c090074014014205003040304400079941d40191107000c239503031490404403411f5100c2004891000c07940a00a000034542949004801402030303910340e6414554440c41d112410f80361080000c903001c001c0c0458605890314040c1d44603900701c034401b40d604441d51f07040040d68424a10034410310702c0c0110300e401d85614030403030007a003120802442c290007890702c080b80103074855000c1400b905407179000b00090303229203611450134958003034036030425054480c101c00d21410100d0036039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 142457293 1250 142456043 142456051
    0xc030f050c120c0c010b0904060b01111203240904030e0f220c050c06040b06031c05090d050102130303050d05060303040302030307260712030b0103060602070306020c01061706 77
    0x900c45500d408045003001c1c0302d50280c0800303002d4040081407500e014440104050040702d030020502e0f24a000002c2c814500a46c0d0480f0139a6450910342d086580099040b010f41c60000060020a82100d01041c02d6101c0200354200188140e4102480d0001240411410000c0504441c042d032074030f4072b00500160840000c4034440c1d500d210f04605e8628005811403180001a8481035100101c1c0c010600585001b103c81700902c0030502c040300118200700182441580a60344602d26030402c40e052500b01a8072003940c0040100103440c400d21940c118080ba411208151140d03034241ca440d0800c680240180701071450b1402001c0000024540c0c814041c1515000703490041000f500c1d0340d020540e503445580f00080d01500305010340e9022a024170b04050700d0280585c6808100484108084681d9000d0007044403140c3d038590b0102001c1e03526105d90903c0302020700301080010308041020355180c3c500d03c0001c008030740000310003052803402e41241004050148049084a4008510030382304c08040b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 142458543 1250 142457293 142457321
    0x2180702060702071401090e1b0a050a1205131b0b1801020c0a080c01081f0603090b0a090201020601270c0c030210090b010302040c031806020406021e121c0c03 70
    0x4040403030145c410394140b0650f071005031120446185800801000e206000b0400c3c1441e00801090300e0a00c40000300924400a251781c0341640d4040e0342c1c5010340814a1907028030045485d1000300003540d070b8041c00c130342021500503003400c1b00803008200c1d44a049009400018101d240462400161003803c3d17000c1140d52826025156522451b1081c40010001c034420000164412400a64554041d4411076013046640c0310301c446a00c40c4400b00e113801000d55000c54006035840082c001803081081d5829042122000c091000c410107800007903a410040c090710b2130400f5244d4010750040102c1c2000030008120203414041d61030706600141c010b03043c0c4001a4094040d030700a2441c02e04a0703211f115001c0b584811070700100d1b401c41c2c00b0321008009465490040c950358000346081040c40b01649240941305440242e40c45050807002410804011041001c599101d180c40a0403e001303c0c224046000200b191501c1d101002d0311116000100c5454038640c0e4a044070003464140e05412101c803540e400e07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 142459793 1250 142458543 142458553
    0xf01060f080105090d0302070201180609060905060a090509130f05030306040c080108071401050403021309060e0f030304120212040306090b13050c12031309020301031a0702071202180702060702 85
    0x410742a0b00b42c0f041180c0040701900b0108040100c039000e940a0541c0d0360040c503081c0080c641302d00000d201d0700d050b600a400440d4419104006c1c003940001c400780a000140c56680c10416459405170803100e40b030180a2003a41c07210b0009400c15941040301220741e400048200c0300e5102400e125449900c00e075469402130f0308085c46004914080c1c0200e034100c0780f118005200035403078503019040c1c0f03502c042015030421104010010240c3c1c0caa200d50a500c00c640c1030005103c50709481c121040352901190003280e90402c22aaa01290011042d04da100c0d801414020351200c290008038104008010f21008484021a010051001c103901041016100d170001c000640c4526095488803010140d0040c00c5500150640d8600d00780100e50100041414088174240256800c48a0084620740c010080055004c070040050021040440c11404501d4140340c0722404d1202c4029214810381c05000000b03005d4032018021074480d49060140180e006041e00c0550401c01d800a4481d05e05403100c6005101e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 142461043 1250 142459793 142459799
    0x50c030106030308010e0c0409050a05090c040501120303050907150f02151023040608030c1506090f0c0913021b06010602100e07050607080301030221030306040b0409050f01060f 78
    0x81481410300b0307030750541c407811540da00e05030340c403400b00070020850400400e0500c00007650756468064a4041d2908400c003240b14a40308019500d0321044542c040c1c0304a05080041101103804010249125054034001c5419500c40c403860f45070006030762103060348041c0061038402881d03005181d840103245503070039150641d001001005412205881c03600201c2d0440108104483e8032030f080104207104152004040e1009000190486010744d0003030ba0250400160f00c001c4403000d02204070109492800c000340c2d07040c01c40118841600003050001000112000704410b0700c2a001990180d540013000c2000441a200000d00030350000c002c0d803c02c1d03a00d00700500c0c3c00c1b41000b04055040e50a168002c01d18800b4800b0b014003d00041141090301d405082c0010445868a03402040f002d406650701035503a52542c8140b215a0502c08828540c1480c4800b5288001c032010080f60b800a00440300400e1814403040054018070714100c0003050f0b0711410950b000b00c103030103401040407601039841001c02903503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 142462293 1250 142461043 142461049
    0xe0106090f15121d0708060a0608070e07030209120106140f03240619081b0303271305041a0606070b0f0408070b0408030f22020907050d0204030b04050c 67
    0x4261a40c640c0418501150500102c3c2c543c0c0c454403c0713034010001d403c0100030080015082c44220340010a02d900302c001003042100e414007884009010702c000500700700d0310707001300741c10310075000b034040420140c000601080583c2c03082d0981c5092000303500200030069840124010401494041e1b600030704010385403170030500e00070036010000d140850548003441080c0d184c401150304014929036000c60031065042a562410001c2c9014003100d03001820090f0000b40c818180a03180e50b1807600c20303401004500811075114040214440d10301c6d1404c050200d4010000c6c0c050580000f0316a5524039100400013400081c102d00f50341048140c8100440d81c80d001c050000e82d100d06d00d40074056880c10808181500240105241d0050003145100d0500c0c1c61665030440c0c00800b80c1d002e462980300170050115a074a00c801080e0080103074100400c8104801110b203540c41c07250784010f031042c0d1000c800a00101c2c003410842c4c11010600b60210b5640f9244d1400707017020700081c4c1f0b0595142c0721b60918001541 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 142463543 1250 142462293 142462319
    0x210050301030b0609090f10020306040e010b0a031202010f0e010912050f07110d02040c08070806010503060d06051801020408100b04060f0e04030c0b040b07080610050d090c0e0106090f 81
    0x2034002d07410f206640c0c0c6110500c8003224000d0001580d03031240200ca005501014449904912000d14000d60703a802c10b40c0030407056423101242e02c142c40e498030781c0f010f245a4440e0948401c89510031009a600d6090315000e9004080c120100c104a505040e0745c0e0244d40019881058924411a04610b41078440c160480f42809030f0b4020102d5a50100308540104070306204542c42242d009246408081032540030905542940c3c0202011848010512074503c2d00040c525034403035000e180841c11450f04c1c80014886252080e405040319a4800206520104900c0304889030ba5000c0d00170f56a890303a40300c505a4500882011500c00743c501462060b040c901409950104d4a0643c04038400c5806d01188941d4980b02a1040381070081900702000010700d5005020702c1240553310b00c482d10f00d411440500103e0700100054410758503d250080d00a401c6000c1e940703590b0304580b00203440318980c07034008240c10b546e41040c04600d00910002461a9020b60391070103459108203c0c0c914a80c0d01e140b40c8140c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 142464793 1250 142463543 142463549
    0x190815040c240305090d05040b2b0b090906040201120e0f160f0609030c030209071b08030105010906110d1d0303030117070501050412080304030c020402030a1a0d022103040f0b070210050301 83
    0xe07d0030001002502000303c040c2c21550200716102d07400e040c8004200044c044a840d500d0314050301c810a002045c5046d0a81c1584124100090400791406500090205400d00001c001c1c1c035549000c074045035202000107644440111045030a0b4260140d01c40031880c0e03a0344034400d000a420100410014032a14407413044942c01840030a24500f10343c200080b52000a110008100c107400b01e051842028126000d0900d004403d0140c4d6541450001010403240c1d4100130103101028142d04460795001070aa406454245050050740b03c02a1921440d001854400c2d541844080004a412400c0810081501d0042000c84003901c6da200c00644490141d80314407090728003040510004140c0350001560702c40c0c0f0038500210b50010300e50000e412a0425107002e04100e036190444108401186800140b80d00200c401808421140d4000342190044541c6801c000300031b480380c0c440c4d00c0400c00507100a07040301c200c1036911350780320000c00c1c07400e8100100981c0f16800c008407280ca401d00500403a81a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 142466043 1250 142464793 142464797
    0x30b0f060318031c0c0503012103020c060a050d05100e0403120216060e070e0c07060207020607051507080a060312050a021e01020405190815040c240305090d 69
    0x2011900020024a40c00041c25407110152015610007846801d2005081c2000d030754040c00e040a000403840c030200c8032400580d01c01d01c0800c10040c020940c80f000a0b05104c500300c1204504481d0a103000c0342041e0081d07038801d810a0011408840c0f440c2c00c40c1c050580c2e0410300200700004e980d100c18400c0c48075407170300c07401a1005c9140081004a481141c0120300992081c01c0940b9041c00120000e400c500b10b9031068908c159035540c0003091000070711601c4002d000b0001c1440721414000c00102441c41a188000e10701c641c001000000c640302e4005860300c054108099403951380100d00340382000f0b0800c42d00310002400b0300d40091a120000d100300d000381da4200803003240c44a280c42c8141e502da4003e03246e40d0107601c103510413401e0740d861842c4051030b01c65400e000943c5840c503000a10044802c0c6550032201d0703074840c01c1e00b0312000000240131415038448056428140d2900d050200102c02d60360031800b003c0a0500f0000004500c01c143e486000c6501c1d03070200b109940c2c2c1801c2d6034a4046199507240 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 142467293 1250 142466043 142466059
    0x12061104051011070b04180c020703030509040c02070e040f031709100905030705060703020a0212090d0f0309030609080729041101030f150503241f12030e0a06030b 72
    0x31151088561500f400d51150807188490b480d001d6035482c0d074000d03a0000d4071014600e1705003c0c002010b03000d60620264140000d141031411594040c0080c0034442c3e0150080c2c1d40c0d00c484501c02c40c800c01004000302009601c840d0103050500384801031081040d01076010841c240c54140742034003a21545071245400e04051704054072049804005040481c0d415034480c8010701003c00404c00a00c800c43c0540001d480040e5038886181c2c0207402d200810b4441030710400180704240d05074543c0e4101303c418903408456003211031118501a649800d9942001d0300d468504070b0030004210081e0020000180a038000140448030310304012110f2140740284213088051201203000034810aa034403401e000c050402040d5955840d910348101d80d4100c0754142c480d070300d1200401043c107080c00107094038192a50b698551040706000410140c20181c0003200c00520b0105080c0c40c50711120000b4040e152004d48071407407030340e036040040106003600b00e1544109a400030018141d4000e1081c0c080383c41c00642260 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 142468543 1250 142467293 142467319
    0x7080706050a02040b0c070806090a0b0f0a0905030c070f09050c090103050a110a0c0b1003080313030c0b070e090f06010e010e03100509030304050708071202060d06050301061206110405 81
    0x440070308006400314010030740a000109041d000c4602411a514591000f803101c68a000c40d42c5140005c040c0c46214203800540307260001c41c8040800e2503110880203184c0c9841d4881e989404c0007040280c6c40070380f1707034000411410108007001c1800022194200381c9aa1070030384850b030280840d0020703a101000d400c01003200e5a0a540030f42c101950144000344c002500300080c1c1d140403000c1d8008401c000024020080d840100000204c2142d0000504079002400c03d055030b4a07d00303141b002a107044c0c80c407908692840d04040c402d0700c4104035036a00100a50583c217001c040904410103040b440d82c40703120000c0004030a481c004410f140b043e0341c160755101480362014010341d000400c00d44040d825002d01c089801851481e40290741c0542c0d034801c01036640e4586030910f51f0500c3c04c036801205540d0800c040030016007908032500d0007459012254182d031151201030384402004580d0010b80c06500300800041c0746405010200110360040d2400e00400101c100003e50a10035401040d500c151550914 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 142469793 1250 142468543 142468553
    0xd080a110105062107030c12060e01050408030402120c03070e0703180206040605130902121602030a090b031305060a0c09050d02060d1113090b0a05010315030303051513060602060903070807 83
    0x124901131001050f20000360f142d4440700c1c02d610242c0c00a001d1014a50961001c00050b8420310103058240802001181000e5076200118800500060b10401400c0c580b00081841803042260b1840002d0865801d295590144241414100c4a8101180c98204820109414500600e0510383c1c000c1503646002d050036010ba410340c01c40a0b115030952503500001c10f010016200400c52068800c0c411640e45c98491003603e804481c070b14104003113404c28400c01c0007058001455030705030703101ca070b91160302c1c1d0b9a9201100043d072040c01024203584505000e000a150540c0d0010441948643e607064103503444406100000400750750094001d9820040504008a140e2020014049039a482850711752031500300381800348a42c000302030403940e81d28418007500c2e2411100f00105002c0c20180b000b05402d100105804440741b0011f0300345511070700001c0c21003000c0032201380b0501006040342400052a0729210050400b4000c00c409489000c003c0745040c06d0020076201000d90001070b00e4981515961381d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 142471043 1250 142469793 142469839
    0x3060109021b102c070909141507110f060f070306051206100f03030c020f030319180902032a0906071103070609050d08180d080a11010506 61
    0xa03036000042d28820240140010b1090109511880c940454840c00381c440081e881c03618004241c040e40441c0d00315002595020500004a4035500400520081c40d8180b403a84800290000c180c0c0b030056000d00400095040720f180c1c002c81c030960700c0e000c120040344a469034a01c1030f2801c111565003d0000203121061200131107078003800510300801c00594540214150000b02c010346001c0350401402c01850300ca031500d21000801d140b69070440b5040c65a103020f40a01d10098019020360702c0441c100000d0b41b0100100c500d03a0040340c0d5108032002c151003000300082c48400c10345800c2c00c2104400601e0175024000c0e02c0c003440100383c40003280c00f60401c480c422510003180a44003030b035007402002c08603a100380251004034003801907024010030b004c04150510b00c1d203400a800303002e518842030041c0d031240310801c005150701500c003a40e00c5140c45140d000c40c1c1e00c0812107070b5105101a00b0b8004026800c0d0240c046044152aa15400498140309a0170b8a00c1115216004601c0f40c1885c074600f040790f11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 142472293 1250 142471043 142471057
    0xf090f1305040c061b0b0a020723070905180c1309060c1d0a03050c060702060f0403050f060f070503040b0c0d0f061701020306062b09060c0806030307020306010902 72
    0x31020442040c480200401c0d1003040301c05030744400d01c0071400c00c2500d421645640d0002069a005202c581d01139640102502c0040c00901d00181c0c040340c45c00400c03209000510540c0a9a910b1200b080791841a699a40c4824062041e0b03a900b4030001c150311009029008900389d402002608210740c8082c180502c0d1080801d940107895124256180400c08900c00c005401c4401d07901d10341c040c3d84030404c2c44054444c090056020300c010380e5040000c51400b00e40300c0d00f000e20803140903986811a00004035240500190f0000c0c200001600004001f00090300320b00c0000848107503030059942c070240c1006010100c0388003003c540d0400004002070701100c076443d800f044070051281003e00c100c004504445038407078851009603031185c05020b0481e01039030002000c13420310025880c0d8034140c40455141d0003080c4041c02051609980c5410300240b8110b1060020100142000350000b68200100030f01003110104002c200e00e0400300340141404402c031078503190054018080703640f910078804000d42c0190303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 142473543 1250 142472293 142472299
    0xa0b060d0203010f0609270506060c031306140a05071704120c030201080c0a0e0f0105090d151803170a0b270109091707060617030c01060602030f090f 66
    0x4020358501034805140a48600744058005a003424400f818040d4941c21400341c2c0f068807015071034820442c45a024035003000755404aa9900c581008c01d40700e029a801069080c00040740e031042319428001200c00b203071310b91340d1011004025854408414402d4802520018408102d0003000c1002c41182942210146071050700e49656020071121075a40d030007044841600400342001036680c40000c0f1038004d5130700c0700c0e407510740b5441000141c0500142c0103c6406443c01c00e0144034260300450940b1160340c805882102604420b00c3c0200e0340100c2c0d00401480a0b1400400310345038164070300780b000203e505032500e0701800b004000040313107050f008102e40512501d50030440300c0c903110030226242c04054500c0b030321102d900521260388804016002112000c0c80e1103400700c0800d48180d811400c291350100d48a0341c0c0e075041d003054000b4041c9500b0603404132060350405100e091000006142c6020704c800200301603038840c031049880340700742c0007405510903003800041c4c020f10b060451000c3e80c00c401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 142474793 1250 142473543 142473547
    0x503270d180f0b0d0c0810030f060e0619061a0f0c0708120a030609050408090d05100911090603070303080109020d0f0c0809150420010507020d200604030b0a0b06 71
    0x80c55040b90100038603003048492140c040380400710140680100212400306003449039440c0f0380310801060740103092001801440030509400b003880015231004c0c1901074408180d4046141c0039900c0c41c07421010038090b041c202d25010307001402c00c0c0b042400004010540480e140f500303000003104005a002080078044502503a000050440c4040101420981c80c43c5003841d00d502c0415800f4003240c24513413003080000d0401040000185c0700754216694400100c0e404100c2041904010740703000305804002c0078041c9442c01d040d00f40300968000d1094000300b00d0780401c0690b224414035490301a039100c000c02081605c40184040320158010b0b014403400003c0006131010f841440005a58030802000d010802800600149180c140400380010b6460134840c807103400c1603540e452001701145c146810241c4507101d2580603030320070303000c45160b213800030946c10050115061992403280e00380c200f07070038202c0ca168601c004d40c100345064508494000d81c80e142e26039a0985404007400c0c0c8640c1c0c1662040c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 142476043 1250 142474793 142474799
    0xf0a020c0a060206010501030f06030b01030305160506070519031802040e010f05011d0705070b0403050d0905060f1012050a06020a02070302090a0509060604020705100e030d020a0503270d18 83
    0x51103107640700030b000d2603004103a20b51400e4005000c0f51109903419140e141440e40920205600048190449506241183e038a5500c03107220880d00c1d00702e40740203100307002d9607040c011410341c02000b8003030003110505101007904001e2010f50444112000c04e002504a074911440035142c40d41c00703140c20002e02000806e90031004134500c022240300340c1224017040c109040c4001c42000c4074030f607103900000e00c0c1485480c04800f612584542c1c0002803000f41046000182e0001d00001900700005030b9a1010440e1030b54103096401c0c100680c01101c800004000510700041c01100300384d40d01001176040b07405420264141d8460740f020b94020500d00065204074400000180c981d80f00541c032070211010001002c3c00c04804450500901402081c070450041c84004003040011030001d4a08200c0b50b4001081c070b006c9420942580921307200001030790700c085001c2541c940c1280045215008040c012481a02189100ba8091259406400f003541c4213080450394940104e660302c015402182405028503a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 142477293 1250 142476043 142476049
    0x3060424020a09080f0604050712110d050307050d03060b04090906140108150a050606040902090d022112030903040314030904020a0e0f1e0d03031103070305040c09110f0a020c 77
    0x3004144403800030302c0f40981046141c0c810720905002422807006030040d8200342e00d44694511640c010501010303600d00c0c000c41004030b80100440b40307200140156081e02005c0c02d00c2c54894100001c1654031f0302a542e500141c0e18407038030408040d41c00c04111301b030034607081c08104802440e100300c040700d1582d611780742c01108540003aa414001c0c003114000b40b4102d040d00710003015000e00600b40303000440c00d000038014681e6400081da03081e0755040c1030040c0c903504071600041d071074100c14101a4100022030070700742c500c0ca500c07624041100d00280031600a02c80795003100c2080e1000302c981c0a002d400501c000d100252850552603035401031181142d0a1007048c034009012079100c00050004140601e803100194201000f9151181600311100441c003901c034020b41440ba250007402a12902511505c042058003913801881d070f0f450760105158492800302d80141c000c00064400380c9400244c102c4c0001e01d07101303c0c01288403131300380080d0940c1403200703011405465170821808101580030f16891018151 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 142478543 1250 142477293 142477297
    0x1050412140a0c05130c0504062714100c20120d0305100501030209030c04021309020f0903120a050d1a0d0c09050109020f030c0f04170105010305010506010e0306042402 74
    0xa400346208401562520713081103e0310022070342203081c49003818203c3d50581d030014207450440f500fa00307003416113040510845a4a020f6080303004552015003401017403d41c60500c101c0c4d00307180c0c1911050b0802c2e06005003620040300c000c40080c400d80303038012070818400122400409100000d0109580c05500003c071906000c40d1043c85000696030300704001014403400d121500604080c20118507024810011944410b5846411401103070001400950b250780499440010849480c046440c0e42096031041e4440c0e10040c4450b10a21403104014121080d4008456030310341140c45840c5070141214028001c0c28040030303c065001580c50100c0341070b0300c4002642d8100ea00c00e490010100e41441e41d400d0449106800c90912503105201ca02259914072003280d0b044807221004544500394908900000d1181e41c1103d00d02c0d2240c11300e203541c46041508014181c0307105000034006540d8060044410070798504c40705a02d6440100800d010503c46040381c0800c0d0151901c10070004c002511040c16a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 142479793 1250 142478543 142478563
    0x110309030c160e060d050c0d05030913060b030103110d0209090303040b0f1003030302130909050a290411010324060e09040305030610111b0f0a050105041214 69
    0x9500006018502107030184040980c190075000b142512030308001450540000c0141024010300c10b048000c2c0500c041000714540c008002020542000400d184c013584981100890350700809566000c18642d42142c0034510540d2103d0300054250307841c2d903e40043c0c2803c1702c02100d4001e089842c44902588901d407506100d40b45c12001581d4a04291130806480000188583c29440900042c4509110142d1800080780d40518000d40c94a42c2442105480300c0f0071b41c0b080102c203184c0300d103da00f089000b260801805009203c0614021819003001103000e100e09a80050703010020b00150004d209100080e48002c01031600181401140c0300013200303641c82c50903641800d41c40440802041c0c2d8005072807142e6207400c4d60030b42c016042c81e40e40175100d40000380140303109603560b00490200620804c900004400944202c441181c600d180d42c9818000f82c110170b90044807085100813041c245403c080c0d0031a60103075500d6151600e4003140c0c444210035032400315040c030703091844010043d81c10001c40c144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 142481043 1250 142479793 142479811
    0xf0607141005091e060703091e0b0711160501120b090103050102090f010201110a080606070c061d0303070308010603050c09030a23070f060f09180b011d03060c0d1103 73
    0x32410305035903052070150701031302c10522a11041100520784c1d0000c190103030820ba107400c0106040c10f02e40791189481f0801c0049020414245c00ba0b84248540080c165000712310b941c89030b4250a01190003107458840d04100690841c1400104001551042b040c449c00e024111b200014009070b54000110400350a034400d65850b03401060f0090b9070b05c1c0240c100303041c17004240000c2000c03e90402034078035a070166414040601c411500050f0042e2078100c2118900c6904c403041e0006140c0303402018120310101c8a402c900c920b001120f00806050000c200c0740b0864141d2030307040680c5e02c0c102c4128050480104003805c1008140b00049250b141001600c0046100704d0340c2c60100d19105a00030214a550621240e80e07921080c005c200d0030525040c3c550a480a5203015468441d0080042ea060801e682c01501c40302410140c03111186800c0e030051544000990300e41d44d02c00c5884000807108051240e40d02d50503040040400c4501218200901e119002d8090202d86400680030080641d0022604480 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 142482293 1250 142481043 142481051
    0x504030207080c0402120c180d060f0c0912260d0203060f040203010f230616052505130f05040803010e06150906071b15080a0b0f06071410 61
    0x21907000384600898500c00b030314218240300346c20a02400c040e1000d4140180f5075000243c601791b90780401529920014090b00300d103039081ea24a0003000a1950b81000c4c0c2c1800c0ca42000c0081c7c01c0e03c200000ca003250b1600960440003c03003516612540344101c1e01208401c40300841d51204805280081d2800c503028050041e120310b002e800303100495200501541c40303944108014040ea120f190710010580d01c8404a060708114042515000502c0b81c0200c540c0c428004142000891420610000f20034407601c01d5074003080d1300041c02d2205c5142060400c01e02e448a85090156041020b1400c0d402e6050303000100b001000a80d00d0800c48e01d0944003034890f43c0001006018081da00382d096508101d00307850fa10450f4802d142d8041d2355015070090540304083c002070420500c000c1c000407942c004016287c000708155035070300a210080c0021000c00200e04008005a6000c3c000d118456094001502000880001c801084625481020129034101038400070074000c20b02084125a00e01040000003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 142483543 1250 142482293 142482299
    0x30b0a17010b0306040507170102130f090e06060a060e030304120b07080c07050a02091905010f06180e0103031b060c02010606110d171008011a0f09070903030c0c08010504030207 78
    0xa402e54403031900d0356000f940010240130002c2c030002144800c44820401d1a52000103444001e80a442480c1005400241500d80070600c008001d602c00c088a40c407010400c03c042200b1101034840d801104c0c80c543c0310584080030802c40b4040e543c082c0c03040e82c00400303503858a62540248030042c1c03ca14401e484420b00c0310200200c0c240c01501c115040003aa201c402d0030b1401654440e6030302c215a040c0240a12a800082031600c03803918140041202a0041441f06684440441c0c510780800c5c0303e500c000498a0501d10800009402c0041c1600d400240d6480c803603096450680c0d2000210300d14003120070941e8010703c0402c2c428400d4a20124107507002140c840e142850081c0300c6040c049007050035400400d201074400b90040f285075940c80304254080d20f00d03902c0e6124400d002604e40d10038103165080c410201070300e03a0084203240501408660b190000e212001c1400084c840449501c03010601c08503042c030110b80a50350420f200ea101e00c1051020340d0b142c50146081d2501603408a0150b40411018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 142484793 1250 142483543 142483589
    0x9030d050c03150904080f0a030b040222120804051e091e010b03090303070c02030309040c12060b030106020a0f06062309010e06030d03020d150e040516030819030b0a 73
    0x50a8000d004480300d0784e0394241515569240c4c41900c4001c0100380b00014807040050180e00308030f000243c014021074840003000051507103e0181c2e1804000f0a840e1100858083d6500626507a071a8002011310308180c208002d101c00300d0314501486007120300d20004040d040c1d8070a20031500c0b81d20300d00c443d640c1101e07e10680c404404010f070022402a2000d10400c10a142c0c00400d880d1300032410315104a40d850140086411481140d0f00d03581c01030300700410000465040000901c030b41c0180384041061035030310b40d14851280400c0c098080180c00c41070040021035a8556a140190f00501c030000301c007590392143c00e01c0780d41b1108010703c048001515149540c038186000c18010140546142c000d8500640000e490f200c4d4400a5000d05501003080c00303031a412640440340d000614000d08501a884804540b0303425800c0310101e40c9441841d5117600350070079032010b40040b01d40c41136496003000004200e444510b8002c5420004043e5140e049910650f41c822286005256078030544400148803103039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 142486043 1250 142484793 142484821
    0x30a020412120f030b01080406091401020406050909010506090102120a050405061917010515070501060806071e050901050319020705010903030b01020d090e06040e07080102030c04360509030d050c03 87
    0x280d0300a1505e01110210181d800c202090b0f070142d4400c60016915107107240c207040b00e10074600c0104003903101050100c0d0765a000340c0100750041003111603200e10b0381d0340c3c010005184100c0d4002c80c0180c02050fa00082c43d48481c1c05070600c10182c0c00e040d0b05140c0c41d94041070880e002401c1d5040d189154103244a105138020010700e200359034034055100190b04100219505903c0030340c01c01d02c0d00300300040410600c00294007000c00342c04404156511390401150050004600c440030b0365518040c00381040c00f40d4000e4003112010700701a100d8901790765500c520103002d04c4003084000c031501e400700880800a4000e226001005109403800212600f004000925291011a04030240480c51401740b144032070310140c00703900c150b089030041284900e0900990824105a205400642c000310502c0b2010012402510a6030058601003006001c1040c035002c204581340c88a010105441c40c00c4e1b40345400a401080d4001049012603140285100034a0120ba900f16100d4680d1034000c0140020341560b044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 142487293 1250 142486043 142486067
    0x813171905031312020313090e060f100605090d02180109050c040315020a1b0c03031e050307030c0e030a0c090b040507080f0604090b13060b030f12030a02041212 71
    0x341490940c9400303c840061807000f02006811800e216500204c514030030000c07100000d41e504c800d503281aa9076921132010f40164031100c03445000303100c001031400f000408031900c6080d401d0018141c1918281040d41e0950202446a821910b20701e83c04000d61182104103801c044410b090300c0c01c0e90715110391f203011030b5006014511000703010403080001c07403001844801c1103d90f01c0001a0b5400c014072082d42d54000700704280141c0c02042400310144010a030341d003000c0300d00984402203101c65081c01018494901800c40010400c2480494281c0e071080d4410001a0413505040e408885c4100002c5d1600c4131250f4206c401190055080c003001080e4010150300c180f041d1410f001c40e0900c15030241ca080300007044c2c12901201f60000600c65500c5400000840c1d800c103980d4074441c01d10301114420080c1d5058141c0f03110b0f00b0b000d0500d007907090008a41480c40c0c041c8015000e10074031000b000105074400703407618152940a01004c0343c900d4602400b980987e2140090104280301041c02403c2850418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 142488543 1250 142487293 142487297
    0x31801020309010c111c0c090c0509090103121713030905030f06071b0803040b04031805030607031112130c06020114040b0405031c060801060b03090d08131719 70
    0x220144100f40d800c01122849a98070100341d02c0c030709125001003552880300007440c44e0310341d0181c105a410700101d090414143c0f0f10300c21060005680510050313038075200304001c603504080e080300100b0104245483c11000c0a103545001c60141c940064440c46110066580640c07643d89820390b1400c054005140000070702055000e801c101440c010402e885850080ca4802801035208600e0051042c614007030280690100358640c903030400e400c01000c480c00c200d17401c40100c2d00d0000c0c0c204041e82292840c0080b42c0d030040040c02c00350340e2403800324054164002d01504e00107003440321004600e100c0003a9842101d5040801581a10302e062829034020658011000d43e403402c03030007d440d0803c03008460303030054011030f282c0e40585482c03609501e0740c80303014541c80008a070a1a12090b007099908010210313150b603030091003038540704c0800403824030080e80e00c85401d6000e0741e181a001401144450741c0000c0c0407442140025650700e5035907064030000101c06080e080050b02058081188883c02850718042c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 142489793 1250 142488543 142488547
    0x60e160c05070e060d060509031b01140c0a0302120c0702040c08070c17070f060509120414090709030c0e040506160215060a0512100b030307030504060c030e040e0318010203 76
    0x751911625603241d400b0b400341d050049000100552104090a9201503000c0c40400452038030012140c0c6a420505802140c91050141c0d40c3d95503005010301060749003989210b50060320340c00111100c560004044505142e000d114040c910805850464810f400988101c0d46d1140c0a00c100f001f00c615003018141440346074014404450b52190501405540c0f004041c2c8454031108400341c00ea01846100500003503c1406040401c8040c1d0801d0f07025030151411528a0900004465094000d5010f0316400306c21441c1891050b04d4512900d54000302103041c14001c0544a0300c0b05071a0803015000884404800b1082c0410460100100c0e41c0c088034001241212a07203020000791104035001750b02c00b01d140c0c03002c003041c100d5031a0308102d4024000201b10341e45c1114501e0219850301c80da4103840035401e240ca1700c2c84103a404e001c02180c220a5066662074642030401f1300a42e401c80300d100c02902003003031070100711718162038502c18038014030a0034005607280c0e1180700107424040f4036031b40103078115001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 142491043 1250 142489793 142489817
    0x30d2d021e011506080402181303020714010e060306040e0105090f0708070509010306230a0e0601120c12151103010302030d1419020a020a0b0a0f05091005030901090204060e16 77
    0x1041c0700443c103403403540c0703070502c15a140c0b030001030050240f00da598405003128100f0b01c600444005401c8a0040c4203800352401d10f96544140f03014002d60030340b10340c0880c5e81d0b02c850038014680320004543c007100080000070154006140b1508686044526030b4140d800382107840c882040c100040030040180400900c441400e00c0041100f195062100030622602c03161000c2004008181c8543c2003810a14556030601d05002894040c0001c1d2120130032900035500045001e500b580c0e800096540c2004c800910300786452240246c00300014016100d00408000c0710041641074050900c100054094607601d80d4150700406007480a8614140306100910180c03480c1c01000400396070000c02101c604040020741c0c1a016401c0040190300258004480e96010803950780c1d80003d807820241540e1a640800c020103001da03403503c291a0002c0c0d11850644000c01c41034400d000075544590000000300301c00b02998086000d88032a600003600154110080061450014058041e045483c4c6060483d07404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 142492293 1250 142491043 142491071
    0x712020a02190f150c060c0917030915070f0503030a02130b07050d11010b1903032a060f0612050d03051b07020f060408030309011505040605030d2d021e01 68
    0x880b0f13200c0e0b06030450901201c0f1590303e01488003110002e801c800240030b21044141d00502c2d0a01130301035600e205803420399503d0390741c0000041e2030301c45070003a016080359000801e4410540e00521011140c80c8120b8002c480040c40a101850280300014400b6031654032019600c068800540c0086000b81420b002040109000080c2d80c004c0d02030a003011445000c0c4440c0f014090310850745013030780003198013602c000308211010103003040320b0296403100c1303500b1000210300c0050b12002644081c000f20380c41641022a10590008840400c0004c000a109555810400c141182c191041d1050b800c0008011b20701500f42c002c140e0b00409404c080c1100315130307441d8401c2c0c1324002d02c000a4098090071441050a0301d03140100c80c0908a540c048a46900c2c10010b464003904442188031a1030006200001d101d0070f05028070029142d004000e40040381900304100d0341058289041c802a06203110f1001000f00743c2501c041c0822042da000c0c103000d11406840591000b61149299401e82c500000c40450308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 142493543 1250 142492293 142492319
    0x51b0901051b12280212070b0718080102070311010501051c0c0302210c010915030203070207050a080c010216030b040b18030a0305070e0901290712020a0219 69
    0x80e04001180d0503a24511101902d000404807112681c1e5400203609011035a0303a01c042200000d0b4041d0300070441c01d840381c0403a207071224902c5110110b2421f100780310001e4204002d80c3c1d03008526292155904001c0340c0307081d080c0c60b810381c4400f0303059500085a20526500001141d180603558000340304d03551504000c14448241c4030300c645e0302512104403060030400c09081c10030065400510030f07114080c04440c440fa001c0b054070340051a078070403850181c01d20350090406108944502c05894000c1e0810b41066000e5400180300b04118020707050302084640c1c81c20805406008a07400502000d14032000280c40c0a019540e04082800605c80070000981c102d03003036036445a4000c920003100d84403400701d80d00c2d880b40d1289500d140c3c08040385030403010754558003144c8207041c541e40e0b0f02184e03c60b09050110290080c0a0f10308900c1c0d07001c0d20315186000904444c894491114601850111261100c3d1660407241d440d0754010703040702da880c406500e081a0103451041c06a0f84041395903142001091902c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 142494793 1250 142493543 142493557
    0x501020613060207080a0305090f0c09060609040902030d0306080705120d0f02030f0708190e0f100c051506090916031101050c010f051b070309121410051b090105 71
    0x15018181c100c400c110b2660141c07240b566205400540b10301d103040d0040d000c1d060031901c991092080c1d0326818014440001c04246d070000242400c8080d45440c0240311041c3d0007121790f641c0150b141c001b00310042e02c04101d081440005580c2c0000c0d040e0805e2505818018103501061140b020690146803401c400701c2d1001e080c6d011400c0180e19503d000700280d0460250411900155001003250130907c0341120041142c4840c11013600905881c000c03055480322501c0041540000c44100341049034140032140111544003410590030f9032806a030741d9864140c1d16160704503050200c8052000d1400d110010a400185030300c0603003808000411034000d00d2046100c050010b040d0600600500d902400480d205442440004e200a040384082c490207003c0c180c4020944038030a03101c4080c1000d0301e80603a0743e0241e01d0342c0c507941418034001c444001030000d0038041d1030340368000300d02c40c0007002c0800001e070486030360390000f0440f442c1c0400505842c22030800111100f0108104801c40e603a4000129401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 142496043 1250 142494793 142494811
    0x23070801060e030c130b0d0804090f090803270313050406050d021e040b0406080a03080f16050714010501060206090606040203010b04051e12010b040506060903030403230a030f02061005010206 84
    0x280000d82c0404001b0b014400c2482e41c1101150040c00c082c070402c07000600030740f00c6482040c0710394100d81c80701c81e0490f5400c4201905418050001c1040900320b1240c29049058403582640103c0d005440703c1d040d503220a9041900a0415104002030700705402800002c11080b5907034900700c1d5064001c00c04242d041c542c10303000b07480100c4020356a40e845074800740f540c4c000030b0300420210380c96001d400e0340c44050503400d4021802c0e0400154003002c2e08961a4481e0b03038840d1051013440b00000c010740d519041528207ca08104100c0003c105003000d2041c00e0003031080d90300604240c10a54005400d00b140981500e0146004100500164102600f12400c40d44180d64035211a038500e1502984e06498015907036005881d00c0d400405824150040b004a61044800b04019200c6c003081050350301c100034030180c068000744001c00101d1160f140012515036551680c1443e800100c01450070004411012408500400300b550321442e4104611584070401c0302a6196031410540041c0d5208001091800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 142497293 1250 142496043 142496059
    0x3020d0c0318030803040303140c09010c0f060504050105010e160504060e060706050f09190c140a0e01030507030b0a0504030e1507060f060501020f2a0423070801060e030c 75
    0x1018070a15611120000c0d40441028054603444c24000c10350041e10190300007400c0c02400700c89822403001003805800085507107441c0074a60300c0151038101a5032070681ea180911608000410310074044e591040713209000004540d81004446100000d01805d103109941d07420520b4400107070080200c80a4a1a50030400f40c603952000000d54940b1900c0c2e00144441c0c101070502901465803d00540102443c0e0240c40400c04502c000010000381c6c00030160000002c62020031035144190101c480e81200070705a07070322054407054204040b020aa02c02c58451b405207100700140041116a55005a06900c05001a080940b002480602d8001c4898419104c00301840d907504041d60450782030b1580a54184000c5060301388081c0204894400e040c0580030715403100c808114003003011001445408d00d40b0004000702d603600030210440141c0300d604182c0e40c9211410100341541a002c03140b640c20220442440d024070300030318580069020100388800403072a0705003680c01040c4409000019107a1301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 142498543 1250 142497293 142497317
    0x5010906051204081810020c0109050609060d1d030711030105130506061002010e150114030303040c1e0f0b0706060b04080d05030405190f06050903041503020c0708010f06030b1303020d 81
    0x170f00c0340e2810001540300c0d5001681032807440e008039140000314000d880b0292041d0f03481040c0002842484089544140c04204c2c00e2200c0041d94004603051580d000301e886e40d2001416850301c0d40e03001c00030581c1c00d207032102c81581c06440c09024480d840030f0402c0040b01d1042055443e10303030301c1001406051140041e6100414031074400d60110300d840c03540030100da0a001c0902c1e10000580028020342c010380c030701c86020792a607003800800c503802294082e1140b1045c515104c449941560028085018000c00d02d0000400702d0000104c48003a0030030010790342e17644220745030840c2220020351019101c49418001040180404100030020303010900305180c1d641e130780b850040c0c03e0a584140c002c48070b542c0040301006021000d441b1404461241504100907100e40704413580d40e005a1203151011510401c074139400510035000f0f4031803007010508840c0001c3e00c8d1a409400d5401b9003501c4180665100410410301483c41c1700b0a0f08900f2524000c0750f0a07410ba10001c3d103c000100812041c01409007100b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 142499793 1250 142498543 142498567
    0x106120c06230409020901080a09030c0b15100801050102010b030706210e0601120203102f28030f06050d03030b0d05060106080a0b030c031005070311070501060501090605120408 78
    0x1d070311503051005160f40d200e4036159444000c3d0400040c103030001c3e210000281d41405944201804075170135840d240e00c110420780d514801410002e05180803917110b52500c0066403a00801203480c511561200001581403030002401c4990300b182030b034420343c000c40b001c00501c0c1d0402025070b40c00070001003100d01e001040344208003905900c040030701640b06013030000911003081d41380e020200703108138103907a01d40c40a5407495044c0c2d458400b10010f0b00003e03041128103803d5002341d84294049002e40c280c100000c5200c60311001c074a04991505c01c0c0c6018090503d6a5410300c294582c0f0440da02040000d90f0611005c107500c3d61560800030245aa0b8241c3c501059841c17200075101541c1c45000c442042d038403030400404070740e000c0d1142e014585c10a00480030034038020545201c2c00c00c1c003400030100b10041100b00b4001d050040d01c090141aa6062203e40001c0110010603050f4007400c0041503003864200010a00034940d0f00c0b040070080e080c008800341d914070400190300250003929254585000e0012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 142501043 1250 142499793 142499837
    0x20d031a0a0b0d06080a050c010906051c0207020f0405131101090e010905100e070e01180302101404090606020c120105010f03060f1104180b0103050603030a030207170a020f0106120c06 81
    0xa160340300e1030711841b007088000524107594200a82c1c644000c999194401e039a01d01540d010740483c40e05070606144907111541c060b05055000520a001350420a00454103c0d0360070794a01c0c4042e2480c90041081c041c2d0403103190720101d03080c0b0b40714200030315005201402c1030041c0110901c1e151a600482e01e80e0700f5054400e009402d102050b01d02ea410690710103001c0c000000e03000d81c0840d41c040e0503583d08501810441c000c59802819008810780c1040c1c0440b2110005940401200410700c0040ba041c5050320489024264a40040004100203400c01600036180c0b000d40045070b04003001803184140c00c01d1160300b00c0754000d4001c141c42d54581081f5004d00440246003000700b40209002502c881e086c11845009591131b202005101d031410011400d40b001180c015806070f00400100524070710a50003050403900a000b110070340f0341104403185055002d030f5035030b17070040e4042c80300039844031001e101c2c100c02801020500d5040c0319032550b440401070b0003480b803030061000900c13040204213002c001e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 142502293 1250 142501043 142501049
    0x8060f09060a08011506080105031f0207061d0c03251701020705061006031a091b1201031b0806010f0303050a0e0310020d0605010e130506011101050403020d031a0a0b0d06 75
    0xe114404003488081174045040c03040c0400141d003907000043c14180401c5505400c030380380248152100d1004800380c0a50300405080b5030080d0f8030070343d10305440000d031ba0405040c04000301810015204004252404d00130040f1000303003505404000010b00c41000c0000200c03400c01007081055400c00b0700701c90080c0140e03000a4068041c4408100c600182000b060040c0d4400391010003046074880080b02c40c00e0207014506402944050104048100140d0429581d09101c0000e900d0a0880420005943c2003a88100c411606a0020000050f500d003162005851000c00404440d80f51148100c0310000d54400a81030140015101170480c8c451244841d01721805030444242524a0744940001d5009a10041e420b074a00300b0045034542c4503101c0340c00401801403804c5d099042400340c0c4002040c000d0b02481c14030031304c1411075204960a0080510660094025210000000d1409419140760500300206208070302103a46c00c9a030340a54403c142c4011762030f103039103441c02d50384103800505a0350 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 142503543 1250 142502293 142502309
    0x2d04020919091b0821130801020f1b0a11040510080f070303020d210c0c0c0b250b1501030b12030316020606010903110307031505040b0708060f09060a 66
    0x100e958070034004141c003000c01e992060700000c0803442e03440113140d4880807450042e00c1980820000d98a40361005000f0300031007603004c81001c4078251307120344503400c90303000b40c851040c04580814000071038112b10403400329800355800980500c129950325008680d0035040d24031700c5151f0b46d0700460303c1c141c0b00c030054501074100e102c201c94492281d02c4280ea0b45040e10b20084006109081000802c9441403001170194405150301c07054042208040d40301404c0342618140820006203181004140c0102e40310004003040d142091381c6029000d05807e03841503407200b11010904440e50003002505c6140350580c003082c4c01d0700e201e20440031140100c0181000080c0380e50702480601070b0b05140c1d28040000c50141030800d4400c07036003100c0d440003a030700e401084a0007400f0641a500c100049001c006c0d80e261244402015651b5580c1c036995070f841c02007400548140300d60b030313504108010015080b0364250000c000e81440c0403146805000141c1c2c135076606900c240507100700c9010031400c0d180e034400100075060300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 142504793 1250 142503543 142503551
    0x6090b04030c02041a010905060d0e0d09170d0504060c021305090c0108060d0c1206021303080405011b2301110a0e210a030509030c1005032d04020919 66
    0xe414000c000d104502030aa1041e4604501c0101c03204460742c3c0c0c0c082a0b00c041e1544c00285141108002007500550b00d1040401d460b8000030f1000c500c00d102e05120304d0141e441d80308800c0c0c10320306400c1310303c006660100c1040e40224190845681c20005580071610540382c0800c6002d01840030a9104e00100d4a5010481c20a8103004d5401ca01103190407619600380d903000ba86d03680d8103081050003100d540f4068590409545c040c4213188080282c0003481e406100050724000284071940c0c03910015501c242c2e5504004034003804150b83c4640c03001007450601440100111035038603a10042c09119222064140880c900045800000c1d0019000321a008010701c3e2681e440c0800900001c2c0d4030058284914901255040d981d915221105403091560004050501c4c20b95419241076010240d844d0741841503c80c0845569641c40000005000b0b83d655551a42403406d00c1428403a0390004803000008170094981e8104150041254400d070100d8025155072110400c078980740401c0380d0101c00407410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 142506043 1250 142504793 142504801
    0x50d0c03050a180b04060504022e0932010215010b12010f0803190908030309070602060105030d1e03060b03150306070c050d0e01090902040305010509010c110d050706090b 75
    0x503844203124a0340c5000c00d00a50401065070512183c4002e0010704640360302c3c0100700440c045506c040d0b806403000d8256804907602a81003506480d400001c4007080d030040c9081402e2039440030003107000341000c00c40046005210700c40045000c503411000d8010401001e11210540e10801129460182c9480014407958403031a40790720b183d05c40305104600c49100c0e000029400445007000f011a10080041c50400b515480c2c0302c0320035000461004104005401c01054620f400d04c0198024488a80101b81d02032078444040d041c001c050348810f01ca50407148941d4070780d940141e5101492000c203a02c030b80a40401100550050200e03420500e140307140401080f1a603040b01032b800101d50380440464403166a084001c1320f5200900b00c009045400440c42400d03524044c0245003501074050500e00040f507158100351040340c220b42d0050310169113840900044070070a1060310005051440d122803a01c18000c1c185035509401e003d01010001c000622006000032a808510340b5540308228085600f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 142507293 1250 142506043 142506047
    0x904020114121f03020303041e0905070e09070e060f07060e060718080304140d0201090308030a0f0e030a08010b0a0c17040e0709180c121814011103060d03050d0c 71
    0x1040781c540e92035045030b80d072001d00350f04440c4180d01100e90040046d032802c0d00740600d940400480302c01030108101c855601040566aa006a9201b90042d0361440050703041801000a0784601620710002d0242c582c0d0b20440f42d481c0d2204551440500c8500b1503a80c01c003034a050b4000703200001250781e83d80628420300c0505503000e8401c440b841301048c281d0700c81d1911165110788910580c460700e40d005c09048201d038184d0519124020b20b283c01410305403205940c90710f1700185540304944000d402035507284402030110040c85125440d103203190040d800c05890f4400900340c280c042c003880090601c040380602603244a81c02d5400d00a0f808034002c0758a80c00104034403d1500b05000f040d0300110707007400080c5a00c0c4110007440848501c404d5111854084540c0c80340142081c003514001c0180208500e00a03e1860190440280c0300740081c0e03030710111302d003004003ca00505c440d4110030f074100302e2240c004145590071307a500004112200407000d89680750646091144444400c24681030403200c8074030076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 142508543 1250 142507293 142507327
    0x40c020a020102060907081b13060303090f0b0f0901200312040605011e031403090a080c010f050748090e0c22090b040c080d0306140904020114 63
    0x510070303021241c0584031700c4c0c0e03501d850b42c42d1401502c8182c1d10801c075031484124010f8202d850b0130000f90440013070f498100d1844041d2155504142d000c100701e54410000b4020010010008000341c102090811701500c3c403510703040c410480c5030343c100036281c0b501d100d140f003490900010010170341d4212580e27242d0400e01d5101c005001c071000d0b641c4034640300002a22244080c0e50b1031051001400a10040703065940c0c0e400c282d22241000c00300f0f40b0040c03102c000d1645402c55040040c0209100034003152081c070000421a0400a02c4942044000d000740d0f07002a04409441e110800c108408400703100306411060b503006030f5280300c08040300e140600c1a081081d4110504242c600a0000380076460507810a182c0d2100c0540e482d0b500030607551000350707094561800c03000b0b0306101000c000c216180144c480711280c07a030a403000c2d00d00350752140c2c0c1001908810131980500360202d081c00d2001a1512020304280110001008c0c00303418540b000408581c410302c120140e8018807190a1b48410223211000315030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 142509793 1250 142508543 142508563
    0x605040602090d0b041a040f061d1608060a0204120f170a0c050607020606061c0b040c0512010e061c11130c0917031b010b03060103060f050a050412030218040c02 71
    0x1140c100848100882161441d21f1140350481807440145009a54020040101c411400c0c49a000c4e07011070036605070309210384003480328901500c820103070908000302d04180c800f070300c8104440d20400040156901262503501416041140086804050b0030503c40303540003252074500708507002406105546d045495000030900407404c1325442d03590180242d0b511501075a600790b01075020320110070345c0154081001c242400e142d00114640910781c3c08101a00c8214010001003180815003c070b248800d0b8507214010302503950f40084504100001c0f510000200c2803140c24440100e01000c1408800c079640b5a1004018045040b070350405045000242003c078200000120550b00008000120099400041c4a280091880e000e40030002d1001c000c104490f070111035481380e1502a060350107006142c000c1d0302401e000320b04a0303140402c2008541d0004e1802c4d480c245041e00784004980c0c003000140f080e0409040040c1e481c04107060f102c00300307041d00300c04c07035405800c10003a0345c5480d1780402c0c05914 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 142511043 1250 142509793 142509803
    0x50d121103070605250e040e07030c03260906040302280801020415030e07140d05030c01020a09060512010302040b150309030a0e060309060c07031214061504030209040605040602090d0b04 82
    0x11845c1c0314900c0f14903480300300030005036801d442e0f011280341030b601c03400c1040006400c46600540ea035860640e40c080584c030070355080a02600d850f141c815550030244240c005d40744040d140060042c0080c4082c00b403800064050015401404070410605103620800300401810f4400d2070741e1034591324081e500030302583c17540f4210510400000b030f0083c0100d4441d07003034020182c04902d00303141c0e00d42e07c032503050400c903a4040751449001001c10000c3c00206480c0c1e503076900169565041c4d43d005019042241d04c5901009800c11a400c8402c2407407207a00e041d240d04890100780e09441c1000520030402408840704e41d0400001480301c04140000140340c8030019885030b60203609420100700d1030b40002c6903a0400c64026400203040010014010900140303c1e040001d90310078083c05402c00c03a281c80c4141000c0324202c00a00100346044d540080d0040c11081c034080c034090a40e40492000c031000f51008103c152980c02107010015160103844004c107001e000c400a822190502c001228416101529 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 142512293 1250 142511043 142511071
    0x903011e1b05070609051c051201060f080a0e1204060c020f0612010605071506090b0102070504051506160f030c03080c030f0c0d0f0e0c1306050d121103070605 70
    0x40803140001c00c03207038000070b03450b5541000807503100c0d2006000c0a00d811038040c003600001c4604104101700c000d4440c481a80c404e5100d48418580c80240710b03041e009003040c000c41c1c6020050599004010a070700c10300c44280840d1301c11420f1401441c0550200100745414000300303000c540300e41e1291300c512565000b19510b121003111a014030800e40304110340d140031001104014845c09000b00e004141140c13080c0c110346208a500a40720307045a81982050542940354035080c2c7c45582c0c10007480d00a460100c40801c00e5040a81d514200c80303940048250190704007184400c4000303200100100007680200d8610b969a4441c40e000f012000880000c5002c0740030079010410080c070000c00c0d28440c0210b60751a080c0c46d22060703083c1140e50410b00c1e0711540c3e144c846034650300b0b5440030f002c2c42004655803001481600161000c0060420700790b550400f280c1d180c0001080241d452015070401181c104000e080301002410741100d03007280448010f101d905c00096071000b0040182e01c024458040300c45025 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 142513543 1250 142512293 142512311
    0xd020a0c02030706170f040f031d09150909010516031a04020415020d090e06010e0d050f01020405030d020a0b0c0c100501061805060a08010b0903032503020705120a06020d020903011e 80
    0x2044c400320031f0b28040c10750101004803900190050301000780e404484115551440d044000003000304501300d510720b1042d240110000081d0900d0000540c025000d28001d20407450310580c03040b10200000103504c2055111038281007142c1240002130011500a403041d95610f44a2245d02c0540d079484034240c00502c18252580350181c032500011040e01c0c1e0b41d8502d56918ac03500d000445581210040590340421280940c1002400401c202c02080010900150f180c620313140c10507092081c0c5400c150305540104060100040c21070a9959001c03070308070341c034070f8030b441961040c540307010400140c0300d1529240800115203d90030400907842802202c19119005840b1800d010b214040d64007003030702098006006101181c1c4040282984030746c0030b02241d082c103800c4030959a600b042200755020074422410130006142e0f0512010010301000d0350390403a140d8176070604c9660ba01030804042c0445034040345203403008003039070121940c00300000c0081c000100030220f203006a4101e98a415003c5207000c9480e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 142514793 1250 142513543 142513561
    0x906070f050703050a0f0306170a02031006080c060309010e0604050c03070b0403050d0c152c0a03020316020d14031207182102030106060c05070803030c0d020a0c0203070617 76
    0x68100d039030f06640d05818000ba10303006480d0040d00c3d65506003030507225000481d04460058088600044c0301c401015201d501e4018107003400c1042e0100c50030386041440500409100194108000b002510b100e070f600d9030b41022081c01020007003c03c0c0d10b01d005020501050000001c0d40e00c919020031420745d404d1503550031060010344110b2000410681090048400950140c07540400040c01801200200402540c8001c100ca103c451150100881140400d414504030b10110780c46c140e40310b004042c0d050003510040d6030381c000d1014018411a40300303800000c5480340022000741e41d0b032080ca20190740401792580c684030307084550768180e00030700351000521180c800c4600e02c4160a458075402d8100c5d080121003c0b5500c2000c00119202e080a18a00d0058909108003801401a0b644240700311074245040c50500307507940d11075041c591050040c4043d122100b800c8480c59004020010b07640d408483c0162050b280c107040c0607500d0f004502001400340d8102d0340703100180020b55844080c650b200550 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 142516043 1250 142514793 142514797
    0x209010e04030f05130909050f030d14060d020a0b1b070b0901030513030e06070201020111121902070812040204090501060905060a060c0c06030c050d0f06090f02090f060904140906070f05 82
    0xc1720901c00000c04208440ca01d95844032615601910680f40b410768030710300c018519884042c0701d50038a80c0c0c0703201c0d0403084d034003502c800c41c1c0004c1c04543e03240511503280c0005840400c2c502850608010000e01103680c180c1011842a9140c990002c5d11800e035590582000315800c80200035004c6818480040e910207900c40302c0300070a90b810345800e148240e90100f80100d40c1c21040e03040b815036580c1c00281c0405040030300a0281c2030841c0024503003a02d8280030b55050f903034034070302c4206140e4014844a0000b42c604e0040d2400e00110801608481c2d5a5000090107080d10740e0024050b0b5190603408500f400454010510803001038900d6040719903039243c226403624034400042c0c00310140910034010a40310b508440c09062080c5880e03801c01c0e00c0300000104940208407003c00b22507490703204000d6010240502825a083c0d00d00850400c1d03d03510104d04903030000d141640c400d03840020f04140d25566a4005402c10540b125907840e00e01d82019140e0359928241d90780c0c004901c400d500941901c1c49030003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 142517293 1250 142516043 142516057
    0x10c0f081006120b03062d0c030a15051905010e030a0203030f07050109020306010e09100218100306081002031e13030318080309030a0809010b0102280209010e04030f05 74
    0x41c000721034500d402c20840395611544082200680c40740590341d95554104541030103503403a00f0b07280d0040d442c9082c903542c06680d030b4100711145064440800000a07803420a5070b40c00709101c0c1000c50b450b40c50820780304001c05150050f80d440219035086091098a0340003507400d60300e081e01ea2070302c000380f04410541e44000b06d0400039030543c020000d8800030f500100c0501a014810300c000f0880d05043e0740000d04000c4241c01144210640c9000c2045c064000c00210485c1202600110b20f00b0030f00c40d4071943d260003c000720500404540250010741c0e4405d501c401c006121400942c4c0300c4075000c1030400007a610075039201d0b1162a403e40942a03410420442a00603140183d0000400c1d01998003a80035100400d02e0528540000c1c0340c4402081c0344000071845084544d020f9a59a0782010000d07040210191071600103138034050091000e40d8001401c075082c189510905001a9502100b9040302c040c0f08500035000312060000043e40000e0044140c0190b1081d1a002c44c958500c0808840c0f500030b0003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 142518543 1250 142517293 142517311
    0xc0105040513090606091d01051509041202070b0a0c050c0406050918010b041d1618020f0c0a03030b130c0c0b04050f06070203030a1d03030a02090a17010c0f08 70
    0xd05100e42e5030316a5200303c8100c3d22404010480343e82e0b440382101104e0034540c030480c07109050400118980428440c45910005841d8400410200c82c400325140c41070007031009241200722004241014004c1022030000c09214005a564401032540100020030b510022600707445040c5210740e251825000354010340d0b6000e002d505c2240e50341d00f18094500010000d003d080d55840141e60417645803070241c1e0900c03d0031004d0f16510b11254080b010b1401c02c1c80c0040d8080c14400704000d100381032840d03800c0c050035900b00c40302503241d480c0b000180c803a0340b20b240c00548242c410542d02c6c030109901600101a80007045488100300c100441c131b10025600d401015400046114484500044c92018000c1e0007600034001c40d55803001070388a40385000340540e00c4402590000c400c210041c40c40d070140650440200e80042520313182004042d50f00e01000e01800392080c1c0100c0d0900c001e03243e40d8545001820440c104104005243c40381038006c20003c0c5046001a02400381461028015840e10b402030b00b40e8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 142519793 1250 142518543 142518559
    0xc01020f070e0f071106010905070e120604150f150914010f0614090607030806090c0405010c1101020c13060617070507170d060305010501090e0d080708041b0303110c01050405 77
    0x181d211003d8985004040078103002094011004406080008501038000340c0340000e1075003044040513000700e061b5070250744921400e615903060300801052032900071340d110030000c00c0311928040d40c0001d4180503401c4100f49182440e103414450b07001132188100e8184000812100b030076540f100600b00c600f402001c840c0c0101d074004000f554869449146107124101a89041c4000d100c000351440e4080c03081a800100350034280195494074225154000c24071035800d9190602d0003002030503041c0401000741000c94078215480b42d9034020300009890680060203080d60380c1c1c0c88012100102032a0003541c00050180c07044100640000703008600a040540fa06824800c00b030380c42110200c100f20346103000001c10300001c00c0d061058020741018521400011600c1d6061107203602c104c840703200070500d555200400c59000a41c01c140c0f401c3c4c0041c410701c0c1c205526a00c1d8207000c90360b0484081000588500c47c0c5001050551141600400309120030584041c03a1201c0011149030003140034041e403010103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 142521043 1250 142519793 142519801
    0x501030c14180112050106091509050a06030609050307030207091406060a0e03030f0a0e030c090105060c0330060d12030b01030e030a0e01180806071d0d050c01020f070e 74
    0x1001c0701240309500400000d40110301c01040072500c2d00a910004040b06002510000c00c2000c1c0100d5010b031204040c00c00c28034800b0402d2688980044c07080010746640c0b00701080348801e280e0082401f56401080034032146296182541d502e43c0320000980c0103010f0f000011440050501407070300c0c1c1c16220321310b0072001d03191407040101c2c0d0790010890324180b0904203003080c40354034180080c0400c190032618160301c41035a154050003084c1490302280c4a43c000034401051a03803a5101e06042d0340c070079985113855a0340e20308454036511403480750b140700446118111103d1940c0418407601811313801814045a120b03103050091100720395000501050010640f415094846d41c401c05000b401490301245107074280c00c6481c11035010414441c00502665901a2135580002800034540d68050802000782e10304042c03070791a60006403000007040007a10849098800110011101e840c2c0140b48429801161400e02c2e614400443d9003405402184c0701224000001315100e411107165615000e65542c07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 142522293 1250 142521043 142521059
    0xa1809050112030e18180d030b0310020702060d14012301080c030a090b0a090c120f030815060c06010305190201020604060e070f030c050a21020108190e03090909010501030c 76
    0x41c844c9583c11400b0024030510701ca483c80d250781c2c0110301c4800d8103041c8542c1040e5079410303d50103202402c185070a0141030810b54400041210010b244c003000140c0f00c2c0803610002e070b0542300c1c2001c03100c04a07003004030781044244220503645c100c80800d441c8241c0040403032400f90034100e4400310309022541c0b004c00946401d024400440c0d00074441900051034008079560907018400c1540c4907940940e40e29801070400081d52144006080e03100541d040000a81d0b40d852604000c0324001410002c8580c003041035a1070100c100c0003c04001022242c80d80c1c1e40380980d03035440000b44000e581500c54020300851451005000340c03c000c2d010390180c00181c0d01c0380c507120090710034002c0d0801144541100000d0011a0f08079a00155100e1015005654648020403070740c4900398000040c28182420030200c40c9800e1002541e5090342030900c040c081c1e8600f103084620381103604902d205107050174810407142d1004001820b0ba100308459110f41034039513004880c02c07203c00f400010a40300c901c000174040c801c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 142523543 1250 142522293 142522307
    0xa0909060f150305282309030403030c031403011212080601170c040b12041b0501090905100b041701140609010501080c0702100914030616051c020a180905011203 71
    0x140745c501d1540c100742c2501d40882d840261141c54a08420b6888210001d0001070b8a031170340c0c1800c0008010801c904050182603103d2045200040900c85002180410140181003140402c600c1480b00c0e5120340e960580107005036078502c0110fa640b00e1004074140583d000d81442d5009440c180c0d10000404914902041d1401c17006d080c4121001c0c0a000000d520103d940c02082c41c50300c0c09980c0b001c5410649085881c01e007403c94032035036034049a4030034000381c2d07441081041111100d10011400e030300ca410480c5044003060b0012403040c0000107001c222000c910450344040500c4900030800307072a03111601b0078407a20640358950b00000e00c41c010811588543c615640106401900c14a0f02005a00141c1c00081d442844404280101d000300310484203107202c40c4141006030046c140d5460700070034510403490450750340000e002010800c1a01e10980710303050210501d44030811940c84191160151003081400d84000300740003845008241c1c1b82060280b2412644400a10340c010f15281c2d40c1600d940f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 142524793 1250 142523543 142523551
    0x1061e08161e0c0b070903080322020306160f03020913090c0b1804060b0a02060417090604030605061f0e0103110909070903031d030c09040305040b0a0909060f150305 73
    0x10002000c480b00c2c1450016100641408540300d000d030702d03030071441c2c56021810014030003800c0c080107400810210b5440e004a950000001c503103215010141d518211040c101c1450103501441201c0401038141034000c51003d074041103803180351101d00b075450102c09a2140e03609a903001082c5800700b001c0da0510b80c004410341c030700c1002071800050f2501d81170445600022142000c0304030200e5007010509183c451940070b006e04e0000b0516280540760301030f50f5103002034002484d000c0c6200340c0a8445444070162951040010800f560301c981d42d0401d43c020380380582d0907511134110182d402d618901c0192007840050540d840313580c0780710303103178001034000307203c92084c10050540800408407a0354503032071020b102e0f114030b440f025249030841c100100740310082c0d0480d02c040011040c00480035500050181008102101c40110035a180d1030211018000c503484144084008603000c10416007015040301541e400020400c211a0741b43c49001d10001e00e0320841501000f1403503505083d80c401d030001584 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 142526043 1250 142524793 142524797
    0x801060501170703020f0c0705010f0302120f09030d09030302070b070c0308040611040f0902030702010b1203040b0c0f03191b080f18030607030f1a0307060f03060801050f01061e0816 80
    0x41446e16080e40143c1c0d44004001d200940240700e0a12540da042144000e028240c7c0c82c00310300f08010490701d2010b0040140100798800c8a0380000303010310708108202c4800c9903420400307101403001d500d005000394108240c00c032105840c840004845078494566521410f030503540702e0302e042e2542d4681e44020722220404000c6641c00b0080420150311341d0080b0001000401401a940d02c2c5c4120000e0848110a100d203102d422000c803200d08810001080c3d40640e000800341550392500c58414501c2d0007080310321209180004a90914459412000004907448544810910901081c001022029411001414404148509501c0024050240240c4490107107041b5a16510340c0000389094400c50310f660020307880e400711048155440c041d0a01c02000c2c8a0041c03400000200003c0d1109118094441000650845100002c0c07081c1c101e80c0c010800c020081003141086070082c11445001d000e070030040b98200705d816110f400c44800080c0d00c1c00a69403a4102034864400b01c4500070101107110003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 142527293 1250 142526043 142526047
    0x1602010c060b0d0f0501050a09021e0103062c0c3402030a0c0f060512130c120c05041406030c060c1509030304020a06090e01051309050d1701080106050117070302 71
    0x10b0a8441280314985207005154035284013509242c42400d481d0000c2400c01502d0805442e4401616450110007007040c1001c980169104054012001414150301881c1074658003040011080d044c003ca001010310444003040c1680d543e41001001c44c030400d4503004021002585482100d21a40d1000e010740f01e00c0703904055102602d8000074908040e0410560388820020300401115840d514204010120360400c1820b201d50902240d044040040036030200c400d03484400d43c2000103141c00c82c0007034408400c100044903070506100c03404000030300509014915010f8a01036071400c03a00b1039446201c00034020b00741c0c10780010520003640c0140106d007001e44141d0b00c125881e8803a030003109e40f0420805000315100d01e0507004100d0f0124041d8441c07405e00c404004148880882e6100c0581541d009460f001e50344450700c90400c00815460001618034007441d1b400800c411743c010022004e80181c01503001c442c3e41c0302d106c0c1500300d410038411140400c0d400c1000c14035140b0443c00380c81d44410345080040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 142528543 1250 142527293 142527311
    0x1050403050115050a0f0f0e1003050318090f040222110c1b0103200a05090a0e060415080a021c05011b08100b07030e03070b0406050705121602010c06 66
    0x90a41c1c40c00710030070009100e896810721041c10f116481e0001043c6208201c6d42e01460031182c00e850401c00c1c00380806800d040f41c0021400c9600f00e00b10401943c0c0501101c0d80ca00f20f4820800003182c0140da1980703e0381d1a0400b051000d030000e0344031400349400401400a25686840810b00d00880f24054100a81c0700c48804410140400241510701c1103074000c2c0003001507a44505004080c120f40c0c103411b1500d40042c3c48489030000c900e8011003550a600190b450004902c01c3d507403801080450b80d400070000c00041044a41010309a00a0106840c14040e560058400801c1d42c0e40c180140781c4142d10280010001d440c140c5140d4414840c1031504444000b42030303c40c1400e5843c83c0403802502c01650b5013640c2c0050384000c003254040038407180f51b030a10703040c03003164040e41c03280d404082c080000c500140ea40a80e028060b41000700713810312116641e40e41c2d130403000e000d0744c0000b4010340f00c42c0218235a1108941d001c4003214644c40c8a01340a042d0500d0641c01550710301e84202090342d606607a08540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 142529793 1250 142528543 142528553
    0x8031c09050a08030c0409060504020f041215061403010f20090a05030a0803070f020c0109180213060806010306090e07260708280b0c03150a1701050c0304031b0201050403 75
    0x114042e404019401e40d40d0b50400807d14142d0301c07180d002130f00541c07041080048441000003920705440c50b00780100d040701c266090400d544035403081f800c404640340040004a0310100822030803031183c150004d000c50822280c00f02c00721903180c1c503c8131043c0c0100301e0515001000c1d4006203c20400141a43d48007a20384001c60b1030400d005c00110703403040c0c000013070219054012000300e40c444014401030280c1c85d00b0000080038802c01c0e01c41c07580d03210000e60521000113002d80544440c04455400310440c103540b03880043c280c10303003914450b010900d4620b02180c43c0c92036014012000c0010130040444616100c00301008240e680728005d22b030100d1082c00e80c1418020300c0194010000c40c0010642241ea9101c1c0089416110b8003c02038200d00c940c0000000313820098071948510482c0043d501c980c0c914184002180390007001d254130101d16035010030340556030104480020716200003040350740c0d501d8030260300f0380c03100381c0f00a80404c0491809003003145107140e203106424810314109007011703569030314 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 142531043 1250 142529793 142529797
    0x1006080105010603051807030f0201030b0621010f1d07110609010603020f04020c06180c0d1b090b0913030507080301030b0a0c020304050d06020919170708031c09050a08 74
    0x1080080303945400040245982c540a201d4011040c0013022050b918110042507a4030490310004000d880c0b500340003419a80240c0c00202d0044001d02801d0b900c500300100c00f09040721140801800140003030022039420301c005801001c1c0c0b050201c5244807410203442103916940014420400c00c0b05c01d000d086002d080a01c94a030289090800115140e8154070402c2940c0201c554054041e910500000e1210b60001980d41d030807814074070016070419021a0128145515041007a810011018002080110314502041c42709120201d41c400d154440c0800c0381924036400c0c00c9544a0b160310081040040d51014200c6114030034103066113400820343c0c0d10304642d0801d0380180e99070a810401c001880425001d01c0803803000303902c09945494100030005100c001c1104002e00400c0d40032a42030000c2d00e8018020001290f890080b6078065502c0400d0410100c44c01c00e0b048090140e0000000d003000d00005841c8100d0340c154640342c1c0c0302c1c5400210001414178884c151580e11401308808049280800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 142532293 1250 142531043 142531049
    0xf0212043804211119020d0605070c0606060203040e0a0e0c01050c0109120c0210020c150f09030106080303060a1a120403120519060b03010311090405100f0603020a05010e01201006 79
    0x1c940005000d52200c6508000c03082c0ca541401c810085e02e44070050356680d51b1901103503440340c0000340c1c42d102c1d400121092902508010082d80c5040c030301040c850b80000181c82101c1500b0b40f1501a90344500c00d5606031104104940307034550042c0da89a46541c081c5014283e00c4650800020f85403a8940ba000000c480000d40080403a000c0d242c6d0509504080c01052150003150009100a0303078054017192008000c040780c220541800301d110504441400200e0f041120010024000da075240e8030416202c0d48142c600714803603048201c0020b64141040c0007202c1c50549113498508001e40c08402c0d82210740010811400c02c01c00800440c94100140f0800340150301d480e400128500b035a4100380b084805541101c02c00b040140700420000d544507815076816038054a070302001741c4840c03410a1a116010381800141d0781880c0d10300c0c1d0f4507589540404112030007241e140c1304041d42c440040d642039151030150360000320781498403040c90400d40c40c01400020111704850140c0c15090b487d00403a05150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 142533543 1250 142532293 142532297
    0x21503010e040b0606030f070e01020c06070c06030e12040501050901030b031507021e03040b0a020c0a0e091c020d0305060307050a18150501050a0305060102010f021204380421 77
    0x20180000d000900d242c1ca913024006451240c51800c294003210700707145005103010100007000028602e141d1081c8001440d040e0003402480e107a05051038017050290300c074000c21000034600b01c503080035180c00041d20b035038282c03034000c400b454941040e0046406512961a15041c103440c1d0194440e10788080009000350102d241114403941000780000342811a100d5103000305490030b404d00e0244000201c00c40b4202c82ca140c81031541d0301001c2e034040e420b144200b0029a484900080006824128060031522a007000d0064880d481008070115880104e03401c581001603200011031504c0c98000e5001c550072580090440f41520790b5140010305041d01a00b002d29400704541d1001c2c400c1d102c1d8025131103060500c104084040342010002032490041c002d603901003540798004208980d00030f6001c1c46810728030501c2550399402591000c00700482c02d82e07003140c54104c0907641548011503605409400854800940400d00c1c2840141140d46070240c401c4c2c6100b510101c600f1765295000c40c7c40c0629401035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 142534793 1250 142533543 142533569
    0x30c020a0305010903030c2c1512010303030b040c0903110a03020919060e0606030402090c0408062e06140a0e0d03020d11060402090a0c2309031002040b1602150301 72
    0x41d217070080c1611710b9100e240061000c2c481c2124404c0a5031309018045400384241080c038541182d000400c4034002c29006110100001440900820b108454505a034001d031814400156008144022a403035034a4a10004030303038140510004400390001181d014000300809003840c0c581d000990340d0ba4040d5403640407007050b4010221032600d540500c0000702601310381c0351410f00d44100440c8084c840100024417810b51900050304510325201660060041c80c0200c400780d1521580001000c8014907a0285101c1074406541c209040940c004c010340b00155140501251120210f21583d00924510002d00110400900083d19400000c0d03801a0085e4028600d211151001402c0ca150049680c4daa54011030300f08005620f0703188080e500100404e0000454941541c001c88259406085034049a05001c510f81d030015801405402e07000012002d0b6103030800382044032000c07407246210f44d0309040d42c2800462410a0000c41c802c081d01d0025121241e0441005616005076000741c00c0005044d1403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 142536043 1250 142534793 142534811
    0x6240e0a181b14040b06042d080a06050f13020f0a050618091311060d140406090b0a0c0c02060f0f0304061506210e030c0102120105040b04061a07030c020a030501 71
    0xe040300b0f100c0c40050a48080002c0141c045c042652440346009215a4030400b07995005400708840103004020b00c0e04503024810390b201c0304240d03100c05850742c09440c41d07802c1c580422451902100c045009481501303021000c104258207001d07022250548607548140190400180341e11800014084d10381501038603100b01c0b04820420544c01c0c3c2c060a0700070310030182d400c03103000100244104000d0680407141c40e074a669101c40420701134901c1c6480300e00c1031500d9805100401425800c007668980c07250a0460640d0ba480790203c0485034080a0360700000c500780d1500d005401d04600504038401c14542ca1841e081c10030080b1101a4001da81c221425035503a0b090030405809211b1100c040c261510300050095040d0a0030580440c14080d290700709607907506c1010140c02d040007110860010300f8000c0d5202e40d03007074424040c065000d108490259042c006014020702d020b1188905540012190f0600401d9000030850303d80c01c2003408a0501200c1000880544d648045178001144030790004034651f20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 142537293 1250 142536043 142536059
    0x12051c1b0806060d050604020d0f05040605071b02010c080f070804091107022107051507020307080303131e050a24090b06060702030109020d06240e0a181b 68
    0xc0191680c004020350030050001d03076030b00d2000311030707000d5860301e008503490725100006802072140e8001c0021991416008100c406215000f07148075a0041e40100401c6d80ea0b01002c2d03880c004c884280c0311a00070400b400300300541c050240410510b004584542c24082c03412000001c40c0e10601c0103a506100100b0100881c0c40b15006071050304210fa040582444800d40c0440c41000d4105012031600c1c00c003c0030b0024100f81006584020b000050400440080d00081e512069124a0040c0c3c020f00070440301144011000046a008559181040d4085134031510340b0760a00c0303080656201140003205100c0082001080f107840d1142c020040d4a01000c0c1e0070f030203500e5240741002e80703000e071a041200781408201380682a43d840001607851642c0c42d03c0f54800a40146040d4400a42c00a00311990b1400d0161b141d21145000c003610401d60080c01c550000d056111140740b107586c4800c0712900000d204079140f034120040c40044017480078448080350f40e800c0c146014140ba4031910700010b20040013140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 142538543 1250 142537293 142537331
    0x3030801080f1507120b131a04060803090409050a0c06020313060e030a060f0914010b010305010e090705040c12020a031509110f03180703050708060a050601020a12051c 74
    0xc1c0008000f008881804501c65000e01070082940702840700d0655840082031098000d0b1071040380040c5032030540c56001c030020300241149400d00982a80c604881b2440f418984070b9442500e040c40010b5003086003e00800018003941c0c60111918020446008001102500180302400e083e0300910b895851480c4031105620b81d41e808030301001100c504140040d00e02007240420180c2003940454807030008138061001d40707001d46000340601668001502c61039030652050402e920242e800b4881030b42d0703540c44d9030008071080e101035030340c1e40258000304a5450f10b0741c480c81c1d40c18901c1c1800e1782c80724441311155040b41c00c00c8641c5c0b40402d480f111402d201d000e1b08a01c0300302900b00f444003046413440401300004140580c542d614003400c7c001021070070f45410700d002e066a040a0004462140d0740340c4c1381450310340900384901240b0340701c0d900202c1c4007480d0502450b441440181c1c010302081e6402d407038016880c0001c0b54114140700007002803103255000011041840070004c4804a07403c0c440b0340c0841051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 142539793 1250 142538543 142538563
    0x40302100b060d0c1e0c0b060a0302090c0313060e010504122f0c101106070516080d0905010204080109050c060301080322050d030807110c06041203050c070303080108 73
    0x3585480411201c0d551000240d0780800f02c00701e80058442410401621900c001e81059100703025070540c0c2904090f440144007451038452110031071140c5800090100000312800001d44c004458000200c000f0383c403501441c2e000c10701d0700306055810129255001258282c10503044aa5194002c10080c4001c1c04d221004075a111b01d17190300c6148041c0c01a01310400750428216182000e4080340d5000c4030b0030009580350110045c0780e541d4148800350007404156480034028981d0103070390700084019020300c098034100c2c04507020949817112103a9030602282e1096a40c00c1400e96a0011400483c0e000d00c0034202030318a0b000001842d4040d42844ca281a8034698414840d0f4000c000501041802100350341104a4503561106100e00c0c540c0050b0440c12280c0145402c1101c142d19a800d241d03100d40c0d000e000e4821500c42c4040c40101c2d100302c0b5107645820007101e0308030100f00405c1080a80c01c400412504c2d0081c42e001b4101440c4041440c01d22aa0f42d00c02d900141005005101040c001c2c0141d07086 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 142541043 1250 142539793 142539823
    0x1404180f180201050f0a030908030a020307080a0b030d030c120515043207140309060f011e050f060d020c010615020307030c0210050d050a09060b010c020102150a02040b030f040302 79
    0x1d811425800200103210704800d00020741c0001c5603682c84a80240c00045110b54420b456544034540528044000d400450305100000c0b00c100220b0110f00311486012076003d000b8014000e8070102850a4018002a560880800c65080c0160481940c03500c102d0780900b8202055075036005e0520200015206007120b900800100840d040b800f10840181212101100c0b043c40e000c0341c3d50340a0141c0f01c1700b00c403000c00d202c400c00010400c9280500410322502c542e204002030b10300c81c1d8030b425004ca4003424103441401204c018100500c00c07071410a03030400102900804240ca03000390210168140e03040b948103405c180e9105c403420700a9404801440c01026000d100441c02c00c100d54400405110b545100a402001c504c2007000c42d2038800d0040359081443c0c3c441c18021070070705526400083c400310100307550b03440c540355011850b580b0501c0c104580b00c1d016030042c08802031107100d0848504001e00249001d0350308000001e40010500044d6100c1c40a03524620303020300d417500f0007038200342d408605104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 142542293 1250 142541043 142541081
    0x31c0905150d110708030c030a0507080621100204091a04140703021602060307081b030702070e100302040c020d090801090c03110118260d0903031404180f 68
    0x10299000401d40c0c2d25030342c044070041000381c482001e011142c4542a005070030701c10004100030038522a58010b50040a05003030802c002d68a41c0c60403210007100b81e5000341c0c88900810307440418000301810528039060709003515004a0b80c820b44504980c000d42c0600c05d001d855000e0b10b03201441c482e5420000c00c030152014802402001d0380800d0444c2c005000c4414140d000c180d40d017a244500ba0900070465010f021590f41b0b08100001401f6050700311055400c1d40e003004404103241c601442528015074103a002068400e003844c152109048000b049030840c990702120000241e41c03240144800100b460b00035120141d84808001c01c002d080380c00094450f0b051002c580c000403118000081220b42000c1d04001c280724600040f01d10303a00611f001d24445012103004038856851004205d284e078404d0400707440f540140300d51a07403942d0f602c1207100007003814100e0400c0030a00550307a0828040750031601c0c61401d0f03200d001c036551030820090b11030708440c1d454034155940166445100a1340b010103503501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 142543543 1250 142542293 142542319
    0x1205061212210c09131a010e0303070c03030306051903050c09070c0f051c03050405060106080702030408010606030c110c030730080d1b0504030f11031c0905 69
    0x56600c40c070040c000d106001000034000d0004184005100100510030039000050502c03100240041e088010780e20b2043c00d091030b22081e480703203a00c10003445107908040426591544030040d10102d1910103815010301080154400007148000b40002443c460b48001500606190500c911030409840303101c041c0308108014404100001032043d01280101c0300724100341d407130351000c803a44120031000070100420264406c00304038001c1120f14429002020886a81010302c9044080e55400da40c0075000d600400010300c91380e4450324100e40d10401e240100c80c031b8507584203001ca0844440f580aa00041c1d5940806001309038405608100400c0d13040080c50005203600000c1e45603802c9200781401c451082100d500c84010740c0e00d0b007941c3d6204081642f002155541040c040c1c0303038007041e40340d01034520b8195400d108007900c64a8880c41a05070352001d041c41c0c00c6070340b1000c000c922140d01352000003800035001010340d0104800c6021121000b2614507c0c241154050440e251179000b4502c518002d0580ca = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 142544793 1250 142543543 142543579
    0xf08030a05120c07050a0b04050d03110304020d03020c060310180e0309090402150a0302070b1e1306090b07120f050c0a05130506070804081002190503060102070e07120506 75
    0x41d9540c0d05030b8615030041030300d8642e050501c9108503500100035006034040c40c428409420100391043d400351701038440548607110704a003101c0350888440001e000a001003005414140d500c010b00d41e00c00d00460707100c804c840000038120b40040f507a0160b00e280c00c1209124000300100e01d1080b803807030188140040c1c007920080d00d80b01d01903aa04540180d04907000075041d0b40c0c0d20300540fa00b541004100c281e880c00c41c0c08006010b0760003500140e89140031880810381e510000c4c000c002c02041c85a400d44510307100c47c0324070303502211a1481a905103482d4808a070208240d8a5290b01844c4140c4803101d03402040e22140090300c44c11035008541c64600810890302d1801201101d40b107600c14030300070381d42d1000309644501d242c089400180c0c21003004210301e01003084442c0244140c5550104440c401089042c414040e40302d0380c40a070540d428200b80f1410054011b01c0a1504444140107035008035446400d0040c0c00d48080b591076001910060982c01c07075400034440c00350005416100692402d09408031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 142546043 1250 142544793 142544797
    0x312040e1b070305090405040f17040f0f030302150403030e07141c0b0c090102030403080301082503080403170c0d0f09050103050c0703200f01091203090b0c0c01140c040f08030a05 79
    0x17103019644400000e01008140908000381e0f0707501109407511801a0521000642c00500401e04070301212074000c1a2003d41c45582000c80b54503500501900282c40260303c480b010160044060649405403143c8031002407200b000509207050182c00031805100401c03000e540880801d82006a20550705400f02d0308881c940c0d80d12901950110340d8030102a00100e18500c2a40d20103040c441001c0000f18a0000104044541001844002c00581000745629001008501c801800c10000700002c000241c0c03070303101c0702c01d80c01102d08116042550751a401800c00c10701c010350300e0003d0340400c40700840d290010000d001500080c60200128a00b40140c1c0c050391150580203428481d00081002540440c1180500c032600c1040a803001c80b00521200b9011b0903c8000865801e0080900105d05074400d100da074003890b4100040910549034941c51400c2035000b5407840000d0354886010407000340d01303015094007503800b031055035a0b44d42c81c140b1b0792503080c480f030f0300004669082006405c41c540d81c8801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 142547293 1250 142546043 142546057
    0x20a0f0305040c053a1a010815061807030504060509031c020c0a0f080a021c0c02221a0a060302030108030a0e01030603021027050303180312040e1b070305 68
    0x241c12580c0d004215205040b0501d540403008000840300300c00d59600d010b000705c541c4400d201d00f010b10301401d0091000c0c0a004000d00442880740d1101910400000e40030b00318a40082c030190814000004031071301c071120b183e02151000e02007500c0f03006000410180344140c030750210300c000286041c0ba0054100418038400b03207030714180454000c62020300c0c88000340311a58040b0391244030072080840034604044203070850000007003d801303000c0b02c9441000e15032040c102401d02076500c1d0440303004954200301103c40d01486080300e410500b000307040b00144030310928a60b034002020a081c140c0d421400c0000441203504800101401403004000185000040d01c0100950b810b0402c8489a550300403070082405a0000e0342c0300e1190a80c1d800d03160f800006c982d0142c0503d5010303000c05030903a01c82c0c00500500e48545030705070b40100300c41c0340000d46d6840e60018030440101a1014a191420030500b2a0050b4201084141c3c9142c1408002815840c0b245c00d030b500c6203d80740d4105560f0f51000f40c000c0c081c650b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 142548543 1250 142547293 142547299
    0xa090b06090103111917070201150b03090703051006031e03020a230d030b0f040506010e041109030a0c06020f0601030c05040209041b0f020f0624010c0c09020a0f0305040c05 76
    0x41444004c01e410020703100042c1c41140b2482c03000c0011303d0020048078111141148441d41000407602480c13041c06600c14281d4190405025185400c150a000d03900040c1900d10303d025003d00800002d50501c6a010a0740640c0d00100707115045041003144402540c0d641c4100590b0102a14006074010a410900030b0f000600c1c91107030701d002c0d0b41a42c1800c030604500c4141d80584908000c40540640c000d64503034400382c62441403200301300240030484a0030b5034103501003075029140c281185820f80000520601a403c6c003400c151740312011900c2d00b20381c0c10b81105e403e109600300b03004040e03040150b1a00701041c0300081c51076500d1a01c0c1c0141070b46050150500685d000211304400e13880e40c1d0040b0003089a555540340c1c5480c03d440d401450007000c8c0001d00b0041c002c200b080340705000005000b90081203210780c1d440343d61420500d10800d400c0e07829000360500c9034000080c00496400d0388104000e083c070680241c1c0e07800403550f0080c030030f00394140b120b000d2515013800d11003c90030040c0501c0681c3c8041d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 142549793 1250 142548543 142548551
    0x6090b180906130c03080d02030a05010803030609160c060e032812091109040c1a070b0610090b040807090f05010b0d09030302090a0f17010209010807080402061e090a090b06090103 79
    0x1030a000140d500c5030f800251010b0400214907d06041c2030340114030038540b4020800003a601c03488150b03160300c81941c81d40c6d44850b548000c90340340c0c40c49400101c8280c0d10750802141000380c0c0d0707444109403007007080840b680f0f400210300c031150000007824551034211810308180310135501a20103003d900c00a04185003259031a60303050304000d2a06000280c80b03000900060a40c60240b812400146240c01490030302c203010308000b0b070085d0112040ea240c00c3c1c1c0c420b50b90681c41c0d0340c0342c084c4052800350504802c20000f031104009011045540100040e1014a0140c02018241002c500039994038007568403485142400412400b12000143c1d144405040340100f080d4440342003c0b03000e0301600b11a01e61140801400040100702c202900d0201c1e11308581511105024074146801c07030041841c0e071070100700c0b41c10000e64454480e8a40e00e91161000702500d0078071190180c000c021034440b000d00507002600051108003480d100b1014801004500801e01011041d180030032918065160514141915 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 142551043 1250 142549793 142549831
    0x40e010605031c0f080907090e060714031e040f0f050a0b1609050402030a060b0a03090201020f03040b040b0a031407050702030613020312090a1a0306091e011202040902030106090b180906 82
    0x810300900009208c0082e09001030700c00c028100d81c17070b0340040e6003440c04502864030380b1281e00c0c03105041c0c4c1e2140100f06041021648104480111040000c204965042199185030300062405a9204d0382901900061812802c5e91030801c1030840d000c0e12440141c5640030546021030f52201085060311001d0b01c3c003503100e4036180c45100103400c6d1034008024803107021603441040d0740e141d844021943d0007603003120320180040b10801d850703214501030314201160801040c003880e41801e00070840d031461440c001550081c1030405040e603034000c0ea000800501700065041c11340c9010071045402080461100405148550003e56501c02c8a1301ca00080e480200781d84840d80d88485040c1d00410b5000c002201da0380350b40d810485941d10072180ca511408840010459070800e00c4035412030044440031401c156424240c86c007504484819080740d00c00e03100c111000041e1030a000e03071030092010302004600b0b007403008100b0403076a80f0148480f41e018468020001c1c40c82c00011038641004441ea100204045 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 142552293 1250 142551043 142551061
    0x309090203190f18080d150506190203120c04090b040b0306070810080a1b080a12050708071a040519031b0219081006060f0f120209040e010605031c0f08 67
    0x54200960300c044c400e01c40440060041c0706009011400000c5820444085500c0740c03918410014029103400031014800000c80c001d0301d0015503081201401200d0800e403100911035402031080b52040407481c0040b80c2000ba200144c01303840040c402c1114107012031031074100400d90321103009101c1c40403c0f94580109040241341085c0e04050a10b95081c0c48010f02c250030304203202c260412040e034094001308400a10b0070360102c3d81803145c071303441004101c020018038000c541d180c0001c035040d0b40407901000f1202c000303481c500349540240300703038004162503280c2805c11500389a0810f1001e111442c01d212040e0000e64090a5800c11503010950800103003514000315140144031407410184070700c400d0000ca11440d0004150038010710800090010685454045800d0b41207590b011011445000710409001e004416410b105100c0e28001810b10314100001404d98001e54041143e59541d01d0051005050502011001800ba0628810402d41d8888000d100364012030103441080005c40c04288940 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 142553543 1250 142552293 142552301
    0x8040209040b100506040603021c06061b05100e100605030d0909110408010c0801030c1d0a0c02010f1d060a0605090f0712141e010f1e0306180309090203190f 69
    0x41303406800a9161a143c85010303000354001e80340394002038030380350650030340010341c1c060742069074125500c2d42d521b091071401002c4000b10008040b105400340074000b00c1e1818482c8100e00000d070700d1310000c040c01e41c0c01034440c0e030442e0940d40286000c0d030850706005406982080d0810102c0f8941c820004d414000100401100e01494002188a50070203036012001c40d030244403141130300d0003025000c0c50140d4405580041c4558000c1d001d070791481a00000380810b04c594000009540740780000724561802104500031074101001104642d0740c81102406506801c0024036030008018008108080c2803d0000b07041c190010080441010102c00143c40d451240d00700341d0309040341c0582401a90811040210703560002c031180141810715440d010301882c00c038003d00b030403035004283c039040b0300381003101038020702070508060f803a1101007010010018549200708003200c000c6000140c03483c0702e280b8000b01810443e038094100f0314014020f2003c02e0103488803000301d8039000040020b00f5001107030681e000e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 142554793 1250 142553543 142553549
    0x705010e03030c01020406180f060804020d030318060501060306060305011a0c0a0609120806010c0b0f062805040b12061906030501020c070611010c020c09040303060b0f1908040209040b10 82
    0x84d50020400048881d04229481200ea500d41c0024404503100d41e60002c03031941c0792040000140c40c60002c200981070240e041d29200d8080e1502140c4030500b00e00e40041c00181c03240456a055841004010069240c89000083c25080c541400b803035140140c4951903034254508003020301d0b4000347c281002d0070200003420041e0f81c0140f0510500c0351a043c030900f08402030f000d07400071035440c0b000160507610551803080d001c0d42c400600c3d01c5503200d42d002d07081c0d000c50003845c0d1a001150508211441c0e210120490824a052070340900c042d0300b44000d000075074070340c055120b010321a804c52004030710364046100c5501202a032078002554140d9071011b4040d0a050380050220b502c001010b2901d000d000c02c0c5101910010384442508030706c40c48095003224402d1400400503003001c100540c0710f1610404c465040ad020b8980421465296000000300d40c2c46101841a9010700103000c18400c100203480140044241c202a90b881c5026008a104000b000703200070055210040010b01c1c0c10410159107001e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 142556043 1250 142554793 142554817
    0x1150e09090706080a0209010c0f03050f0705030301050a081903050a1218050d0e06070b040206090604080d0f0305041109040501060902031518040c0501080a02091008010e180705010e0303 82
    0x28148460070325100d218900800b0f00050580700002c4c616140c83c001c4440d80c00040c0e4540c3d01194554a038000b81b00036820b0700b2070070800200407170740b848480607010780f49060150010b556254076100800c03084420990001d411504240c180580d09018060088005078050070300715628800e646003154400e504400a68100c6d1030b00752142040c40c80c81222030245403003607044440f0241030040503152500c500c460701c4c7e4004000c101f000f00107041e20120030740040c4050103007400c0c400740d05c00180b05900190014481644400340004100754428800340c0c546246041c1080725041540b80d4098020074040128000d080c0390001c1000c004003541b010b0020010841c046469041031030004041d441900c2a00d8462031001111072007081007070021038066544805a90740d01441e020040d507005200610b15034030641d003402000c5042d00e0314240d2030b18009541e696048030f9814150400d05516000e07047d18201e0400c0140302e005224005003d4042e82c0090908a404244240000e0b2461040b078900c550 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 142557293 1250 142556043 142556059
    0x50a020c0d06060e1503030412020f06180918190201120509100f020c030301090504021f03020304020411031501080a0e12090f0d0807031202040503010504050c090105010207050901150e 81
    0x105024607a4444000d44e074202c4104155619046955603040c2c203c1d1440356415081080301b00300409a480020000700e2000d040c13100e4150380392001a6030b0342c010407481c14a505d2a0701044080e03151130201e40398000c036400d49200c15100d510008954490054610001111156400304256800346009821111900c4010b000c9464010703071164540001020340901181132005a40c544105802a5103080d03030f90340003c50a682c81d26803d034002c3c20700030b0b000740d030400121501c0c0070344152200411500035515071030251380e034105441032100b29001d030041880c80c48000d20904c02daa40b10540100001142481e200c142c0e0340b90084010002c1203c5001d07408070f0701c00c43c150701209810b200c000e881a0340044811800050120051082520040c82e000702001800c1046500007070040c1c0109500c007420f01001810036845901090840340191800d6856070b0000c00d0440803403400c8607a0314058042840a801440c2c5003002041d41c10606004080540d200f00c0603a020742c6100e600c40703100c15070000302482 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 142558543 1250 142557293 142557319
    0x60904020405220e0f1b270609010f0302060304030c1b0609080705030f03041707171b0307060c020f040b04140405060a110d020c10060605130f0501080403050a020c 72
    0xa0fa980b900200d12075036103040510040f13240e1030110b0300799050200200900f803140071408004c07844c400e02182c0075a000210410212401e0240d09424258100b1503000b086982000300400054410503448056140e524600038801615010103582d040303681414452044961407410b100c0c80300b00149450040c2e05030b028005a61940108250200c0d031100d8180c550140e03d60301450b4803a6040b032000000e0754020001005600f26108010407041c225800340c42d0642e4880100d02000d0000141d07158440d80f020035000c5001d01d40042c030282d004412030080c012189405400f90180c9406003000e4850700d1800400c000544480d00060409240180200000c00790300414004401c0c4c25074080d2518401c85c400608200114801c0c014110b00b01c02b182400e0609a642c1c0300080c0d1b001e0121803105018904031250b0b0724849002c0c02001e020a521250388400842180008a13031440e4413001da002225041044075981000315035401c25010310303010746d03a01c0b00100240e1411a04502058208015290318 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 142559793 1250 142558543 142558579
    0x40c031401020a08010801092607020604090c030f0e0d031503150c02102706020d0510052803230a11010305090d0206010b031008031605070f0f05060904020405 70
    0x20070b0001150344440c1070b0f0b80d8070784d80345602302c2d444c140c00102046440580802d0203110440e1140c40482541c2c0e82a00d040441c0e40805c0f166046940810707035854451050001d000d4260103401200a2401030070022000110b480541c0c4480441c081028541c0d10074888800c80a1010fa0720051030b0058001d003600405424240010f000b000c10507001400360400e420040b0207107001c2c0c07018400f8140c20614081c91210403102e00c4100181d02110040d45c200004400102580940f9205001140c015050140303844203005480c0342240246014001d00740ba14000036600018000590341c001107801181101408495103c0f0312081c1f0070509449002000400c000f1340c4c458010001c0000c0e60148269161014941e9032403521002010158010300d00512240c0311080141d548042889041140c0d2aa242000d0b82540d015034002000c6600e15901071040c85000c002c94001032541038403000c1c0e003624140c640080307600c20340a100d12582000451020036622501510080d2800504c1036800d240c3d52450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 142561043 1250 142559793 142559797
    0xa0c06090812010f0311010e04180615050105131707050a09020a03140103120f020705300304181503080318010e0c0612092509050a020313020108040c03140102 70
    0x1000302e26584200c0003161611992480100f03ca60000e1801d000312010b20054600d044000b49541d0815030fa800d1150464280d40408281c09004110014601a4902d8900c01441468014506200081007a030383c51070400c9052800715201c1a080b009071100c0d0808050a100d210fa2015520400e808001728542e40d05030300907d880400c0e40c5040181000002c08440014401d22000c3c00d0780880005405c501c50140b02c100111050a2040d02c041a4407103001070440481810312000350490082e01c0460045809180309031001502d00841c2881e00c0c00c0c0700c000d074051281e1010300c0500c0e02c03282c000008180700b4805001450703004503207035140e1401c00d050003844003404200030700540c01c1c5a0f60040712400403c1c0010104c601910300f5140103041021140d020390090032402c014401c07a8014246681104210850342070090f01c9042100c0c41c010261041d0b6001904c0d800301f80e4410400c2c405414484840c8082e040d90a0070703d40c0080d52f413810100c545010542c400740c88031600e030303509814104041d80 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 142562293 1250 142561043 142561057
    0x203011508010515010c0f02040608030a1d0607020307030f08070501021b010b09010f170a080f1306030501080d030e0f010504030f030e0a0c3320031c020a0c060908 72
    0x2008121540e00c1395400d8640920014001c2e021808540c0000041200800d017071125074000352020501590f00c11500307295034402055000056203e003542010b8201407204400c1d04181100c0441c1080210340020340c488884ac2b000a207904141e402c40c0c020008600d041d28800c6410400071510f072031a0107010b000310a40349841030440c0d4a00b4140009502d815500241603a04442c9541d46890500d103074109421101200294144140711203030001440c03500080607036200c158041070b12511440c501d550a89100d81181041c5800c0100510039408001883c0400c0055864085a082104c0e42d515003060400c40c043c038207950800e8100310a25401c00310003e4102950340d002c00000305139142e243e80354116198002c1c0b02443d95602000040e03603400d608103d04035400210b5509854018086a450070300450344400b10740403806121940344151180b03560812000051841c00209032943c140d403a143c807070358000156000c01c0d40f0b94010b00c01c1c000042560350120042003c1d00b61401d00049079002a9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 142563543 1250 142562293 142562309
    0x3020108090105160e0d02150a0e06040605030606090406080610030506070f0c11040b030604031101050f0103080304021e030d03140709080343031d010e010305040f02030115 76
    0x3004284125014070070207100703000901c11159403551100303080354a260305420b6107500c00115499000540e4501c1032841140b07424004450343c80307442800140c903001903404614803031201400100309003604001120b51281c07045440ba590384403000300080c0184240c2c2c008010500c2044100b200c1c494520240000396401241162102c0ea40c2c61030403500303c03003950842800580321040c928002610344802c1800e0b101e008001144645c0000042071034003a0489041d80054100484c40c6146e0900b84074007a000340c030360241c507905903065407500c880c61300c0003800080c056031920398048501c2000000c0da0401d070400034155860701e0f100e4440100a0b20340005a500d1a07040c6034045600c141c000c14803c0c00700c170020406142040c02d44c40a038503010b0b038000001070107000340e5003081c85040340c401c803562000c050000c600d00300c3c90210f0800521080b240b80c4c4020b00c100c60079156a00076030704003004010031142481c000c12159160304c2d1941c40d054500c3d40007900f540c03d101c2c6002413001e80da86104140c1d4440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 142564793 1250 142563543 142563557
    0xc1b0c090c04063e03030411031207020111010b06040b071e03020c06180415080609010605011b03110f0604020915010801150e0a08030a091403060105060304150e07030201 75
    0x122a00846889544285030100e0700340a41003001d9980c0d19680e131120b09050202c010b00d4218000840004020703161003501c5508000300300002c11200c12080d02010000360003e0015000c02810041c0d54800c80300040c0c144210b10396a200000000d400504600c04060401781d02c4903a01c40100030190003003101103868408601803220708030010510b40c01c100360154010204114000107200300daa12000d1103c0059907010304141d42501d9900441c0b0030048400007400c0100c2c07800c0c807a20305002c80580501100e0f410440200103582c1e001d103044220b0003212890742d0304078a503880d0660b4014011082034045024101c058044090302040042c880c9000390f48076511591542c1c0810000317000d800030035001c03421400040c03000d81c03a10090a400c83c511400d141c8503450b007800c0001d03040d4101d0b0b4401d40c2161300004000d40e94991216240c002010509003448203204203c00107512064140105805a0300100006081c0860a103400c448155801d40c20464801d050300c901e915141c65001c240e002c5642 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 142566043 1250 142564793 142564801
    0x1030b030c0a050405040503040305160e090c1f1106040b010f0e01030f06090f150c0e04060b220f090203040b010506070b04020f011115010911070b07080c1b0c09 71
    0x481c1401e0400001811145214205002c110007807201920030b5031180b01c107000c040b00241d010044800c1ca0030302e550400c5440c86c9401e040b0401c102c401003038102c046e0445090030616441d01c80d06500301d2111059032040c0c155405200316001c280c040c100381307141c0c400d51041c4818000c8260256042c0c0d07451410a000458071580d1008140100b07200041c02c01c003101d181c201c0130507a654440b81072a48105020302c2600801d840358840e02c440001202c1c00e41d5503440309100e105802001c2c0d105100411380d41404007d04c0d1001c81c81c03460181c9200c000388009002401100c0341024941c10010304844111520210f8862643e030380250002c580449840100900100729840c0c4602968801a80030120405c00d9580f64240f08178018141440b90502c4024824000915800c0c400202e120080100010b42e0b0b624003c20542503a2070700107424071000c81008480040f502400080b0391010301c6050645940c1c5030480039400922400828502c6440d202c040188400c1020a1081ea0700d0f408881000082d22 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 142567293 1250 142566043 142566049
    0x302040c030e0618030906071a0906090c090c040b041503051003110d06060b0f0703030501170618070b07060e0d030e1038090718090b12070e0601030b 66
    0x11503048040e03071140340000d40207041810802c80080c5440c0a0702e040800b14800318850740c104030f000b1541c0409205202c120300c1c0c45101b810b9030000440f0002d2886080c41c11010344c3752100f07250310a009958800c00100c044840c001243d00520142c03409655950380da801442e0104000404540001d00b8200030a00d1051000d0745c5005a0360000d0ba000000c0000908101c4d85601034441218100d8544000040601000c400f8214146201c1070399980c1d407410380740040484230160003044200000c103d425010710740001c1e41a6011822101825103000325031202890130a455201e41000c2c0c000141101c204810b1b074110130382d43b0000e00704a580300015400140c050700c600c6800807070740e41e10030b0207607c0286050f40c000c3e4100c1c2e442c405e144501d508a02021004824000403d01c40007034500740748052505101c1c0780c0c00da0005191802600022203965110880a4103120b1004490303250324025000d691164080f01103109101e08a40200c0d0b91001c41c00c50a440469069020078946000001941 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 142568543 1250 142567293 142567301
    0x100305060105090409110d030e030c040207080d2a0207030c082a0607081305100c03080403141c06060908030405090609070e060c01051501030606170403031b090302040c03 75
    0xc0058503601d0038400b4241c203110060403c000281d0307003017900760046905a1920490141c40901941e00e42c180e00860806240ca410201ca041600071841002081c0210340020140d441603d884130021420b00401400179100c2c2c4100d180107048082c0a03d0206483d5400059041c11a445032190f141c03226612002551140051a86560480501002964456102c000382a2441c00041c000b50512415441e0313000c00d508a4100740c540d0401e03450f001c1c4650b242200200da50105103141c94601011359a0f00103000c094040c0000b03003800b10303c3e070342c0e081c0541461041d1400005510301201080300d4003044e07140035080074071031100865514440401c00c0d0902008882c241d401c0038010503c02d031122400d100700308400500c10400c01010005030041d03a0344010040c04a04484400803505043c030340940000d18482e945c10505140c50a101048020307000911100d00f0300254000300d14555840c00c060f80684039000031180c501c1221500380c0c4d102131300300c1c5a0b030003aa40203039002c000d0a0704080e42a0304031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 142569793 1250 142568543 142568551
    0x715020607030e0712140c0913060b06071e02010306050a12031d040903020325020d03030506040906050a090c080303040b060904030207050312030a1b08010b1b06070509100305 77
    0x5800210000304041c0c0280c0042e800c1c07072290343c2141c02c0c503039035601c240010610b0148100c42244207140b500741714003070400481c0c48001c000c4030681c05609102d400500d4006c1c041c6c60040c13000e529512000d40343d950309001d60700595000200c140c08021003030040c82220305000b50803404645030000116060410b00d000c0030690f041e2243c03106024100d038800b42c07548141c0e0f102500c031f03200440400003030303a86a0b0b01500ea0010301ca60011071310f4038591010503040b0f05008110722000e444c5050301d10050390324103680c0c0303203103540608000840c0d03103038400890064038a4242c0502500d0504007440601300c0707158003018000d0700610110701c00079100c0b020141c0380d1000761406480d10450501140d45854005513040c2c00a02c240111240c2c2551200428105114141c2002c00c4070300200820000402c6805110f45100364078800010a0380d031644080c10b001c50600400c4c0c020700d000f25104580e40c8946429048a540d02d0702120302d0391a00301d40c01845a4800d0150078060104075051204a6000e40a801d001d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 142571043 1250 142569793 142569797
    0x9030c0b0306040c0807140d18050a150207150905010906050c0414181b070506090313080d1d0a0e0907140a06090312120509160b13090e0a020310020901020715 70
    0x11280b990444800e1a80040c2201d02340340c1d80e00c1c80c18641c6c9640040d05150540e2148010b1300882043d81020181c00300c3c5c201d41d118070103004002040000729402a104c5c00460075001c009204111801c0882c010080b46c4001032160b8600000c0c003400d018a40094801c40b030380f804e03414000080075024050b500c1102d0450010b0001c1c142c0c0443c144d02e0350450b044d640028000d4640c1c0c10070106495640c038142d41500d610320190000242030f040041e028101070003918001c8001c01d130b10892400005c200c0c2002c0200c2d18181c85440000140aa5440c50000c006045002e0303d20b03e1030400d503485030b490b100980310ba0f035900070750404008080c1c10840f29840c00c8504a442c0c20905910f90f403a503620b100d030300296003405c0010000105601d01c4403442000e00566000000b010001c2c1c0c00300644207403010030740200c250301006201941d0500016085442502d81c0000041010010201184d14207200110001d50600403120f948031400350300d03400350101410907803c842160f0754a40c80d41003121044521000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 142572293 1250 142571043 142571057
    0x1b0201060e060a0e0f0402030a02030a0602040614030403051206190801050604060512031902150901090b010603110409180203010509160e01060f0302070507150905040509010203070e1009030c0b0306040c0807 91
    0x545ca0700e0f5200b0465000d4009015201030462550019041090030402101c010384c2c041000c0c0f15603036002e120140c0d100038042d105032450030a074070f0180207402101e4542e022a0b188a00268054486801029201c007030210703c0c1c040c80351030f0f004d103e02800c002c80d80c0c1340c0a540740210000da6071038009400201090000051450050b1040c0001c0500e51040c280000350b10800791081840740c1107408982c41000407400000c0d20700002e00d4004490b81042e07112804040c200219410600e0022040f1021241701d07540004403101d0502411300944040c040103076065180004001c0358040c0031403038106d085001020355220b651101c114441300781003805034000044250460303140c013a00a034020615140213204070b0b645140d0f64aa4034282039180040c2c04001099101704100a06250040e40d401c0880c10b8000d505600d800c41e0020280c414441c506072060138600d03409481c5034040e086001c003842d0409604000d468540e54a0351040d80290340060040346448020b07180c8601c40e40000c0d008a0360b55841c09 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 142573543 1250 142572293 142572301
    0xc1202071205160b04060209040e010e100905070f0f15030207080304020d1109010b19050c0a030e150c06071d100e13051f0e0c030c030a1b0201060e060a0e 68
    0x2202c503004060300001e00d4a0314114200400d9250862511451081001596030941081400705a541341c2c50303d004113a0400b40c142c000e009003c5030310401062101c0000440c01030508025103012030543c070070403c4000d1140082030440c0c040c010b8005581c244001c41450078800b490842c228460b9000181c41c44038280f010500618051700c40c038003258000c490204c0320140401c0011480e00b0281d100255000001600815648161405040d500e04504105040c0700810344526102c0d500b07840c0003403c01603da03d405000c1d03a03400c00b0b00d810f4050401e0003941c50b81205055260b90310b4050721880081402d010038145284068290703c9000080074001c2d1582662421090351000c035080721580d404941c000d003522016080d40b08041c03285042d030f1501851a003112400d40b60064440d0060900021201d04000b0000741c10821030350801c4000c0c0e40c665480c0e8481e0043c0c0010400c404038881c54200c2102c0d102891070f41500301e5020b55207031f0540f03628a9207800081102d0490705204400d50604201e00003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 142574793 1250 142573543 142573547
    0x10c02070806010320060d09030e01140d05060103140103060501030215041d1008011401030b0109020309150907030b01082103011809080c010c0908100212060f01020a150c12020712 79
    0x10008543c0e0082056403035195039800146c641c0c21050070461040d540d00030000a042e4001030300d214070710302800c1c800820b0011200500c114400c140358584200d440b600070448603403095004000a41000c003090b0402c0d40c41c7d162807400317020280301c1680308803094001100c240400204403011501c10881d042641078641038030350120b803401800201900b2110b6000114002e00780641e082110b8200b89140342c644c118500202840810303040650a14418420801e0741400091040d10004c05000b50742c0165a600704500d1070903581d50402400c00000c1c20002450708000035180c484810801109036054943d4548080240024400d00c0130021511505000704c0e1125405240381034000d2804a10727124911000c0360030b5501a2032103a00043c0709800030001d000061255070b40c00b1101081c1585080d4650904001601029104a100f4600038469024984c001c0111641d8207604c2213440400581d9040344400401903000c2c0350000c5980d603e5070110160a40c030840307042c6640400c00b141c15185401c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 142576043 1250 142574793 142574813
    0x1003020d020d06020c030a090b0406050306010c2103050a0506030f0d0e0a03080a0c0201091a0a030203192a0219080708040b0c03090a05040207110f01030207061b02010c020708060103 80
    0x80c2e8000c580611654040b0f9194001040c030000c06000039551a40c010344c0c002c280c80e030107500107110450248002d00c1129030003022250030500903c1e00b031082003000d042000c0c0303104002d00d002d4100000e00428850391a05900594400c0121040c01c10583e500d503428035454009580030010190000d00f0108030450144502c08800c00c2c0161482c0740321602c80d601c040700c544c403515400000c00c060f03c0207042107690120010380585051004600c00203051504200140101c40e000000d064000c000101c00d2262006047d8002212407024040d2105203080c03000480ea000c83c0b1003090b120004481c0102034000110900e0116441c0c8951810720300d95141c085a6401c12402198000c004200001d040d101e00c0000e01140410302028503030700d6015008000341848c080c1d00503405a030041c03240c0c01c08a10b2a40d501583c010054035076080486000700100e000b489a960700820092a2141102d1068110f02105010702595002044001c1325030f001a40d943c1e241c3d00c0341032510b034040c80c0140300065171885 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 142577293 1250 142576043 142576069
    0x16031b02030c1323011a1801080a090b0709061e0503011208070b010806090d110c10090906060e03010501060801120602070303180305030906010b04080c120309040608030a0215100302 80
    0xc00150b000603a103004008a15840114035a40548001880324680303004800c103030031a110308840d11f0328503600c80301a001c0e00e000800506109500300091048501a0401842c445d809040c1120700e1505034000781120b0b9a5000c1e1000040400c507145c1e0f00d04070421740d43d40c42d00569880341811a03191082c1401154001103017116000381c00d10078803001403021a1964080c0c22031001608861418080e01884c0c4002c00c1c00d99801c1009040da0440a40c10203d4131749004041030302c0081d2045004182566414840c1c0e01144485292900000e003c035402901325052900480003400711380d0366101c0c1210400c9081c02140441c208460380e540c005415540140303450762090401041c1c01c514015002010018140d0507000b04a00100700004060b040c09864090301e5032541071800e003420702c43d070700380d403809501c0605028141005001c0300f0300b00c0800c207a994100008100740656a2502c40c4151a500114480b0780580306024845202203070f040d05491140700110380078000146540c0800c01c454981d48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 142578543 1250 142577293 142577329
    0x3030f060b0a0903110a0905010e180c0108160201090b07030c140408121b0616110a03050319020906040303090f12020f06030612060a0506010e09060a06050a120216031b02030c 77
    0x1980005807d02d40d801500d000b4a410b400b03044091510b19000300000c0c0901d17103481c01e0364000a040308056031b00150744d0741e044884c00c4501c5214032882482030b40101941c00014004130b070f4030410000b000f0b92503084050300c20b2440c6e40e425104005440c0c4584070b4000da00480080781c21014006030303032000300c1c000b40110000c221107a002ca1200080c5130780c10315000f62000071400000009030f0024980050910349000c00b1440140409007031074800405500002d41480ea4841c480f210301942a8601e4040d02c1d00c1ca01c00030701d52175036983d076868041e00944540c45101c01409103048009545c0066141c00c80c00c0e10380243c050300860118200b0404140d00040156511005801e01d05c4c0240c00101b0810b03102c0c030b0000030005184d04004002500504100000074402c61342c0b80104001c81d15806068000c450341803c0c13030303500d40219405c15604078540400c4100a24070110300000b009248200b0980304134001c0e1611400b81c545240440c02c0b0242c1400041e4040c1e0203c549180ea0382802080815408440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 142579793 1250 142578543 142578559
    0x6010e070c0314120601090815040305090105040f0e0619080c0d1505070c14070b0f070f14100b0103020a020d2106091b0e0a03110a0504060303030f060b0a090311 71
    0x28404000719080709a4a013100d00741841004100c0d6005002080900303c0c0ca002000c400c1c040d01c24801d22004000e2008080000120f8005400d90080702650090b02007203104001e4113458591100c80c52000300d44481c89070744104c002800030111841d00c40143e5154a024041e61186481800103042c1c6403001110150500014441c41a640784110b0b805041c0c0307076507040d507400180e00b0a00c2641106034141e800c5500901e200300403007681e0b401290b43d0500c1c00c8851b152201f0590a00d140366402c2d00c0c0780a406130074010844840188003041e45c04949800361800c00102d090180118100e014000403071000d41e210701c00d10360006001e402c0c50b28010507052800d00304081690100c1095400079400904500e0f256030031400f40e500c0c01026441441030900d03082c8001c00c0b41c44c0000725800340387c1c88003902200190350040740d03685954240c400a004041c009001e00da50b2841c0050003010400040701e4a203203000b4000c00c842c0c0340c0504a5007110b41c0766a401c601a411611a807003407034010203540d40e010001c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 142581043 1250 142579793 142579817
    0x5030709030f170d0e0f011b1209050a0812070c0206040b030411040c02160803090d080a090308030f060306090d020d030b0d0c03060b0312040b0703080403200705010e0306010e070c03 80
    0x1414002c0095192007040410580e00c0c80b44010321704200701d9014045641080003030081078240300030301248c00e1407030724140c030041d144079602400800017604d0140903401040c202000307200242c4000d026002d503501080704075503904681110103164100e0000c1d40701c4420003041001054940142d504a4060050000040003440000301150f80c41c1c1c03c6000540c110f05100310550440075085001012898040c62401c0c2c40403001520310710030840300402d108808602007410f01c1c4a8240314020319071165215580b41051184040c0c550380c12255a48a0310039540090b003e000d0108203181015600d400520321000b0088094000d00320b0070b10056000507510903110085580c040c07800700103502800c800070340c4226100c01e050810981403185441d01c98104420019080b4007012a41000c0d050328105040e922140b0b42101c80c151003101d0341c0c0f5202d4a4a450f0604920041005001c0b1a0262296800d6101c1c0100749601c524003489024007000c0100c001502640c02100c00780c41881c460700e0300d000380c181 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 142582293 1250 142581043 142581083
    0x3010903020715030b090c1e130e01060507031e140403080c010501060206100302151611040c0c03020303160c0b01080d020106050d0f021912050c09060105030709030f 73
    0x44001058005902000040096840443d0140720b00c90407480c0500c69100900c1c041b440e0341001509030044001d00080850220000310300c5a4007207181d00c1007841d514110103040540d5510b15016005605460000000f00180202c04441420340e0546441c0d02c50850140d121600c440a030030398405011002c0000c1842c1d549910080c005140300f060203640314031300e1001107030842d1b0050b007055066600050500c0300380b8805140390030272a030f41103c001e40000d0000d4000031980c05038080315054010a02032031030800c03040f1011507964200c180c41c108201d50055a084566000c06c1d000500980c200708013041d4989500340d20400450b00500b4a002d0b0f84000340d541c107c085800340d01582090304180ca405602c01e41c28014140204001c8411521004e41601c0340407a0180303031032000b8400d8010500800700704c60061100c030010101c0c010310120707140c00b030f061640d12a003803034002622600c5504000f1300a03600400c03c0d2806100c0320394810020900f103903644143d00b01704110903601d07030081d5001c40c6607100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 142583543 1250 142582293 142582301
    0x405010b130509060105030d020a0f1104020403050c13180b0603070308130f060c151a030d17060405090607110102130f140a080c0105091302030a02032a07020d060b0301 74
    0x8801c01d0000a202e00d050a006420810107130400d51003600506010450141e000520b10303000c0360081005210f683c0d580ca400e00400c0b003130320300e6141c115001003030000c0ae004c2d0200d142040100c058038100680c80b0b00e114146c044030a11030680014100ca04281070200309401061544008058216040680ca0b6203d00040707070400300c01c2041c1c0c0b800f82d040501001d5180c0b4031a20003814a03040003823170a10035030384a9403420749041001c94504eaa03450100c400d00031003403952840c12000340588840f00507030340e401401c5002c5003291381a6194540040313407540c00d00e4440c00340f0032540e28005c1c107582d0311480760842d08170000d00d140910390740d02845014800d01420b210880100702d104040c03a0241d1901030080040074201c10007900c229680002001038400104007100200d00c01d10340107548491403400901c0168405200a000038404001c000c1c0c09802603000b5070080d0001d001720481001c01c0c4400003040003184e03288280961052000078018108203004602c81c910512000c1032400050001c07a00311 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 142584793 1250 142583543 142583569
    0x50609060108101806051f06090501080c0702010c0b01060503070e01020c0604060e0114030907051201021303140a080310060201051b0703080a0914012a020a15021e0406140c150405010b 81
    0x21f9295200e4411486020580701c200520060804000b03261400c400605250402024011551000070310300e0300f160710a640740c100ca00d034808041c2c90a547c451100a241e81c0044400102107055522a81e00340c1d80001080c45010070001d00951426080c51302c00c507585c4c0c1d40140780700d041c07103070b4004c16800f020b4601000e14443c1840400038a9034a2a00040100250a00000c104d0b02d03407040000742200196503561400f50707030b000081400d485225109161a0104164002c2c0c42450b0220074800803c24014456080381c41c20341c002d209944078081d8003401038104056825070f1500400260b80040e00903000203510003c840c0d00040e03554142d44a1800841005145041c0c1e070355201024003411504040f9110102e01d21420000400d9450002a5680b00c0d016005403e03140c40261120301055181c0450303c4018101020b251900d1450108034902d41241c095400480c90b810403080c2d03524002402e44940c1f110402c014942c2e4076001e180142c01c10f03030140c0705070741079500c0e4001c0c0b4031280c039252021040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 142586043 1250 142584793 142584811
    0x30c13020f0a0203250201080604110423091521030f0703030509151b0c0f0703030c050601050306042103060b0a0507060b03030a0e13021306080405060906010810180605 74
    0x80c0b0340702d07520703c104141c082918105c41e4401e44e080100150345e0200e500c5030320245c2541c0021340d034148501004698010342d0720018903902e031241844034516a51180c0c44000c2d400381c51507400703616882040301c41c4001c1054030a40110720a918042a185417a41405c1c5101c51041606c4c0762551903160000c1c2c0d540402c1e015001300341ca0381d042c801d02a50802502c15040c00b007100c40001400c10030402242d01c090885004007003130300450701c1030308103100b0700841d90340c0098603045403040c0ba528034010302000141d50054406000d1400001a03e08011a00c00c0c0b069510040c4c070018001d805046c109482048210041050b07954440442c60a00c208014070301101681c5606468440c180b03842400d480d840c0100602075001442450112500150710454210048801c400321401e0041980c009004040c2c004000ea011110000741d100d41100f51a17000d1806030702a19003e5441d040718a640b8a000e2103010050341c414010081e0001a503404449692012100ca0f0490040c07a221802175900545204d44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 142587293 1250 142586043 142586047
    0x70e1305041202011517070512011d0c01120e0f060106200a0803070f110a0606140d030e150c070e09010e0607020604060f060909061407030902030c13020f0a0203 71
    0x24414000703036002c08008a4802442190790407010f00d8241511840340194550107542c910300e070980c0a1014001400002e848119440745000711280a481d4580300001070f4145003441c24040040401d014442c0078041e15107003050f06c8446a0f6400500c107441340070740309000b8040320078519201401041c1c000d0459594105180c48001349200b0304a10000e00452260720003c2d6150000d2200070a50742d1044079400d150502a9045174242c0340980042e0303c00441d40504203040003086101e90000054030501d90740d98030051065018000304025903900074002c500300050b44070003868541140344401c080c094401d0b040442e00003865180c4501c07a0040568a68400100135008209114160401580400034241400c0000006e17448400250000c2d21f07044d2550b0701d4200e00d0145801801c000d01c0002c4081140d00c10b641003140c010300100020740800950700c400300301c00e00e20034040c65409580040c0588004852002003150321080c0404801e1050340910800320004111005000040d40c9900615 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 142588543 1250 142587293 142587301
    0x4030210021e0a0f060b0307050a15081506090d060e0106090905120301180504061805030304030e030715111c050c060a0510030305071a010f08011d0307030503070e1305 74
    0x1d40b181a4141004010390021514030301040c90003035a1800607802c41400250441c60f1804241000d003903411654022400d240001030300164550400c0c00d00300c143d50782c483d240c0caa00342e5900000700440d4400b9442507080c03000044524003d0107101740703540f15900000d0b004000b8544076096848641c80303110200e036910600700a0000a0241301c0720400800e00076869507042c00c0640c0010783c80b005801c15041c3d6035000040c10418168009440e1442503100341d918000a40303000c6070f5940c8201d0b800c03000200c14030703100c651604002401e2010340d2684800d40c01c00700c00d4844200d03058a2001c1c40e400d058800c004818035079a80f030700c0d6001884441c60343d07410754400282c003481e89050740203031044011503c0c01f010012178204111100003074a030302d031500746c0c3d55403a28206440802103d0079034040414000c00005120b0250a92a40485114000a01020070b140260002c0d00801340c52540c81a04200680c02c002840703034008681c03002c018289220003c3d6000040340c503503480507019140c3c06907554240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 142589793 1250 142588543 142588573
    0x5011709010f0f0e0f011515020f0106030605010501110d0912170a0507051606020d05220602030904060e0f0408090a030b040501020304061a01300203040f11010507080f0d020403021002 81
    0x1010045a200300a0140e0035144a1034151000688900c04906823801c1d0b40c42802c901c24001900241e145000a0000b9500c070b0900d00000c050078886d00b4085200c50f814100c0348180030988105114040d100d0b2504549000c16903180480750700303c101e0708403840342d0184d401807000202610300e0301e0b419a5901d880e1101032402d03d01c0c02c1c4501d4025000b14454400c200582640000d5221a650a510b0810b441e1413509800074610401d101c10344601071504078001c00e1050707000015103550402294140555907a0f0040c410303001c6070940307940211070724150004022403145002042c3c0c2442c05070001c000c0355920303100c03010310000548040360503940000030b1200740a000d0081045540400f004083c41009000c006031980f1301d605031030803103448160004071042c11100c1c1000c840b000989410355492070240f50984090102e0002102c103c042c003030505005521070001d4501280d40110600c2c40c01194480d02801504071642d070351040740d001c000c0440141c075112010141c18100303400520f001810601c203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 142591043 1250 142589793 142589803
    0xc05070f090501171b060705012d091104020924070c0e0105010206070815030106120213051303050711180f010510021902030f0a03020303070e03030405011709010f0f0e 74
    0x341d414000c260111083c2404074141c4c10320810888445c1c0c0301c02102c40810b0240c003c20b14058019407900c080903400401c3e050385040300c3d615031540c82500b2aa5400520111603213424040c140506e11455401241055401444040c20041c141c3d46403803250080c4a1a0841e40c842c06816208085028410442040301080242410a60b0480c0d03543c1080700003952640020201420011840d0200d035150182407480070101c5c9010b00280708468030342181000c42038422130101c0c044c20036a0800c1070b0448180c418540150080c1c00855540c1d80746403811100b03500f145400355400307920005907921a40d40d07164841c2404518680700091881c16400c01048100140d004c42d000d01000d503054108a9404603998005502e8012606030590f814000b01e0325104045074009458400c0000c54424145c001020358424400c5659008007940b085041c15181e008900c1414040307061750181c051010b0006001540c13180f040c000001d10240d40e0602d2809440f402031880c0d00382c0342e403040c1c0c0d025002003c6c01f03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 142592293 1250 142591043 142591049
    0xe10050402042720070c0512070302030c030609060f040302030d0f05160309080f39070611030a0305040311120912060c0706020c030409020706020a0e011b030503070c05070f090501 79
    0x3800b00000d400c69160409078490b880c071813002480780094030004110111003a400071b02406415000c5505481030503c0c1e82ea0001d002c164801c1c0320380381d5080b4103850b00207561485130b0039038005844030f5220110740d0010408060003c9056000c24060050410814460100e4903407220f02d0126150905401040c4210b413666003031030030981444c00e0304000c540d54108640c0c1400c01200025901c03c255080d48000c0c0305100382c2c03400306254121031030241201100c1c1240416031004141c0307404995030070b03040d150302c49031551900c400d8100b80213038102d0368003ea20035070f0b00c2806802c200c03241640c002d0a1505040910584150908010942025600384a40001c070b0200e06c000081c00307507060005498205008103000145116000034509114001c248180c2c0d0040458080075034990540d8030303007800650030021001d8005103221880348010340c4a01c0c8800058803500059030070034007403a14200c656600080804082c00f2000703107840c00041041254000820050000c01041401c1400340b00640700c0680c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 142593543 1250 142592293 142592369
    0x903030f020d0f0806030c0603040b0f010503030403030f030228082707090b0d0c060306080d051204060c02010b0a0b120106020a0c06080a0b0d0f020108010509100e1005040204 77
    0xc0780e141c0d440d0741c100e034050a41c0001c03428134240c2e9907201070000b0b2a1225aa004580090002c010300c8108a103c8100c2802107e0041c3e1252050b80c84000341592800396100180000756078604460241d8040c2e4011304110700b80e0505450b00c030200c0d1074000a42045c0808040019034035808201c00920b918840900210424a6100740d020141c0381c401d50f02c588a02036922035955400b62001c00e07594201c00b41c070200c0e921540311140d80341d40300400340040c0782c2c5100700c007224041d103220080c0c03161254048a62000c81e000a120840c1c440d51122001402c000c1105419990317200a12600350750b400c50070f000205942400a07540f80d104400001183d8010790003001950f0040c1406c0c000110900082e8068a01c00d14043c0e5032641e50700056006812891145034105801004450511040840c01d041c850f0007a200e48403a130f6a0345081c0007403110222400340101a9805c01800f6542042c2c3e800c0347c004d410019014800c41c1c0b82e000203000c0340d20580c40229080204804074846044081e4565002d100f18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 142594793 1250 142593543 142593553
    0xa020108060402212e090c0f121a041a01020c0406060e12250303020105130c12051c0801030302160303140307021015081e0a0210020a050d0903030f02 66
    0xc0440c1c4003001d004d40024040328441200065551219011848030f2218900c035080000b01500e104440c00541d80d000c1e0500340c1d801d102c2c0010049001d14128404654140d9416081c01d0380301042c2c800070501c10384c80000b00880820814100d580e45c1c043d20312210403c099007403c685600d80013900e44414192074900490030f025041140f0b6412415442c0d0021007642d00e0018240355420042c1014084110300801c8400c0142c0c03c0c06544544440350240c9101750004c120319114400d4940c0c401030700600c01003861090280900c000001511a111054440e0086500c103200a140c0003241400f0000b0100000c0d50313000040052542c1000b40d462180038024104800c43e00315200200f403c1c01084981c44854000404104601d200b0000314242113480c080801042804c221040c043c0941c91050005503c40c1e00786403846500707034001c528105001c100051008403810b50a00c0b10100300d10003400c0940c01115070400c0802d8052200000308200c07030f03607503192007400c504c0c01400344054955408215400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 142596043 1250 142594793 142594807
    0x170603060105150c0a210806100f02150f0604050f191a13090c0f27140117010f090b041b05060c01140603010e1b1c050a020108060402 59
    0x1010424a06541055600b0301800300d20084980407441105a0001e140c8a2101c40d04107120b140301c261400000c2541c40b17040da0f80007002d012a0301c28015a4403da00c5449d030324407801d189004400c025013400171801926904e40c0d004181c0480518111611090b00384000c2c200b00366403502d4841d01742d12040c89030100c40329040c00c60915420070803038910034907500c1d80d42c103003000d0b4081c81a2400b8040d400c000c0020440c203442d856032034003400300150b0407100030301645004540740080030b40b640260794a2090030350902112000c501d80c1540002c449100aa036900d00500591140380e11050280a10b802800758243e28200020b0860b8890007009120f580f614400900042c48000016081a00b0019041c03c40c050102d01402e40800c50780900d602000024a0281104064202000c0d050788400f0b50000ca80e200c0080c10301340d03032082d41e2040b0960004084030b0081035410094995420000c0c000644201d030039903154400e01c3c0684402d58441d803050308035200710f40c1d208a4071684044141c1d410760130284 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 142597293 1250 142596043 142596049
    0x4111303110310090807060e010b010f081e1312030605130506030708030c010e1624030e010f090203060a0618091502040e160f020312040614090d1706 66
    0x115a0000070020704407400020301580e010072860084240300304040019920514003044c00e580000001c0b81e0307003030070300c10060080a0180302e042c0f506013041e16002d1030961443c07030898400100601c82c101000030045a01614500628824031130b022540d81d040000b01e0030f081c07141404140741209810541024410b200644503400701c0282d1680710403010940362130345000a410107805c0d4101b072503d031101007100007600348150401a003810329042522000303418040c0122982141d40030f501d0441440300301c0781000044580d600703486000da521380010848507051003942950400440c000105441d00050340544c5804d0201e031f40c000d07040c01400c1225910380004400120030f0f0444015545540b12094014800345c9610070403040a480000c558840e151898201d5408081d51691050241403030f800c3c860b039006561010a90089030021410141c90381c5001d149040028000c484031501d495158030741310260301c200c0e4081c00c110703c0540000d114000c00244030040f1501184035458104060001c1a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 142598543 1250 142597293 142597327
    0x1103031009020903010902040c1d01050c06070e0a0e070909060e100b0901020304030c0e010303030605010c0816020f060a0206060301050903090901030b0411130207021c030f0f09090f05060411 84
    0x10301c8110050388032108000028010000701070301039003140c00c2c20070003d2165404454124119001c8a0716101840d8071001185c0318050f607407076410300c4d034024004101142e00a0b4480746c02d80030300904064145446010100b400c0d07405a9580c00803d010000510000c001d90041401420070181c04814500c0c0001240f42c41c18064404e80301c41240009905074103174803d004480146400126000c4150b603500d4400306c18500921085c0c0010780b43c040d0100700c6601c0340c03211009103500f0240c0340d41002503250700c1c02d10304901c55000326484101c0716580607040d1100300c0506002580e0303070081c100c0c0d4602002807500f5500e006111410030740082080c41d809540f0015602e0640e5003105104543e81c2c1c49103000000440042c00d4181d0250f4041a0b06500381019001040520300c02e40d001d0340444024032840c0d00b0780d500014010080366065090384031080c880c2c6803e600600f243e01c1d12694050340c03682440d084030324011000c226581c0394801c0140605080c081d01d0004010450907a00d4180d000c04a18804 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 142599793 1250 142598543 142598549
    0x207121214090c0904031e020c030d020601030819090302151902060108030d0f02090604170d05030f2d0114120a05120a030b100c0b0612061302011e090611030310 71
    0x104d02860100341032510441c02a0351035400c080204c4094220f44030042c7d650382c891a800c512920401030b03008001c51000c5051412203030301010290400d0b1400700780d90380034075031001d96008100380f1803c00409696035954090074a44a404d105541d144805003801042450903500f00035580008010001050000219010403800c9074001a8146810310818081d1242266065001c0c3c8003150200b4007480351507412070840d001ca01110b01125008006507280c4c0000c07581d0020901c141c0300007540c0c50528803100c4054a620250070441d02e03480e841040300c0d040084c1c01071808111200e6445041d418100b10100c4044203200c003c0c0051020ba583d03481c0d64802000d00850726002c00b080c0894164001e8200103214913008041c0344124140c08030003040d58124030700686944a900b0040742c518204010720300050021100504510f50b036401074510450400c1608904001c903003542142c1c00740c078100421040011951782c0052a510f451401001e980c4040110f403490780042045c40188101c1c071803110b0807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 142601043 1250 142599793 142599799
    0x803251e030612050303010f060c030c03032408010605120a121412070206060a0603020a0903060203060d050703050304030210080106020c0d02060c01020313020a0f032003010207121214090c 83
    0x242514120201c0180001d03902203030014031201c14540803c140070000c0c41c169102c1c1148207880030f44d110800c4030010f07107001002d40400d240307890010109200760010328880e03c0034024068010002c1d0401c08408010f0b6200e2613542e555140c1c140036500d4505005100c5003105c000a20203400039843d50440c000c002c10a0406000d001c90f441c1e560010101c09a8517051088091030210303242581002c1c1d16504100d0b120ba1240889a401107611350180c42920000f01090391030082c41303400c42da1480020740c0090107443c0e02c10155444a00000c0c000c1082030040c0d449240903603161455441481016144405d038041030104213001404120b0b40000c800c80200811910100124024004503009101d88081e65002e54000010020f01c681d80c401030000c2548203540a80c520340ea165140f44203070049020050190303c0952440310b00e10201c5020161298000b4001883c0c01d0882e5940c039424502d55038501d0200c3d664a490b44080c10381071041c00740941291540ca4a5840c0074908151101c240b8100c3d588 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 142602293 1250 142601043 142601087
    0x2070b0d050601020106050306070e040605180414010e0a050703020306010b040e1b0702061b0708011a04020906040b13030b01080a020a03060504030e0301050c0705061e010302010f050f0304080325 86
    0x41a44c0c401d4225600420014094940d24204a00300605200402c04003d01032420441c00144c107081800702e40701584580c24603200180c45540d11449882d10555418403190340341c145211242e442808001c211911600c000c103100c3d8690b00c14982002416130081400e650144400c01208003481c0c2d40c0340e400328444c10010140088143d1840d40ca02074400c0181d001034000c9440500c1315041e140b03a20030940d06004036916070b0740e01c2030360a00740c1318040403070301e01460402e491040c182007070b40180443c00d0008100a0400e919101c22003800d0300305148210025441d00010424441e118551a0150909201606044805401003501102d55110003803900d5a900700050506102e01400108040000d0007880340c0c0c100001652640d810120f000d8595000c0d8001140e8502200a4003103002070300d090000140707a01c5d54006490000582d8480d40c01e01008006601480c051100218407440c03040c0c2030036880f414407000c181c94418107103c0404078204440180414290884903107000380044a580003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 142603543 1250 142602293 142602301
    0x1612050c0405010f15121a011d1e0a0302040c0e0a0f0806060609010c0b01060806030114100e070504030b072606030604080306030a020303040902030f060d080702010c230d030b0102070b0d05 83
    0x48403000405020280c5a02d0141d05003c41c5a60307447c08080c00c0c10980c1c40110000c50003460300321860034020a581d20806007000c0d0100600c0070004100107540050680000d65501e1300460240c442120a49000401610441241d40f0b4654844000f514602d0b4140d02c13641d0420051a9413458064081442044082081940c0e0781c400c1c2508039446e41e000c4007200455a4920b00500b44080546400e0b01c02c0d400c000400508600d40b81c2c1c850710406420b40324040b001d1600e814031215400142c000c0c01000f0303042001101007441200d80600503040c540d5005121258080c80710002c0c0c0481d031400d100c00c02d10009002c1e803030360001789458019030081a400da81c6d8444900091070090b00504c025098040407a002881204644c00b86102c0c9000c040345e9402507a5031400c00c144103d4002004140110910030030004d035100f402c0d10102da500c1a42c1e1295005626821010210fa1300b482442141e403101c0d003003812143d45030050030013481081c0020035581d400c0c03c0c4c0712065030068036001d08005658130005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 142604793 1250 142603543 142603547
    0x509060115031805030d0501030507141c02010c050a030e010801050103050106080a2c0318040c120905070918060c02010e032b0507170f0f0c03091612050c0405010f15 73
    0xd03c1c1e05540c450100d03599513148030144001b0300070034402a1f801d03025052002030803803040104001c0a0b08003d1820081c1d099100101905e020181404c0c0c0c100101c45030088002101003101c55440d0f40a034881c0f0700c0c101c07407400004007031990507040f0604060405004001c0242c1040c480342c1c0010301c2d07010100b911011840c00d10382c040040340b0805104024840a107664031408170040030008540c170410600042001e0034801504d80200481c0e000500c5200004818426680b18242d691310801c10740c0ca299030b542e8040025100301c40d01c0d4800e810300110109042096a1003088101f8205000a01c00042d4600303041d034890040103c2c4404170070720081568822200d560110080c440311540800c218205050002d01d985080b0020100e40b05100001c41c40a103002640c0c0d5100c3c140464001d81907690b801303034142e042e42003c3c140304080c1c4103645810441000841c002d42c050301c80032100600100003801c0c414500900030207641e0183c1d20b4000103010202002c950307003040d544888080201401a1a01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 142606043 1250 142604793 142604831
    0xc1207030e10231308070b13020402120901140609011401020f0304091b02150a0902030f0607080702010b1903080a0203120406090b0702010b01120b011b050a06050906011503 76
    0x1e4080443c5000000700d0021100101022403080203880d260322503403203068685407012002c1015001c1c103818440794002550700c0710b05650184881600c090304c40655404101030b80c00c201580321681842d2800c110200601344550042c0c1d84d0050f030b4510076801c0010100b40f84007010b00413481d00e4061050145410390080000c2204a00c000f02240d5560342e460413100020000d220055282d1003103408200c070307034604c0041c0ca00070709602c41408054580b122900d45d402001080c2040340c250044090342d00f6403110501003244501e480e0340f5284403526060100a08441c00200014032490307039409069403400b2810381900680780c1c0b200c4035503a60450560140d24600410315400010403002c1c080100300009500015032640c866415031000d52110001a420780702100034607400561400d810014048076600150800141070502c1c0e0400b00e00241e403d10544040c0006880d254003010ba48802c00a1912a180d4480c03140e00c05000103504108600081c284031b04000d200b05030b15054075030310b1084c003010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 142607293 1250 142606043 142606063
    0x30b010309022d0d030203040605030601030b100810290d14070e01080c0a210216030518060306060d1a280b0c030901030f060b070f0b0c1207030e 64
    0x30b50461000296020701d00316224501a20f860f03100c401a80303401d401d09800c0036548a61517009942000c0c00d056040b111508000d24141c105030300c4a003160119111541d0003c1c0c8070a8542e034180403480d0114255003042807071b07071141c0b1882c080c803440074902c030740c0040c0e41c800c0c8c410460f100d00342c0d140c540314080300240c0140c0e200d501c0400900390902c41034036000384080c000720a00b07132030b00c440b039a0b07c070010000c490040d03152240c080752100e0021100711543c1146100850601640103040c00b81211b06c90389004003a01007103000c22130024640c0c00076031101080010f42c01049030b000c7d10390b02e00000814464007a2503840c2e00d005481c1e0f01d5a00100d0112103240c0c010320ba029100354018000e0404122104160070343e40c1070490104000481e800244000b1502c6091007140218540568a001103009021401c1a001d80556460000c218170300b02100400b002d5002c2c2442c401502d2190410399245500582079200c030080c1081802c4c01224140401c641c044500e0500003042c1d50742c4404582000f080417 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 142608543 1250 142607293 142607299
    0x50406081b0d020a060806011404060201020901090b07020607140304030609231b1011060a020a0f0e09130501140703020301140102151b040807060806092401030b01030902 75
    0x80118000c0800a01800341c800c003404220310501e1590240203a00440c200e003c0d40041000e0401d00019000381c1540303820801c103145c280d001f209510149801900b141d00500010b07500026030149560788008848041c110039005245011030715030000e941446000401031184400c1031070300381c4220081c000c0e1801190808410f00c07052901e0302c0d084d600686402a00e42c140910000b03141c07141e01d4006030000c0c590f03000046846144030448104212204032482c5c10013000150004d12410304030602c1268020b81c00c0040142e162030b0b00c0000901041c10700c1000c0d0b01084440039210b0070560390814904d4104424141009202c58030382401405404841d000e04440b0000e1024411216410b9004504a50084980544180c40c41004a880c4c42c0b00c3c200007840d03a0001b402040c082c403866494400d1030900310388020320f030030f07581d14000742030496075413004000c01c114204000003400d0880740300b54081014a5a140c80c103c0100071619150b0b0351000b4141059a038500d03c50171f07640658040039140e5001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 142609793 1250 142608543 142608551
    0xa0b2b0906020301090e010e0a08090301061d0f0916140d1b0305070b04030b06061b0a03050705120a1d0105160f0c060305060303041202010210050a022218020706060504 74
    0x500706440a5030081c49403501851410020b10207044041c4200241c0f13401c00c0001c0c0c1104c00f059181c44501c4d070003c51005601d55030301c8c480000e54102d075031000d40d03d8000c038000021051511213042c03042c2c200300070480b0000303400103034201d002c0100604081c001d4130800031892054651000200c0d1441c103c2442c010030502e400300492420a400700e8260707007240d110380d086a003455210b4203580e4150141d444018062000307030020070076910308000a001c40341c641880c515010000103040701d103802c614605c184c1c0403d4000034070b0001d2000c14400149901d00c42d0008914201420400610b1075064000f03064000030301942c0d80e211030780f1520490381208650844801e0048442c108184800c0641d00f00700c40505c0e02010018219029005036880b862008018508003840c14280c2100310a104800b281140a6001181c0019406201e4103000c0c1070101001a00c030310f041402c00000901004403050051102201001008184801c444c00368086140140c0c031420949804806015160041c0d5840390070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 142611043 1250 142609793 142609811
    0x3051c0c0c0c14060403020105090f06030708150a030213091a070201060602070e0606070f060906050a090212070e01140a03021002010519110a050c390a0b2b 69
    0x884018078107010302a90748404070740d03922003050041c0603040441d0750b0008801c1c0030410266004202034416170310050041da442c1c40220300024442e5004980901c0030480840c180400c6a00003d156001040706890f4182a1419600028103024400104a0035140c42c1c522180070031000d41610364045240b0701000800d410b1100c0302901034401400f5903c01807194100001d48050803018050044001810360f910303090303a5480c0da11000821140036505140c881c1840d0b00052154811282719603c0300200199884040c8108114038040b00703602d542030341c01250306100c0042c10303201c0300f0b044444030076403007a6009165001c40d83c10302455001952203c4d181c6a1190702a40640215110303140207410b000d004a1105038204c00c8031000081154000c0003846500d007828064801804914110012508041301c0c0d158101c544480301c0340c500108941446128503400d146071000825898110b03002c0c0291810507100f407074540210005d6400503080c040e4002c1a05d148503e44210140201c4002e00c50041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 142612293 1250 142611043 142611047
    0x12030e03010515030f06010b1819030c03140606010f11010b03060a09031b0809060a1b0c0f12150c05070c090203010810061d0c0d021b0f03070b010303051c0c 69
    0xa43c150306000e40202d210240034180085016810b0300c00c0043c1c81408c0207045000050843c0c41c4d40c14468010301120f0001d4030f003884e10034201c070045215910300b9010b94114070308200b072840500d5008003580c0c084003e00500340e030031440754035102c2003524000170103850030f1480e24007525048140c2d5400d8000e507004c0c04500076098004820032406500ca040c1308134245941d074814000210300190850fa02840340240d81e18100c0000c4c2003803001442c254a2024207060501d40711000e5101c03c07213441203408410081d00083c016000300401c81240010808449078454000140c00c00c10744d044100c0c0c2e211881802c460040007924140b03074121000c51034142e1542c400300c2c0254428041c0314a64451383c80068100c1d00c1c42e01950007a200860050b44c0300d03079460354a0b0008094041d20072020303032001340003074102288030b031019101901040407036420f0a4407442020b401c1881a103260703e240c0e08100300c60b01c01700c1c202142c030340e0442e6410b01e002651070034416040500c0c556120084120507092600c0342340d070340e5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 142613543 1250 142612293 142612321
    0x80408090d1406060a030305030a150513020d11090607060e030409020313030908030313060c0905031606030f0203061c030302090406090c0806031c050c0c0901090519110412030e030105 81
    0x6070302c02049401a850708410440204011312008000813403c000080040202e030300180810108951420301103503c500c00100704130885200c0a0200307502140781d007105000c5003d16592135003560102c0d840c142e8024049100c92045400c0580000c0e120f0140400010007002154010040c3c280c08540f85e0800c0485c4e01d00082c00180103500007400000081408100401143d005a08002400c9084d0b42c0300c0e5038903005447c5100c4480d0034442d4070f09000030292014850340304006000d14190701541d09114002d01100e1500740a2a481881070040000302d464080f180a00c1041138078035044030246d00e18040300070740b0a60049079001818114000f800b01300c3c5030002c015414403901d444a80e0b940350400e159541d4441008400500141c8401010f0f1900501c01400c82c0300c00002618503555094000c00d45481c403e80c410004165034030100b24013060310662210084824040610510644043c0030156002d140107101c814400c2400010030940079444400c1e8061f009030007441907103000c40308a0510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 142614793 1250 142613543 142613573
    0x40b0d060e090c0f0907230406020706021603080304020303040b0414040b091003140a080c0f0d09080303010e060109120b09010c0302090102072d090608010612030f080408090d 77
    0x9100000d000c0b81030740d07501007815250b003c0301801d007400d42200e034002c002c940b0354080c0c00901071100140300381d07542d90080010914284c1c2d0079560303175645925001d0001d261a900e544440b0464201051072448007c0700400c5000f1a0340040406403a52a0f5000103411440307242d108094032000041c00040ea114410356042c1e0840b0111010000b6004000a00408020486002c1c003242c40f0b000080c03000403024a0342011020001d000c0342d50500c02907448002603030060003440203d50010001550000c8100060600c01f10310b4907000008500e03081e800c1e9a41d00060048000340552080040c40c079074450b07064100207040103200300040b240c2038201055043d00a840c03100d0b595080c10401509107000e8000caa082c810180d0003001a14036055403d0403181c1d40f24184200000e902c1c420b48015a02e209400c000f8006025000840c00d1a2010990859040794001c9100308030070401200443c0d0414400780b032002035030424640c01c0e902c41c0307048851071040301071055004103e81c0c113a006018003800d001c190 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 142616043 1250 142614793 142614809
    0x90603010623031302040f0b060a08150a050a03080a140403080703030b010e0a050103020702030c030d02060f010806040b07050915040b040303090e0411060c160608091e120f040b0d06 80
    0x910b02001c0c0024070510049540c12075070042450f80310014249540414111510703003070001840c0d05024001041e039406807182000003208081403041d8410444024801e6400c02c03203c10210030b1602010401d902403611000e40b05240104480c2c503003600425008000000c8201120790b280e86074500b14200e604404d000758002860a0035031000d80d401010707100044030008001d603c410f07160038011000b81d4132036001282c15000d154030360b20185c2c50030003800c464000b254025220750311f050198400e10aa050f444034105074003860a01c0007148800605540040e11450030a03611500100802d80e50a2000c01c252700596000034000340e502904006041628880d660700c0f07001ca0f5452044201d505400e84020317001c860340740344183c042d01d056401080134074944821344a10041d069446e09040c11564010404142140c041140b200c1061015130790070040d00c61086086603a102c807035a603e10310400038012018000038004030030000340f000d0fa8000d118110710b003661807400c01048030245c005481800c00b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 142617293 1250 142616043 142616087
    0x71404091a04050103081c0b0a0b03040203060c07030816111209130b060a030b12010e0102190309050c0f060c010e0a031716081008010c020a120906050313080906030106 74
    0x4661801c3d0250504903504601c10506050100c511121003005035890040c0c03480e9607110b80c21080e2510b251400c000c010307400e11036031246003d0040c5400c1c041c008114541c05074042040f500081d8106040c00d411084401c1e484011141c6510103030b5280c1d16001d00b10301c29100b854590040784620000401406100341c4a070b1080e00c42e079040d80001c1c1c5582c00d2600f684200c050011602d2544a94000d01701d620380100051480294035480508403a060b04156806940000d0b0000e900b010b4481901a943c0061a007002002c3c0542c442580301d81c2c0444405114900d102c1c3c146140703545100c20740300091440402000b8041203440c1440d81c3d022a008110b01240c4081c00100c2ca01c003441d8a1584158180304241c041242210b804541d185002400314130584900000403a8019003441380f08070003291a0020201d0608a00345085a040c81c618224104043d5400901203580e222054a80000d10f072140c5920319082864046102e024103178031b0030740106001c0700010301180c0c410800b182c000002d0315001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 142618543 1250 142617293 142617341
    0x90d050d0315030203070e09030f040305010606030c050c03030a0e100212160c0803070f1e0210050c21180a0b0a0e030a090308091306090906060806011d07140409 71
    0xb040d0704010311000c2d5054004100c100820030180800740c1e40190450203032460a905c0d241509004d401640080d18603030342d00c1c2070038043c55815214141e0711000c01c2c100030b4184101e20f12007a5903480020326800815858002c00c0000b05000c10040800c0c0c514660151346815404282c42007a07502152580d54694154030300b038641c0c0e03001c2d0344d86c8890a60003001c22031459503512000c1d07070102c101d445204204241903017241e500001c040044091412154050103d49141d4402d046c1642ea0242501100100c20400c40414070f040c41c680007000415030501400503030742c550418070480c07401c2e651600315000700e801e110100300c01000c05030720603104864100001c00360300c1c5050740d4074001d054a01c80130584a0000380b0114a0460142040600003000201d401c13086010400541c0c103540c2c13007500e000340c0741c0710000c080080d14020200074200800081546624041560320300041c40c0141400081031a4041251141300d1030f410851415208a101c5d5a1580c6d05440c50050807103802268404c60281003407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 142619793 1250 142618543 142618571
    0x60d0e0c12030a090b03131214041e0b0c2d07030b06091f05040c031112160201050402100503061908010605030c010203071109090a06060602060a1a0d120203090307030c0515070b04080906090d050d03 87
    0xa80e2101d034dd202e0060807880c0c18406035000c0c042144141c80391054003900d00081d00c00307003040904061889103200300383c10300f02441071007410000500300c1d0460841c14910455580c40403000c180482c8c2c0b0449011440304100d00041c1d00030942440c0c10841950000b40e080b21780001101014011104115417200d0000d1100c801c074207c43c0182e030003d50020700d003d0201242ca2080024617045000103026213400e5200488207000e094a948c46900180d445980401c403d00c0e051240000400c0d080c0080c5192401e6640c1e103140300c8000d5080c3c2445040c5260100c0d0300c0708020407818018690040003007251b42c0c0c9828010b552118116040743e0b078541803c3d004407090b155504d003400080000f030100e0551000c01c0d99540d580306040c05800b800c600c410300000d83e056a01700300180045000c0c0062030405810030041c01844140d00100045130401044440001411176540325402a081100c43c3d40303450500c2d00080441c8a807194540e030212038807000e8810300c08042020f081c0032555440420170030100d03200c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 142621043 1250 142619793 142619797
    0x315090c0806181b0f07141002181002010e0708030304060605180703050408160b0a0507020c101206030b0109020309070503010506060d0e0c12030a090b03131214041e0b 74
    0x2180501114100219242d000310340f1085805100352032150742003803140c00410380701b0703040315005a801c8403550004061110050164408203048528158503250310000c0c2500101d42d9000c1c82d500030b59180f81140042c6200f0f40c4804a01d03030758a00ae07640b150790340c0c845260303407a00160740c10756116140c41d000141c1842c0001440400390000388000d45903a079840d106070020440100241c604040400100500d0b00b81088030140032845034000880d2814000030100444000a007080c0540d8001000e0300440d03641c680e03041e07231070070b1140c50040c1c1c005a1440075a00501220340c8000c04968580c0001b181d2020300780c000e148100700c01070807074a1290ba181c0426090313500544500d40c02280401902c00000100d0b041040800c1fa21002c0b1141c407014440400da00d40c074000c806903500c2e01b02044545900e0390102c2034a009289035844c4905600705000703c4840070410441c01402c48200304586e2070b505014040c07000386400722072121611190780da60000c01281001c5e00c044030020404c400864540700c0d402c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 142622293 1250 142621043 142621069
    0x801021201050f0d15020a031404020d020607050a120801032006031506040b040806090d020703050d0804060b0409060209030c091b0f0c011a1c020d11010315090c0806 73
    0x2140e852164a0001400801814040302c140c100080400a0001c40c503242c1e4500c40e448906800181e460b13801d06801402c13110428002042442100240070240e0b4405071001d5800c0d8040700c001d9a500c05c030f032522501d4813000700402442101ca480d41480c201da00007410760304036405002e1141d034003201f2016001d0044908408203034005010f0011407080c003d2010000245500501801e1a20340c4070100b40600341c201e60701c00c4041e5403204003041648039090060444015040c00144001411035a400d034561800098900400111100242c20300aa1341c104a145801c050400c0012251505205020354000340305a40680b0803034040154504080403180c0c07040b4001009600c10182084403200c1c59070101312507100450b8144003c9030b00d05001e11032900c0140404c46d0032034880d0010414041e541900321454001d010b0b15420300d10158171005115582294003500079442c86c40040c005030001c0441010001c2c020407200d4011075007040341d500c003141c070802da6100c00600f6a940000c004481c10044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 142623543 1250 142622293 142622317
    0x1050d050616050c1b12070605070609030507020d05070905090d050913021207120f0c0f18120b01090b0609010f050a1209050307170f040e1f0e10080102 67
    0x1400100070090b080725801d8001014500b507843d000710030070402d1414030f2094085251030804078020040f0310b41200c8203a01026101d001d88403e51030846c0107480d5005d4030314090300b0541c944040b00201403180084820059000307182d40072100b0300e402c2541da81d10301402604d0449140c080812241d07070001951124400c0190745280c548041c04003071100c840486040c141406400380728002c10411368465a0b8132840940d9104000a0402003d05013510100000200b01c0f07485c24908041490380144001c480d41b0040c18070f41d15807402c8480384010a0300d0359015181c4503820130750000030011403068090403106511014440391142004000e03d40c0b18140d4858040b403225203558064500a1011b0710740c510507030406d007440402c013a510364140d81090348116076907000060f401040040105003048070500c11b01e20141428500403036101144514094005658644000036085c0b000b0740300140e00d100d6840f81c0c0c6420042d40c500c200104048283c8601003550015640402d883e0b20500c01d0700c801180c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 142624793 1250 142623543 142623553
    0x9130b0a0605070c03050102030f1f030c050f1915031406180a0f1b08070e0913060603150204030308090c0901090b030a02101211030108030306010305090a0b13020901050d05 76
    0x1c015125544000002c4500d60340d01c0d0000400300b0020b2001e1741c40b41000d250580c2c03035840c0400d1401c11003a0007841605804424120920100c0d03400a501c0c000d03103030242c441c0482800c0c0b80700005c070850b036410344a1142080308080811081002c0100c1c03418076130785803401e000c802410324509603868000c0703803129040501d131b18440b4210445484403030b411480b405000a9a1400044001c0650303181943c5020b03000ca916601102195220b20841d6000805141051720707442c080c000900c2c64400030300720055400c9a407011500307105d200d501c410000c5502020305140c4100d110000000394100303104c02e4010a420708000b40c181100420394501401008041403841ea0800d01c01c000144055000103405224901d0f20200503211400c04071901503036501c1e1121a0610343c1044020fa402c08074021a40d49400e0004000e40c00d00002580e4022400b401c000c2240e60b64180030506d001054034000c0d01c41c44200046c440c411010f0038488084074000d840000d256a06d80080c404c0f0f0001c03840c0014030b2030388030b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 142625899 1106 142624793 142624799
    0x303080106020f0a140c030115050907090303020d0518060d050a0e010204080a06020f120a020319050f0a1a03120913090b01031b03020604030809130b0a 67
    0xe1407000f0000b0780100780c11951208130b6414000c001045103014454004014003e00d0f804044c0038001300107001170130103c424285207030f10a040c02034203c9004a0740107407090310200d0580c0d40507002014440203112045420742c0c81003070038800340b080d00609600140c2d0368000400244002c3c45003c00c45007130100101003100d50740e81041e0101e0b803040008002c420408074030207240035001400141c030b507a8104210030a0f840751041007150140d110042104026043c0d001d10f029000b2110304100c1c9e00004c1c81d03c1811510140d43c100407201000c00000c00d01c0c0b08a070003000381402d280c040740c1c0310008444042031901c40c1c3c0041001c0c14810220f07d201c1d00d41000c070082c03401d00010701c01c144945c00080c0c42c2c4c1d43d0000b6041c0000f0705022010b800c030303681e10002a51918015036018106d03940c1c40e552030a0416481d04002c01d880e104148491011803104c2060103103075007050300200403d8070303145 = true := by decide +kernel

theorem cover : BRFrame.Cov 142446043 142625899 := by
  have h0 := BRFrame.cov_init 142446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 142446043 ≤ n) (h2 : n < 142625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
