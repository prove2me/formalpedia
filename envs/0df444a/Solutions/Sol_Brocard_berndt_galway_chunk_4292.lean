-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4292
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:08:56.087803+00:00
-- url     : https://prove2.me/submissions/a9f2ca76-c2fa-4ed1-8550-de51e007dac7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 771762589 ≤ n < 771942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 771763839 1250 771762589 771762599
    0xc0f06034212071203021504110411090d14031608031005060c2508100b131505090a0b0a09090201080c1207081018150f0b0313031e18 59
    0x1503124402402d080140344441c01e01074459001204c140088046225103622004122042508240603500c10002544880d03090001c00c002d90708401d258106a510610500d0101c2d51401002c4d900710350010302040d40440402d07040f50a51040900ca00c6485c40008171030303810006403000541c800c107034070b4802104840d211002c1005034400c84001d001543d10511510407000080c6028010820707040c00d21030b80c21503641402c00e0802090240c3c5a4016584080d4074404e410903151a000740c0082e201c04211400303500813140d1a14030f660080a00410030750340040d00112090384010185c900003003400003010307034619000b800b070041e5800403130010b1060b1b4003007407a0459000a89030000c00c010400703009a0f46022080315003000080000220317000705440010b01040c1c0d080d8000e40c5a028810203d2001c1c60070642d65210361a0368404881085440c1e420400705413803c080d0b030b0f0080f4080400c401584a1420112040c01189000e0b10190000107070a101180d049051088032041194401c0c12242e911 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 771765089 1250 771763839 771763849
    0x121106120406240801020309010f020316030e030412121205061f0c020a092406230903070e0403020f010902030c101e08090f0c0f060342 60
    0x1032103400d1a00030260000c100080e003590846155201c92140f041240941120350407100d0902c0c0e0f1000056075800828000750030428000c0325101031102100758034504002c000b5900104408001004250765130380c080c800d2800500448004106040016401000c10305200607e070365416900c101083c035032444181101418085c851050308010a01c2c441d01d0300484a50707540c010b0b198014420021105a9040142d0703800c0c8818000d4072142c0340c0090751400f01e00c8200682c1440090b00c0104440c0e4020030840300d980101240c8003a0307245901421a8030b005500004c0e40c0c000c20354102d0b458060100c000c9040d800807400b05104a01a40c00c0b610380515109140d0300303c51002001a401d80c001101443c03090030000c1c3c5440f191843c0785000c0d04501000a0300040000c015000b0500044d62a02404452041009180d5160300c01d40050f0103204094400514100a081078103400780b0004000541c0300c50341c060583c50780c21041c0e0b00d403180300818001007032601c888070780a810460316100d294800c50300301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 771766339 1250 771765089 771765097
    0x706020f0a2f0d0c09060e091e0f01020703120f021905030601140c0d0809030a0207050f120a0b010501110318040905010e15010302090109021815040f121106 69
    0x1160002408550b004180c440309000042210380d11810604007419190391041c6407101c0d0041007100c000c141060845020380e039880e03000c1040f40103000144412401c001c50b03219a195038560002c58074801c040314150034030401480040d0a0b5101050500c1855040110001220154681040759403803080480080340515003c19401d003054580c1ca414080c0034074000c540162050400700301040304110540050f520680c2109415001100c1c100c624541040014ac0c02107160b001440c10205d21071402981c1c3c00c0d80e841510b12600c0e04035213000386500c9007007c1f81080704030b2000380c421114107402c0c80102100288103050000d13120796080428004044103035040e00000d1490700e034141c00e0240c10030000e8038102100341c455559520b44400740340d1041000e4889207410540e86a207640c9580104803142c81d0590006070002e004105c0c42d0009a05038400030202e21040b207030303889162020840c05c052406960406100b5502680e0040750011010540804e2540700d21003d044071500303032050000c02c4c06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 771767589 1250 771766339 771766343
    0x30a061a0d050903041701021201150206040b0c120103030e030f0d0c0b19090c030308060423250e03010b03031206060f07060c110d02210a050f03090706020f0a 70
    0x19041c4007490803401c85810403608459540c00f141d0505455070504e801060803080080803d03940011540d05400708072014500414603071021500f031021084010703448000042c03006115024010000c1c2c4903130800c40c1a0788140011442000c00d6603106d1602920790160740000a1080c0701d40511180b0f44080081c1c102404540c1d82c2d102044803815581e0340c0b405000c09440c40707150010a0740c208011171003511848030000d018420080f880d518509010303020400142982d80603030304140310000f9013071180700c01c08813041988499054503510380175100083e0000c00008910007c00010400040380e12403035100741c0304001c4000b00840842d11041561b03d203d000802d801004244c00050060b2402c080038000c00c0394807640c814904201c2c0c0e035440048442400c50800450324407040151900c004100300698800540000c0c00c2000c5032000114041d003164000045e0b1030b00001d041c5000511503400da800c500e540800864407820220341c20741e140c074481e016810040c0302e0580881c0d82c0010000d0040c11a50b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 771768839 1250 771767589 771767639
    0x1509031a180f1002090609060d05011802030105091b0909070327051e21040f1205061609091a0108090d081f0b03040b010311030c1f180902030a06 64
    0x20f20320a0b0002d020350469411705a20400a002c01261600c0c1c60000744046c199031b0000181c03a40c10494500c800e0000380d41e0201c05248180014030107615800405a04004081c0c50aa5602020700c0312020b0f501c144c500362070b0801d1049040c46442501604440c5088502d5a103103030851190f2050005903490032480030b081a881540c51000c204c0c1580340110034403c440c0e00b034540c0041141c12041c1030b502d80003802c0010000005041218960482c0e000025100d11141c01d600c40c1da42c0d4071029914032019100c41945612482e0b10790005004101e900300620718081c041c041006013481c0c3c411142114680607000c64222070015600c00404506500c00500d591600c0c5642d03110850019050408501c4070703040e1b80d0454074041112a2100042c5200b584201c3d6a00b07001c1d810340c5400c500145040003d40c0c083c0e48941e1a84901d5a00c44d21044074200181c2c0040c10150080d103000c0720441c00301105e9400c034018042020502c00c0058000703500c1100c9003041030003030307641da040c510143c940007454810030b0b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 771770089 1250 771768839 771768853
    0xf180a06021603140f071401081303020a06150909050a05150105010c030e010c080c01391d041e06150504030f1406090d030b09010b041509031a180f 65
    0x1035604064602c201d41130750840ba40d044140c224103282002c650005290034400000114056074804065940142c210f4041c045030701495501941d0341aa0750002081039441c0e09440c24642d0140200d0401008190b20a0100300702d1400c00f9900e82d8000b02059415008071020107043c1440751034610304131201a0b44814541c0c40d41e4034116600c45007010036604000e14004c8002c0482c1c0c500c40a040b511100130700008022410103440c8112400c0111850386150300c084031040d10b42843d04000101003410300b0039410b00300f2081014034a80181d50b111941c480d20302039540307d000600140761504000130100800c0b525447c4c416450302c40d0b074140100d2002403000c0000b0f000051440e400303000001c2c03245401e10710880d083e01402e03007007030400c461003100c03640004201041e103645400780340c1d88850f0030f540c00c0074070713505001d144059403095004010520300c00d228a42000d41c8240c6071500210303046007036500381400100650768204001c0e180c1e42402e0303a02d1941500c400d840851202c0b42803041500404603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 771771339 1250 771770089 771770093
    0xe0607050613060207020a03060c0206090708030d0e0c030706020309011701260c0d050607021b0607060902010c051203011805070f030c0e0904050a1e081606020f180a06021603 77
    0x5a21000404403200c03134091002500507100c40316640007840c402c0360017280340324002800030710f001401008050300341d214400800000402000701e41ba10362654502040100051100d1881e081107012040e80601c5007880001794246c1c00b0000c4c01e110102644c600c00b1075440a0903615020200303004441005032050b461000007003540c2e070101030040c507410564841c1c200301c00014022055071141520325400000421043c598184582d0f83d00e500300000c04213240c140b25020604030300491400a102a035521042425a80500704c5200d45076440001c0310140105c00541e214290004c1c49050701520065602c044802541d004081c45844c0541e0f80b032a1182d203208080300a0000311450b031050240c1c1c49001461620340076181c0b44140d018100a14802d191403030980840141c0e180007444014110b890500040e42810448040d124065840360f01c600881c20b200b8002d125500003a807142000050055030000b6240300d40c601403030100d90082c000c0c1c2e0384010603a03c8c2c0801c1103111000c3d03612002c040c40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 771772589 1250 771771339 771771361
    0xf01210b0f030d0f031d030c06041b08121e0d0c030f0c0e210304120b0109050c19020106050909010e0c151b070302040c050712020c010c0803060103110a0f0e06070506 73
    0xd4682004a499003e142c00c0d00101d82c15a8880e0b23040c08200c0c2c005c4010401404052522445414010700d03d4118503494aa1803035100d44120307404a410410004039104042c400100c0c01c41e81c14080e2016954070441c4d8109240242944900480440d04209000741d060a5a114041d81001e8549540b0316a9040d00700b0410044240038041c42401d0562078845d280c80c1c0d003000030740702400800401e000c40704a542440070384107205a201c1015a4280340030001c10302209402d484c13106e10000ca1107401c0107041c1d54164050700460f00065004040501040300090301500443d013041151026a03d0000c1000300303104540460340c1841100c10020801d5000230006c0e0603107881c21103c0c4105403034840b6140d600003001e5820700f100410000750046000e40a0081d0180b544440303049038001880c14440c4100040c1601c207409201524200d000300000742264003980140d00c0011140c810f05a40d03c8072154060840b100c00c082c05030000310301e085400c1982c00c00788201c40303900b90840014403042d40ca200500c0703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 771773839 1250 771772589 771772601
    0x80d180f050d0c09060906030c05060a05040302012a1223030c070c0b030a02090a0b07050a1101020a050d05130603051003021026160203090a050f01210b0f030d0f03 72
    0x5a03c202200d4001501062520a403000340c004180041030003803541c14001000500ca0700700a00c59201004005605c41d040404c840c2269070a00707044d07060140e0a120b6400d54410602d280d00300f103c0500ad1340d41006800140050914503980701c21a8100e4041d1044160007011800034241540410100f100c800d030780c0001e03000c518803480e8030760341c42c0c0d856142c021081d0304142c86407101c0781d401143e01e03802c515240005e880585005d08226060054588401c0e07520000031001604001031410000c0e200e91007408005085600314040b54250243d841000f02664030a030011a800c0002e0400864200e10900802d0301507140031481c90021801c5800308030114481e00d04a400b8001c81d10180c1c000090005c104940d00041000c500060307180001c84100724103010314848045420070003000c4000d540c0c0070743c09030540b2000c0c2e0381e4030300714410719005031826004d08501c041d4510481c0107042c80120590016505107006440000310240004e040c550740303a0382c1442c50782c00300d049626880d400750301c242c0c040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 771775089 1250 771773839 771773843
    0x703021201061b0c08010f0e0a0b0f040807081801110a02060706021323040b01090e19110d0f150f0e0c0f071b0e0c09090619080d180f050d 61
    0x480100d103e10303515031aa1820304d81c01206182d46a212040420203039100d0440f80301e4082e8090500055669038180075400f0007080d00d50314250715000704090095407026254501ea2004205580350070903640004040703440d03c401400564440c5201c1c41003280482d001469541c0542058200710495407400c01035040b025031a24008441c0d0400281002c625407400e507003000c8035444180b805001010700c8143d840d075029a9050001401c81044105401e6481c140c3c090103900350280802c60000d460000351019002e0b02410880211301c046856242c2d0f449401200c110480070008141000ac008003268400e201c2c0d42c540c0c0c82c400200700030307500101c02c41a601040541096150017040c3c100c3c200d030b9400121003a05e080b92640c3d10346040c030b0342000c0500090651006c6492040c0b43c2901517408610076442c02c0b0340a0042e2030040307441601d40b020b4180c0c61250300d5010021480c0c03290291980c44000410f4003002a00a2041c07080c0d080700041a181642e01d8460951000d40c14203080c081f00508441c02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 771776339 1250 771775089 771775127
    0x902040e160909150c0f1e08010b070609020402040b0408060f04020d081b03310b04060e06040914090607172d070302041502030f0702042a0512070302120106 69
    0x29601040940c442c010b017684907034861004a08051400802c13188001c9070700c040100c000304400c0102904040094119100441d016940b8561481d22074040c0c50a40c100940242c004200420704003a0320010f0010360302002c04440465960134801115030000750b60294101222040c2000231031403203401406007a800610300c10100b01080d04075440c41c3d028090300000d06001ea8681080c10510762406604140c00c0c0f0f04041c5a1410401c4800741840703548905018030209507180348207504c450f010b903001403c40000070015800e0000c1014110402100c0400f560f02032880090103850189102c0c4581d074905005280c01644d5032021034100cbd494040300c030308100107114644a6071400b04014644900401ea50141e10b85141070b0000c620440f0303464250003550010300460340307603c2150007680e40e4540c041b03d0200301c140791082000c100d9a14000c00301043d20316145086a1250024000c04041910b4260410f490f902e03c94201d007280280c03c404501542c2c44401007000070310580d507080412901200d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 771777589 1250 771776339 771776363
    0x3010f0b130305151501030e0c240f121003030c08030c07050613020108010522050a020915120105040b1804050c040207060b0a1508011707090f0902040e160909 70
    0x486a03e403003030f036042000b0130080d54000c201c200001c01c03075038596400082c201070103940c1c100c0d06050780300d8105800c01070207442050b0090300b800203c2540710380104120ba0031150303600c16000e42403186a0003450001b002c80c1001c4041544605c400d41c144049a82503614202c1e20000c50303540038003640c80604001c120f00d10901000c4041a01449254003034606403040d0808001c16200150200c2016403089100d40e45103500d24100100c0303d030006400d01d1000a0000d100e41c0e80308401402030150404085c0c1111480c0700c20300980000c24020161200c5004030050301307030703070300e10411060303130305040403c0d400c0740300e0034107003a400c203000e0180303a400c0b512403426201d0182d145000f040c101d03041b154041d1348003034442280003402d0510f101d88070f000c0c4c914084202100000e00030041c24034a81071040d02c01c0388840c1002600601070500c0b02d400508918001071111040e03e610020240141c4030042c0d100340c2c500328001a8441d00062080741602200282c040c0f40351400c0322140c0140a2a94203554200d0012 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 771778839 1250 771777589 771777593
    0x15030a03030c03110315240f09180907170c060906090a1e06091703041a130902030a0507020c0f060d0b09010e01080f0a0f080c030d1401090e0303010f0b1303 69
    0x1002440c1b103850500fa207151010820401c00481700390021080c3c41c0180e101450140f52808841102c2c2e010030f0700c0c0e4800f80d8455040010545030a20030703500c100400d00150500150006c0403d00400f101e036940c141401105642000b10785030030749600001c0d4050400c100751109030a100001e465101c80060000c220711f0b580f10554003582d24680c4081000c0300d8070b00000c0c1308840c1c00208074406003400c01c00b46026200c104001555034459402203d154072141c2000d5041c03908800c0172200000868003062241c20342d00c07550303800030350825510b02a500d8105000200c410744001840d00c625140203103c441d4030702c0d10300140692640680381c0208401d4807101810003a0701c80d2480780e0300808041034403048642c54001400d081242c0c1900210840d0019200c0401150340c0c59400c0d2220b035000a421992070600d10348603071452150103085000c082c1014019558000b80030f120034103d5042c0705007480001c42c2d482c00107031640701c00d00810818070f1884801307020451000c3c01a2041054416031049150745035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 771780089 1250 771778839 771778871
    0x702060a1407120b0d050c0301061406070204022d040335031012110f011b030e010507050105040c060e0102030703081815161b11040b040f1406040515030a03030c03 72
    0x11745401e55050344050b1100d038003800d0074401c01004200140519580c00280000140b20340b24866020340305640104038083c3d50070076201d00f0042c030074580e541d060325501ca07c0840016500148400c0d81e5071071380c10752403c0e104000313424640f080864a00070390740c0108180b50118240c0d0000381070b00109200c0c4090100c1e42c1c401d50b544d92580c25015500c851440086d013400c004260070154078890411106901000c2c805006a0000c50180d90504ec4850301d0003207400100c41c140101070700600301b9030a1605100c20310040f8074580c001d0b0380c282e9a540102c0440035005aa481c46400c00007000140690b00282c02990300a140511944064041d1001c200f0f141810038501b07103003030391001c500c0c03e44202e5181409030811080c280e010748059004403031b1002510f4202d5200e84484226001e00c4c0c0340d8252540940d42c81d0320451605c030200c0410000d07402c1008150b81e000f2421552907003d1850304000c20541c2c80700907090100031400400502150003541e43c02c80141120724000000d154491001e2500582c207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 771781339 1250 771780089 771780109
    0x7140703050408060703020a0c030e13050103080c061b090d0f1202030c01180c0605091201110c0609060412140415080901140103020a060507020f040509060702060a1407120b 76
    0x90796040d031581d04283c011404d000000e81581e00b8144104054004a500090a40941c41c4c05040c85400c0044910210382d000e040040c1140c800d500c2c201c000320400840740054508842034800716142d66a419500d001c1202041c0b4501140d0340046c0722028082c5081c00c0e480c098907224031000482180140c1e58071400c2d0b560440740704056000882c145040310000d01c0b035400c01581040409800601d982c862508203440c602078801023040014003540703140c862100351100d544100000700090343e40845c088203990451425941d4034011840450001840014154015178000880c010003402d0104140c0701c42940c0b040321490711401b80305c00103040711280c07494061112281c40700c04891410008403400c442c1b1525002a201d0704410051009d40c48220388074059961504140e5a0b030340d0580002115848210182580203082004214008001240c600c0c094501742d02100d025031141e48410060707a0300c106c80c081c00422000009500c40d0301c02d22064552080c07032b0200003542c00407600400c1c1141e103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 771782589 1250 771781339 771781343
    0x3030307030911031f0c1202031302032b1d0d0302010209040f110f07050a0f21111b0d050a060c1b1101030c031410030c060914060901020c10030902031014040b071407 73
    0xf1035480305c0194141071006144400c03182e00d480c42005144140c01c0c444209204dd48002c01c000c45941c41c0001400f007052000d6110004e0400050529925009010b5030100351203d018034104840125000c40502819031807050068400d0f08105003513003020b2441d081140d0a581c64401e1031035000203e007200301042c4c015401901c0003049440301a07003600d2000700420b500b0003080070500c0c00f01d0790ba490110321010181701c40c0c0c20941800c142c1c01d000071342084440d01c0c050418010241c480003002007560107015000070070748410180c541040c00d0010b41c1d04580c0c8010b0309840502686030303115807003a4045000100c00d030800045080d400d41c400744064000f00c5440072407002020b01070090041d13821140c0020207661900f80c807120305041e14242c10f100030541c0d007400b60381c010130048000ea000b404034504217803006d4110a11440e6889004000d0181078409a009000c0d06030000743c0c030708043c0106541c0d0700341c8002600c000d0700c1d541e4034620700301801452070040001c6c00451100310840c500040c502c01d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 771783839 1250 771782589 771782611
    0x20a030c14040501060f270f080c090604090314070f0b010306051503010506031509010905160f0f0b030627090d03060504050403020a15020903030307030911031f0c120203 75
    0x100542082c0021100183c101d003040c0314820000540680d1301418509000844a407803101d6103104046080d49403082d07403c296420f200c0240f02242c0c8010000c0d107103400070380445240c0c1c12038542c181407000b101c640d124080c0001d00210900a011511003000b040982d204000c1040001d0464803100c034140000c0c3c0044841c0e64403081804034103680020301170300c0d01308110000c211b03602301403002903511079280d1314581011403140c0c00142420800e500210300c4581040a807442d81a502c3e040044140f454082c50510070705501c40461840540c8502106030380e01c480302c1a1641d100d041c02c200c40b40e02c0440f44156498a80040c950144c20320071490b50081e05100000c040b03000309044081c003654210b8016130300441c981800c110110340d00048440f1040e1300210958102e003c4650010064410315001c0da030544000010720580c0795140d07002ea50f049000d00e4215a030507018004151f2961000b0b070700210083c400c03002c0170340000400e90004050292500309020101c1d04021034005030780003103866600403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 771785089 1250 771783839 771783869
    0x80a020f150406290409050313080717060411011409040603060c030b031903030908070b041a0a1e0e03040e010b1305010c030210050a0605030f06040c06031a040207020a030c 76
    0xb1901441000e44c3c0c0190a00402880e40320380c92248001342c80b6070078801e548a890040030300c881802242c6003004072100224255840f062182d41e100c50520594100e40072844807118180d0000c901d050249501610a81d84441d850004645170200d0701c8800403214010800103280e5a500e2040303d000714444c42002c00d0001c8929005401c4542700140c00b80a074001c8045036400c125409c041c1d81905078142000141c0500a050044990041550051050300f2502c14030042c005500072490b800544190300740703030701c0c0c0c1c4076044282900d2070300c143e403091441c6000c00d40d1000e0b405a0040042e0303403c0c4100b282d0400383e0303c4070450071401c0e081c0c3c00700710f40a00000e240b4100c122400700c0307030001e00800e0800301012003841d07600a40e03900708480340c40da002d55038801003454001c203504140c0c01808014102d138510003460f64103e8982106032411036070b0040c101d000081e4103000e03003c1d018444641403884007140100c6c0052001952000c281240e1011121070044009165280244050403140b4401684 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 771786339 1250 771785089 771785093
    0x2012601060306090606020a0f03140d02030a0510030203150c190903060b041404030c020a0302060406031a030c180a020d0c09031b0b0d0c091a090306010e0103050604080a020f1504 79
    0x40f2040d6421096807142070100500056400007082d8400640c024038004901015017070448615001e03804030032403103a0010700340f5401f0480e500607501034015aa410009611900c3d030104145010b440002d425421948181c04c0b008101c9050350340c00601b6810036071500081e00620314030b050f00181c170310b80480d601c0f100c10b0050003007071700c280c80c40e00a080d2401c0041051818002240010050004003002614a00c1008540315041c5c1c1d80011076000d403080351030300c0d1120000340c09082d0094402c038030311600d80e40b014840e140024114180000c06040a02d0300e2548004241103c2e10081549030b6040d0200031a8018410b80d1040d5100035417603a5540c4c1d001804d618100704441e0680741c1e00322440a00140c2030001ca41c880044515415102200007425882400240d81400190340881070301ca2001440207141440d80008240c02c2d14210292402681c803611000106502030202500d00c0e40800000380008490740b00401003084c09004881c0f088103914051460617124244405090143c5070501c41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 771787589 1250 771786339 771786341
    0x30e101701120309050d060b19050108091c0c02030715050c0f070b0423180105150712050c190c0e0105040b1509012705121207020409020126010603 65
    0x405004860460b4205660079140103082c0909070040c0c80c41070500b024600704100c0e4650081c00703850800b900340b021240a008100c54252407070312460b4045110040040c41c20080032919030703132080600040c040050021001150300000c0d14100300d03094802c0a80120344440c1e250046d040200940e595140d03900030300c00c680d500382213a20950040c1a0b1102105102a401c443c064905460003c0324485001e5140f8142c2d04800d0400c890194000d0942c1c01f00c00c52800c44882c1c12816980e083d1500c1c1e14284011200d5490344c45030880c00360500c0c0303500603400034140c4504000c201d220448411111141021041e00e03410100d404400c071075064007080b04018a240019529004000407507080000c040380001150b03800c00c05000c03031807851074001800e010580c0517010440b0718200b0050f0130021510f03850552014030089000c0c540c41204030500700200c16800081c44400c5010b882d44040c01c00c8060303401e00018020000d012818000801d5a07080074100700313a003d41d800000709005010701c1d494290068 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 771788839 1250 771787589 771787591
    0xf040806060f0901060c08030c071505222303040803040905040302010f050f130507120f0203250e2710051b0403081c0608070315060e010e04030e1017 66
    0x50007041c401e0010043c454100021b10768040d044500e5035540d50341c80003000c0c2a48134034040200010f640d0408200450620751280d4480c08240144c40a070020048115000805400008007103c09070070340362240c45400010718095040450860b030804d51681111410340c1c000b5001a445196245d0401c02815824041d9640c9103600300000c00040c1030031924403180820081c070400320382a00324007540800a0810404001703150040384110903946510f02080c41c01d50950007039200740f00c2c1d1b18100040208007100703080042c6405036000c844a1400404010b882c0000b8070f0510f40d481140d40e00e118000d54a841008d20f10802c074054001c0030101c00500c0200c440107416244420300c5000908154003418048805407508030707480c80e480301d8035680c40b000380141c5007001e131f130143d800c1c01c20004401000082400c244c0b0311681150a0100c0f44210740c4040310270034403403102c1c00141800100300180c03588010030340140c001d02d000c01c2d1400c0048003046c94500040003200003d01c0f8480c03404c403070041c000011703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 771790089 1250 771788839 771788869
    0x304030b190b220b030703061805060c031314031909090c2c030c0d120908030f1207020a020d1b06110a02040b01090905010e06040c05070f060b060f04080606 69
    0x20b0308800f09441401001a80ca480c1000800790b840500c07824640d0304000020003544c4c001300511003012540203121400300f0f1030038125564400e02e404104240c100d070082d40e1207072002a220f80584500c075181c0c0e00100f000001c060950b80410004082e4280c00d003459024007029a440d00c4203d00c0c60450000100d5205005d076404001c99094146288843c0003840b00d80c5c0780e4041a51003503070480780e0002c0d0400c0ca5020342c044d44090044d49031000c114851902041150320341d1105105503540f0042036489100d0052803c1c00790104102d48044003140c0201c054004074148120b0300b1040c12540421803103402140d0a0b54041e1412182c0010078a400100300c0250003e841c0980700412202c1c0883d540c1d0030919802407140c3c0d125a800f10ac1640310f010350000038003c0500a010959540a00d0141700c8005d40311180550b080200f84502c845c0228110b860184d8003d09441c0309582c20348030103005005000340194070050030496074209950f01706c040d01c050f00001e0054541802e06500300141014034601d9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 771791339 1250 771790089 771790099
    0x406030504021e090105060c010609020c011a09011d072705100207030f0b04060e060c090301060509010b190509030f03040510090515030c0706050103031809111b0304030b190b 77
    0x210070383c00d031034100003203044450a4940740c1c2c0340c040c100d1400d4094011074111501851000c641d4000248054105d8071542c0303aa13509101072803548105200b040082401507070002c801d00c06110351402544100c665001c049407900b4095240c0502000ba9120b480441c4482501c41d0143c05001518086105200c4c98a00d8001000842e2455035084801c0030002400303840030380c60b0710018041c00f60347d400a6545500c01810307034000d4500340d015240142c1207454003601962070100007040f1400d003024071078140c480c1e582040e81064856a11041d001c40005ea510301080021b1142041b00c0d14100300180d02c68405101454946007444240640e006002070354404100320010300b006079031140c1a034448050480b803040c6e03569584040710301095110702c040041000d0b150a000205150b8030070504c040042d460404403602540d20042c0301e064034102c810500e490103003002004c88a8405041090981c00c0a1b0203403401c0a980307442c0c040000d9011202d030314211780196421203101186100d090b01001c000c0729 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 771792589 1250 771791339 771791389
    0x30f15180501110a12091a0106170c0403020d110f120a170310030807060915090210030e06070e030a05011a0111070b030604051504050103120e04060e070503180102040603050402 78
    0x1400071701504075007400d6407800703942d0150841484920000b40d1001e290b01400001c103940c0d64880102089181545020041c00c1d44000c039200103180e40844084940060041c00003001d6516a9820a1424400503520180e20001072980d0385805800703078481c2e00b001c4040c04410238681018007240310b849201c0011140104108014a203606010300c040c0da4002482c01d072201c1451800000070f041544001c1e201e028000840c948001d0181c2040281070f2017500c0c0070003012102441901540c0a00c42a140c1c1c1d904034400040901e841460210404440203040710f00000040d16100e08560383d817080800039040300303076807580c295030009542401020700f100144421351408810101178000a480588515203500106021044400394010042b0008000300139a50f07503807426200b1081d00c0003820000c582601c0c0d103120b9625017407084000320781c54a071400306550781d8680210340f194002000c90906c1d045c561682c500c0c0e0002440604080c148507200000c09080500403c111400001d28058241c038180d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 771793839 1250 771792589 771792607
    0x92409041203020a0207170d0e01021b04020f0f130602010b011b1523100f03050604080d1104030f030e090c2d0706140f040309030f1518050111 63
    0x40d2440c0c1c40080d00d4016112000c500080b410710710554040079000d51281c8110f809150301080f041480000b5488980300089100b0040e80c41f2a0305104075407d00c508801030a00c5414a0307001810500683c1c0809450300c0144800480180c00805600d03036143c900d07200502c03850782c0900c40c0020594003400c00041303109540213507007140b100000004000c90303680703028040d14881c5500000c1600409071110090300725020050314100d5012030340e404000741340c0030b800501e0b41d5074208102d00b0313250803030040d103096910303900c0304443e5911001071710f02c2d0030765151081c910035440c440c050b00145100700c80c406035148003070030010500d060203034600380300703601c1c48060007138800c076103c1220f15050714001804010114044484001001e41180d00d41070f40e0005904410442258004503010401d000201000d440314965698940012140100421072600040c40440c10007188403000b148512240c203000901f117042d003070035941c07015050000846030101d00341c1000000c1c005c48103201c46401e982d50601c0b00035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 771795089 1250 771793839 771793853
    0x30a0503030411010c0c0801150509070c0201050f0906030108030d1109060403061d01111b0d0c0b040609021309020f030a0308190e0102040608040c0b0c07170a0209240904 75
    0x41e00050411201691810f607a9024204a040c1590001d190b0044c170740e40e40d01814064554125013600100751010086050300d04580840d02500643e81d444540046990066034103138004200d10030809018002ea10066407264000c5010b0652000a90b0b103070050b840c044c100b550100902417002040034000e001d06500e4070001d490403250841000719441c0d290342000b49030105504080308207542019015111150302c0e070000d011030782100465290b8164000d0705140c40d82250003050000030888480580844d4104800c10f4020380252030000c1d0151142d03000030381d010400c84a0a55054850040a003545080d030105100c0840503806000e000e20300e950000c2008500501e050044200c080803070701c2c035126a601400308040508002c6546503103604e0007802c2c0c004111000c0700d011018482c00300d140032980e42900e032109100d00040821900704043c811007900c0559040700c0b0b9124a001050240e03a030021200d003d1813802ca10036200548000c903141100c8120b044181c020000c0e001480006105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 771796339 1250 771795089 771795091
    0x5150a09150207060f05040602090f12250f0303020c01080f041a15030a0525031220100f180317070513060908060f0c07020103150b070305120105030a050303 69
    0x111500180d4604640c03600e600100f58810201743d07140d192070304120030001a40d0003407191104c205c42e083c4200c46c0c200200903a0314004001210035400050b4800c8500100c1054142640c94000406102503203582c0c8811a041e56940140c0c0140e1014064016950300225243c1e001050549100a149013036155440d618645040c1c0c40100d000243c0095013a101c0250480d0991000500b40d40c246000d03410115076507000001e10490f0b80b003050b07004407615200001035104030303540401000c00003105018144c0d07940c807000e5510b454800c1d00c08004008280144110441080b82050004903003102c1d407280b604998052805500c01e21368010b2071070210f81c002c1d54103180990f524181c10119641e0394000c9440d8019031060070b2070a088090085141500f000d189426140b100089403850382e1500c401c08845c01c1d0650f44040301c01420021038015511981004400021080c0102131f4103035290400300071a803101e90187c00040b404980c2804d034404c400c0e00c4ca0b0042070128000c1200c0c80c0c1c9a00e0780da440f488 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 771797589 1250 771796339 771796373
    0x32b050f0910051323010e03190f170d0501060906050405060906070b1e0606090f09040f050f010f060f0317070c081f050a0608073005150a09 62
    0x2207004050100c03807203003044a4107030f8040d00742103107107a40c0c40426000d508040c1c001c07070041e0141481c85c00324652207a00099440c050040c01491151910744411740c07016213840098411f91454035030000030400c40e0300c12100c8a01c560611607510b450503e105000c598060b0461010007151400403c4000d5000e0160b405641040701e9082e61418035030300141c0240700358180240506514010001d1021441500c2b441707820a01504031426030b244000c101c00340c4110400c841d0711440b80c031a0404681071244105074024451090300070002c2e0306840f0030346441031000000981d60345034000c0c0494182c107401a00c0082400147c5800803e096643d2b000179030480c2070f98203841d06d0000c9804018440094a5440200050021ba98030140a20340d211000d4146e402420805030422380407542400da50310481048401e00741c06024803c3c2060201c40c40c100a5002c01c20017030790062508800c003001541c1610380c440c4900010607003201130900403a169140100b400e401545800c80450108085c1c8100d00c1e01c6007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 771798839 1250 771797589 771797599
    0x302010801181b03020403330b040e01140115140306060906040b03010308070204051f0e0702010f050c120906090c0f01090b030414010513050a0b070c02032b050f09 72
    0x4442d603a0801c001c20b03080300044480c6050700c040c0340000d5010360051003075078061030540c14200450040c0d10403440c881c05d801c0f40d28492502c90200d00402603800781c036105000900100d08410304208542c00c2d102261402000212141c00402c140c4411002e1100318015134142101342070410703c2a02401c0c00001c1003540195000948070100340d4404044078064000e030319107203850b941c49080034007513600680705c00c901852503c400308035400d00300701c0d801c44c2c1c5180031281c8194039800c000c104980483d01078615010342d900c0b940f085040c00c181c1d0051920480c0740c1c10310f00391101200011900b1018001e03102075800d4004505210781c035600858041c3c4808020740300395441000310001265454400d6114240d540004810312080040c40085480702540c00780083c00f1b2500c1c0d03062401da40100f14100208194040b0b000c00f4000707142c4d44210344e03001940e4100002c0002481e00824107010034031068120b01c1c0818084140048450461045101c0103850800d06042c030030004d41013640f0895004512403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 771800089 1250 771798839 771798869
    0x7080705011107140a080d0201060e070318330506031006150c051e010b01030c020c010903060f090204090302281109042f0405011d040b041115030a0e070302010801 72
    0x952035200303401c8010a51541207d100d0803541200074002e0a42d40610004005c41c0004615040d109000e840d4610000c08046d002c050034982d207050071100c9a40ca001590800001c100d410010649013509003801d502c00040380300d1521030f04250034141044000348241d840d00c50244205410a28210002d60035810045844841810501d203410340c1000510b5072a44c80318000d4800c0a0190407502c07001000f03032004d0141002c094002ea03103e41c082c00c5000e001400d550300070000305680d034100084a41d204840001c0300c80b956008203056810303102c01a005688144a01c407040001003c2002c2314a880300580b8503060f651740d981c448c14490310b000c418441d080d1100803d041c862004440300841040c0000c903e0844454002d284002d01c42001e540d10461400c00001500e90040c0740000001041c0300d00380440b50340d541d0310301d201e407038010700140c45100d80005142e41e00d80b240308508540b400e070f07114219180e10b40000c800c41500d0507980c0035845c940040c4405c00c0140d03084049607064400ca85145a02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 771801339 1250 771800089 771800129
    0x6060e0c161106070c03031206081f0204030515010501080109050c070b07200c0112150915150504090f0903120e0c030a080301030c051927050907080705011107 70
    0x185620280240764000e0380003a004c402c003d4180401400c482c8662110702e011a8081c05a038200d40092240c00e266030840b049102841140a00c0c458040c00d402c0b20041c00c0c0b5403640c507400d2805c0b201d070442c440b00304104001031102d5078003e60010300400c05400184858036002d104a007240c0500c59004002198600118514a000d80e00025480c110180203002402d030380340d0816540c0304084a52400300e4504003a200050354103000d00806103504980700081c0c1481d110140e0020311241003500203002c1001c2c00440c00e6864002c41300d402c03035219a520f98645003044507800460b070140714000c04243c0b41800007030010740c10000c0c00031030150100d400070b140d1030880c812a042448414032298075000b40c0b01001d04114110001d1416a4010003e002c4000d44a90500c40a03040b00714102d8440d178100082003100302c81010101c0310304403070094400c403020304100c0b5181c10740d00151003d004030b0300080c1040c01a4a8100030303100041400340307000c1c2d4502d40341c0c007c0c890b1595100d000c0d411134132180b211704140c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 771802589 1250 771801339 771801353
    0x4140411070218010311010905220207140f0106150f0e0310020a02010203040510060807030624030510140118020906041205031312080301060806031002041206060e0c16 74
    0x41c50503005070610314100c900d00c0c1c02161110090008407550444012043e100f54860b201400507654040c0c0f2041d24001c00342c0e01405801d0b50f14800845485d000c01c60840011b007017040c0804c3d00c040e00e2004007205880203103200d0955015030402d002c100b08110075040401d40c40700c010520305078581012003030742c80d050300130070709000c1d45551201d40349000107036000304141d055004510481c00b40c8244d5461010902210040c0c940501c1a00340a81c048101440800e0f1140c0c02403811005100c0108121020b4101c08a01050154400d56203608920303074070201c41c0c0c224061403c080714042c2d04000990306000e1f03440f06880e22103108004441c0e0200f002890390701d80408440150800444089540e50680742c215540ea121400395143d00b0b00c0d01c0b1001034641144160000f4165224400701d0840c2e090460450701e40900502c3c00307503d4406d40361100e801c18ac0c0c610040c000b0301422382414080c040780381008000d0b1809075009030808a52013040200441d400c4042d625140b82030310403010341604500f0000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 771803839 1250 771802589 771802597
    0xa0e070308040b0a08060301150e13021804030201050f0f13050a0803180d020d050702011d0d03091a04030c06231903140402301002090a0b04140411 65
    0x101400d000082c00320b030b450120405040078a90542d41c940c001e581e003c0a1600b6200c54803001245000d103000c040c04124014542158015943c5686052031001d40d00001c103d1100c000c04640c060051506001c00d2542c280206a8044681f4501a5040c10050940700e148980103141004030400d0860700000c015051110301c1400f0341002c149500c90800300041c1c0c03a032540c2402c4100c018440d10380c12901c00750002c141303a01510741940f42c85080c00340c29001501d84010110003200d038151101c0d60b4031525900c50aa44070b00b18000d507520b01c490b070704088804490b006c00703039030070200d0034400d000400c0012100b0720141c0039035980c2d00e04107003d00d00c42407003050341c042400d1000603c0213020070148110b04040b0240b45007603605a406001400140070701c2050041c0584000e9040701000c00c10004400203107141c03c4ca000c0082c1803114004095038901400c04d8901d2080b20b03207980e00010101e200d4030f0200705040141408007800c41c0b030a0310f45664408802c5116040314081c0d503ea868186011201100303403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 771805089 1250 771803839 771803843
    0x270b03190203191b0203030c090f04092406080c120c03060115030501060306030f1106090402070605060406050616170d0204060c06050c090d06091707050d1101090b0a0e0703 76
    0x195181d0501450720041030603100c0d40010104d240c100f10103880700d1881402c4a01070303002d40145107542c41d01c0c004281c0f0366100341040307a004500391034020819140c602c5848030072405180001e103c80011281c1c15005551340d0188180303641491001d008003440400e4040d6144401c0380c1b0188147c003100e192030305000b02803201a9040c003914000048132070141c03550320b0036501242d81c02c01c81c0742e0f211007003501120403a010180c6550742c4200040001003045e81c609211140003000076003050403a500107404d80c0d0161400725a02d680782e03014007059003002d0050728082d100445031039050159401e240403000290b031300080c1c4035180b03100b6142c213010791000481c2e41d009220303002596950f0312100094914200998119416490003000500e882c02030010707200c0c01a001003210304480102e8540740081c01c4a5134003076440044508001c1700c0c13507554000a01c1030714401e42c040c0200501032417026047d10840e0318441040d03414503201c48001030b060a4441d40c40300b00501300003900000e40e4207903460450b480e040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 771806339 1250 771805089 771805091
    0x304050106051210060e0705071e170c0606030303070212220e010e0a1e2c01061d0f1b0702090405031e0f090f0d05060f07270b0319 58
    0x4030f0300100468000c11990500406104c00c03980d44200c0050040100c503005c0000303101340903c400080304030401d00095541d04150340300042c01502d80b07000000920207800300b0b0940000e008172028800344203295005a04901a41c110300d000c0314003035142c03008a020f500b03030711900040009254020b0001d00f100d458202c80346219040d150881c0e403160020030f0142030080101207000403000103c82c00351074a2076010040340c2e07642d15000c03d0070741d01030070a9042090020401c00d59010b07034107001e03030710420701102d4040000c00c031585002c203090101b02c03003001314100035003c00c420801010204000340d07401801480001041c100c2003041c5a80707034001c80d28001c3d0300069071400d0105224001000c0d00d034440041c148100c08032406100780302d03d44a8180070f1280c0710700078001c1c0ca1003450125024411000090400035801500307903140d03420400d003160501e5079144030030b060145550b07002c4540310444c1c1c48024a070170000c512607802c542d0a0740502c00c10807140e20000001c0d8225020b8600b8081e031020fa050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 771807589 1250 771806339 771806359
    0x2603030a052503020d050a050610030510050603090d08100b070f1a070f08061804120c022e030e0309091503030a0e030d1e030924090309090b0114030405010605 70
    0x3c019500158000da001410030b4080b806004a6218150207080000d10440701e00110078801e501500b402088601d01c041240c900081e551614001544a140c81c040508040c102000c0043c1c64888080d145441c0c28061050901c1813a4114045450b40b9401904504040303200c0c0c540f56180c01c1d8655075005410847d02c062003285a000031f2904600125601c0b03c1354a503503410140051042c24650108101e0014408240070a810b0000126400500d2414001c0c11005401013881d01441c0540d0404900d45c1ea00d001c001d41034280b101401001303c0e4681481400581c1306031030340e42e0180005451240d45041c000c6420b030481d42e046005040000340660791030b04612a0050114070b04003071000d020340039411075211b031180326011000c001002640513000201d90380404030300801603004125600c20f074002002c0341240d824004000c0c201203c43c00418450340c1490010443c01a681c41031a10314203254141c00d05a820516413901408004009622035449003031807400340c60703280d00860308030071410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 771808839 1250 771807589 771807661
    0x50304080903033c0c0c06090f03060c0310050411040902161e140307080301060c03090b13051201090b060f13020c0a03140a0c030c030c0b010806012603030a05 70
    0x4412900003404e00c42c1c00346590781032090090024418142c50003480e40044003601058075021b80500003c1c040940080000d40e0b1100100b8984002076032802030240c804800c0003061741e041c085240117440700782c5061240e1082e000d15011180210300840b95129004160f000004410141c01914150410840e000303ea0302c50301540800c0415400c00c0c0d80c9010403458000c00c0781000002c03a5040c03035011701036519507840d00104980035203c1c111b0444c00c103c0d01074000280b414680c406400701e10854615428800d00d040100b02150000c0e030100c640507410b0001800100d200700c428958044015981042e0407241e1034001502019035546c480000d41c404285e080c8800000114108190321903240c5e8a510002e03422101414018064400002541c1c2480d40700003a1041d480104010f21a04101c14204601d0b0350320300214000345c20084c00c644c40a0010041d2005484407298070f10101d000c01060402522104da481c1e2200034039103c0601d840d0340100348001d6030651510101014032109400b01b005030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 771810089 1250 771808839 771808897
    0x6092511010e070603020903010e0307020a211b06110a05060a020f0408070f030302010507080c09040221090f07090204240c08070804061823011218020307060f05030408090303 77
    0x120f1f850096103002500420280000122080190001d00c5c0851191808025a01841240f13a00722003006e04106580009072509a20b00c1c008402c0852524101e0b041120040c40d9514140c01a04a039009604010220700c1c00304545801c2004628050307034643c5070a00e010740c0d0344100d502c030441e60722440b200020180710b204461002d0b20b00c20360013440072b80c5803100704613421402902e00d40d94020040104006600d440d90060030360600e02800d50f26900a11401b14030301110071140f918068002d08074a0900903801d1000d030016240b688011030510303080c1500d41b0910040d0000c02c048040c002c1e0b44a1361050b000713100004807203500c0070265546d0441d52a000c149a0010302c91000402c0840d16040030503949100a80c1c1912400c03070780034071703820031603000b02c0307644058154094140050920714107440307400c50061440d00507104901e01e104402078818145480c0841d40190100031041040b4208250302008a980040d00510400c1d11100d01600007070031881000c5415844481d122800042c0f01c80d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 771811339 1250 771810089 771810097
    0xd0312061814100b0d0b03010f020d020a030b03010e0c0904050f01150f050102010b06030a1a130605031009020901050d080d0f0501060e010914040f0f0509030306092511010e07060302 80
    0x2c440b101c8641d0f03191050343e0040a940fa01420300e03c4401030008200266a80d400b441080f20000d002181803084140e40002b21b034040c1d030404401d6900011584075141c1c15008044803d40d003900200008024440d185844003240f2954900c1005501e0104061100412509442424000003040030314008525415020000d201c0d00601d650f070944000758641c0181b280b0504100c0c00381000d440c50361070203482c5008080358544002001e0003c2d08180030343d100c110407121818843d400000711a42044201403421300e820020410043c2084416001611240c181078111501039076000112042351601118a00503120150342c0e5a10f01490b0a4000b01d60f40c0060307040b41c00988400440621004c011110f21049000d21902d035040c214503400c0d1414968094140c0448414000814104002808c41503c105481d265210740c000f00a00046140a00b40e45403c500109268140c2c124906110040203520700302203400e010124070301010144c001c0d00000301002110054070015500c900010b002904 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 771812589 1250 771811339 771811361
    0x19020604350f070b070f0507062d06052404060507150207030305060a0518060f010e15090a170709050403050c2b21021602090f06041a0d03120618 64
    0x290100c041801c80b402500c0c0895106c0c0155249441c1003502c0c4c446501401040441c0107881c68214402c21007816281c0740481c032004802800700d40c803440c20003049074071428110401c8041103103180800711100c582d01258219400d608106485104905129018000074400c00c045240001408001c040e8150b02080c424501200c043c8081501e41040c059400c55011443da904400503021504030f00d0403040520f02045c05241c042e50458850002c14504030580e24600400500800c075080c0620b490510b64000e00b1403011804480d04080003100e40d600c010307100c0c48602540d80d8000c507003858860703421560401c1c6400216000550301c0325501180200d06040386030f1030703001e40004920301441080040840c404250401141448480010300207621610400311002c542105510040e210000058440d161103501c02c102803410400784015203912a0702c2200502c0d50b818100c22590301c0411440e103080e010301e40390b40421014107042d00205259003100036040c009524000b0907020f1900a480b183c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 771813839 1250 771812589 771812603
    0x703181202061501020a02041d0304030305030a061508040807080405060f070201020f07080a030e1807020d0210020f07030309050709060b09010315030203250f030819020604350f07 79
    0xa0f80d11a0707054980d0044100b05801a009204c0c9040586070036000000b0230324101d040d41c840117001110240c40e40d4403541c8100e0101d4008800c00102076024410380c0000d0211821009404080c1c41c4010115240100b0051213408049102000d0040c0c4134192006800003501341c1c0d03903441310200029031540240d10100d00600c01e0460240c81400b012640c8800c803030803c0c00410b4480b1495400384e400c942a540000d410031450085401c00911101100340910b1031a009095902125800203080600041d0340420190041000b041d44c3c03118507044402031074040c03030f0000e8045220300c0c1440c10035111307134070040700c440c10807202203003a0b00c60344004d0401c014240c03001c200c0f41c080741e076003c840c000c1c080c4000780d41904200080682a03803400c2d0f00f42010049c1c2c140b400311990301d5010458440f445034000f911003031404a0b80041c2c0041042c907080c01507941d80024052807901e695840c10400300c900424403407a0041c0d030b100d6403505501140070b83c00c5c8100e005460700c5191a10700d240361604514026200c1c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 771815089 1250 771813839 771813841
    0x307020d20190b28090503130f1a0406050d180f050c040e151f03140705040c020f1c0203070b250503160c0c030b04030c05010501090c0c0209070318120206 68
    0x40d03030304c0500604040b62110a210304001040d04201c0080540c0302c0706403440c2c0407c02149841c030100c5204040600842888090000d0520b41012501201c20801c10302c00360b0b00304414400c45800c02c056a50b02d80011201080d29400d4224503107488102e060f00a044420521810040140125025442c00026182008840340c20a030b1a0f0b81e4060400000c0c1888981e00b01040d903d00303d0031551104003060f00fa4015407550307a1307a03901100d211402a840000d0704040014005442c10703003d0000c81c400c09200034400700d0305c400e038a15103c40200c08501065001c1c800c0e001e80300f500a000b940e0050781c0105001595280100d00c07403402011030302c40342d0f00c0070120410301042e481c01107041c1c0c3c1c05071002c0400c040d0015070702c040540cbe4042c4410300a035881400084e00100241c24010b03403034401d82c030a40e50003206180354a85142901d4042e000000c10500308111755843c20752210b030344d08070541c0454041080703403a1080240e00500c00d02600014110740780b01c910040c821003006c00c403996038131a400c440366 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 771816339 1250 771815089 771815101
    0x60601080915010510030e07060201050603060610082701020c06091612141002070f060b0a0b16060204090507020d090501030203010f17070510020d140307020d20190b 73
    0x860080c0090542c81c0405a001480107080000da001658181421b0000b0010b0b42512454a40140d40d0300040060b034581c0100403680c00e00788035050b00310750103130740c1070703030b603600800806004600014000fa02c172208042d03010b641030300d09141080ba0f1080c1440215034035603d0301d0409403235580469083c0f0180c402d040e41e482000105102c018100d400741101020705c0101551a6442041685c403c801c1f10701c03c001020000c14102c5c401000c0d900e1241005030048103071403034404c0c191280d0400444c442c2c45900300802080314100d003240c0b044040e01c0030042040a186c44c007500240640c1d04440211480c00c0100450700707400040102c07058800b0707101c00148560b501c00440c1a031009004e110701daa281a00101300b000540e0f03440c80302904505003a1000d003900c500118140082600041c070040c0d0040b40c143c4d00a60300840c444045a0544010340d18510300312901a68448081d9240402c001000070181000700390040035440340341101d400c0d240000800003103c40c02c0400d520090350304801c94030200f44 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 771817589 1250 771816339 771816343
    0x7090f05030703030905090a0e03030a090317010e0c0a020f010905240601050d020705100908091008010311060703090807080d1409030c060c03120a02030106090605070515070c050a050606010809 85
    0x2c201c96141c0e586400f65824003040c0003030703124064602450a511908003003100e0600b80080d601c02e07650080005100341507403c000345024034000440c0c070580032440040c0f00c0c00100700031040d480861505000da0f154040c8404074a00b0240900941d101d518141911040040c02b02e40d08a00071030702c542d501c158401d1429134540000c025103a07a80860410443c0d00380091286e0003801c0121300604c180c03103807803a40c2a2440161341001030104c0340d00d20b0000e03000b0300a01d0911240b201d003c51a281094042d070541d5180f50710019100c0040340b040c0030120b114070400d88a0882440588840c00a644540350303586042c070f581d6001c03d1a50390100e07045505030080780c05020240c82241c00c00400512009480000b4051998402c601d8060f0342c1c04100141200d40050090190288409c80d100507542c2d85807a80042401e54660080801c11104214200124000041d00029189800180b1a840d00c4069040e110207010300380c0200203010f803c07419014000c020840522070982a02c402a20303540d00d4401d56 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 771818839 1250 771817589 771817603
    0x30901080601082206111303151a0d1b08150f040f061104050d0503070510020708040b0a02010f0c11060606030c1206040e0307260306060d0902011707090f0503 70
    0x11003502c4513404040c14512050b84030113142c091440000d8002d0615194010b90b40300700d00711b8028400e090020010001c1020500207880100101000725006840c444d15a0800300b2007450f00c1002c0144101c2d040c070a500090113580c6001d58503004503180c0c2c80078041d4460501d4213080c040804880006a100242c176503080e44900c3d80815404400501c07a82c803400201603078990721140c45030034000403506444000650542ca40120010f40e180c00c12494001d10300f14004440754401070050001c40c000901902c1624262a0080c507866240e86640004074014224040c60181c1103003031208040841d5001011420205900703019500e0030341c0c03020f0922038039100540d2082900f04040110030841c5d032402200c1c1d500200028004100302c031841c0705c807500c3d40d08081010380300e50b00440c5085810507001c900031883e000f02140000c0c02c600d40a00040c1c9140214801c4c201c125880d241700c2d608683c8210000280840c400e001d07001c45081100c0000c0c80361480d07008800d88a00120b001240615000a8603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 771820089 1250 771818839 771818851
    0x30c120b07030f0f05072f0309060a0201200c0d1106070c05190b0919110904020315090f10050c041a07080309010b0109060e03210904060803090108060108 68
    0x4804140c03107071001100101084428280c2d9590f99000e00c00c0401542c0c041e55001d65001c0e901c3d4140030440440c0340d01034400a00f2000c40c1c80300c0c114140410301801000b941d0000c00211242a200c0da11000282d0152110702c250034920024200f01e844408117250140c2807840380e24040301c0994403d01015586c0941c8010100307440c0d40f000380000c0c083c1e8820521280c1d0b50380301303009842c4036900c0f0355842807200d0319000f8112400c5c02110100320f495101000414880300b1021b10f5035030405419100d140c85c1e000101d41040c002c1d05480006410344d20100304000440d804d0f0001030100d0300c4d0160b1030719100c540c2148480c51900400c1a552101c1446001ea640116502c15416207050324003000c90a40154008141c51064804e11800012403003040156215400290000c02c0f20302080000510b06c4040da040710080c06003500750050b807518001200b4400c01c0c9100c03d01c01c8420301e5200310207014020314081d154040e042c80c43c041003482c0c2c04030280c91213031401c1e2a1540152554801500c1c4801d0444603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 771821339 1250 771820089 771820103
    0x3030f05130e130828080103111005040b0310030c06020d1d04110c10060b121602010e030f0403020a0911031303210e161a07051c09030c12 61
    0x50041400400040d40c100806940c003e42d0140d255694000d0b507048582400c401d0480c4001100031a00541c0326580400180e1030000c0d069030443e940e8080001060b801c0364090305280c0c00c0032200e1030003a81200e0161540914a940f03d1804146244405082c1d00084602c0326986000050060000500c6c0105030b070646c4403c6081092960f2505951682c6480f8980c014cca4081183e4850003400c0103090902c0c004000c0d00c00031901074400e006803181ca80c003c0102407010081c810308813803040a2650802c0c52011f039030600e054095012405031508001c0ca68071800300040300b40042c01908010012280b09513041103140f0f603141a8001121841400c0c021005010400503070000400803942c043c8038440d08000d442140c8a1025100b48080044001030307841e6030301180d03030301104100848011800c685c15056460f50401940e03003924808921a120004408961001040006d002d8000501c20825001d00a240010f00050000101e440191200d00b040003001c2217042c00981c991840d903403c480b03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 771822589 1250 771821339 771821377
    0x405030c010c0c090c0809010501140d030509010201090c090212090304060e13140a14090a021e010504030f0308400201050714011a0a0f031e05150103030f05 69
    0x42d01c00048a0008440038030242e9004910011130784114440300c02190785003542840d00000705403c40710181c0100f01030540c80841c101d01a0744994240035841c0d030505e00191100115230040c0e000d0032070b9040040030038000385404218451541e0161404155400101d581740d190307215915241d2096010340c000147d5007a4000301c2908080003408200c80c0144800a5a50103034074654016140640303603c500c082c2c0307480002e420845c0c01c450300c40d0051600070103005c0381d0b0700a600044809988031250320300d5849101d00c0310826030141e800c0c5e0713008540001c000800810940342c0100540c1c3c04907800140c10752440500c01d080f0303a46240c60148003c000c50300080460500c9003c03a404412251300f01d040090811010001a07800712051448030a01c030008904001c01c110340f10180b0642d144802d001e00383c0310700c0400121400e140240c00710b0380c2110055400102c400300b050300b00e40c0004409445445074100007400b56000403403280c100c80c0241e40d900e110a26010b8200d4091042e0341c4104082e0620384 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 771823839 1250 771822589 771822613
    0x1b0305060303030a111c0f0506030c0901090c0507060f0510150c0818061b0705040b09011404020909091c110d0e03010b030f15010f0807031707140307060e0102040503 73
    0x68000880300003d001d030207042c00031819400100c03a421b14200071503a9115003036040b058146000f0560030410803400303072070214207420224859003014030540c0c1005882e2403042c40d515009200304c480c20341e0426002d10024101944205c0a40780c25200c09001c1d140d0b40c040018032070100c0522803410011513a4143d01400d6646542030203402c5007089000d03e140d603c000080c03541e5004020700c50342c2000c01039400800d43c0300003040d08009096005900441c1012401da035507640b2150800e040d01d0748817440ca03040c000000003140003400f409124642000114084c064010030015078201c8030b000720aa1100700c420400022500010480c0402800ba800711404507612409804105500382d406000090220500e20009140491000c04240a6000300085215021988004901502d0008610100a0315004005a07030308990300c80544110840300c00094281c07141c900719503a850b00040c1c582c4c3c03006c0c0b4142001d88c0700e5000c504111141d62800c11400c190000600035101102c0008000d802c00603521 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 771825089 1250 771823839 771823841
    0x40803041b080604060509010203090a02091911040e07051804050402030f030307030605010e0d03020a120e0d060204080105090607140a030e0111040609080a0c05040b0d020904061b0305060303030a 86
    0x10303004031144080c1c040d0712070101d1600c40e501e030010603110008151070b00300790400c40c044841c00307480007030541d00400800601d0100000c10000d05030b419601800b1658501e0400b0003c201d01c0582003141070b0401e000d00c040415043d01801c2641c0591541c2d203030307540f200482a00c03039101f040c640f45c81a00010b00c401d003052401d0b0b0301980e4894001b806540e8040000802c60341580c0c0101c071100040380d965401403180f541d00030f05004400707400b607a04942644c5a40c801a6880300c005e8030040110201d00b0768085964490000d860168030041c211424441c0c80b4900003020350080c0c02118107540c03030040054401d1200280c0180282c007541c94091050b0a0501403451036807000b040d400c1819220a0042c110710301c24414021281c0e014103080e500c0e607050401c010074101040c2d2056450794481d0385030f140443c550740005811030700100c0300054500051404103190049048010750300007080c00402c014040c0c2c2d07800140310079083d90b0100c034600700901e0b015400c0314016a0910b815507c1031000598003481c2d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 771826339 1250 771825089 771825091
    0x705060f150d03031404150b420c0a0b060f210102070b0a1d150a0c1e021005131e020406030f080915090f010c020a120606030c0b04050108040803 64
    0x74980841c541703207003a00c0c00d0030009040c0c070f045038090807485031034114002611828452940403030b450486545088a0f03060000085c150f4047c01980d0600d8607400c449050200545104a41544d552210b00d040103c540710f4840c4601501c1507200080041c20910380401d000c00b020704010705044d103a0307640c2a0f2201c80680d690035001d08966003008650081a1000103951041300c0070140807880e114045194100d1004064501100d9402540100340c14403106421703580c41884403500140002074208115841c420701c4880e400040c8400201c1041c032a03010460440e40c624043c4140121340b00d0b640c500103601000c41d00a031610021803041c0c01e903c800d00342e22140080c0010300100fa91500c030388402c0301d9441010000c84000c88002a01d0a882c20102011200c10740c40414440c180035a41010549030071801041904228030504e2840c00c540c0c03031a200c4409400c80910b000b918500900e4444010a22808180c0d0004501c1c3c0000413021045003c0303d00745c030b5040e591054075803a1a0744846850300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 771827589 1250 771826339 771826343
    0x9550e030a0c0c0515211e0c040b070b0f071107030303050a060b0310030b09010501030b060d0f060507230316050d09050a060209040c020c06040b0c010609020a050705060f150d 77
    0x3240c000000d010360751541c0301d2154003941000c0d1580c40d13a1403112111464000713429010004584401c102c20000101920600240820440d03e016914081d010323005108540014403491380201d0354009101c24641c00510548201084003e00e0f111100c0560b00540312029000351940310344400d2000078480e07000103801000c880c6010600c1030f00c50000c4c501c40d4008a68410541c940380100b001402154200035401c6405407008102c41d5040da2526200c40000402c4d070b43c0141e003143c4000040146010041c50701c6500260100b009081800c1d0080492080019420103610010000344003540803604a81c0036080c0c01c268044400c0000350b058405420245905074140c0c1e40d02055000714409000e1401810f2048100581d21494002000101d600200540c02198030000c00c00400340c0340c01003180e05460141141940f01d8080c146494090a515000400600e002041e10078195401102034118244100b09958503030380c41d41c40034a1190402c80e54400101119000d034800b9050050364024039034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 771828839 1250 771827589 771827603
    0x909023124090b070323031b030403020f07030c1401031401120c030803010605030f24130e190203060106050a08040609030e090403092309550e030a0c 66
    0x282d5549050f2400f60850f0074140c01160020a01003043c0d007030800400742c5450201e21690460034020011502c0050580d443c070004100000401c090500030404203208103039450854032030076100c0c035001040e50003601c202c50140c420b20070390b0740c01e9601a0040100110f10b092140030030340e203000e038000344829201400340e90006075940d01002140c5200c00960180c641502d4042e82d0741840901d0420b5540f00410000380c422045c01c0b481c036000300c400304600759808112081d40d12015003203100340003429003100b0340000b8860900f0301c4618911645000c44204d008800b66201681e0b03804054031203115900143d030014802100080000d0b5259002800b550301a28014903000e01880201d1601d01d02030b503090b00421103003030007085201d56442044095110314010b010340140c0c9403000c5050104c028202002e08000b16961110340791030003075100d04100003140e1200c00d0f105000301c0311040807440103001d9500c80075815403203c0c28003140119440c100007040110315021074100300329a4005561000c84800b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 771830089 1250 771828839 771828857
    0x9010e0318121b0a0504020702060d0c1215030203010b03011b0507030302192309031908070c0312030605180403230f0a0219020105030609070909023124 67
    0x101000c00c4040c0440f407071000c40308480da04240c01c0121400c116804588241e0042003420016142e000995406161560b00858400300a00302903c0d00c1580c104c0030f40095103081000b1020b00720040005007280c0c025070007000411010b0003130601361041e00c0340c001400d80c81007a070018242c0c414001000c056000b450014203010b044040d04001419400401c0009032801d980c51040f501444c0242e243e0400d41c080c8903103801e2544000c03035110204801c0711414407002914503000d01030020115045140d0140181910a44914112201070307040e025a000180c90000301080702c1c2814818100d860000d82a0030341c03a0303034907903508948400d20340c0c504000760703c569001581920321100c0a41020035881c00100e84859030706c1802850040e021105846c91982092160f0160340c02100b125000700d41036400e202a6070f11090305450100c07850b404901124400142c4103944d800f5540c00c0c99811000e045400e003940619007402080007824019010100350060000d00300504c102503c03540000541022001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 771831339 1250 771830089 771830119
    0xe190e071202040e181b0607050c091e09060106050717070230033f1e01060e03060c090a030503040e010e0f04050c010302070303090221010509010e0318 67
    0x41c3d03089980000100c00003003081c0800c01c004024036100c442001002440c0da000c0c4102d0701c10b0b56039002407613240100300004244090000501ca20340b1441d40240000f512800c100c8440b1541d000107003140210b910b50000031560f9400085007150407218107a54090a00c081c58884a148880c5000d66812900d4200140070040c0c4802001c1031644500d106031101c4603100800138580c04011924103c12600104040d0048070000904072503801c4021250b00461406013074480e440880300f200011a1040c518200405040102012402c01c1d00d20940d4106690381c401046d07400c89060803009074550000c034006032041e60100054205d40d10300403c420002e80da81e842d0b59056602c160401e814000e070940040c0810030348105400e80151080500f001d442c03400d0b031621901d40c6102d203442410036400281302d10906110783c0003001c10320307002000e80d44a01012404080100c5000c100040a9428580020520704042c801d40c0907226020001d14500701c10242c2c0340140d01042140d09501520311118054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 771832589 1250 771831339 771831341
    0x200f030a060902090c070b0f042a0305010b040e191b060201151502070306200a120623190e09031b0307120e010c1e02010e190e0712 58
    0x200250041d500000c07010294018080c0c184002015400d40e003108002140000703100102031a406043c0c2c9023048a6901e0310b29180c08413001c055aa00a0050340841c480c90031901181d200d01100d1090340200000c0c52503800b4403041c0c1d003003400c2c40c0540f90801c0c1c03003080b111443c1502d0044560b100d2144452000008400c12501c480190842c0005039034500f41444600a2546084094041400381445413480900000e41d908818040142802d0f200c00ca022592030f048000d0340035845240c8241900c0d500c08000003031030b00c200030955018013428131000083e0009a44d0405400a03a0b001400c0da00120340d20074815403084680b0002c00d9410000000107030003800b03107107090003106900061a070790503551803e111000304020310058a500b040001d1800114180800450384000d07040242800301d4030801603903e003a0320200a4401039004043e035624411000000160f01d200740c07200c080c0d0180f401c0502800720100e60300002c41d0501c00c0018000b02070741c07c40c40ca602c8119881d200d19080d228400e568 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 771833839 1250 771832589 771832603
    0x5010c030b011106151314040b04030815010203041a0f04090203091c05091221030718121106041706040201030509030c060105041505030124050607200f03 68
    0x10000740e4600e03014480d0341e40701c1c0401d4400d01280c4024802e5007071401007400b44004500406201d40c00340d0400280708666500039240307003600c140c0c04490310310b418202452000c2007160704a000514210000300650801342e4400032800b0103034020360070203040c00b040d4001202e101071003070405e481c140854a0711181000c01813010340750100016849003484030341146050054004221491404510128440e52200950701100d40c1203412143e564003610040c0c0c1000d4025410454aa0581c2012481c9080c0300b0001e6000e8603103683c0b40c1e00e0400320100c10800c0c0e007815002e1010740c800c148400f03402244c10303503402c8001050018a114681139465018000c07480303001d88055500c0e0813a8003004150341e003501c130f9154000d012030003551809005d80c4000352503000501600f071003a40c0d00c0304c03450000e00d1034200000142001a0081028503002070700100000c400040040c0d161050120200d03141c146003041d65040307a84010b04800c0080d48403480c400b0010f40740862600f1045640c9000d4840d40d00b00024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 771835089 1250 771833839 771833861
    0x903020f031f0c02010b090c070b060402071a0402010f0c050a080f0903060711010c0c02090a0e1e01151a030f07021f0902010f090828020a0e091603150e0a0501 70
    0xa583c8201e504041d095030081149503202e41461070401c9000c88010044490865000e003058600741e4031040054001e0140582c0940400d4400105da401c0400b0760710b42a014a000344c80305400140f103220111126001d21500901c0b5410400c42e01700001c00f80c4000d00100008000550309050002d404a40b0b003910807920680002c0b115801075031039030801e00c9441d281060a16003148801004e030049120702074050152070752155142d15090048001303010043c050b90721104180f01010607070500602030103400c0d2403190401d40e03040001032205d400e20780c00507074100d01180c25401d550b80d00d955030038003035402003a46041d4020144a9488540c20203400d020740030b8102c50010b8001d030180001045002d0385440e502c203100d000b8030180705007000003440303122082d0344410039426011480310f103800010050700029000076148a020030f14801d1182460b05c03e80d294800c0b100c2804042c8400318102c0305034440603180300c0000c07251503014403403508105000c402c000d0483e06060030030750303c0500f125003040714 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 771836339 1250 771835089 771835091
    0xa0507051e0a170a050405010f0201140703020702030c060304170313050607090801050a0b030304091a0607050601030314190c1a0117070503071d0612010510240903020f031f 76
    0x1010b0030001d107001c0030b11041d54406807242c10000089000b80040c46a8010715040c0106c011080c540d41c1d1007500300715610401c0b29103640450401d5038015019401500f0100d210b8080e82e1503200f80c905054017602e116941042c50405013041c0b10b001c6c960300d54005008003580894088130b02021a0007040b81e070303000300c00c99a10910303841e00e0304400c1e41c21980094112540d031810005a030280340c1c1c001050310103441040340c000903442d06001011400c42c031440031082d0446004560102401808645141200c0c02616131460003c6904030041052107404d02203d00220b079001b024050a02c01c0d9401c202c0503100d040808901c141b02d203859041c03020242d000d40c8140c40000088048600207028000c0241070070b90007042c2450810f8040250480100c050241c03040b003040c00120707940c2d500422600203088180003080b4900344414280c0010605002c0c00050f03840034410010201800366404095405943c2d03841d94450441c0e080151111100c990035038140f203002103800c00b00980d0150500d0080070080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 771837589 1250 771836339 771836353
    0x8040f0b0106023a031112010f08070f062f030d09030e010c020108010306020d090c030c05040b0612180129030606060403200402040b2a01020408030a0507051e 70
    0x9040c1c2c8251130656400c3d01c960141120742030030051025041d05a03045040c0030410800580140710680074080c107203ca5401500c00001e0000003650304407042e40d0710081642c201c29100c2c800c1070481c11151050800103a01c202c904186200d911a0300e45070400c100b98607100f18850954010303e5a00955840f0f210103954964030010150403080381d5034010350030309021044042940000e841030300140300203003010f90000350444070314250b40c0c050050f881c1e01000c140440c1c1c3d04c03401d000c1d03c81c00640c0645070081d440c10280f00c4c0549000003e554818005180d91038240d50b442c505234211040c1103081110640d00c440c000d88401c04400500694481c2c8400035019001036079081620b131050107441180078100410091010941c2841511501c0c1c620524040518070400b0105d002031003541c0c030160a010707000c21122840751400009024901c8164940034092400c40b1440d4203d205030f108030f254a900402049814902a0010b007100728080d2040d540720402e10f0303219010420340c1d40c814821541041c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 771838839 1250 771837589 771837613
    0x1080d0e0102100c0e0f100f2619050109090210030f061a0d0b1008040209041e1a060a0608010612140108031e180f0303070507240e03030a08040f0b010602 68
    0x80f00100c40c108101d0302c0d2111a600900c003d4103004800d11142300b0081c10000c07000c0c1c0c01c4640039982c40022010790000a0354a032030718500403140d03921018807400700e0410b400003c1c003605502400c00d17525001403e040314240452402d030700820141c8164200603403941300c0000d040042181c0d401c86a0310034640703d662040d4030500c08040380e41da003440500c80c0d0005100c50203616400b001c0c603a80303c1e5042c1d03001102c2c2c1c0c8640c100b030107011816110522406800382c0f810410070008408140500c4002c514814194440d44104118240e4034000d000c005045800104002d03032081048101c072820350380c00041c01d103030b41d80042c41c03200388249c1042c001d5030710020301403610000b030300c08512190f500c800101c0d042400c45a40702d00d0f6a0144a212072240061002280d811398007401215401035001048810060340c0740001040902e210003506080441d1250307000d02940191001c40801000801071403400242c0402550400310282c010340303044065a500f0341c00140f10441070341c0078004a400521004088c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 771840089 1250 771838839 771838849
    0x60204050a0801050c0d09020117090706081608041e140f0d0c05101109090901090c050a1a0705030c0307060b0a1a07030e03010b031204090c050301080d0e0102100c0e 73
    0x5a842a0780740d13032401e0100700388990110309032286456140c2011682d08041e000403100c602d00070a9403842101a5130512030343c0e0000140c40411180e0503200c08040e85d40301d442016003030328500c550f01e0103d0b0352840000d0001d01400e080794400800500301c50f005644c0c644030614024052480071100c1c0d0f0003206010046081048a040d42800d14645600c8207081c90340ca4503110540c1035070407218071752140b80ca20300d4907005505980032604050312048031403070701069550180c00c4564081d1520360404002042030301309001703d03005480302c6881004400301c0e0010850f07810342c03200c2002d80395800b0500c85140b043d1018402012800d0090034042401c2e00701c2070410011064a038046010902840c0384240f80d401f84009991a458140c10061500904030002c6030140140f00329a9615004510716183c3c5511480f014109456201c0c104204510030b001013510181310070301039000d0543c40602c520355658811000c4c00e21b13400d01071041d5100c0c00042c1c001c94096510241c40a004900b0007a1300100c02e08003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 771841339 1250 771840089 771840109
    0x60b0c0604111207140102010902041806050604180b1b0f0406031116080a0e1323060a0b13030c06030b03160303140f07140d09090507050d230406020405 67
    0x441d183c961080d1001c10090b035520070f6201d0040c01d000350f0543c40380c0980c000e5025038425500540300344591020070394035020712140396100b01d4080f0301e00b0020030a0790420b031182e40c10442d19090300b03021600403038460301d03a00c40009243c603816600740340000ea00325140030302425261140c010450b448a041080c0601610403005401d112010140042c5a2289955000e8034000d03400100440d0307200b002c0e0780d040325549080e222480e00f100b40c22000701540c0341d065100442c12900701d030b101c85914070303440003004414900340c07105035011551440a000310003043d00180380e40802c601201c0c0400e03599554984000c00c050703214202181d51107003442943d050034001c1501c6500c2034042080710508607600a024000c8030720818400980c0810000f080c500c100303080b6080290800b201011503010f00018954800420380410001400c21100040348001c1d400780600560842e02d5903070410070000c111400074100040300c5c20f240e007401409210788440d0f5101c424012401183d0160f41d481c10038092100c8100c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 771842589 1250 771841339 771841373
    0xb031608060f040c0603021b0d0e10110c040b010c0c030c1805070906050c010b030a0b041b1a03060109120c051e090a0e07030b0f0114060a050304021201060b0c0604 72
    0x3202c1410040003a03a0b820100c070070354840c1d040060322110809200488071010b40d604102074031412103c2e001e2140c2200d20350240b1001194020412080d01c00d0480368843c00410300c007080d6000380c1201c1c803249010741050101510614000ca400b560648a00d4240e5955601c00d403100d0050450501c9a0046101512180b404000082c492802c00000007000c05003107101d65001c0000201c0e000808102c2034000c034441031002000c4608517001400c08025015041e5402c890501c3c064403540d802000d5152610304a03a04080d09500507030302c0c81410641984001e045178104008107101084503c04e412036500d2043c010343c103405500b0304200a003c0d4094174007043c41c69185114541000503501d2040d06540100c4010010840300c80443c0c416290449641000b028075405408001150120b00425412520440004c000545040c4180541403048802c001c000500820004015081940c41415842d40d208000a03107030396508210780403a04144e5401500703422042c1480103001c0b0492405250302 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 771843839 1250 771842589 771842611
    0x120c0a03112d31120209070c0206070204140403110304121106250317040b0408031306020c0f01050a0c0206070807020c221410050607060b03160806 65
    0x760080c0d4002d03141d00c0220310301c19100b1211452110031942e11030240e6421801d056942482807400c102052081c0400200c00707100101844030000312848207105003040d107a005882034200c0e4648002c01c80306103c0d04201070740c100008100040c0180c9803072054600c0c1012070540781660782400d107401800c2481240021181c0c0d0700c144003d00551482c0c503002012143c4c00460f0407040081e8101281a5009500742d06290342c0d8007c2a0380ca0481d6204000301180d4426a070b08134100910300b0440011103000e55015201c0e03400040001c0000d51482e00454108542022400c1c0c5550150f03110400d0381e0200542e11001d402400c44a000800f09000340e94010303201c02c3d024800340240c2c6d0b90095070390000a01400c10024600007141a82e130081c490581080310240c10804519141c04001e089401005d541104061520f4a00900ca980c55092035000b24000070790120300c03528103810000380340c00c101800e8030142d03910b003a001c003960b800b0000000ca0000300c0e01c1c01c520301031801c800c071400d00d603005002071411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 771845089 1250 771843839 771843847
    0xc0103090b06210a1202061602031e0d060f0f0905130305130801090305120f250908060a0f0b09010311040c030e190c06030e1005070302120c0a0311 65
    0x407540315030154010010341d10a1104409030040c1d072101c41e00302401090600032184004140a010f0007800410a042e0302110711680740d0400c002d0a0459101580c1c2c01a00f0074000040c81c1008040700e002d80c2c01c1040790035405c0c1b076240140300c800c4a00540c024420010421420800006103014581c0244450a01004585450142c60b84001c50304280241009070000300548052940d41c0a6000380526030020441d0144e6481c01408962000105180201101c00000d032500e13030100c803044c82000400301e00c6400140300708009000d640e00c003401c4010300108401c0401c0d1500100700076413040707000340710128025451204180444840d4407415002e0318081c4018804034104280c0c0b00b0041c0015034000407c500d0745031044004094100c21645071b07000302850300c034030070100e5000800d40d80d0007000400206651620160b049400c0d8200d807e2070394214011580310201241d11103640092a414090300d8010b80300e41d561103185080350780414401000ca44002d506a00d4403a020a21141c0c0c0782301d500e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 771846339 1250 771845089 771845093
    0x2012090d1416030c0b070507170711130608160f080d020a08030a0b0402120405010f1802040504060f09030c0b07140313031e09060315061710180b030c010309 69
    0x180c850030b9001c0003481150410356040611450007001083d42100d14400745040a1000030070991008400780c1c0d001d0f1100924100c00040d000c12500b45175031014203120350704500800d00440034280350101d00210340c1c40c00700148080c018010702100b1308108041c10143e030f043ca049480c049013980c01168440e48002d561448407500000c400240300d030462216900c0340d56005d26900503000b074440a680050010444920402c0c00a2182e030050780f03d1002031103201c80e402c0b0b1f0181210749000d800421100c50782e0b500005400c0c0f80e40030700e070040c1c010b8a01141c07070b09464140304140c070f050f00004ca00040d030154066041c4802460559000f0506241c514040000502503118900001d810103e040030090ba82800f014000c0c854022a880c0300c140c0b1240703501403100082d00701c4081d03100707035000b0a082840018101291148400540b50345881d051600c0580d0100324081d03400c02007180344003011000021840c1072019029840d2150a0340000c1381c480644014503041c020381c030403903e040c0340c101900800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 771847589 1250 771846339 771846377
    0x41d0f2104060c0c050301090b150906010f050f090d050d080a0b030a02012d051e0f0d090528061d070e070201090206040b0904050606120a2012090d 65
    0x81141e03038620340b4841d01e03078075820001301c400742d41d920080d070541c42c0c215690704014919554a00c02c07034420502e1415210240e080c07214450040701d00c40e00103030503808004891800f641c098600d8011666500f07080c480c0703000c0403401c0e0010ba54801d80c0d0fa50302042e502c01101d50700c0302c200307680031003a510280300e2031894002007071751401c8040000b418130941c0e000f0140114990180040303011030204034510080503958015180b40d105200e0301c01511141c03101c0640041141d821a01c00401c1c81100a280034440d180c542c0c0103122011044a4034010bc201140305904110203440f0b051000308e402c484008180c2c07030100200d170402071030724500e22800b4840d01010100452210103c1d000b07071041c0c910302e0391000022401094040b6000f036100c2c20100e004600003282c000034103580b03082960200000d80320390080003814042e541d030203001d48400000040d02c4091981246440d451041d80391b0818400051181191b81c000c3d14288101c0e420500810905200c10420036017400d507030341003c200d91350311140441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 771848839 1250 771847589 771847597
    0x60103140d0219150c0e030c01031406040b060f041707050103142710060f0e1324050f070917152d07090f0f14041d0f21 53
    0xc3c0e8680005842c80d0600150382c0c010210342162042c1049000020341015145510940d040c50003441001c10455455001c1d100e10154a05c050020301016a11041008040c118510040da0403920602030201412606005440601081145e000700710200c0c4060314545036003a0301041c105400d01047d04940404010900e0308842c008482045a01480c0f03944000402a405080260b20849424180d00d2103d5801003054400d003010340604036035a104900e61100007540c01c86d81e040242512400044c0c4400400640d01c0040c40781d00844e60480e146180c00c5510803035800800c101c0c1a8100b044031079101038200060101d407a84032908614a054081e41c4810f50040e0401440e06e44000c1504080501056103864811801d410f0343c50508151450f17514606482c204003103400d490000c103064051005982c1071341c2200c0c12140d0a186000c2007041a03860500c11203400641e42c3d144541c80881c00c0f10580d0001c03591900a0a8606079214024640640750b00c0012540800138010040c01b40c2c440700f11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 771850089 1250 771848839 771848863
    0xf14040e0408070303141008060903030c190c050304030b0952031a1303020c06070327080c0414070305040302121c0b0d0c050415080f060103140d02 65
    0x25521040c003460240c00034086c1e44044404418060304002804a000c10306e031b016900854160307109910341910345684d03400244c501110b2204141300121001c041500c103241c580480e40f400c00340840075501c4860540d030003604180d0300240500104021040e0401942d00c2103880c94204101082e412210ba1350480300c00741040b126040c07142001c08400d049000600001d01140c83c03511051031b40e81c40c1a08695000c0304520110031403400c001454a0f01c09800c044101d80c050300074001e040e154400b00b004a40c0200402c40a00280e2614101e0003500b00b03800c06040c8000c074101125260030500650716010a540081e88202c1c24107003d5803036007072040ba410707401c84050308000c980760721a80307000d9041c0550f1400400e680c2e03801041034040e01341400054106081c0540c4200b1042c59400c041c80406004400c02400807000003d0810180c00d00703a05c10300700c54100e0090250300c0758070790740e4090600500e002c05845560100005100344000c000c482c0c41c4052005000308000721034010040c4d00e030074021100f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 771851339 1250 771850089 771850103
    0xc09060f090902030a0f0f151203020c0d0812070e040e121e0702060d0203040c1401200c03070602030706060e040f060b01020a082110081b040605060304030f14040e04 73
    0x400c5c520011904140358814044805200b840f4104800720014014120201d03068103030094002800c2003250320b0710300865010303030140c4003244890050160014034214100c1c1c0083d000c100c00030704090541401402954241d4801c00c0c101c81000401003614400e15801915812000d0030325841100601140c12401940c840001880e80e01c941841a500659034042d400400000780c004ea509010341c01503128500c41c00603100705a481d0751041900b24864180640407c0c0750032544401c40c8200c1c0d0854848138030075411540b1000d1b07a440800d041400d154400c20241e480414110200080c50181781c028009181113005a480c06855205000104210180c05a69207424140320b6034424042e48400e942c0240080d0f0751510103442c800002c50542c40803107210100c5e000400c041041c4500d084048030103400c01440185c40c00108a1880724800c034489a100707650308030002e043d403145009548514040c0c1c4480101d544001c9028001c070030003001d803910800c400c202c10700c95110064038464000d03412500c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 771852589 1250 771851339 771851341
    0x181624050a0e190e07090e0a1404080306190605040f0801020c0a150204120c060206071e0f0c060c02031e090117040f2013090b13020117010602010c09060f09090203 72
    0x140010b4806107a046031301c000c0040d00030814000c2d004603a150460756150000061130340c0303100080d011590004080501403550f1400300e40481c41d044051904404000d2000c2c604100f404540740c03a1145a0340560f0100b000410300304014480100c484d001000c40500075031410000f41180c0c0d88400c0882802045900d03004880c1c1c1070803007154151400f401000d0004022022542000c1c0d040c10b1540c400c02d070041c030510300011003492145840d8071090900d6141c16003100102c000a07a0448400c026204c1049400301180d00414458021040d014003150003442d5601c1200610305032800b0902c020008820b0100329000e8180d92000782d60704081d0b806007000e6065121403900c0b00782d05004020140500c808050020903c544150480d000030100300c4a00c040c3c1080445684140ca88124003d0720620101c000600b03a000034200348001a4814500040e81000c02002c140d8020406e030442c00060b0366840d90b220910340c128a03503401400344e0b42854100c2281e00c0c1002440d1045501514140b150040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 771853839 1250 771852589 771852619
    0xc03061314030c0145060506010c0f0b09070b0a1e03020409091b21080a021203070c0b0c0301080c010c03200a0b010b070209181624050a0e 61
    0x401a01c00c0d8045207802030141700441c1c5048400500407500d82050b0054240511925030180501500c07520b201d007212580c1d8020303030744414000704001030000c1d0502081103182c2e000201105c0c40788000b188207010900c0382c1d043c0010340324500755242c0c01c00c1c003c410040003c1002e06400001d00c0c042c11040003a20145180300a104401070b000e075a0014400c00d0400418104204100711550a469030b000c20300c0402c5680c03240190905082c070420b0088051040ba0a0000b00c3c1c4004000c0c1610750280c011205031b00000b00f49600360b5070040b01d03800d0008504d5441401000f00403d101d41e002030b0108515030540d4100244242c8070810018002d041c03003d402c1c0309400701409610344580ca1145c0018402544010a00700da07205c0854080484080d040c440011801d050ba48080e160b130b044c1c02074501c01061303440c58408107203c405001543c4803441048102c02e0300c0c64060036000042c00160008190b50301051914141407818640b081052050a00c001418540d002c1400c040c4540c040320031640c0b481c402 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 771855089 1250 771853839 771853843
    0x6040902060f0706052415070803240d08030604090f0b0106050409200f030c0903030f180a230a09060803070309170703241a030c03061314 61
    0x1500000750440c6000c154441100200b40241c4022401150244125551444000715075604056050a0989003510552860601c0c010811043c14180c0402e0f1030000c0584070016640c0040392001c01d03a9200f05100c0c00c841a69042c040395078401600c04410b401006c0d0794001141c08000c0c000307802075544080f010148000500e080300c000f60040b0310f0341995610f90700010401d50007400f417103a106040200d54881448810341003a4044440c592060518109111014842d48003074078681001005111041c1c85503414002050306007050400c0f41c0d42c03540380d00a02c08101d07048400c903c4c85100d04450070800001511859400c0b0030302e00d2a081c0304a82c054000825803a02034000d0100e0920b020004100b0090000040001078001e455201c1d06580e6214807003c01840792a00d00142e0b040140100b00041085a80c0000008420b003200c03404444081858201d503003107192890384241c010f03482016401d061021052a80c0c040c1c02804991070846030001220403090b200800305a81c3c181c030701603045ca003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 771856339 1250 771855089 771855101
    0xf0f090203071b05010c02011d0d0e130606081902211e01090504170f0a05030a0e0f071e060801050d1e0809040c030624030e010f021b0d05030f0604 65
    0xc1c02c28046055a0034213010f40240b04100031140036629000c403524010501c80002180409540010280000c40c02030445a403c405000d250300044101c01142c1c81d00014064038014120b00c0e51191202c3c40d02d0054414503a1040508900c060310421808020001c11300b03180800b8500c0e00c0100340d142d1200c0000c619595500d4400e0a40000c1240c000300741c00500d900190300440c091100c00c040f0017008096614240315001c6503c1005008000460105000b1805954030641460001076540e450700ba0703040c2014108140c14495404c00d5000b030145c14403c850004511035040040f20784141480c034007400036241805007612440070051301c0303800c0080c06e10584600c804441d4103104a100039240c442c1c02904806030b000c2c825428107140703004141c881d11035501207454410344d200c0c8601c0700103031444500c15810039980806071101c02c4154a500c09008202c26120302181c0180e4074080011a002d5141141c5142100c3c1c1c0c0103043c044801d40d134448162030b0400c1c0c8c81741800300c00f0740310400042c0c01004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 771857589 1250 771856339 771856367
    0x201030c200303150316090b0d0c0303030b0a06050f180d3003051b0903070911070201110c03070302090c0c152d182d070f0f09020307 59
    0x71103100901d9030a20100256025003402c140c03401100501c00f00305512061081e5001502141000c0b08000f10055904600c00340d940c05845084412202e4445405482141e00b0a40c0030a031595120f6203a401c040c00071100601003807030000c0c2850b50400d102c0c000340c49500c0e4142c9070081c00c4604c208079690f6941102e40300ea688170b40740820b020219171003d64042c60102c04140c1840e522112860b407203010780034480c0314132031a080b82100c00c10103c1201141d80c01000300282c040c4201400030075180c03414800e0101d02244000e2036515003074603100040008819240d0035040d508044d0b03030000d2070b442c000790482c1039950446030104290740700c18614609004440400c1e50500c103600303106086940c1c00c003040d03004088440c29824101180401c0f08088180001420400000c0303100081d80c2c00d0202d0404490306a4080c140c59070b12810f5901c03401c812800c0c00401c01c045043c00300780303108070404000b07210050140300c641040c42031401d40300f2010688580310700c0419940010000354602d100e44d00e00c40480c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 771858839 1250 771857589 771857627
    0xf09091a270714120a0b10080613020c060105221a01030f0506011202030c130f08012003070e121504020405280b0a08070801050a0506090103050a0201030c 68
    0x340140301c1244104122000c0544000444011420040c400d4003d03d20016890b19100d1600310780b104000a8408001e001617034696a4000c0790303185030346101c203446200303c2c0e035501c1c034215042030700411180c01445561100568030400c1026050361000c20003904403402103920800e60032041c401c140c009446c110050040d80e00d011515810581c102c0400c001a603800e0341c00f00072035024481c016044480c10381c0d085011440c00400c403054036a90350021903210014140c40d030305040c504145685100c007280c00010bd100005502030081407001d1044ca0305580c2c070f140c04003090410b82c20b40c010043c4000703000c410420104441e845d0030380d103800344010186aa15001c40303081c81c0300b400d80c00e0300412040c0c804030700c80c0341002c000c00d007141c0941815040100111200b600e45000c40d10180d03005080c50003e403500203210200000c0c2404082c4010070090440000106491814034518011148001d22551051003a00010300c01311b013000600810181d42030800042101c0790280c142c03030941c51807888030100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 771860089 1250 771858839 771858859
    0xf050f031b0f0909070602100209090a1a03100219030c0921140109020f041b030213151824230408010903021522150c05070209070f09091a 61
    0x7103000020303c2070491b20740c2d5007950001c2c200f000d5114264072030607070216031200300d14000c1034250303002d070f40100703401303280c0c80c0000d0345012145000c241803010094002a00d1a40810940840d400240780b400b000d1010740740030170841c441d220001d02191068000e00960105400303280c1428290700040d6a803403900b008070001f804c42084013482c060107000b0000c0b40a00302800e80040706003840c0c002d01d515500d8240008066540d058402c038001d4200030310300c1480b0780480200181102400a250b21040e0066407040c1d100407d1080a5080e118242d20500f041c0c0350307143e000310f0300d9082c0e4410034040704c038a0726250552186104070350140040041d2070b020944400203001030030090541c42880c210740710341c00340c1702007951881042c865103004030ac503040d00c2052140502e460b500c1c0da0010044581c81140c0640c00404502d403c802203900c00000c0ba408940001584021351802d052010b40c82078031440c0c880e0001110f0f21005000e00704900c90710228a0303c1d280618101114000280029000039041e6280f03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 771861339 1250 771860089 771860101
    0x309120b070f2a1103060c09040b0a12060221040506070c0602070507180c02031303060e160e06090a020a0210020a0309020312041a0a0c03050a21060f050f031b0f09 72
    0x10740343d4a0320200e602d0100c0076138004c8181000300d402d038030512a0348101c0741800020001e02003d080c16080050b0321006a40c070110b909201c60181080d524055000103885962078840800980e803203941c58132107883c002c4200700010714006441540a04180f0702030407407840d42c0c90518083d001e413034801030541c080c2c500003080c0c1501c1a42d241d400b41540c0c010070307c070308840701905036113901c10888404c50b4110800414804101036410038039104a1034030840d482c0d0f802144001050721040c0d000303011072004c0b60091001910306103080c150410308240c4114079040d0407603c06503880d241d560041c20420b402090401100c2c0c041d41c0700328030040d0040c064407540042c160341d441b03842d030050061100a038842c0920680386550002030b82d5540c42c25031290a01804140c40540c1e0a400212894080180100608050315940c0403440514160700d0004100715040078880030303154002c3c0c0c0110340184901e0300c0741c0000743e50020300d5408042d50340150501c40181980419007400f584620030f90428100414040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 771862589 1250 771861339 771861407
    0xd03110c0607021f110601080f100605010509010c05160e061018180b0d03050c0c0609131a0415150203031b0a030e01060b04030309120b070f 62
    0x80101200640d000c0d80c0c0504100411400703042c42c043d41100c80d048620010300380c290310007202c03103241e810700514102c454542d103840c1c428241c1008905801440100003420420803580343d902100600c2402403a08140001f4400c4c0900386c00641001038594444041c8035090010600040c40710480c000380584400c1c2e23054010360141da44500880c0410352442c011403003844404048060340039800341c82072420010f118081d000400401005584074a854500d645143c405040e1511a40318191100030b290041c80c20680711139500c0d8010705040060340c00f9560391951415a041c3c02a03400100c25261305103018001c0f99101d200703900140f800868019040400381d1060031990300d524606e104040a903412a142d00065a01c0c3c0341000c0c112030758912101c40314001e40f10f82911480c00089191404c0e01c01c0d400d4418541c00303840c518000042c1481410350000814018060941100d410f0f405655920948190001d12010400c444c1669840320036108a80b03502c50141400c40d40f0038660100c0501e41d13 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 771863839 1250 771862589 771862607
    0xf11011b03052806051e030703080c010b1f031a0603071110110304050706030225020d0b0421020613021512010321030c0206011a0d020f0a0e011b0f0f020d03 69
    0x584141e080c040c1e441c0d913001e000c1b00c0e94020303904040d010b48130082c51a96042966002400c0c081d038031f5520f5000002c4070381c90b2245e241090240320807418480f16039840000d4106c91140c4490000000103806844050301c5280480f90002011303d007042e02007265040e45803c003092004030454460401c54600c101d01913120246016900500070781e401c45503205400da089201e4400e81c0715603051102444010145242e020103000d90001d40001000c070a1507403450110b80080b10308070f400048841901c00b40d1860b20050341e5003406d55000914841c00e080c0044d9280f900000c40c001d1207600009100c0c2e050002800540b00d42820100c01500c1958480c51f05001ca80e51400714205144000005010302c10301c280540c0076080440d4002c0e2445d40d003800e80600190804003903020710f003c401c2040d40407448891009001c3d003814414010303103a030401800104030b001c603807004904111601101c1e480165218400c0b02030b0740d07401030450a44403020700d40b000300a50944000307035021104000307540034150898501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 771865089 1250 771863839 771863849
    0x310080609030a170f04021306091b020f010902241b0106080c0405041e03050f0f042d0e060307030c231c030c02041503030f11011b03052806 62
    0x30420340d51804100650044c0c01c450305001418000045405801c14003a0814102c2c0c1b940c0d00801d4160301c510129040d10400604040c5240392110240c090b550b042c01f2220414031810001d2050080640015151880111201028032100d00a50008020079402c645002c200002014410301065403018000d100a1103554400d01a0882202e00c529143c8641441503070320a642c4c003550031190858040340c2c03407102c00840a1040420840c042000c400c005080200d0300d440c2c2c00d650b61420546154001103c0703507071400d000c0c08415184080d40f840c1c4186036040e86d4038040041003c0d40c1c0c0d240000e1034403025a20150803c008440b001c124884440d8078481c24145008100840d6000750003840038401c088401c10440c4501c1c0c616040c0080d114030120785001d0b0009001046804918403a40c102c8615507104230081003074407140c07600c40c513009540c00c511180444000c106804040d0603085010030401c0038801050754410010303000022412851540c19822150090740000080c181d04c002d05a6000e2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 771866339 1250 771865089 771865097
    0xc010905070b07050d0905090c0a0e0411040f0504020a050f07060b0907110f06090c240c01200a0e102001050109060b04082e020f030a0b04021e0310080609030a 70
    0x5c000d12180194508400c490001e80000441c1d03440d000228299003280304036508000c0b00040d01702c00713950383c2d014400f90032523500c10840c1d031140b07824081d0341046c0e81948158000c81c018000602071541000981e41141c1c2a50401c030780d20416880c2000081c0f440803c041d03881f448840a01107607551040c801200600080c01700c80c6e124041c0b141c5d06686617021108a11a984050100302a82c201070401c0291b00802611104c0020003003101d841060b00540f071003501a80d0340e40083d1a0b0486806c55208202c00d81d05d004a107011030140d401441c950104210030b02038404a0030228886200d600c51207061100f2991140d001109448500c0c041c1500380304008034030b400c103000821140c0c8007904132011108084020046040d0420000440c5600a88100c1c184001c0c07481d0500c0e80081e500041240001580040c0da03249040e0b80d0f80021500304120341405903105008401d2040304032021143e207103e04254003a141c1e070360b03a00c81400b500055000301e03155000348401c0c44041400003000c2c0401aa254403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 771867589 1250 771866339 771866353
    0x13030609060e011505040e160305011b081905270604050f2d0a050d090302030d0801030b04382d07050f070c030305070201030f061a0c010905070b0705 66
    0x20b6524280c0700d28141d1a5900380407514208214034155010306441c94801d001e965002500429100c800c940d2507201b0f8642e80d44a001c281842c4a84014240c00c103841c03810080f10a040c41141e039040e45e904103c9030030320283c1e0740000c1110324000130b0b100c1e035401c403049440400e480042c2800c9521188140e0301110380340305500c00d072070102c1c0d000310303200310340402d644100e80c0c11100d2481100c00807e02042c041160f4010010060013250080c4030312a40e0b0001525036821262461041c1460302c00c8030164481000f054400604c0059000440580c006802201c40030074003125010501489c905802c03c000700c1c00c0c0c80c0c1032880300100030403202485030300208843c2c1388510143d203042c0c0744201d000002d210100e00b588002a0003070300801c007030015841109111420b0040d42e41e1012080141d54200390003241e00410703201c0840da414080c1a202c0011040c0074040d845c41d00c03840c003448130a02d003418401c00a001c0388000030704109500804202d40c002c0304450909540303020a50710741e03002800c02d60303003805000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 771868839 1250 771867589 771867611
    0xf020306070509030a151d06010f150f0f032c0c0f030604030c050a0807060f0506030f0303150f1302070b0c12010b0906220602070608060a030303111303060906 70
    0x6401d881560f403000e0003420040321640e4030701104000e00c1c0c564200b103507611040c01294110803000a210083c90200030f1409504002142c0400c5245900441c4c0000c120403202e1007481e80141d00402c5090f140c1080c2480c020009019006004140303002c1005070020084002c003ca2320303000340c058082c8050203070746101041d10700b80000c41e2040b038111900340e4045800318001074800ea51400f0102e0145058440c20189a5201041580100c8058851302e86851400851581e58800d241d0840e2003100180003070120b44c0115034903400014080c800425104900c01066107821005182c11038004015150f0b0840c072600300002500f025400b0785055144000050627040c540d422200f0055110302102c81c00c0c4c0ca0328080c0b03401c2e40d00a02e4a5508060180014410408a00368000f030032085c668407400e1030350070414005d20742440c0303a001504110b11102400385c85c3c1c030340108030400e881c0c01d45804504444e000d0340308040d611400030803100071028000b00100380502d0751301c120140c1d4403c0750280062070501c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 771870089 1250 771868839 771868847
    0xf0439030b0301111e070b040b2205070306050c090d0606031a01030503120a0e01020c07061b0812060f03150a0b1002030d090606050409030203130605040819080f070f02030607 77
    0x35880130200907404004c0d080040c0020344806a042c0650a042c620f07085071540d900d0000c010540e421a40300d45100280f28a95400803d0807400518016a8802118460702e405944030789620003e000ea65803100802c5200a03240308480007000003a04082140c0c0c4c50f450000000c01d0684001e45661410a0410a12450b400325060407241c1140c0114104041d655180c010114060402c004c030598918241a0103e002e002400507410b05002400006140c8600500740180500303d0841c1c07603200c004400d000501c42015142241c1c44040e4003d281da40f184089047c01035034101d40fa9141c0300d40360b1080c1608029103e501c2c41807010b483c0500c00f80b80350f2400d21080800e40380203903002d40c0040c0005008024194859240c0340c2c024440400c0003030341c440100d0b007100c05602040d0f0040e000000e2000d4600c44821088000384038501d4010702d05450580180d481d0900c207040400202c2a07122040d00348484030042e200004001d002c0c0b15920703030341450101720116100504034003d000780d00c0095095806 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 771871339 1250 771870089 771870101
    0x60f0620010506060a08100302040513200612090c0d120311120402090a11030a1a0a0542030711011512020d060e010b1801050f0439030b0301 62
    0x25120300d017001c48120b810f944000c00144a5100700da40c0705000405a91240903403030141001080421070070344503061031007540c901c80700000d001811488441d0520707290328046800321646074031302c010980c548440ca5810320071004015940801240701c0d0708103100034a50001592501c0ba202005940142e0312a9006030160720a4018151002400200542480d0746c0855100039004000280032880481c01002e640003561010b1400d0f0395101521003d0113444160740d00b400c402c440c220b100302e1a0500290007002c0e002500340382e180c05100c99881d18108020840c04076480d042a900c500800c128130510180c00454200c0e0001c0c2c0c0070b03501100c1740ca2041c0f180c1040102c0c65110b0005080c1010b1412001c00d4002c4005c03030f00300320281204c40108010b8440c00c94800398040020545400140803c15420070b01030003e0401594034004005950741d10032031540320b0300c0036100402d40341e00009288114251513044014940707080f01e11880c2001da02d00078200244803680381040207404c004181803c0b115 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 771872589 1250 771871339 771871351
    0x7080610170a123504030309030c142b0210021c050903041d07020309091e040510060618030204020f070c1403070501260901060f06200105 61
    0x180301800d00082900c94000c0d80603400e20380484201d007440340c1e42c41c0100490107410500040e01240003d900e61040c500d03060004240c00c3c8442141300e1400c0543c1c41244000e4801003c0c50742c1c070441001018003802500c40c42a8000c540781050700142e10b0642c0d201d6001c110114051020f0380b85540e21816521400109424154010310020200c10081402540040b006000e15800c2c900c80c80b00000041c09503070720a40c0c054002c1e54586141800b030b030114100d00c0030322000d103500b0042000b454960001c2030b81c429040c103c584940c1d0382c9801000c150704070020714040721084030039410402844030000340e1107008a1030751410440b480d0f40e89012074801c030302c3c0300401200c51240402000580340c580c02402031403103030350b0819180207030b50b54401e4507204c425404058092000e20080d00d0707624041c0100001800300313080050400c4402c1108500d403e5042440074014505103000c42c4203142d0952002001e042d0200401c1c1c801034a40c00c0281c007000d030700b16030220b8544003201c40f06020035042c0a2280254 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 771873839 1250 771872589 771872611
    0x3050c0a1112131502010902010206070807090914090c030d0903020118210c050f011413030b0a0f1d1e01150b180f01050412060b060a090602070806 65
    0x4648003140c400c01562103114040c807a4103501c0c0100c0b401d0b034000f4034025400140350350342c840c944001c5810800c80d5003020415039244c040360303c0140c0d1300841c2d50f07a4071106500e0003a0103039075040b6003035a13121410f80201118a01e090121a940e000c07250019000d101901c0c102c518030500e002c105559010070190704d0b00010404041007005500404e0405003e004100d500d40c81c060300c0352604101c1b80b0412040e40343d910781e9000103000b0b11590410300c0c030161001383c03074440c1c171646200c002a10032503000603400701c00b400018140c1c1000b001400040007860303100c1c1c2003480a041c0340442c10050021800201c401c0ca15080d1918070075498244121309141c0d6000c0640314031412161740e140f40341c1190428220654807403e6628003e400c00e0f0440c0094018601c0707080d2240c0710b811891a241e00f03c000b00c075006100302803039440540e80140a4908542c0601605c1403c0c0025107411405003039201013103030308808045003541c103003500075508409492059086698095a840354550344070f4054500700108 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 771875089 1250 771873839 771873847
    0x30e030c09190b040e0a030e1c05060708060414010b04090b040e0d20063309060f0f0406121109040308160306120605040b070f0e100e09040602071203050c 68
    0x59406070800480703c400200009400c8a1030342550b41480207031941100080d003171074810304451500b1940c0030b030000d103000580004e8100706e503199a903624002c0c001c107050107005030020301d507691580c104121680030010720110315607681d000180c40390014002c40c64004d0401c3d0202c0082c3c106807103031440c4026444000d00310007010820640e40d00000305112003404807043d0960294000030400c4d680150b0f9085401c1006542d55104009072000c814a401003c0641020758100340e44c595407a50341151088818440710802500020010081080d01e160010b051141c0041c9440d60224003650142c05004218080702e444002c001c0d5180d400ca40045c0403e1010010031a65202d04008080904003030600003451501c43e4007071000701d100d00008031000b0f40c66608001c10010680781c2a9000700e41e9041c00d00400c2d04d00e0b01e01500c441003c1250f140141c80821640101c2d5100e04140400024042d00445880c101030a00c4d5019510214041d2441c1241420703c0711014440e1144c2032055a044030b001f414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 771876339 1250 771875089 771875131
    0xb120a0902120601060c0317090d0f09090e060103020a061e1202040b0d0524150c101b080c0909060904030903061e050f06060f0d0216030e030c09 64
    0xd1000c400e090b604010031101e0140e10741e8040103400d000e4800c0d80c680707801c0c8112605e4000d00380155100b0304110b440c000f00c14048601000120030a00e40028241041c0603410138408540d03403c001c0c2e000034030f1941403030307038203140501b011070170f02c0c141d03402510140111504c400081c0d440e1940d0007900405482e404102c1000144101c1e03000800f290b60400151a056584155203016080000750b0710302941c1c0e510074850340022031300d102440c103454000b5a00d920020384002400308904410201c5400c400003130301c1040c03d03109000d0342a107000824402c014031001078040c214170340d4100c00c01201160070f901c00701e00071101c20401d40d640e07648000c003c00029a600f106100390702c040503104405000344d80b0004800904c66003d0302c0d03e034a00200e074551802c2c0d0100140303002e41c1c0e00500500104030707500c8288406c1e134898030215000100a01e00039696034407041d90210080c0b181180300d02080203150000c0040582c1b18196111104080b07003207400c0c170000d407420000034001c10385021611050428881c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 771877589 1250 771876339 771876341
    0xe04020c0316080d09030306061b021c05011b0203030117010212010501121b08090c0a3030181424042d050f0a1212090b120a 55
    0x14083c452101c1e1414400300e40c0741d810580c2c00f60041100400c1d2501c2c814803415a104200c4d450398603071400a05d015052740d4011a406140302843d22502844c6803600b4020b020f401d4001e521484940050a01302c86c8000034020740f40d81080c022400013581001880140740e40500a40d460341c10030009030b00780c903441c2500654501029951100d2044d8072140c04580400c600400303480104440c0c0c503020f00710724020080034108000012424864001c002d0240800b00350100120450b010006c10b481d0000b9841141c900c02c03500d5054024040c0254002d003c0c10b0624141030164140001c0c00d145c25804180042618001c3d460207080f5103441020004001c40d5119080300001e1000c00307803201000841303481ea0400e00c00000b080080b08490002070810000b1050045502c0d07070300e808034442229007030700b0102c020034404a214a0b44180e00a010410403a52000c4009004040d41c4030840715074140c615190140c00490306124000ca40d10b00702c00a20000308004840076100104171040080ea0f4900d1580 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 771878839 1250 771877589 771877627
    0x11412011503110a02070612060b0340060606030905030a14090301060902040e0108010501210816051507050313080318120309070918150b0402190e04020c03 69
    0x1104154a44003c0d03d200064031005040c0c0304003550140030b459007800d05c00f409910400b45d409040c103240c41c000304050003801d030549070007074003240101c5c00912040fa03d10010f248080221041e04400e0307821070503e0807141c540c5e546000c1c81a0f10910040e0f5a4181c26001c1312210315014110360070410102d5403c43c4514006c28290200c04559401c0001c0040403900b10740c0305802100d0003660002d8140001680d1080d0b03580100707817403c020301040d814400300c0850041c0c5004510280340a2000b004108507441d015204050a00d4070201c5419110342456590759025036036003a440810200801c1c0114800c4c400c40c0d11800c5068951ba11400d501c3d81e07000c0071580001c6c2179145407034070301409010610061020080000e00c10300410707100d080c80074506042c8507442d8404000c103072410a80100c0300300c0282c8001002a0451031061000c2003600615001c5e1041080090b0310a10004101003203007450315500e400d0310204e64450b445120720106200483c410101070094a50061101e16a8104402400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 771880089 1250 771878839 771878879
    0x3010e070f021e0c03060c0307090b0a090905040f060c020c0102030306211501030510020406020d0806130e06070f05091c02010513092a0f030f0902060c010b01141201 73
    0xd8a011188030384821060071030f420407030003582240052070300c0c80c079040080e5a00b040e80044c55514504007400050302100b003130320400048841c049550a80680190000001072040e560709001914080c038007080700c0812080200c40461401615458062001859440540c4c041e0000c1d4619141c040400c000c2d80228840307641040d4410b510302c2d100c0c08081c040d0101e146807000b200340c03155046280c52400e0a140c0302d100c0405510600042100c031382d00240041c240b03420b42c108000342c0d07120180421008044411005101801c0840e07440202c100041e10078440d200d15600d18403203000e07041044400e0300c28121a50360010b9000d208440381da4000072101c44141c41418200c0ca4000c0d01102d0400d0342c102e43e031114540c01e940780d80d08461002e600d010700d07505406400c8810000744403580054150340202c100f82d8201580c640702d0f0701040036560300c80d04070b60703800602803506c03482e4070300009000e03001d05981180052030040c0480c284241c1c000c25101201051400c0b588103a00300350049400d076a62841c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 771881339 1250 771880089 771880093
    0x120402060c0a05011b0915020705010f0e0409050a0302010f060f09020d091a0901060b0406021b0307092a0305010515070f0f030c02150a02210403060606020303180303010e070f02 78
    0x40700d40002c0d0b09218002d01c6280640c030850150807905c3d40506040b0f0641c0c0504146843c0ea14070b00344a6034003142020603650f0074280090103118642007140c407403504006440e002480d01e41840140000003c0d0410064420740c02030080f079003400050429034003203204007480c0c00003001080c0040c000075005001100307072115001444482c13903100d01d107079912038084417000f038000e140c20b001041000303014043c060092138442d1481d1a10700140250751b4030791402111a02410004420718580e0140154070052654140070300c07104080c203200016252050840600c50903006420031400c1e0300a0003a14100d84006104290b0f01122200310303002607005000c101c61201c85643d81000041c00304810b840303254001c1e40d410740b50028903c14052010040115030101140030b000d01004690700251000c5a20182000c0d40f41280b564a03648465000b540c0004001908011000c1005039000010b50300c40c03c1c68240401c0c0000802d0403147c0c50b03120038020328040d285014000386249000309500c1d08a4080f505c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 771882589 1250 771881339 771881353
    0x110c0304170f0a0b041a270708030a020304090b1005070b040503130914180309011812081e191d0d0501060504150f06080c19050d060b120402060c 64
    0x1202c9080440c0d03400d04545803c0c8840c28031050011240b1502c09a8035441400ea440f41852220752076000a0700740d0203201c09540c0d1400d0002c2800074442000100518401c480c2c072a45510f0019480b034226000b23141c035591412000b0701030381c0ba04035102466802692281840c0a1603919000c0100100803c10750301e034803040243d0a8658000c10012000742142c240000392022808028400d0714005000100d4200e4221402c0780701c0b55001c4103e480001c401d0034100411016981518010801c0d64019000040c903800b1840c1840b8005000f00302d100008159903140c110034201d003031458002c004018000f103d40c00012641d0310300940c13800211090039190320b1820244400040d01100003810204c9040e51640000c120904143c0100c80d800454010f0319001a420604c44002c00300e400d1090800300500d01c800308a9182e030240890f204c1c00660420400d15031228840505141e1004110f40b803401e1034810001100d20716178042c1e5161401d017200044c030603280c6400700f0909400c084080d807114040d0070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 771883839 1250 771882589 771882613
    0xa0312090b030a0b0405070c03090e071b1101091205070e07090302030118051006240318051501051e120106080f010902040f050402030319020a06060612110c030417 72
    0x107184103d00d004808280c001010081c44261400941f5850502482d80040c60010340c202c070301c5c9010340d09a0041a03a0540da4000c046480070001342c802a40040c4031203460090100c50740350700806040a80f035007400f02307903107950507000b0304802030340589070f504038403401c0c460780c2c0c0340c8441c1c2174003c92070745000f8041d45d48980029003107810000120301030070850403210042107000c2c00840340c1c03410403200070040d281c07404481301c980700326001c2e50a400c0e540844001f0358030346c00b07a0705c4440350100c0083c218401d55182d240055560207510803d26200180c80d000181a00d0421030f01c00400a0303d00880c10304880b86414081000c1459000e0a076135500c4160215405c3d00c10046c0b1603800c0d0f490750020030088400c0c0188401ca81c002900315545500b00340c20840962000801c40300b1609003050b40b035030302400080c8100e09185c0d64030001011242404000500241e02c000f02140c40130126404010340000c103031246d0220311a6000f03030301c0680c20500c0100450040c61407ca48900c0825050300d00c404110703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 771885089 1250 771883839 771883859
    0x711120a02030d0b06031e06041d0307031116090b1f051c06050a120606030804030804080f0a020a0b09010915110708011e0b0612040308090d08060a031209 68
    0x4008003100603440402ca1a110408501032010100000d8804501e9070030040c003030303a80c10180441c0303050031007540c880454110b03101c50f800402d0a000002e80450b5002800004039240d40c0a03400950010300c01040c0ca004607680456006254a250340010500780d2601d4031403000741142c00e440c0c44c0d0003651031180c0d45036000840d20a403190324580c3d840301d070b940e4401e420060b1000d01d90034000c210f0b00d1030701c078081c8401c0e140c2003800c00c280c486106180c2c0c82d1b01a5031420300041d24154000811038000820004100502c8001400650ba81c0506464100d41042c140c60f036204a200d5000e548907824a034100120001030000748500315041c54510b01c3c103a202c20b0030a0740f0025551000340091120138030780c61580400c1c8000ea028161490003030061141e5080110b885a2101003040b202c0e6658117009402c03079444030f0885146c1d030100c803e00e0903145000c1c00c02400742041251001028003c2c07503c2c03c0116481405258400c2c10018488400e41c1d08544500007580702c0700c80e680003402100d0030085404ca2038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 771886339 1250 771885089 771885097
    0xf0201110609011b021f200d0b010f080f0c091309050a02030c061c0203070e0d050109030806060a09030602070f0209041202070605030106020a1115120901140708071112 74
    0x2540c00100d2609500c1c03030b51903106400094a130045400c03a013140200b000c0740c001a400c11411485020070b940c0060f069041c2210680408071001c0d00000904010801440c0c0001d241040262141aa2003032602c1080e01d0000e821110b00c9440308880b80003c032000340c00406459203d201070000340c0425800510041101c54400302510030741e005041417002c52030100a02e00c107141041d942c10b414401300f10f101070801281d41d1501201c1c1d40c0c0110000c0c03078031845060400c505c070800401c441ca004040d0f0603c03c0c000d000060084d000200080001403803814001d04071034000305a507a0300811107103141c82c1c50000750858201102c110800500850146c0e40d5016414000c5028100303091907520388250191501510754040414020103000401030141c01040010340d580d000b01c0c5091005928400081c152944066154103259011440b4144114402d00042c030034140710340204a0a03010300d0200d584a80e04807202c50004107144001005c0c0ca202c0c5041c0e8108581c404211072140c9440a024001500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 771887589 1250 771886339 771886351
    0xc060b060c06160c020a14061c05070206010b191b0b0103200f0f19030501020d150806090c011101020f0a050a0f030b090a09170301030f020108220f02011106 69
    0x100c41c2040c0711189502516072000c980e02404c10f00e040c80610340c04a880f002480c851800b203040b010352200c4040d142d102c2201c2d4207000a008040c0c1c510380245038000144030580e0100010711400002103a2100b8487c02c0352075801c0341480034480364a000200711580c49019412121003480810110006000340c4c0100f8061032003122909014400030001c3d00b424100182c41a214013000c0c54100c52a03158a80703800780c90304060308c070392104421420000341a201c80303900c010404c0d803000603135410291040d40051030040440640c91145030351112440c3d5200d03020b90748400a9048203861020940c040e6840c6078282c28910700142c2001110f0f40200300c980c0040701800b012a41c000780c05001c003039016540201210160800f0001a9034601c003140c801003005044144c01581c40d07042c401842443c004c00e0312f10000769100107580c0d41e12807a051042c8154420104d0204003000d002c14150203400d130740c089400400030107500c0e070120183c0f907000116030720420903414030208070744441100809020043c4902 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 771888839 1250 771887589 771887593
    0x501050f0916081e0322151706040f090f03020607020705040212070f3e01182009040809031501060206070323101401020307030e0402031b040e0910050402100c060b060c 74
    0x192409601d03c1f10365960b6034001081000600900c0e800c2c04141d5865500050107a40006074140c04401100041c01ea0034805032076420446d100604042d40044e40c10712940d00340e0309440b24240d0710b005000903070003504154170a01801c0000503544511070b4440751386801c410301e010740f80c1d03404030b000b1301000c400c16408a00481a030140901030009924850280080031200200004880080c2021180d02000300007805000c52841641012022006690000304011316940d05418280b030404000d5001c0e00203140a4080c2d045186c08080421007082d04944075a0050005543c912100b01e005142e5108180d40d41c490310070040329850450081c191090881d004880695800e144112610032a0007410038110340c0300b0030010000075440384145005210544000d07849032100c030001e0f01d08500104007145108800300b400128060f5030709030b550145912205440c000030801030210141c51003203c000c2e4014500d800e441903198030490800050030701442000031018410740c0024010740c4400424130080d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 771890089 1250 771888839 771888907
    0x406030b01050c0604030c170a0305011a0309070608060d0b07030507030b0316050105030a0f1e06080705060f0a1713170a0c020603130501050f0916081e03 68
    0x5415120380c128490090034040d080802c1440600e81c1c0700c1000788003c0c20030405240d1242000b0030b400700391168403800d01c2c0359a00c50381107160040041c10240f2403040d041c3d507400340003400524078208a80c0181c441b80094000300e42400d906681100c2d001e42a203420180307140003400811490b0059601402003950b01251500b040301c4002d00341d030410314009120780c02c050351108040b110704000800b256420300345161a40d95100c01c1030028a9001541c0b074800d030420140030804050f070381900c6420780c00381400b040740741e4072030b05920b0740c43c0c0d02409141d812640800101c0c9081007110007511a041c0305140150502c03104181c2024254419110507403419010b207811020040210041181001c01490a900f001d00e0350074010001c04030210080c0c00b404002000c1444d1816107100c001c1160b410034000c0c1b0180c18400d03100c52107542c00b12211210380c01140508460f05100b6590142105c1020004140e0405005c80c106030490007022041020300c410041072101400c21080895040030085581d402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 771891339 1250 771890089 771890099
    0xa03050c12030d05130b0708071209050106030501050901061802030103020a12150c09091a060301030320060103081201050d051507170c07030e0a0b0406120603140705130c0503060411070b0c04 84
    0x146c60030182050092100c46020020b107594400c01102d10104c0b0b0440210305042c040c10468010011a00041c1c20795080004211044105402c09002c440115540706040c0b802a441c032000c902080c00001c2d8001903041c2c0070000301c1c0c0449031681807640944880b03e003400e110704c07013a01160561038105000c0717134409408000e0050b90f445041d4040455030f6111a1003140e0f040001d00038401404005c0c2071015100104190600810110190902840c00c40d500c80d40c490a084106400100f8a03141a9020500116a03400c02600060f6400c0e07004000309400040e10060100c1c82400030140c60420285180c41d00e42c442406402d82d0091404850080c0d82c0c6000c0d0500a00a21546024500800d56008100000d03d804011103080394154034101c0b001c6180354544c03001414241d4400f600a400000ea00060385101007000d10446108a0702c1c0c02400701901040001d440d1860080b10110b0000e10001d407007070826800c500c1000b902c103c242460100c59a6400240c400207454045120300c0100302480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 771892589 1250 771891339 771891353
    0x30a0906020d05250303060f0b1306050a0807030b03030d02070602030f0108060601120207060f0207140708010510230312040e090c0607140c150a09050a03050c12030d0513 75
    0xe42d526461030440e20b040180b0082e014500404098040541e01000d0748105040c0b09a0040000d80158001d1400d4990741343c25111080c0c00921140b070b89119007600014a80307000310b0449040d0b16a50b01ca5050503500c0303250540090515944403a010b0100700440c0500a803944007c1c00c00510441c00107841b81002e102c0c07882c00141c140c00c58042a13101605000e40707a82c00580880140f08514005640e0364080d15100c00604401c0d6406000715002040f10420084003001c11440b80ca4814101c0c1d07a8299203224003802d0760010342e4410707110482e1200c14449a01958106040c2e0700c3c0052100d0150203070b4001191900c0c4040202441c180000708080c4101c640746103d46800003440c0c001400c11014110016076a0b03c680900281000194100003610410034814040d24030b07030040800d4120780c04802c11010580c001c44005001840d4003034081506e1a0030310250064a80143c0100200a031003410300c1450b203006442011a44030901000324002418060640714000e50a42011410011b1600764 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 771893839 1250 771892589 771892603
    0xe0c180303040b0d1506020c060c0a0204050f040b073908030a0203041202032a0c1503010812041503021c02070501060609052211040308130e07020a08121008030a090602 74
    0x207045c0f41c2414008210856000804042407d000c1341e01030350720303000001007a1400c0c5c50010000e400a00b40010003d0440c648541e6a21541c0a01c00030081e82d03503050402c540301e018038881e11280041c14110041c144449450b0303608600980c0030100c055204545503800540c104031a0f9800194001041201708814802c00b005400018002981004100a00d651003034081c416104002001012005010032040105101c0054090810381d09a4140c200c6c1a8842d03100b40690b91482c4a0f1419102c070381001c0e40b0840302191001148000030929040c01180a07503c14000c1e100e0213007640c44080d11044051000f0000b1a00c40c00000941601c2d003080030f0102038003503001511880754289800d00c0a401000b0404400184c24030004810b052191070039114041c1e40c10182c01050b000c5007030b0082070b00035581d032019180300745200d02d16036842c02400c907900d0b480c101004003005014040e00044103c1442480d4000902e041c0c0316800c2601c03800b0003455a0410825500024040201000f072a50144207078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 771895089 1250 771893839 771893861
    0x110307260f0d080105060f0d020d0e0706210f020f0a0c0b1608060918030c061b0c1b0102011e090201200c37031b0e0c180303040b0d 58
    0x38080100300e0350300140103c0414400c8600072400091405030700c0c004c840031199400e4900008540354050b070100368000f054506060151303442501d40c04120103020b03203001283c0c1e44803a00f00c682002058017080000d4081000380d00d0100e9024000e041000b55800050a5a08400c2e516103c1d076281d40c1c03c20313003000c01e0301400001038015040120301038103602000241d4824020340d4070080035110b6021402c0410b00d0003500582501010070751a18850010451601884111400d0311a190a200300d000c01c0380300e2601c01c84c0450344049840440b100d81c90703003a0016208140000540d800364051000d405482e00705100c01840d65461200c8115038102c10002040070f1400030200183c5008403d9940e00d00e5910040380c421107018004800100301c0c08681d812000f040ca03034400740012019000501804140400c48203401c01d02d036030401c42c508146503d4115000e150440025484103041c4840607482a0810402d45140110003086620100004d000810204048503950040f4215071422142c1071070f11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 771896339 1250 771895089 771895093
    0xd11030702361918021509030f0309030a0210110303040b01081504020312090d0212010b1302070807020405090c1207050a0902040e0f190e0604031101140103110307260f 74
    0x20300802403e07510711001e20510000b000203507681003188624070303285000300003540034440307111404225181c80042e10b4510340640c11211f9030342003800c00c03685a000b00105d0540540c04610990098541003004501c10340c00360030b19a42182481c5074150540d80121360544002405c0030040003268003c01040c0245d00b4140115592410320b68000f039122038080c064a001101d01061843c140d80d61800c54030702c9194010003001c00e03401c2d06e0400c18007030301d06001403038414900c400d040540503980f4001c1320360032540f00015030700d0b0031a585d0802c0001c10018001c440319100325011550503490f103a110900c14944c0e880200041032421003000341a8030a0b070441d880940c0140010008016014055034200300100d0f003104096507a003140d84003c0c00b00a500116040c2030a50680d989080404e2a90085000f581c642180303c08403d10306080c0c030040400c110b5601d9911004002091100000242e140802010784501c9962810b02d490f4541c0d5596008520b489000304a0241c248104803039940740201d080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 771897589 1250 771896339 771896341
    0x1e0b01020f030d23070804121707080907080618010c05030106080606070305040905091b01021617011b03140708010b1602010224010f0e040512130f03110405090705030d1103070236 79
    0x103407501d045070029080cac0003802080c001003103003200c0c06e000440c003030444c8004542d0300f86440c0d401c90880d51100303540c08180c0c0d4a458640d602c2c0703130301c6882101e058038407e84400e400b030b45900013070000d140c6c003d120a0b0200300c800e000100c0c01c4145070240e5402040c62000174210906211a0400407006c034500c05d40c103560005041440e10806000908121540200881c034140480844a40900704000c022220714103401c00c9105a05d230903a100d40300b0640b240d200d8528a649012050305c66542c28000d6500c80d040a1201c40c000012500c038000b010740c41032054031a140c0c0c0361034070045100158a00c113140a54040014000d00240b035580700001d104900d84040141480d44546440303000440801c1c41c002400a020401003000c59054402070806648222409550381045a110f00070b0203c220320650810010441204002503010305442004014011b80c3c130130110262501c0d003e030310700c9070450300080c0082405a5940704008640840c041e22402c0c546244031004100c82c04806421074000c08180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 771898839 1250 771897589 771897617
    0x3030405030a03080901140103030518030c01120c210b091b030708090c030304090e0607030c020309011805100207050108070f0c0b060102101e0b01020f030d2307080412 74
    0x2050865580c15080040d000d407140d104184c090000e003184100347d21082c500002c00c056015000b400103075400c460004e0300c2c000341c008264032551086604e0f4000307804210107254180c280d52059a941d011820142451142c0b80302c1842202c1c1e800e405102c0311075880540184904120741016170144030380b1103074603c0e4120742c03554251750300001c1d08150402c03000c7c81c0085c800440070091813420800c0241200e40f42c070741da603008501400104c0d0068880c0d000f00d001081449000b40250780502e801500914200340c610401111600c010b500d69040c507400326800029291a240a00c0c0d2902c42d20f0707030292000c142031500241c00280003511074010003103900c0ca050385d080d500220740801d00d544040c0119a030703290240100d01d00510f64200c1c60005103022036129242d40c6002034a80c104440032000d005501c119801a6103886600e410591190010080444c1d10f0300241d010012041c60b01c19841440003800824180443c4200d903c1d00206803442d080c44240002401074500208103843c2c00d0620441c11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 771900089 1250 771898839 771898843
    0xa09050301052205031c051005120706030506060d020d05060a12050d03023103021002160e1e15090f01240e03010c050715020c06041e0204060909060b0303040503 71
    0x24038141c5090310f45100e114007040710030300407100d40503040010f0000c10811610440000c00d0117a801d001c480300070303420002c2c03141002d0a40c850b0b411b10f01070141074a1444d021080c3c01a1030000c00762b41d0700c41810441c20f844012580702070074034000030303140c0020f0034500b500c140038919599400084547e1411180f4400145d000035800a9a0906142c0542c440c40b104400d49070710384500341090383c0d00c3d4000ba6041185c00b41c2e40702880450740210f5140d15410515001a80c8a04c0f50030101c0901d8005a1410b0041c1501216003039004940c1d6000d5040400d02505c510521040c01e44420603002d4140c558403246140030303d0420f402850380110a816940f40c5500e140f245000a60320160711310303100400754111402040510441d42014009110907007520350014865400420200c40340030b04070060520202c101c1c0b0039250200f040300018a0780362610b840d0001d00c10f124040a41c030b503904500040e0f0040e02c1b98002c00c401411001f00119040c03005191100c140d490141065000e64001d0008106c1c0d9940 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 771901339 1250 771900089 771900121
    0x50d020a021c020607170316030209010905040e0a06022b06053303011202090a0605030606120109060204061d010810060c0507030501091a070c0b01060f18030302030a0905030105 78
    0x242c80020300061085201042040c090760384050008452810751010008101004520680c0c00f00e01420f0b5000a000c0203404038003881c52042d0000b0300c1207100344a43d0401e90311441401c41a98112000310a155494000f80d038880383d0744400c00050352018103590450070103c117007500002c91042c0115818a00410815503c115801c07481604c141505840c00b090a070001a0300e507030031080c113550f030740c0c541418414144500307208038020904080026a007200c1c40c0310b1041694070040c0685000e841d10001c000807901d480d10041c085550f541290000500c00e44010300040049440b9200442000410000184c08070820141031040c400c0c20072a0f08007904090105540c91801c03d0a818422030401a1406a0a81009283c0e6180050304402d105407150f15100c940b02401c0741000030b130b44500c0212030703d0032100da0084c15912035200500c030f190702031039590392055540d01d81000c140c0200603814444140590054015805c00619002c02c1036100b0241d201514060700244982d0911403d8844c4e1415 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 771902589 1250 771901339 771901369
    0x50304030305070c0c030c0617040209040209062106010611240703061d0105120d170402010309120903050d090b04051215070e131a0d03020708030706020304050d020a02 74
    0x42c0d107800040f003450055100203800c82d002075020b2407680c0c507803428000c0301d03415000f03010210b10210b02007414500f03d141250301c582c0e40a480c02c221521584c2c01e221000102a00180e804040345180c00c090f08a03a0b2040c3c1381c0855054003c1c845940341901c0908949241001340c001a000040c0c01c2c595812001c40350003039084d61980800b5039030794180084001b003039140c0182801640c051071140051012945650581c2c008440651901a03184000c56581800180f428080b400c20101c0c601c55081072003503903500c20f00604002c03134500510354418108074842052003020521804c0305205100302000588183c92503030806024050034003090076810b00461190612a00c03140890a012400078040c040d80321b020302200c03861780d04103075202810741039002c4c8125000c1c0014641d030050241040c06403000120f07001701c1d030b80b0a03641c41030184106541c09150660551250650002e401c00c008c100030400e090043d4070068484c2007a241441c14100659100011540600b1000c400360769511901a81c0c24 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 771903839 1250 771902589 771902591
    0xc27071706010e1c05210c07060503071709061503030c0c060319140414060402102303090c0102190b191b1d0301060f05040f0209030f010b150301060503040303 70
    0x5402800041c00006030392080d210944803010004c0800034001000e007410b000048811614010f800c0c00c5c260b082c05920f204249545c00094208150350049004581100040c60b03c200c080b51299204005607000752a068401d07400001080001008103403100011a41140a14640036421160a0741c1e4120340b12190702c41c000000c00b1900b8541412060104440640824040918480416884580112401c1e10f440c03000d07441464240d5004290148510380c014a07044003129082c40c11103c4400d5080000001d0560880d5680341c200014095071188140b00014128010324400080c03c1c05404d1890144015143c810080042d84400f00c503a844444400c9010505285040440103051101300008860810300700c2c0c041e88a50000170f41a1070703558040207170b1b0142c04100c10f042c00c0f52124411282d48a10440c024030092629802480f4441c48409015050103081ca002a040143c4820040c0382030f0341d540c280f500c00d414000440c2007a000101401e40c155894144054058800204018101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 771905089 1250 771903839 771903857
    0x204090b1e060f130b1c020901060302040303021009141203220c1a070f110a1d06010f03020904050f0a0e0d1223091506040603051b01020c2707170601 66
    0x98142c0c020305c1c03c00c400400150402d84070301e01c080c0d605246240b05900a000c85000130070407a00a008a41c1180c7d030543c000e00020440400315002070204e40800c03a4980300b01840c1d045806e8041100164204d6136401840d5241424100c101c41d112140c291000d141c48003142d03403004500c00010583c1102c4081d0034032031890b1410042102c09204144c0c3c01094116802c8035101445078620703038103241e03c406641c002c42e1355444d5240790300f0380440e003000c105000f2031340000034280b9442488420400720741c0d81000b42c02e03e07280360001410350f8030440315040c100119204100301d842e07150099011410b40103002d41525050070a004010b03401c64500c0145460f01d030119804d01040d2202c05510002040d070092aa909007070030103540b50340030b200441c1051410480031960b145040d00c14030040701d034403000a0010700994590b154030711021050043c10b6000f00c0c0d01e209510340b90100c0400c401c000c081060b400ca5000509010a07014014118408220700c81c035041c0307803070301c200c00700207402c000242401c200d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 771906339 1250 771905089 771905119
    0xa080a15050a181d0c0f010801081e1609020304060b0907140c16060c0c23120312042409020112020306040f0e1b1215090a0204090b1e060f 61
    0x1404d503000ca0102c5051006000c5804200d000c101c000d8200402c99050010303003610302c0119010002805000b03295001401080f110316210031802c512246008191650183c80b81e850201c00c1149611041d03a0a40001c200801c200140c07186540d07041f01103d8589190921034001407101c1800720303100c18180c81c0040d000c2845182040341e58001400e004144000c076450750300c01026a0082213040b28407481740e41000c16003811140c544200181c10303250080707158035003c04000700c4c4106440c8110841c04204401c1c045074036010300a61107140200d1a40e003842c088030f0181e180b6504000c2d100d0031120b2600c1d0a600041c0c2e802a05040d4001d64814050388070f40303480000600408807910480151072402c196903801d048041860b00309540045440b000c2c0070030000a01c6a5105601d190746100d03080b84100000c4000440c0909810034203401c00c8072441b000700c0d800304003103400e411800c3c3d540b426080c0403c1600024218110f03842004503242ca10340c2e090410204100905c4895200e119906080b07031090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 771907589 1250 771906339 771906341
    0x6090f060906161427091503030901050706060306051806100e011203180303090f050d08030a09051204031b05010e1e0102030d0510060e0607110103050c0f0a080a15050a18 75
    0xb55030122605100d2100b6404074117282d0940171401d4490152540310005184d0340a203200903500070b440035026510305003028004684d40e80c000d0904aa80641d81d000220115036507218151040341c0d041704c00a490035a00c0d0180f8a04500103001d612035508144080c000341d615a40040c1c1140c030995140c40244a0919003914010f64103075141c0c0d580c00140000005142e03002000504843c80300c4592101c042d00c40050182e6880710381406401407508001203000c0b84155403040c25124061005c2c1d43d101c852121040c0455482a4007d0f40d1030656101e113650440070340007009004050900b1700984101da0400841e0f241041c01041d400c04414805a40d04c0690003441200c04184071000d040003c0c0c90a01032200f1401418041ca02c0010300f0b00310118020700389102261803207038000700c0d019140c205a50044000d000b006041c01c1030faa20520400b81e4400d9044040d000380c01440d110400d25142510500040703c010342100c146051a07402c0c1008551904030b02107050f00e0104920485a101c40307446d80c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 771908839 1250 771907589 771907597
    0x602031f0f05150c0f0c0406080c030312090a2f0a030b13060f0f1e060b030a020309150430051e1e130e041e0f020306090f0609061614 59
    0x2200380d0060f00050032200d800420b07a401c41601c1187c08004041e2609100c0b503851508017461b9070958001c2060710743c1c5030150403400e03520080760021903088981a645d44008020011090320031852844201300c0714808903100b52030031031400e64114282c80d246803512480451301070f16101300006901885030034840180c11048544070b40b202c0c1032080041d1101b004008020b5105420b6044d0810180340c140402c0e24000c0100300c8448050607820342e00d844044900a500151030200d440c8101021901e606011884d218400c0d80220311440c548807526607259801c84d05503030010f006545101c8103018940e04081a0382e00c0440e00c12810301c21001088401c0e2851140040a0305540c01c0c40c041c2d0109810014003d020202da03100360809100d9554114581000090b500200081c0c02c7c0d4090400e8403140d090340803075860140852252500c490f80119050000540b0303c42600d821030108005900d90130491542c0040c0c40500418107071405900c04403651840960355010406040011603a9064040c155 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 771910089 1250 771908839 771908857
    0x2040b0a06020304090e0105013f030825120b19032d03050406030509010f050f0907060c0c1406130902040f06020c09042405040602031f0f0515 63
    0x195200354552902030342c1ca8101d4403a0401d01800c007183e0451019040c000c0038120f0750500f601c41c0c0c0d8000314060810b14020361440782e592a4503140010303052146414040481603000c0e4a03110500d0030400384511000000340e01103100890700040025102e9408080d0044101c1d08440000384034090400055000f02524011481d802c04c0d14004810f01800442d102c4a401d14050442100f0818911107039160300781c0343e8042c01044080c0400c00615009403c00e6500c9247c803000084c1010005d01d600b41212800e40e110002181c003441001f0200100f04103000160103142000c400070b001c25921403160a000e0f0003640319454600216a640380c55040684840e001e124030044040ca4403074080f0002174129116120120743d1142000031a80d00104025044600c05800030016a845031140c24105845c000004140101d80855484490700b5201701401248100380141e0369080800c900c02040881c1030285445408668040001030407490702803044600c1601c00d07411050115140588a0184d1000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 771911339 1250 771910089 771910099
    0x6270f04140105061602040f050f07300e0a0303061701021206040e010e0a05010c080c1224100201061404020f070b0403021906090b0a110409020d02090307060504030b06030a0b0c030402040b 83
    0x20022448205820452103045030b046e20a000c0d64500004483c0081401c0000c0454a031334039003c2c4988030707c84242c03040c4004100d4040f0b1030758030039140245460803584d000c1e00040d0740c4060910200b4203051800c0e80305400c03400254100703612075010403003020000d0061031241da515480040711007030070b400400200d540c040c00d0342c581ca8560b00702035020700707008040d0200160381c003030000d22507007072080c155840342c055600d00800c41c0d0b43e01a0060302061140d00346206002c0e500d0302c00300140d5103a584800454407241c0c00803c3ca1841e044c03000e10003000c01100300d0b20440c01800000240800c000603560055000901c42500e6140c5040030fa0a00600380d0013544940b840607900010f005454000440c101d00c01e1040b44801e03034800d00000112040c00f11a00e802c500c0400042149140640140002c800e05440c010315200c407074000285404070039480000451800f003420401d00003404000c80c0d00c0842030b0060160741c0010391b6101803c00005002680036500840824195201e650042d2003030321016003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 771912589 1250 771911339 771911351
    0x90b0c0109050a03120507090311010f020a02102001050912130b0711030f0a02010221040503151b180105070f0501060305030c0f0106081203040206270f0414010506160204 75
    0x4008203c401c805c031703110030388034102408140520710400035202266004000001742c641c040d00111007800b81e900d000800c41c03081d0300f19180540d0307035402d18894031480c6886040d25118a9200c001c0d24000c034600d102802d91424003007148544021035a00c8030900c401507900d80c1c41e20039109010059034150403010310030b28041040b070100407004401c029246000c0b02282d508030340da0700449541d1840041c009005030040007800880c028242d4403082051441841103050a8894002ca45811804481c082d100420441880068086003551003107640c40b0030a124a08940301c412814078022620216040140000c0c4100034400c42405a0319030740da00c400280800c2ea40c070304145580343c210003a4113803140035050703c2c0a03074400c0c1407007210211041d0034003401c1131024004d040340007504000c00a90300818200705011003902003d2211603410010803011241001d80014000300c411043e0445000d54500301c00d10032064100040c60341121002c441860f034859903200300342c0e030001c42c500c070007500203041c91 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 771913839 1250 771912589 771912593
    0x190c05060a14040f0311090426122a040b03070e120307060501030302061f050603150a060801031104060803031f180b09060f0a1404020421020111070501090b0c0109050a 74
    0x8040044a0061180c0301b0000c0101081210b0050700b80d900801241d020000e015807400c0d581da00c41c1c0d41803a0041c0c01030518111402840c0da0201c101c2d115007ca0180076900070b403816202074a40c2012128900c0d031800d260030001c3c02c02280c4805401c04050000e04407045450f540d860403070104080d0040166600e44149140c218003600d02070108901500904001414000f40032031142d403001d07001c841c42d001051902c01404a503610141000b8110003501d03203804201c0d02c03a854004000c2c0025560704a03158590301b401d00309580c2018650348a00d0074228100680710000050ba6082400c844801d00042c09000d0020202a0f05901c14815214007200f618000711883d03016400038802038444104c1d942e2840c040001c24000002007a51012201c40203200207000320140d02140e0320041c10052030182c07242c502c604200c1101300401050881c0f03242c80c13000c55a000e40da001c081c040d040d0041c440b590030700f00003901542445c001c44030440c8002c21100711600d000d4001c10100380d00481030781d850309854 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 771915089 1250 771913839 771913859
    0x70602031f0815091207030509040603020604081005090a030f030c1707030b0114070c18090b0a060303021509071401090e0f04050f0c0904030804110405070e03190c05060a1404 77
    0x940e0360354484150f082c00250381048003050b0b02841800d0310290b2450032006aa059804d87c1010032456007044d9923070740c084016150b160007000644095001828040402c1c20324205580f401801030340207400802c26400001c0d0400e030044100c000606000c1000700c03141c1c0c3d044603581c9032003800c1007411035101c080c0100140c0640c01050403000a0340d864032100b07090b80c0b00c14200e01c08c00800a01a09000c0001c20400c914403c000110713050080000c0740c517005540328404940030641b80e0000341e50b9981d408000701a01001a130f1004624004060701c03515112030381980310b0a0922440b50f0001311240d00074a1a0f214079a8a03020701418000e8042c1410705403801012148126803c84184c410b618000354040350001e400740948000400f403503510741d07503070b035003198000c0f80504100d41390b1080c0c4070018405d60b5180106489040346a90310910381a60f81c0415103090352411100e041e2126904510000c601100c40080c1501c0081d82c0b003d90340e0b000c210f41154586404a40703004000c00c0890049a4030b207070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 771916339 1250 771915089 771915103
    0x12050c120918010b070308190606050d0b0d0b2805040c0e09030f0405220507030f060909030509150c12070221061303030e011e0f11070602031f08 64
    0x401d485030200c1942e07150554802100a000b100240c1c0c1051080b040002d114551655100c4800600810380203181c4400d4015225190004008204003080d08002c1115920496001040440d2001d10b80a02034460035481c078070150095000094071284e510444d01d60b103000761180e4690a90801942c580f60031300e41e646001030b010fa03500074420320f000724150007000026512104008441c41e40340c40d141800b04030814a209003409050807000f41e409116491707a2040b01d01c10724860328089400c924840c0d42c03900300e501030740100707005601d08000f000200c0e5000040e2100203c0c169101c0f9400d840c0329a00d00c000e0701848821444e82e00c1440c2079140322262080160003030610a65409004524120f00040c5121020003904000da00c00d10000700d4205510000b0006103003e814001511801c0c1041c141c2500c040101d030308840b1644c0405110200c0c3e443c812407000003140801080b8417955102010782500c01d80300b0181090340c001c4041a2034010750650440c4035030040018800441d943c1c0103098a40c25 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 771917589 1250 771916339 771916357
    0x4020d0210052a1b03100504020f0604090219021b0f13110d14150105070c0801020c010b0a0b030708070c05030d0504030c0b0601030c050409110f04090209120c01090312050c12 77
    0x1c0c50400749103108401c0000140c913800401030f00c200303456640104000c000080080e030b4060075800021001d0b8403010000c2c00070700500500503035210002c40000042242e05940002198005494980b40300760600790442d40b42000c0740ca0080c02024080001c0d00400032215074550985440c1010301c400300f02c900240725002559106004034040d603c0303c0c1000850803103080041007090750036040341d58440c0300245145441040780d0a1406d4035034207461f003280c10618151203103a540300c480040700c2c5860101c2e003004002180c1098510301c0c0c2142c00604044014201c1400d0040c500003080400070140300303981003001c0038101084140390506000306200000442a0b860301c0c5124085082e03540b2074020078440900d01c0d101c1038a070602c0d10003910001d200030120014682e200307111000412315031170000c100070880d4030809a282c000070340c1004448600440254107507401400b845450781d070481003500460341c0119412001c0500010141c410b44114070000c0c01c00d0007006510006480300101a03c1c21038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 771918839 1250 771917589 771917593
    0xb0d020c251e0302030c0f0402070c030b1509010b0d32040606170a02090c070512040501091d06040b01050d05071701150206040f02040e0d020105190504020d0210052a 73
    0x1581d45030b4010584022400082c0d0560428410080e5a0401c0300c40e801071100c024100500c0c1103503585407200c1940301e64100b16600b452140511a40d084021808080c2c20000c5070b0204071545401c07880b18a6100300800c40c6803130303901c03550340a0404e4884c400001045002ca44015040c0307a016100c100c14100c2190100c481c5072030944d02152629030a103c000c82036001000914242055030204489610002c10340c1801d950304010000000d0740a006030045903482c14445a140ca08000002d07111100a80000340315210280e0041d40b031160b20905150890015a000200e003409240104c540b4424016004449801c103c180188542d200b551260110910311504c100b99132558039035044104002c08180060f40700c3d03004500401d040f048042d40c024401031000030f05c180c820310303005e041c0300400c1040c4001d40d640340e081181d07031400d01d030700c03080b041d640610100071520381507000414004034000068040d4140185074200c45002d8800c03501010b00c2c000080c4501032694009a00040e0419180d02143c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 771920089 1250 771918839 771918869
    0x25080a030c1d09042604030b06100c0b011206061a0c0106142b02031c120605062a1209010e0a03020901120602040e040f02010e0108010b0d020c25 64
    0x3411111440c8055004028441181620380c0e4440c1201118101c3c408545185d003034207141003040c4060000d00c01544a01c40012480c40d00804008181040803014001d00251105a4000039074000c07505040d100d09145080001c2e925052050040c9859041204100040a1a200c1001d400320140c1101c0c1c507540001e210054403001d0307020461012040c06500506450707112035030141c81c814400181d40c1000920018403c183c0c00082ca08a100c840d000652a11183d803c00100e60120070026240440300040c00614074000101c0c500d403003500ca066080c1803800e0300e0580d1480400c00404894184401212040380c424140d0000036884a210b06c4d0101d200030a003010f090503c00c0c4010122900100f43e800c1c0f6a1800205401c0d010845c1c00c00c4880c6542084041200c007400000c035806240108028800741007944005018064650310b45418021084010480b003100c1030202c2e20f25030102d8001603151348000ca03030030380b83c5507001c69158140d028842c9503041004000c56410100c0f80e0070303c0741d5141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 771921339 1250 771920089 771920117
    0x60d090b1b0901030207030c02040609020406090b090a0608150411040501021510060e010507050a11090901020702090a0b01140706050901060501050c070603020313021e09180325080a030c 82
    0x3008800301840071900e4400d00c040b244a600950203010000c5c02410003408100256001400319480c503003028000603400b181c240000c42e4450443e0010b4503990f07203081d24281500c2d000a000400610511040003400000511064140e07003110181c1000a40305010380c011405929016030020301a2600500c511010035100700c003c80f07a40c0f8000c44481c50042c0c104d90910724100d89046407a0302e081d040c004104030b88400110100418005a4041e440103650a83e070035081081000c030141142180c0e0703006101400141c0e0f28112440c0e0402c900480000d07000740b4a400607500703c042c2448910001c4400720b01ca405002850300f000f41310700d4140008204c4a0f44a000545082c00354403501151588064800e201d124080e90007540c1050f004d00300b050049409500042100100e116131160b01e81c40082c22209c40d09100b42c049030000400c6400c4241c1610341d403400c83e500c1c050b0314032841c84102e03006054924068012000c24500b5004000c003942c0350031049020f805014103040400008811200c0403d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 771922589 1250 771921339 771921361
    0x12110604050601210c15090812030a063203010b0604120b01090501030b1f050a06050706050c04060c300503010e010b190e0a0503010c02010b0102010b0609030a14010209060d090b 78
    0xc3e01640301e4885c3d4005800d0600d40400010300804603030600905880108000707400708041c0708011041c0850943d81d141151400b020f865640d40840385603aa00804000b00c0e8110018000106160020b01d640c1000c2c6980000c0c050003817120440d401c0b400008011030013000301105029a00e00940140900307903030764003034803046030b000340b1001d0b2203801c101c0c0100f80d510344c1007042d10403070f40340c1003421510310358880002428030b071001d0344503502050b00040d085040241e00e000e0f2030b504c041c500c0e044900b068a850340207042c4a8510300c00411061101a13030240343c918040c4a02d6248214191403503880d011540040c00542c0280101c901ccd00c0c03070b80d1000207030500c0710354104c8244040c407160404a080103440140c50240440d01282e502610f10724004c07071180c80c00d01c140161418154000316148410300006821620b50203d40e500036041005500400d0b21700040c028001903111800d16825203220107458020300035007079440d80c00200081c180350403600903080240b00c580030740c039070807203540711000d03004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 771923839 1250 771922589 771922649
    0x51303020a0308040602040e10030209100b1801050c01020f070b13050d050309011b1d040b0d02010507021c24050403080103030e0319140c010f080412110604050601 72
    0x2001a4007030444000042c0c0314410706a0031512485002d410301c0d0b101c000c201030100b01121040d400c2440e80c2020410b5242c046003460300b0000d5858980724080c100b42110010b0f1260005024003190448040f2016910401c00c403404415090001c548498840d00e5480f100c1c3e0080c042603640e0000c107404511540103244010b501c0c035034060020f040701c410300c2201b5501c40d08000d100c1c140d107540c0c40d501c402040034551a5010b2900302d540d203805001000c02c81060302d401070740700c2c9503004900d024003900d001c0d00c0b50420590000e809003861505d440c030360f20019511981050560440d407070002c5a4404004601e420440594140c1e50b20640404400d140e0804031070003181c000d17000940502c01080802e02840344e820345204090141d41c1600701c8204460081c62110104989050b08055444000e980a008880c4c988401f46090005511030480040603045d01910240c0703408031100810312198068081aa88200141d0981e04d003454a800c000b600d9140901c1442d0003042c00a044a10040d4600469 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 771925089 1250 771923839 771923843
    0x70203070303051510020a06050a1a0607050f0a030f022a090703021e12090a02030d03020c0c130f05060a0f120f050a0b090c0603151917070302040513 66
    0x114140389058500b14003401010b00000c15000e40822480c50a4469039044496012a5002456041d6291030309404580008081e2010589080c9941d4141710f06905100c0c00b010049403030f26120070b01c40c10141d0030242e4010000d06c0d14498800b1402c10940c0210585010301d0554003078401012440f02440448a0780011101c20b09010308080c0102c1e18009520981255041c034006003444464040400031004101c4034801810300420301e20740d08243e4a07006070748071841d1805800c85000540c00f01e65a2004c1645007002c0c51b4002c21070000e5901c0400000356a000020902503641c680d2015074002450408580d01550b41030100141286c181031500004a032040c1c504002e045280624000c9000e880c5c40048912040c00e24106020413010061080d115004081e03074500d030b04100880c2031808441d001401e004107010701c10001c5242e01017506a04105c015140d40d0824982641720400f0000990014009081c0000d034030250312a0019080c0140c0740b003a0b408110313070740764070b80486040e030072030480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 771926339 1250 771925089 771925093
    0x1d04030f05090f06160b0a060302040629160206120a1401081902180a1407031119020f010501090501150215060d02060c01090807031b20030a060617150702 68
    0x3c4240030b07080c4200200062051060810070030740599561855240301680c2c0c400300d4036140d1030240b05610709481901d00400c0341040300a00c40c00141401b401411082c207020143c12000b03c3c407510304c4480d602103804901d5000744407940ea02401c0d41809080e240c243c0d0b068014501e04891504408466410503050324040d900070101241c00722030503c440c80e04000201e801100c1d080302c54501c41c40c1840c000d8000c801e100300c0461760085d2200a20381800c2d000b01903c08050500c45403001003520682141d80103c5800c005041c5034900d640264a003202c0d500240b603d0b980380c05d00006500c245640900d0503103090348501c01c0a485541d5080380c0d54240303244100307034032805440490b000307150100440c4e05852014010500303261000e0421030845415043c01d0302c0c8607800017900420541e1140101002c598008008154010b0035158116049070070000032861545104103101c1c969070800c4240c00c496401882480400d4030791000b51020f45288208034490303c601c1000400b042c150303414503031080c1e1190340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 771927589 1250 771926339 771926359
    0xc02060406051f090f05070215060409110d061a2215080a030c051e0303070e03030d0f2325050702040e061801020c070b0d061d04030f0509 61
    0x407108010400074044403460341840c8180301c00b82160300115070052100910003d021182000500e0a5610040c2031900310b4002920b0031624030840100303983c0010040e00c000400008624140c0304d108008001d245d803100900c1c00000802c001034100c1070105042c0f40f03142602000c1342c8140448031001e600e14006052309440511800d60180d0b000c164017200c0c0ba2001c070042030351054a541804040101a000246d60041420600004100d2041d1217030b403908243d07241c04400d0141e1038480c00090108000c020040c0350f6264590390400654441501616041000c040008040001002404040d020103946408104582d014907428280b0a090002801c03284034040000e40752030400d06c1300004140302c4140503110158450303110789018076980c88000c1c54141442a811201c80c81c00f249052090303801000a81c0050701e0100b12a0100d550070f140c4180c071031810510342400341c003440e0070600104003140b5031800b8060244c011a030080e4025110b50090104d0f00504a0303491141c01200e5070000c403949 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 771928839 1250 771927589 771927593
    0x20d21091401051608040b0406020609060c2706040f0905090105040b13170d0617012702011b030323100b0702061b01020301051315030314300a0c020604 67
    0x60f00078a003003081003e040303507450b07000d42e0f5104440e0040e4000001410b40807400380590380d010400150000805001014280f400010340c403c00c1c4107504202da519558440c00c05250003c04d1103248640c140101000c2c0c03100e0721450000d40524880c442d802d0b5040c03c000c0890344014061144ea80100d8000095480c00d54540544152101c40200203c92480060340406010f0b4440400380240d840d5600001c504289442102c1c8000900701c4050a00f9074580740045440d1240d80c5400000801c0d500e1410401d04003600050711111000c220036054484c4500e8080c04240c4d0507441241d0380704000015410302c400101c8880c1c40703010115003010140e02100000d1002100440140021510007080d1030300e05001266025889803281424020390ba402200510407403410720704058400003840020002c2d200100c2020100c1c016511010742030004a903941c0f031703074941c05a003114007d524440c00c08101c4150310f43d40228442c00140900e5000c40d00c00b012070300705c080d5805102c0e400110b5a008044640b40c036 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 771930089 1250 771928839 771928847
    0x2a030d1e0c0206031602120a02010c0f050c060f060604050604181404120815030a030804150207080306060c07030c03051510081b040204080f061605131401020703020d21091401 77
    0x710b00001c158800d451f090204d00b0540f000a000d4840694000b0600e140b00007006421030481034025002d00c072050000071070300580010310a500004020f5984419169600411403d1041d904200d400c444006402300303100da0300b940c0040540c03199200802140e0002c0001c1c1444510640b8010811850080110707a0700b80708680d21500212004d01c1c01c1d0040100800180c502600940300300d010803000800c010074400345201480100a44407420361810b030803075559400b070f0310005002910403030000c2200c44400d1070400100015540c08419600c0f40344d100d04000d03030307100329074280e00705001500c400241c1d0446c03101b0b1408049400c4980201005507190045010b4800380d0300c0041c0c3c000da07003480006000780c02003045031034041400e0b002e42581d003004189680300b0018402c6420901000700000c180307842d1001e00d0302c030441b103104840c404d41180c07590040381020091b42c8081d61014295260170140020120b98004110348074114589a0072075000aa0f051080d82c41101070860403504440b9040d402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 771931339 1250 771930089 771930121
    0xd09020402160f03171005041e0504140d0c03050f1c05070302090f0f0a21210e0d030509010c080f0301030303091b082a030d1e0c020603 60
    0x4024409420505002c07000092440e410308107031070303560010030354005040d08400480c4d503c0542c0444114149820500c90800700c400784039650242d1350340e00030704101010f102c001c140705060180c0c05010034105820400c9810f040d5041c110030601400941d42103140c00340250741d21072585a1200d5041410114210b149901700c106d1a04c401040c0c2000c81d00f080510b84142c1e40304030100d440048e154481078080c42404c4076140883c0740584034a20000c0b46d00d40e240c0c4510011502403488030301152940010f00c10305140c4a141c01840802003200317080310082145054541242641d941140710450507041000240b00c2d403c0203004100c0c208155219540b0600e18220014001c06860340352584100704000594826401500040d40c0e82681a0030414004060b20310314040600000b0601c3c03c00d0324507500c50603020720121030006100c05d6025858030401d00c861307280c1002401d562003151104d8015026101c4101012150714401551a00342c80c09154403d86864001d40880e00316503401d8850074503810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 771932589 1250 771931339 771931343
    0x3010320030c12010507092916060c031d1f1808030405060a06051503161e0c0b18190305091908190f0201081506130e060301060b0d09 59
    0x50801008020b8481540c444042c1c19000000580f61412181c01010444d0303d23017000d001000e001c4007443c4d48072845190412048040101e40d942c52465130300b18210301d424001d0090501c2d04103801004d5080c2c05502c25102c0b01d0240405c81000200755004e642c44840c4004143c0300e41c1203100031945851419844040c480c400e00302420209000ca481c1c0104a0b00308440859a543c040001c02c860700c583c1e4056040140400c0d5680b180e030743e0703908a000d14a03000040c180040e056180303541000c098443c50100d1410002001921541002e11400900139421980c0a0b501c42c4295004284c009005080000c83c1d81d002d0b0000d415034600108403203013000359801058003009401d210b071842c1036031070401005101070749040400c3c0c417a1524115078203155101c41c0028403030414a100401140c8102c401c0c00b2400d90900c3e08000c00e80c1c4280070403a0080310003070b0342078010300003051680e04040110301d0304003901c50b1082642e0065888000b05402e0721181d00860484000602c181d400e040f0041d0000306001e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 771933839 1250 771932589 771932593
    0x91504080405120102190306030218250c030e03032b0617070609120213020d0e1f32040507080321070c020f13090b0c04060908030301032003 62
    0x741e95400024020301035003a00b2001ca0b5400900c280440c8405003003400b91980e1030a01340610382c0395400144000c421414881c000003070314000030350b100006520056442071410844d140118429100400b100200d40c1c0c114042540018200c40500e0b0020546403840910350f50500441c0c0400301c100c009010068000c6032164850501107044000c00d42d880385501100350040c02d00a02e405801030421000e5442414440f00c0f40d0016405078440003003010303810505c0840580e4400900b0030340c0c2d00610451089030451b0060128200303c3c01703020249005006091042804883e03280c220b0800b820901d00303501c401104c1104100c448600180e07000c1a44640958295030099a60b42459415039100500c5920070300003400f0f00f591030a41300d04165410800b20b1400d0305d603441c02e40d4003003205a6403980c0310034814101000f0500841c03415811440441d80d200510b000c041c1811002c262140d0000d024501c00b18480c40c1c00403521410000c140e9040305e40000b101d11a21505c1c010601c00c0380e5030b080700c0395054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 771935089 1250 771933839 771933847
    0x6180a0b030a15151505030c0705030c12130f0b0304020904031704030e01030f020a020c1c0f080d050c1e0d0e06071701080c030a06020d1404050a0b010e09150408 71
    0x100300320b241440c1500e1240031000c071300100f00c6200c0b209504401c1d04081c0314816800c1d54010465445001d0329404224400c4a5984880a09006166000c0d801d0060543d21070b101203e411800400c0181c030b1601c0d00c2511b0303100740c02d80b19489150041c0311802004030220042c4002030152828110103a0464001d0601610300304244851001d5284112000e802198413a040e103140c9503854070030700c1c0c03002c0d0143c0d10440c2055028000251602c040c42c6031144610724010360f08240c946681c52541724250310018400d00c08007a880e012441da04840c800217400742ca8080092001811841141e0f485a4104190128102e00f8402d2003480e07003115490b03a600c5543d480080d440b400c0b00b044a10b0040807a03454009104007010f0708423303401310503004210141c1041881c61007546001550340400d680c030090150702e644100c000e00c0e00501d840c084001800c0d089009205c2030143c00b00d40c40c8511030240c85120382581e2981e626105008046c0ca00108903032003a0405a561a88a040650010701c920241e5141c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 771936339 1250 771935089 771935093
    0x11040c09050312191b1101020f030a020c0307050f03060a09081204031e0f09030305030411030610090f1107061a03060c0408070f030302120c010209030d03020d0506180a0b030a 77
    0x1810f0140b42d010151014009150104510070140304100500b0b50f2905d61400110040f44580b01c04290600a111a414002c2195560700034440c5424220500e800c5a03118404000000e5988024021140c06405001000f046078108060000ca8118010300180065216120741000520424a05489250040c08000d00020101d26010301a500903501ca4402d1426019070b450f180f62186041c4050042141405665682068003241100c0c0c05081082e00d81e562030500040c2101811980c541c140580010440a51080c403946425600e003d101084030410440c185411140e840311401d480c00c80c188409000030f103141d003140080c0e540c0c60f84409280c0c90800d0100789841000d445809291301c010806020102e42080150001c1000d40d04c113030101403039514080e40310102d141245040032000240e00074881001d404542c51480c0280845d0b540e0312180d08010020340003400300d040e00b44d081402090a92800b01c0401140310030008007040f160326280c20103001001c680002c81e80601941d125000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 771937589 1250 771936339 771936343
    0xb13110a0f27031506180c09080106030302032206300f020c0d0201020301051e011b0605010306140403020c130914030702040c0c031b0c091b120911040c090503 70
    0x501d02c040d00100c90350354118580510316215040020f0500da10b450700401460440c022000c4243c0f034944400916000c20308411560b800300d07904401a00e60900c0030000c10158000020a101c1c510760f4200410b043d0300c1031552052440c10300c42d85000404465008580b59101c010800000c01c440060b4510b00d000412000300355445132104030403c0d5404100590341c000c0501c210501b5040c0ca100843c07456050900064400d115043d4246440e501402d20340c00d0799004207104140103003c8a80074000c5110b070720308500503100c00d0100b194110700340604580b031001c2000d605030065500d6000761115802e07000511080e81100c00204c1c2c4840d48580055001c0741c00b07814035210204600300556a00d14040c0181310503035800d040c988040100d02c80c030800100c4d50107440e24206801c440b064107506841c0d0305081c4141e14281d00100c4003103240c64095149121140d02d0002c02c00c5407030b200e031500c800300d04254a044036007085001e003480054030b541100c149026403264141c0505420010b91107610b0300c000c24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 771938839 1250 771937589 771937637
    0x7120209060604170f010b0f01020601031103010905060412090905010e2410030608010c0c170f0d1b1818020903120703050705071a09061c020a030b13110a0f 69
    0x3a413a41101028400010080c000d02541c990103558040c802245000000d580d00300500c005403040000400d0400b09a07003e4100300541600481219150300701400d04076160400e40040b00d001c20441e090002d00d42c5103502809048900318049031400f0399600c03c0307c1040301756040000035801c0003658100700f90798482c00d80b03d00312003150b070b00092001e00f0003001d9400c403a000300421040c802007180348400111182c9103d503604060380d060319201e04e4000355810250056807c4051741c00d082003400500031140801036045800d0551310340c40c02003240680c02c0380350300c480d004030103414a01925095100400d40c005102d602000303402c40f584d0450000805905400c50b14044001400001c2d000050102c104090303805050032500351180c5500c1403060f0005031080c0301d06580580710129035046140c043d42002503c14076824800c3d96140f20b0000001c004000c0c4c1889a40705d0f841e40000304000000600c038500d1403a08003410341d46080790b04901079401d00301144006c0200441204840194030052a400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 771940089 1250 771938839 771938879
    0xb01110118022119080d02040909110d0506070c02010c020d0507151d01030e01140c19020f1b060403050745020310091415010207120209060604 63
    0x207411a03403852040248a0428848200c109800000003c0880c10b010821111118840d0701035203002e009840c00310460300451030480310071840400c00052144894214606081c802c50443c81c4510040d020409028110400030304540c0c41180000c010a0060030503185140c014102204c40018603400226802c0e0892011545900800300400c451005019200700c9010507017016040c07a01c1c030700001840910071031100c50400d6103e0007402c404070b80030351011030410080c3c0c214040503d089850b64113164001400c10000d48290140380d0110785c03000c20114681c0d00044090040720076038288035030100c000105019031001081000000084c010440c180c000d0a802c100c203600702190420b02e046131110007801c104025441400e44240e08909500c0c108c0c40340308130340010303100c0d2290800c40700001d0158000307002d0700307161050350101c20070700c2c0f88258400d21080403028000088540120f0b00d40e02941303e96804c07240c4201541d0014645044015801315020300440e0801d6035034159004480034000c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 771941339 1250 771940089 771940121
    0xa0807050a1a010821040801020d061406040501050306060702010908030c010509150402030a03180909030210050601090e010b0a03150905070e0618010302030411060304080a0314040b0a0b011101 85
    0x80034082007a540b00390581c0411001d540c619940c074015156440300b9100e60310310400b0880045580801000a0a9034044d00ca014021512080800c5400d401402c4500402c9540500d0f8143c60132186071500442d42511410303560b042c115103e450038000d1a03040614200d05101442c540402c100f24108040e0220516540c004242c2d0706114007a035041c8070501290034510301d815420080582c43c001080c1030340340e40c14034050148142e070304403036480701000390850300f030342c904009520301407660009400f40a142040c0c5c04008944a140056541075920310844144000410042211035005805010b6190544c00c0c04541c001a01c92072204421058001701841a9168140302040307510403582000d2100c1611500e142982034440e07418101c0a91554504040d0000009810003080b5541d0b940d105e0400f5081c5a200d042c00c6c078184245410001e0000000b916164440c170ba10b10455400c00e000305c0d040a0440e1643c1c44540100001d420344003100c074140161240b5800a074042445200c544991800c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 771942446 1107 771941339 771941353
    0x30504030e060c153607051e15030403020c0306040201120e07050d030f02120406050f03070512040b240f220203070c03030e190809030a080705 63
    0xd800e031201455800c18801412800081e50b0118100c0002e01c104141d41417090401042d1891061940c1d0fa004020030841c60030f01030020104403092510180c44211060f0100f16060010070800314039440020801c0145a4107200c4900850001c802030103042c101900001c000a01d0307000354442c80d5a65901c0c098001c0d00800a510041602500161949443e800c000d01124105103c0001501904803440800400c04045805562290322882e003014008000585290030007025082484401c0081d11045c08004074128071942c803444140ca41460080808050b80c0c4e114405020402200280142d0315542c4070078081a0b81400e41c0c0002d400030713240e80f0142240d1002205600c420b40300006000c42258000c030303528030441c040d40781440100100002541c0d1820004a003a0240140c80c0b05000003c1d0550000c12005100504841403100701c0c0d203990600d070348000c000300c59070360041fa = true := by decide +kernel

theorem cover : BRFrame.Cov 771762589 771942446 := by
  have h0 := BRFrame.cov_init 771762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 771762589 ≤ n) (h2 : n < 771942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
