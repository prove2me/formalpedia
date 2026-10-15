-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4521
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:53:10.620141+00:00
-- url     : https://prove2.me/submissions/f0736298-5053-4319-9678-a8b2b8e9214d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 812949640 ≤ n < 813129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 812950890 1250 812949640 812949653
    0x3040b0708090a06110d0e060105010314190c030b100215011d0f07170103080720060711210307050111132c070513062a02150417060c07 60
    0x120480134011075190461014180e4260040b50344e0710340100003c1055211000030789850784024070500303000c246800101d4500b003c0d9170309414440c60b4400d4004080d40d0780071b42d11704001c01d560b00065042650303c61020965441c2d248032160001e6982e00101014003040b010041d443d44141c001c1c40148480c000c640300015500c0088a0300f00c00f0b070f200d411a6980d9000380407034552005100702c8420070381000000040c002403000800101e0f00415a0448003440c20408100c6100514680381d0800b07401c01118000c50400302c51800c41c450020007541030710b0480d41c46c080351084902e441658607000007c000040110034440c28030643d036028030640c144045d1020540100c2040c4c0308010310619025180c034504044980480b0107500000c00609550808641c000e2407a0002003559070150a9000701065180c02075483c00c2c4040c400b100740b4202803410784007410741c0181e0444101d800800c220031100f5021100c0000d4005001c0175048484403403030808060b498510050406040b100c020010080070034070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 812952140 1250 812950890 812950903
    0x90a0b010c0f080c030f0d060501030b010903060f0b040f0c030f151503090b0c221a0f04171c030902090402010305041515080f060c070209040c091103040b070809 71
    0xc00c40c0c0408620b0005082c268404c0c815a50900191700000034504a403a12243c05440c2d000460802001080d45400043d41210301070412103020a091080c00c00005420790030401c2d100707020883c0441c1c40ca001001060940b1000f50014642d592038071100f6440c241e041c802c059074500800000e1107000b0301107010803200741e42c2d80101c90204080710441008140a41c0100300f4032030b40729514500c103141c4802c0d1884107420000c61844025104015a8030004480180c00c060b00c0c0039030150301200b01c208070301545035805007d42c44031401050000003940c0d90001c1410b01d0070800700c0051f050000150402e91010451a0b0a01082c0f51038080d416000d0b0700c54600c0260300503820300b030000365520f40341407408101046100c14030b0a1428080202091520b000b502002c45540788103c48280140c2c1d80350342c0c0c80301000c8801c1c1180c200c00384824000741c944181960380050107029020015a1150540c00aa4203130004c034401d0300d20000103010400000d030240543c402854070b40140710b42012a01c00c1e44070617 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 812953390 1250 812952140 812952143
    0x10e0f0a09090201020f061e0a050411041e0905010204050913080403020d0c03022701090e12130806040c03051e0303063a0b0601020c130f06180506090a0b010c 70
    0x39550380c070b94400c41e4000c01c4250300c10080501150781c0c62421403403038508540d40c10710043c12038000760049140300e00c00d4010a4001e0b9400306180c1035441280f000d2000070710202e03003003004003089140d005850f01c0244c440d00c3c6e0707920700400000d641c85d410a424403262002c09811208511003644500012038001010b8400341da1f4102d54643c6a800c640c102650507031242d401c065440348061300301e051011020300c3d101c82100c8403242444082da81c0c8402110072690b009a642c001608502d040c143c0c03500003c2c0c028061040310f6072803000e03038603103c030245d078030b0214200c400700e60214105c10140103120080081c4030503c1c0700c002401c0c0b40c0183c100ca0b11070700c90001030281405003013003540ca100f01d90303074403480003a0348000380e9186815413410042109002c407a5480a484120600c40418000d510115500320312410141c542d00c4414000340d4071f078000b06000141c400c0702c2c43da1140040745060002c00240b1642552000208a50820808200d0419409085031842503c0c2402400c002d982080d40001c105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 812954640 1250 812953390 812953409
    0x90905070c080712091d0a051f03021c08030106091a0a05040302011b1515120302071a16080406031802011409272e09020a0c061a010e0f0a 61
    0x404e02c2550641e61001c49400c001401030700c6400381e0708012829000031b4414600d01c04184125117418aa40d6420507050004400c17008c650744091015090041108d00305408d030410031013908079103489100554000ba0803040015a240d03108008840d454041d502d20800c0c240141403078803203040000740107031041e448000d042c04519601d0194407401c1000c44008140c1001000c0074010105c00e0880c010548099080841c03c0101c4011883c8c0c4075010b803824030381e68190010500c40c4e00b491000000c8103030100d0200320b41c0070104441d01c84603120800740716a052290060744c0d02e0300c0c105030010b425941e041c4171610681401c03a69000150382e0140390001c0342821b2030042c070790320101400401c504001c21041121481c0c0f41030b119050902c60b5940c1c071031050060300c02090802c0965090085d0410700f9030302c0088400d00950003405100800c0d4010b203440782a50500348111807059503814181c0e001d40d02c0c0c0d4844103c0c20b40080072503580003405500409011600910440d01d00f40c009100c9031004d01806122 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 812955890 1250 812954640 812954663
    0x2060c1b0a0506100f120503071b0f0807090c02060906070e0d050316050c0a081b043308030a0504120203120d150b0703021c020319090905070c0807 65
    0x128284010000a82c0010907502c00d440c01601418540c00203103d00c5000c1100c000f00000d891070a03e00c101720456111001d13510300111a180c1d038001d94803590b111902100e00040005070380e44003003030f1000100b111801401c8442e1400903003c085402030140c880035504a02d0411000c1071000c2a0564080b1481c00e01050504891b0301107580c46010000040c000d2000042c0800100082c000701c0800c00d1180b001c844503c5100028450540d240d4843c5445030761120002e070380b0345074400100200260f4003410000c0e1407480f40d8400300d04801c0700d01503000080044114102c805100c0800507010341400c0005620380381d12341c0b80051441c81144207481070016801d2503042155401e100c0000f120040c0b00035152034112140d101c50003070a43c240b18241c1c104030303810300049900b604015100f105030103402620210000c0c06004040700c0c0307103040100440c0000c0000102d180c01c44c030603a02c041d0856a030344001c000d0505458004507100506000180042803402100048041c01103813151a40103255100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 812957140 1250 812955890 812955937
    0x150c07180207020907120f020f0403020a06030c020a08090f09010e060a0608090c0103112b0c09050f10021f0b010201050609010e041704120b090d0c0b01051c0b01060908070602060c 79
    0xe0a10b0701d5101907c0c0d000082d02c000c902e15401c082e0003924005c480b400819a40d564098007110000c004940150b01b0030b080802c0814031400150445a0000e80701050707841c0980d0009150900036044140075101c0d0b80240700b800c0c00c00040d1034014040b01d08000702d42c0d04080104070360b40d0020000c9681095156041d54800a80c0c00054a1020050403003261701d0300c007032103121031003840e0708a40302d044107140000701d04807688102900f004845014080102c90100c00b814044001c02441e007000035403107181c03050401c1110359103006961042d40d0b4400a85a4551030009080d500f02800f454031a002c90320051011203180095160800c0c1e000904032026504660b01c0c04a60095038401c84041010902c020b05004010100c1841000038009480031041c4e0b042d01508d504c2400100a0403010943e001441a4102112110350580c5d14805210682145603141600603800360815000502d80410401c2134000403c036000c090710040c00038145c3d17850400d8800e18103010b15401d00405001d641480c00303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 812958390 1250 812957140 812957177
    0x1d091504020706181406060a03061a09181b13020307021608030a09120c0302100504050d08090f060705060a05070e0301050f011703040f0e06150c07180207020907 71
    0x3000c441e4443c0080c4041041c100403e0300e9200e072080169000305000c07040072450b69001c11280d1040310010801a1000c0c19901c44000611a003401c880561014070300c216560b50b14070a207a40301d8500c00d0801d800c0b80040c84421810075a2010310308000c8801d01ca01c04200da60340a1441d210b040c040e000058696445200492600c0060748c0c80c200700382c1000e01d0208440c0408030041080051036102ca40d1080d540381c83c82c0340c40514015000c1d040980100040c80140340035854008402c155103001130400e0780322800205080800d1008503100c46001a00451504040030b00000c1d40504440c624105881504c0f010740b10200244500d0000340d0364000148058000d003001e0420000142c02000f0919280144001000e028090402c0243c621b040c02c0120040000843d8140d8019420b1410307001d10b032655150060a010340f441e6806001c07200c0540318000b0600c0a001e40d400c4120007800861310703101303c201100001001d003000c039500410000005d45c440040f0355400607010300d80400040300058042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 812959640 1250 812958390 812958397
    0x4020c0c0603090127050606011e080702011104080a0213050415090203010207080d1d120714032b0b0d020a170109290c0307080f090106030c030b04031d09150402 71
    0x8a0014501c5d0f00011181c4860400c3c094501d4402c0b8211103150b21076800554440456001c0d803684411440060001c0611541000c0d030440d46500020403404900044504250880e41044101d9400040810107524185110032002c9803101340070007160070b003600e40c080c0c841444680100800c0e00c0f0741031002152000d6048407074494001d208261281d100d0f52101c009800140c2011000700f0480c0b912034001c0030b0100c4c50b1265418040745a40c44d041d4a03580c1c0314107841e486811042180001d2110304440c50b031951802c0210000721f15924074030064050341c2801c45c2d000700d035070700e001c0c1a9540d0300d14010380f00c0e803440d4070580e04560032221642c030442030384e40c3c00352000c000001c200c3c0c20f02034541007804861269148dc0d0307a0b8000880d1070544e6501000305d0450004441c450700195021020541c00781e1001411601303c0c416200102d41d198581d11000403191240d401140e540f50484200018141e201e20003120050068520045002081000030f01150f40900210032210040c186801c2946e50342d8102c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 812960890 1250 812959640 812959661
    0x30604170d090b01090e010e030318120c0d120b180a0b040603060516080c12041506030809090a0e0703020910030609050a0b06100912170313020f04020c0c06030901 72
    0xb803208001610702400b8001e000e01c80c016a0604060420101e580180614203d02008800460841d580d00341d8420303c000032241180310303d01861507010f40c1000c01600600031554800c004100b039800402000b00104210411040c1680c0390851100b51640c8e4500292100d91030780c0320104640e103551886000800807022404e03070041c41c01c0381c00401c1041c140c200f070388540b0600701d280f841051192001d54000d407084032141c0c903134002084008900c48088007202d80007400f44030308101d90300d43c47c80b03840201d030020b0b0400c0d42d0724180441c5c122128500002c9043c0c0c0b04803e5042403100034210942c02c0d540d8030a5001c001c1c0704409450008001c10500c5240c2d10046800006c01c0c0812607640c00e04a41707a49c15200203540420000c2e00003282400c040e998202010002d50310142c040703281402c40f48a2001110080380d0350310408801100750500034000d5070040e02e503d5000c0c030b40400e4600c10490440810041580110700511115070b03550781c0032074410400c0405440180d43d80d41d41040960042580105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 812962140 1250 812960890 812960917
    0x50f16061d120f060c120109050406111605011503021e0f0d1a15090a0c03021315090509011809050f030703180b0f07080c0c030f0d02150603060417 65
    0x2680e4020080005900f0756601c0c44009560f005d484141c550031880c4100c1d010307540030a1000c0d00410004800f0760146600a02980340005c1031511081d041c440c0c3d62044404108103420400c42d2001d1020a01c2000e41c205c809203003251541c0d00d5580820400d00729100807118100d401c19045030b8a88400b450900c55010041032a1080301e414036201e101d80d03007030b462490700945510000500c624040d01540480803001807900e44565241c83c0450060701d04515000c0c1019000e02100b2240f00348a407504000c0d24a00389401400001f505c4024100141984040d10aa0140c3e00405c0700f501c590801807840111504041101119418984d1404580c811250720a1000003241d1090503449000000074a070381440c02d0100c0c580c3c079040c201d114024880380340105081000001d00041c451001040c0d0b000414090701c148269440c0007130b061848990741c0b40030a4100218400302d00d039041c40001d00d20418401444803605107400440d0786e41c00300400082c10051074007507407810b28202034181d030311505c022103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 812963390 1250 812962140 812962159
    0x2808060a060f14150c0a08120103061b08070e06130b03011707140f0f0307081b011b02090612010c030c0323070813020913050f16061d 59
    0xc82006111a00c541d101c40c11a04501003a0740340ca80f0951003012030010203040180600715440310003030b07104e204003c2c01d5102da11040c03000074007800090310340c0d00d1003001005030640c9541400c4042d29403441c084c04c08510a28410b180d003035001600301e034110b00b640c5401d0040180010107c2c1e114441c05140b01071000d014070000808054500055040e40c211151a420310803494014564620300b0f4040d451020441c10405c81c0b080c140034002c02030600009010621069144000c6810075420781c0180945420a002c0ba549410410b0030082c0b08a42c02e00c0c103070312026041c6903420045014400020b00c1801c15a01040e001e07900c0c0d0040c1c49809499a0080040c45d2200d03102900514150307446c00082400d114400c5040c3c290b5100f029426007000e03084c9070203980c0314101242c181c81c0c0280704c60304207100440d9aa025032900f450701441140050140009003119040262a109000074042c6d4541e10214a12540f600011101c02c219181810300a50300a900e107005e070401d842010006802010340c3e0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 812964640 1250 812963390 812963401
    0xf04050a0903030c142512021501060c020d0206090312031003150903020d030902030304120503070b0c090a1a09040504030e0108010b0c0c01050d060e0403180b0702280806 75
    0xaa001c00c81c00c40c8251001c01c00f481c0d10550665540d80300c0404082c018000340014000180203c0e2018002c25126005120444465481e0a81256040d0a0200507808100359102840c24541014090984c509080450b645a60300040b211040090f000f0f0042c0008a4200d829441c1004450760039680c819005403649401c001a0f00000b6030340c80f00755987c1a00ea802c24440381000e100d1a02d0440d01640034240404c400241034020f07009050040380c040c030080100285541ea070064590010344a08003031070740d0b0440c2d4100117981d464090400c0c40120810010700a00303039100540c42e4100e82c201304020070044810340700246517001c0c041c4e503d5009804d0404110802d0351081d401454007000343c07150010740c1d885030800d440c907000c0d00c001480154410004481c2942c05400a081104101c2d0f0022074415102d08049441e04c10a440440204460441031382243c0558140e5001034078100c0d84090600c0311030b800050118030900a6410311309101d0301001e100504020113080540b11030001c692403414074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 812965890 1250 812964640 812964661
    0x806010302090604120c12150f151412031306080105041b1b0c03141605030d2d09080f0d020c130e0706120e12040b0f040801060b13090213090b0f0405 66
    0x10100b00415585001c2720581e4182851140d98484c0010303c14140040f8107000e2040e144240001e036040d031003810030709404061a000c200402d4080d074102c080d54081490102c01030078060060300034034411070400d004000707040c0c601e0905001c484172a00d000400c130301605508102e00c0d035029501801328581d000010040c8402440c85540c42241034048454107040c81103480c2250b50f1602074180e0580011961041d00c034418200b0310141441c1001280c285207a010301071402c1c58019504802094071b1420400503c0c0c1e0034006902c4054140002d008a054a0341c0029200c01c00100342d584034100e092502c01c442e03842a030180708240d554a045070401a180d01c40a01503903640c9404030341490074001d21980441011542d145c154110401150a20b802d01090224541010404100e084010b020004001c1c2c000d000d2200202030100c100c60f50f8041d2880c404400c880207070805e440c11401000601d0b0b55a010048241c00c89039000000100c00000400140000d0000304001e64058186003d00c03219203a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 812967140 1250 812965890 812965913
    0x5031b070308061302031014130f0b0f060403082704021206120a1a0705121006090b030f182d010c110616030902060309030a0806010302090604120c12 66
    0x74101c0742e1510900980710410117904c0308640107282c40080a100704039044502200c00a02c040040c140000d11840810310000c44040d480c00940d0030751101c10070741d2103040c10888451003410684086150a045841d400218070510001180c00a0f08042410040509000c2a094007500502c199a10001550b000410780c00aa0342d10348148aa10751180e64800000f400a54180d40080506e218400940300c15600300b100030008400d00c03004000c0b00f01c41654481c0c40600c25100b00d07045454843c281314005200c08003c2d00b2544a5070010020300c03401d40d00e114120b550010302218581c1c02464021303031590a10391820441d074403059242640d0a480c030700d1800034080c601030440003002803101c180c00844954410301c980b4641c541140b40459002070a61034007000c0341450307050105005d040c690100e6070a500884240d4403a40005c01d8003640380750b2000f90f050b04240c1c246015801c01c0070a0b800100144598851010010b030304a45060420251301191001400410340200e043c60407410094180c94 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 812968390 1250 812967140 812967151
    0xb03032107210e0d030c0e010c0f061104030b060f090105090604200c0c030102210a150605091f0f120b030307030306051305100902030601050903010510051009050303030705031b070308 81
    0x1c2d43c9040c00304d94881d2048a5a4a1403561229021080800190784162072550165018a80e5005000115000b4000e50200e01d01000140341e032945141403512100c800982107611440086054040315980c010210381907807000c64020902c0d0311503000140007041c0425042842900400e4845071410407030f0043e04c0000782c0d1805a61021f001311042500300d1040850741e40e00f190103c81c1ca0340351459540c5042c0d42c004100400090702d407500c2c02c4d006d03140504551200700001c40004071a00f00d0b040010700011400e1524400300700d070711100c50002d04140c105040c41410450104242903500406411242c02c071107001d07041d04c0e40e43c030881c100207020304510b020701406540c041d441c0948078000d9209051154404002c01d05000c1e007040358010195101410450402c5424000181aa5820b100316802240700c08000101c1c14540760a1001c501c1c140b1104100703000d4480010840c40d10044201c039032140309840c1141d0790f996104441701031915900e141c03038242c12001c10500100b5030841c2d0340171b0194 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 812969640 1250 812968390 812968393
    0x50702030a0b06120102040806010e100b0f070201090b2a0312040b0405071505090f040f0203150f010f0c0807060608030c030a02010501140d060527070302040b03032107210e 76
    0x1130401140c12400c2c0d1080b4400c1403003551049004102903401d070032807107800050015901c40d40720703654007202c2820b400c00005041c8426001451707008641e0804603107002401001c40703003401c11075480061214603030b541c200d0000035240000d1405900c0c50600880300c0c40c580102c440d007960309107428039140004c03040b070b0100d400307100d0b030f0601140045010380003600c00041641c070fa52074150a0000d100d00100040f68290b041912800044d85541c0c0b0b50010b1445011460050540e0500c0d4104000c070104011119605209a80300d400c0b04041c1e100070030000315030f044410213a0303c505618006001b485140e1140c4d40300d000c0895031180a0b10084000d00d18511680c3c000d200304d9803600340c03944c4100510444194071050400040d80041c40c1904203d074086c10395501c007c0c036508000c03041030404168481448075030300400400d104610b014407802e60308010540056041c8208040d41004280003104132149094103040060034441c810f940204071640644d00e40781010f454600e074a4041c00c11f111049205 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 812970890 1250 812969640 812969659
    0x120c021c23011b0e030106091802040b061c2304050a0c0f05010905010c060b030601061101060f0605070f051011030115173c041703010b071101050702030a0b06 70
    0x7208014060108215602c0b034112058010060080e0740a0380c0d0300c220507805548a00700098400340510418a900c880e00c0008440000603104000071580c0f6000f8043c4520014803e0704898031181c04400c2d845604104001821800d00c83c40c144040a5040c415070185c81101c204806c109010413907092051064901002454960b00e1146072070140740951070008200c107200b0801c40d8442c891600c01640030308000101d002803507003c02c0c10004260410700128101c0704110301008000d01c03500d001061518a40b05500341808401811031003271005c058000a00024900c050103424049407110311100038082000d00310030810714525400902c0303544500700408428885841c01050f00780390f2140e699101c050141d40d00f08211516600d992030b03149e9003014000112580080300b4100d2012410032101003102403400d4034104640c88980b0040030090b400610041210000400503070b1440c42d441440318158480d42030040365503004142020394184100c0941505111601123000c0c000c0c0020b8400c101c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 812972140 1250 812970890 812970953
    0x90b1f08060f060d140a0c15080f0411010210090f0204050f27070302120319050c030406030b040908130f060c1505060a030c030303021201060c120c021c 67
    0x2103a2208503484042d40700c50000041c0d0a192428400881d030748113040b15501074aa107822140f0700880500c00b00c81c2c0300c1c201d0400b030102a0511030607803181e00c03a601e0500303e40e2914682c000141100500014050a00c0740300ca0100780c4e00a1299181c0f03100054410008026107040030101e100840400740c0c081c515110100b81c0b0443c07a60311071440780345078150300b903210111920211441481c84103811500c3c006d850021006940b0156101841c201c002e00a50300c80304110390502511031003107070000c10700400300700c000a00c10000c002c2c0c80407a00f843c1400070f220a040742c01b09002e080d00420040c03046000264481c0a201107400c00000c1e42d50015444030003030b8550000b5203040c00c0c06135000c0d05600c0c1203821560840303103981103c0d82c0310402901c540320507aa20781d02c100302000c154100700c2c0400d402281c1c1d84e2030213422881081c0103015900d0915506402e5403a18000d08021407140400c00040d00c1120056440e81c03c0d049186400c02c9007441c604480c02c0c00c007940c0c1d0307000035040350615a01d005114071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 812973390 1250 812972140 812972143
    0x1a15010302041518080307030e180f01060c05030f0313030206070f05040e0604060510080106030e151602070f151202070206090d150c17060d03090513090b1f08 70
    0xa00f40c60301406142d0000c041d50b4415102c19600d4104103c5641800001148858062001c0c0004a10a484170352800503200708122005160381581c94045038040104145c0c142d46d0710f0541c1c111885070520a400d1041418030f40d040d4031500100c90302c900720010511813018001e134010319906000790709403200da85480004035440c00740103907100b00290040c4010300c02c4040340300745c403038202000a200081329070ba101d021a9045094508880104001c0001089442e41500550329171500460140400f03929811003040d038148041c00310140c8002e40655205014003c004c5507028140c0c8004048040d030740c41410001408820a00074002811007540e00342d40300850090740c40e036560043c0300c941050040c50034013503074500c1d45009841d242001c0410202c00450791064840c0c51000d642c070740c603410203104403190002c4c0c0d010307040c2c074050462400c900e07011079885074440003a60340488105407185041a03844028141800300034082f406d110060144080c0c084481200142c1c0841c00000c41e5990f0f100300d03a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 812974640 1250 812973390 812973397
    0x601030c0312141b1006030c081509151305060a0c020f01050606090919050a0c031404020108390a0327020904020a09140106080603070f030f020105071a15010302 71
    0x202c8408030140a01d1031900c48401854130242d04104c00c8403180b481c0186610260b078095030090382c880790182d00c280072100040c8410840c0d825900c21300c4a12782890440c465403102284c01102102d4007680111300500514101003c600c0d402c403049592034280314880700000c01144e14260f0144c8135561a000142006000e002c0c80b841c0000c18440c100904c2c2d80034000f0794000180380e1080b40300030611040d400b443c0e500c2241c1c003a1004010000b082015940083d003168090014144400041b20801c00180e0740104102c2d840076100400c0a1064011042c102c94090540117910840003540c0c103403070940780d02d00041c000260160781c0c203111500214191403000d18040d11324014036044403103070b5000b5040030350300f0030380051010340004505a99103200208a170210ba0702d00c1d1030411078000401c242039010300c0b250307001402140544000362601d075135100b01c81d01d0740c8002406180380e1074462085d03a0141e8280c03030046170800c4c4124180f221170300c99001c0380c44003100d0340f45244200380350114036544070b8800c0c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 812975890 1250 812974640 812974667
    0xc0c0302040f0b0637122a0e040b040501051c05242212030c021006080d0215090d0c0501020d0504030216150806211002040e1f03021306080601030c0312 67
    0x203800009030700c92451000f03010687c0200034145c0f149503c4080c05442a0304800d0070f104a540c6004211998404000c192801d0321191485542410010f0040d40c2e0703031b204800640100c034028225003001c5881d000e810300c907884945881e20080c1003048012014012620751140d0924203209c0419074801d04080340f036642401015040740d10b011950400e150007540441400790b00380c012120310002844642e0300360380594101014542000b03080820036901081400b00e07030004451158046c0ca071424a0300d0395010301c100c09104000448150f017051000039070403a124103210701c0c41401a8900360401950340d00780440c0c0c200206c9030494000034002e0070340c00c072100384141e0381c1d0755091a5101d6000700800401d000c4000084120001c0403031904050411807100030324980c04026031030b585041c110254040c4d000b8000030301c900c220b0803145a15a141469842030740e5040f290003030f180b800c0350f5110004200c00c6c3c205000c1482a94008018403255059036000c491081c00b1070132803c80400030417544180e4480c40c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 812977140 1250 812975890 812975897
    0x61203020a030c14030a09030b1602030a0f090308071a010801050603061816080106050102070501261305191101050901140a0c1703160c0c0302040f0b0637 68
    0x3114001a200c3e5a982c400d05024866049614500b04240c07815176000443c120701140342c0c1d4004004002c0e582a00e56400020741c00c0f43e8076012178496020b901da10603081c08104100c180c5d415080100d00403400c4038003858003c05415210002d903e403820301100b4000c40348181903000400060301000501406101c3ca50240c0980303600d03202c580d00c100c5d1348a44003c40c50154055143e50042c048000c0d0040c100900c444000414500d06c0e20002a007011815004113041000d600404003440315050001408480c1841210855544d641000480d01d1144580200300d40200c00811910141c0001101120360080c50502c004400340c0c001501c1c103210385a0a41e02255280120703c4c3c01c8260701025140040e440c0c1000c3c0104100c9503038241103050345100c100003c8002005104100c03260201d030844801181c11301c046e006c0e04545034913003010303203a10000b41f08035182d8801d13042e04021600103e030040c4020300f2040d00c030448003a5030500001d842002c1d07000d400711202c15066040c080484249010b0f5541c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 812978390 1250 812977140 812977153
    0x6060d0812072a060605011715030f032101090b03060f07122405030f060114061e090111010c140c07030c03120206010f0e071d0a0b090406120302 64
    0x452450091030003840300090140701da143c0f001842500c0000c5640e585a400ea140da052414548441201c5464000c0f904210038518031004c00c1c107115901e039800100e200c0c143c9007600c840c3c000203894950750442c1560701d4000810481112000c08420000c5203c1803c0251016a02da014200c1200c03800c2030290b0349580181c0c08901005481e0040766084003c6180107009621110000401c3d189600d541001c0901d21540054080006000900181000b24040c3c4021a022000155903242c1805001c4405c41245608641d81c1e032a0303000c85001180c016040d0840d07082c4018a500d4070341282038040c2c041340740a05003400d455010720a0f0704031030f002c9456401c00e00d108025035a413150003117006440c00c0d109191010001c51108001d100085104004100c80c920081074000d04154060b032008400e40030100c0c00740240c54800101c01d900c0141403138200810b034201070b118880f0800304411950000300000300800c003100a28000e00f4103000545042c48980d40c1d4600c04440815500c002400603003000b07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 812979640 1250 812978390 812978407
    0x30b040207021005211603050f060328050d08220b070302070804090603061b030c020a0f0201051306110d08010b0d1806060e0f090a02090c0a0201020409020f07030206060d08 76
    0x1000500450003c20400918407014130b5001d00015400f07a1342d500300705541d06c0d080c2941a60500806034800b9000011030524105040401c2d6a03510405a500030700c80002c0c0d80c420814040b821030003001d03410200721841e03215103a402134a04032003a10f080c442c00c06045161601c2c84100803625003100c3e44070840c0300b0166614103086000307400c00881140e80304001c201c00030740b684840c0101d1000d14052000050800769100c4003000700b06400100360241824480080ea40c07580200b82e08100d15001880802045030510048400d0321411408007402900b040300864801c1e4009140656500c007501200c000701f0f01d0b1441502c100c1400d1040051b6510300f0044544d500d10307240c01c600d86400f42c2c0c80c0e150350055106e50700c42d0140c640300d80107051200a04000c00851460700340c0349503004070500d000b40480244030780114903103900c001c0c0500344003070000a07010340c01c0c1d2003541100d00034194010119110030070b8038000403499224901c03d80c01481040301195092601c21044103216510cc208907140c40c014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 812980890 1250 812979640 812979647
    0x604150c0e030a060501050108010f0e0103060b0f04021219020f0318030c0d0503040b0f060f010f1803030c0b0a02090901140604210b090102090d020405041704060f030b0402070210 79
    0x844810400c214008000d50758988080100d1205140b00c0c0402045640c10200010219403050f440107010102d100b000300100c01c0e0000c80c260640f41c00002c04503881c1c0168000c1005250500841c640080c80003070080c0c0d00e0482c000403180603149081e032103404008034210180a07400740b1250080b00c21410008241014100d220300300c11032001009507803d103d000680c0c00e0a21610040240210f180001007004101810100310303400302c0ea200b040040303402c040f00410380c17000b00d4110682c1070280c000c3c0040180d90080040c5c691003400c040da140f002d19103c0c03400910075006400116800601480499224151802950301810303015140c545035038030707002461134102d00515905410410402c00420011000790300900d6030340b070b132044a0044501034a00401c00d0b1000402203804c6901c103001029a5541c4c6034848490160120340108090700e0b14201401c1105050002c00614640080c0005006800810700403811000c0d4070100308003c082d03410f001c03c3e40b2074060001c1d40503103c0c401d0081540d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 812982140 1250 812980890 812980901
    0x40621050124050f120102030c030f0a09080306090415020307020c090f2509180506180402010906051c060909050d030c08010b1c0603080c070801021c092a03060509060415 75
    0x3080c90003c5c00e0a014000d08981c0181c070307040c0c80c40c2000001c004661b40180b148030b401404109080110351702075203d0309810700000e4580c0b4403c401c4080850140019031600b01520356024100719640e051828002c0d42e00c050030403205009034a101c0009045407507a050951140d122240115410b01c801c16001c50310a1242c0c004800348501010b010541c0080402c200090f145400701c0082c50342828000c02c4001c403124400703449a074a1100421005036800b01808040b14018140107440b0060000b151901d41c0003a01d184000c2c03840d010000034210400d401ca039400c940507405079a00d081190400b10151400c51389154041240b240c0100403859442e0001c1082c21440000c81040c40c003031400079070503034905070300c02d850b62000490300044c000f00a01500008250b040021403401c030101c500d459007a15030344402c0b660700b07540c0c00010703081c42801c0480c2a009500c107411942c0c039108001d141c02102c4c00d603000544601f0b07e080d00150921100203030b4070740100e0b00301002c405554500701882c0041e24 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 812983390 1250 812982140 812982169
    0x90c1602062203020a05101d150c0c090c0c1506130e1f0c0c08090d0510061a030106021b01090f0803040e06101d04062105012405 57
    0x1810070002490a07100004014600c03581c00c45100403e1850042203071a0b003283c2c05c82485000c5030403e443c00241c02c60f40240202040ca0f0303000c1da000300c0d00e00000303500000e4004d09402980340064a200c01607030200300c002100c030341220442c0241d10b0344c800306c428038090703520702003c3ca6100f01001380659407040a110342c440002084003258021030300d8038000ba50311110b012115984000300c08600c01c84000c54400055100c060108100042c014000f4000c1250181c0a402082d00160340c02d919140e0b1152892444c1d0448100c3e40106a0041c0f80303401819035102d05581c85900001108482c42040111b03412103101c2e81c0205440b0101122052009006c03168070350510100c00380000e8901d008104a0009243c0c16018540b00c62918001001c4048014002c0c0c1c840c0e1086503411701e0f4140c0058507203001c121030405801c014a00d00010500611041c8c124030004034130980c0341201d0340030070448040e290388160024042082891b01815154440c882508591018400240b00d503090032040b000810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 812984640 1250 812983390 812983399
    0x9050d0c081608030a1a030c331801030203100611070306050115120603021804140307060608010b031614060d0f060303171b0c1f0501080c090c1602 65
    0x88018070b201581d00640034800c581c011004010030000841c10b1040d51031101d0f0485400042ca03440320002074580754400c1c4130600c920b82d98800007800c00d8000e1140c141d540b181d48184450610204a184041c0e0031000303006041c60354100c14450194840d000b82c900403800108612880c6007480400c0e9905a4900c0340c2c54250f1044400010100350395000d154002d040ca20442d00b0040d4242c40e0051075450140001c0740541e041440400050f00da1800d688101d000050908070389490350300d030641481d440414505924030020440c01c0c00e220651b8004401c50361240000c00510003843c0a25880b40124a00320a6106007903100f0800780051902c940350340313030000300f034549031a007490b42e400100d40c50741503141216a41d500003070040541207840d441504640340e81c411682e103411009449200480b2594a280500c00302d04810303c481c1c200036078a812110790503507c040c9108074403940c0042c602485010f0392442a88680f00d05420040780090089581015141c54002907140180c1e0900e40d05400320f810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 812985890 1250 812984640 812984647
    0xa0606050f0706140c09010e04020909011e0306060806010f06020d0207030204020f07022107060c050d260406140a1802310507020d0e1c14070b0309010c0309050d0c08 73
    0x142442141520700c107002c2d61171619107421a00c0001010100110850741c0500d104001418195491543e80e90460340101c0a070030303c940300b00b6280260030b41203901c018141c40c01c040001c60454404595203058940002414410540e42d4030120307982e031101021200036070023030041400942840d40003031101e402d801c11440c1c5051059804119855038507202d4090525440d078140d003525109015050052241d4038101c8888511611625110110b4000e19000e2080315001880340c05006503440004100384c10319a18189898280507000d00f05480448440049141c00601a140740d80300703061400b100d0341c41e81c80310b0390441c0d42440081d03147d4a814000d502c01310406034001c804006d0b2054844408168040384a08141c080a0f10308180700c0c4100e400d2000201c0c120701d8a881e0300000c02580300000505038858903003801c0c0030702e40e80d41c00c00d41c01d200b81c001c0c0000420b025141030015170281c2c1400000f0001800d034410110704850182400400a410040440b04290b1007514480e8040c0d02a40d20a440d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 812987140 1250 812985890 812985911
    0x60d0b1f060c0204060e1b090a0b180a08160e090102040b070c0905060603040f02040b041b02010608160302090403051b01060611210a200609060105090a0606050f0706 73
    0x340d890541c460000204548160000c44c01d00e405444024200100000344905181d101811500512129100086008601c0e0401130b07996402d010f00809007000d4803540e4060441d51042601030542c04540212204240010411400152900d4211680600c0000300341401c580102d1a10060000340d040c0d07400740400725a01140030000d020f118442c800c0d801c400d500d0800c01805807200280725500c00c680c18020403002c80d03c00c81d1441d103e1541158005011091800003e004100019950007004421600901d840760150701200654013040101c60b10b00326840912200110b2901009401c40c2d811000300340068042c002034502c40314805060300701d504140384194215202940802e0009001948025244200748000c1800d001d20540c41003511107003544503122071140402100c20002103d80000c48082042c82d11022501c442055403140e0a01c40300300d5680d50020b0182a100e50354903404541c0c40040d45c41100121042512280c0c03d20b501030108400c941c202c03207425920642ca8069681 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 812988390 1250 812987140 812987191
    0x90408091e0901120240050f0711030c0105010308030118020403120503040f080d020d050109020702030d1d0a080313120f06050c0f030901060602010f060308040311040e070b0a021005060d0b 83
    0x2c55406d0a205504040c18150b03050790a8080501252119146000f06004c50841d0100c1c13001c4c1c0c40311a508052a841a010382c0d5541340d0300ca140c82030b0352503501c1d200004c0104420340006604803607001c6c120100e01c680200420049204d0ba00c00180f840c1d8001e0311040c01c0c035015502035940039024107030005452066441d04401903104460304007a43da030005101d54044210b201c2c150242403800300450800c0204d5011035039402a601a21042c031554001c018850003030700c030100d03c0f0104084d142c0c481c095591a5490345c3c2e80c10103441c8254406142c0c102150041c070b40d41440714056044507800307402541640301d002c000c020241010941e0035007004100480d12150700114001c043c040c0001510b145080780007821901c1c1846007150031401c2c01ca0800101c0c00d00000c0e0f4003a41e030007401c0c0c061003240b00c00028000b405c50f9140c1500e240180000000c80d405054003501085003031f03400340c440b2000304823060b10031036404031050369210806c18405404142d19219203588250502d0005241110140021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 812989640 1250 812988390 812988439
    0x6200a020a0602030c0d0e0325050a06030f0c020c09010b1c050403020607080108060c0d0e010b040c09090c030203130609060f0e0d170708010b0d0902090408091e09011202 75
    0x984d00004880fa24154100801c14107030b0310510b40b8411400c154030009844150320201003104880044d0702005904416075051300900d0018401c0030130603034402c80540038050600c84205064030709200e803c43d1500100d0107141d2800020700707285142c3e09014030481c10b5044031640c130040f608009107004810b207403481080d0003140650001d108615220307000400390701c0c0c140c0000341316800100c1804012038500d001c1e50048282d40b0004510070343c00c0c0040038014a1140242e59009003800507103180190000890803e40d0000311003032000780d0241c10107500ba480b041e51203005091640303040d1008514035034403045400344030b807202092800000e500041540c184020020301e0f5045014900d0050f50002010740c80c801e04150480c0c081d18100d1400340001c0c80503c0342000c0000002020541d001036071b444079500c194018080b2925003050f05010b01a07801c04060a401014a01c0751940701070702081c11010340da42c00412982ba10ba080902c41c00e47c1c220701007000c9802200410450314540e441803440d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 812990890 1250 812989640 812989649
    0x9060203100e06031f0c030b09072102160f1b09051005030c06040302040506010521060a0b09151605101a09010e0c0913020a0906031506200a020a 64
    0x11803a454202810100e0342200a08107500c01e601149908500b00900c0020b10342038191450000780e03010000da0294054011205078550002c0b1000820040d52f030002c0e40ea94060340d400343c80030351800419050354100e01c140d445048002c5ca0002e00d800000e216400701001d5144100b00d007122400c0c01a02c45501580f031500311444403034840e001c100d035140d803800d48480140f0b4110f0003061b10541100c0400d100344124000a80181d07112800640c02e0390281c03044400c509040182c12107241c900809114005109940c5148034210380300000070f80f07000c1e9906462541c0d02c001e00480440d001d094078242d45900961170110409404001900424014014400300b1081140d01094072a8284081422800c0c2683c0750303072007001c1800041c030041c8409145181d100c54407103c2c56654441e1440060005254681c100442600020f03183d0300203a8802200390880302c0c00e450620140b130b10344641c08a00e0185002e00c2c0005580240c844855a850340d84a0310100424015618480344980200341040c5041c0c10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 812992140 1250 812990890 812990911
    0xb071e11030607030c0903061815020a17061320042d0b1905272d0f0a150f08160c150f1802042702010f0309060203 51
    0x103000350103041c1804815800031003460204411422000d01800782400c0d80006421281c0d1080d45e000c01419001c00ca00f01039810805404008010000e864041c0d4050386110000030801301d004070f21030018140941c000da4000b8000c0c800120138031204002403401d0100f0b8048101c0e1900c0645103501c4040082024021500645000242011000303014078801c00d0300545040d00c04804020710301b44002504e54284040441100c40180c10104607201d00450703242030380c02d0f004110f82d410002d40d041341801e00d5a000fa1a0740b88413403056013264600c540066060082c050384140f9185032450010080505c00720002c01042c5e42c65103c0303070b04903c401405a03003000400c2c00c05c4419007c0a801c01d60141c0d00c040003005007481112940300c02048800f8946e03008002007504440c158141a003904083c98054a900b010480451816030617401c84503a800203134052031030458a500703100e45c0071820485010200380072411514072030f4011101ea4440c0b840400c201a40d4601c2d42c00000c1ca18001140580140e00317 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 812993390 1250 812992140 812992163
    0x2106030111210112030906051303060f0e0105060d0519050718060503121602060306012102031906031707031403010905010924060e040e0a14010c02070f0b071e 70
    0x242c586404807010b801000c0e510143e01d1500c40025400304000c400c0c0d038040d285c410703110a908402d01008120315000200302c031b400c020080c03c0d0914154840c500b240c00d68030003032240fa00da4400340040c030b018000b80908190085120141c0e010340c4048611940c9200e07100700d5600550b100d000680c1410900703424500c0340d13242c9000f017090780b50810190051000c0c0241070742c503001880403203080c0c0c6140307440000d0041c0008000035840368000d24460f000070f07244182c441e8135441c290400800950041701c03c032081c1c016900da60a038900c0607100d624140c0303901a90f94a05030046846140c001d1b003000b00c007102002203600544156035201c4010b5030003020210000300b001e504180d4400f0540d0101220789004180000402e05071007c0d06080c00700f02c503007905000034071078040c801140151607041704821a911491408038100010005210500b0410800801c25007c0c2508101d0f00e4040034071804005401c0c0003814804c44111030003c0041620840780c2c1d000005800e22045c02c001e21207101607904243d40c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 812994640 1250 812993390 812993437
    0xc0e191b14030907030b0612030a020703060c090e0a0209040e030a0f09091b11070503032106090907150314090c0a060e010c080d0207051609112106030111 68
    0x142440d40ca156609100038118540f0001c840c1e075442c49444090f11010b190004030700d080c2c64040302000403142c0131003030baa40d40103003103c06542c0e40640d110484840d46080940f464480c45541e8040540340302d003000c0100e07516003c00c07a1029400800c407195005585825020310481c0c200010080c11516131645d503905900410302400c03020040e4888580700e810038031869407100303031000d000314180114113042d480c040400303c45914110b4030760083d07505803200040d02d103860094440c02850b0354480c0c03003043c0d603680c0e240d01c00d0240030402550400070583c00910140280d5081c1c1005162400b41450006524100100d2481004c0d2044d6000400c03500000101985400d10590b62006048541801206020030a000900c0d080250b00702802000c404141c1e40d40102c41e0f40c0403103c88036001002c0341c0c01107011002402119805200c0c0304d1606d440d0202074454291000c09442c42403481d0807541000d060040c0400c404218020043e6034903540c0c50340003c1c81c0010520103044400310030043c502000d09075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 812995890 1250 812994640 812994647
    0xa0b070507090c051303021e03030a030209040f090c05100e10080a2f0d0912020319090305030306010e0d0f0501051905040b06010c170301060216120c0e191b 69
    0x4240401404010910144411758582022030b41c0c15078a010111001114841904030001d41255150200042d04001e055044c1c010302003501040f50700304003021051212908690620a0040ca240d40354075040080d86030401036212000443d09184900d10a06000100000703035107641d05011584000074814220766034418272000c2100a41c0c802d031010f054050107400c0d01c1c42100b54580c014070001d101c05000b055030304100f40342c41d480f41c510607100102d0344000c2c1d26a0020740242661120703207001c45040e584a0002c02044903000740c0910b2854035540c004540713007185c82e2241500807114240010004900000308043d19000700f000103501e007401c250a04482080b8004071a407030b42480148408640c168541a4002009003040c040034291460103451000f0705007100d00c0c0c1c140d40880001545da4011903003148a4a0050010036425107070012141e9004844c8405031216240303150500c4031300802003c44d80c0140661600701160390b5a811071905481c0311240c4c032030661b1407840d009018980c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 812997140 1250 812995890 812995901
    0x22080406170c070c0302060c030f07060603031106070504090504140a030f11120d09020406030c0803070606060908060a2a030b031504030c3203031b04051309020a0b07050709 76
    0x110200b20629000c0107071501c003400415070201a105690014150a8407502041100d00c1c0920f14031919407180100d08100006000b64801034022861000c110302600401007a0a13100d00407580751242094145203085004180c020821600490507800400c1c800504005402c0c60610a40d070381d10702c901c9201001011190100c100f90840d40c011803803c00003011500c00e940194101110005a9444600003e40070b05100e900140c110100c800c0080340c0103501000070004180213200c14400720b84e8a0358121807050b41c5100c3e0f14079682224010681c0c272071541e0040700da034100404039003200920320341d01d00403417100d15a081c5002c2981d40c41c0c1f041c0c407824280705140c2052981300088a952405403800381c2010041c032002004c0c80c246201501003da200060117180001c031503010040c610700c09200d1542d07503006a0310450030222140704200c250008004031400d07580c0c0540120101d00d0145420383c064840c001d030491703100442090100b06084001d016195030341c0500002c0c050b0305c0c58804003200b1910b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 812998390 1250 812997140 812997151
    0xc0108160513090c0e0a0f061b170d110915090a1505040f0f05060f0313050a11011101090c0b0a020c06072301052202031f0e071d2208040617 62
    0x392402c1c410001803000307281c680122140390034850f20340c83c20f880801488000710320707008062b800810852082c3e240120080c1443c01001c2c001000300302c1c03035410b944002e0b003e00b11040d1f901441111407000e04009141c00392034a0f81019040111035612841c81028810200c0a00d0b80052801301d0304005820024801c0402441c244680c8440301d0306250215881e4410400403035140c59000001c500360f0035402031060801a0071000f622102e003540e140003c491481c0d00e03c40390002d001d07007106d034044010611900318016405114102e90520303080b040d41c03168201c0d04c0040254011a55514100d840d4030000b00021417103401c40345001500e1001040100501080192490b8540000c01c50f4450a0340000d910344500300c0f000001440652000911b002c0356110241c042c150240c0d0195040707a903603040451070425031400d55245540f10030981201401c2800300d01e40c4425081d000c564401e100c486182401800300964114811045c0c07180a031a501c140e01c90000600c20104030350307018560790f40054000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 812999640 1250 812998390 812998399
    0x411130e030405040903110a05150901020c060708270c011121070c0b0d05060418050312040f080a02070f090507020d030b210106090e0c0108160513090c0e 68
    0x11034080341015624000c500803c1c0c0115541c170303405003d0500810004c0c1085041004a50b503030100341c0f924540f202001d42c510710b4000140ca0102d11400010f009071a0408150001030141c3c0c3e41e45182140e102d040600000c40030003019021481a0076165060300900c0c04004c001e01e4900401000186611042d42040c0000d400110f03443c2d50300035500e1080c03194001c00086071500ea49060501c1c9410b40f0450b07100c0b60a102c0c00180501a510194001c0c0303110320402c81e008c02041700c10040047d00b80b8101c5800402a8200b0440c0185010200320210340181c010044696021025031324001c665002400307540259210020401c84288030b901d046011345042d10381440a41070501020756280c001c801d8802c149500d4241c0710600e91102070300c10001c003070310304554503d400c1901c2c019070080c40c0034014004090304103406800c00c07690005040c100c3c910180e49252455580c1280d8000c1001510507040401801b084100c21855120440f031015260410b0005122061104041e040c0709103840400d00a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 813000890 1250 812999640 812999651
    0xe0f120d050711030f07060c02040f180606090219031509024006052113020f060f0f030a0b04140601020d2f070305010603050c010f0306120212030c06041113 69
    0x440e98041b850104807030741d5062005000310144002800f400d41420951080c41c5080d886448104180075001c0c0b105018030420800940c40d4060303601a4814400e08914400346c440400b0f003c240f10398010408141e00a800c0403283d0b88506026003a0b038407008051b14000150414903042c000d65400611000612a00c1c10004280004540040f51418441d543c180f140100719059888803c000400401c0d07031301185001285044400c518030783d070403004103a0041004080c0080d450424004031401100300700800c604151800300481e6240d48010310305090039444180310b0b000c503102c500038101150041000880300340341090009241c104000d0001d000c01080c02c2c0301224144107450680c4a407424144440c4210501c006071600e40704242c0c0c0014a95841c000b800014010b02140800d83c04070700341e9916100d0a00d070103048050725000c2c000c500401008070072100062038050f00801d101004041543e0034040701c0b0080c01d0800c9021117098078076054005c201000340c030300180c41440007400f01004210 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 813002140 1250 813000890 813000913
    0x3310f0504020703030b040e0f010c2c030f030f090405131a100503030403060f0c02060108150402042a020106090c0207090507170709080105160e0f120d05071103 71
    0x101028500c140c038016580016036009152281d0460132032410040e0041c0b0070b4100101d2285d6851240c2c0c0c0c0f080e1038035460603181d01e80552056481c1500762203030311b481464003482440440050300070685e60b95031501c9a205a0240c000050000e0641001c60103030032a00c40c071213201071205441e4028000c4422290381c50280b800228a29600206000007180c15803460b46c44d98503d0245400c1900100ea05108c003007000070070031030036410204046030b018100744802c41440e10103071394540080c0112400c40c1c120b240508a040003042020340c1c0540000c00c00b140e00104040c24440038000d014005c1100100745d8050718900b9024060303000144140031081001d5421079030029140c00309401106201500d50740070801035031161078030440f1014030380b91040c440e040000c006401e07800b0511401119500b0a00000d00030031030300064400740700c0c5640740c3c0a88494641e0411048001152001d544040034244070354a5050401980360b110315241c603220794840c01e031304012490240b00100741d4481d0b40b140c2e00180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 813003390 1250 813002140 813002159
    0xa050613060819111302030a060f0312120f0504060c03060e15120f01180b090d050d020d0f0f091109011401110a0b040308181b100306080331 62
    0x988070442011a1180d60356a140c0b86041d044c40c040142d901148040c909503440c5404c0d40118040c030b1143c9001c00515940e0410308407a04c0c00d601c00034013252400d2010150860094003420440c1140c4000003072038030805540001100c109132010380b8026a50044d0160040e010b02c14000076183c010070614051a10341e08002d0141e1180d4800c2e401005200c1021410442c04c110b50824819104020b0040d14050a090b400d2401c6c10302d02a82e9102100b00171481003000071650584824456070340514000d18050108007a502c81c0c42c030382100c50350700d4060b8140c0450f40d1044240c5c0c00444900407600c580e8030b081100c1001c1008130500e1191800030010030000d64038040d1800c0461003800d0000384000e180c5d482c1d1b0306110741c80b84050038006080c6c04110400d039020300315501c0b030502c0410311180340085200d100c5c2da4003210404407282c5445054008a2071810341c29094185e0104d1902180440d1501001c03800d64218070b60740c000703450035a06c52024881036020410940304c0d40d4114080541d150000c0300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 813004640 1250 813003390 813003403
    0x40e0f0c090409020f040204090b0a0b07050c0607020d0218090106090b0d0f08070807080304020108010b03040506010e1005150421080a0e06070803091c020714060a170a0506130608 79
    0x744107a5981c00c000013191510448810b000c90010011504e0310380e5041f100c3c0242c0080f48400e48102c191250103d95605400251226250000c004040d0030010905001c0076902490050f0f034040b44800348100160349004050b07801c903c100002d460a070038000c00341400d40e40d42d40c202101913410002900641d8544510400d40903411401118444055003490303121445000400740110038001207200600c081c070401540111300c01c6ea690044d40e80e803100c0c902c00300d010596004103590003074001008040e070311141a981002d07a8034002016565100000348018850007054401c1060205040010602c030305651191003820900107901c3c501551b80c3d40515200e85003015091101e80c000c49001901c0351801d41b1441548201c0680e901d08019000c10b54074140e40e404481904998a0324428251012070b11134201c0b00c043d017030030108500d2941084040d800c00380c0350104000e80d038042e204809040081d440d00070000f01c0c00020702800c0c442c040c02800a0030340d00321354820381044810040da62002491 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 813005890 1250 813004640 813004657
    0xc0507080706150b040e010603020703051b01060503101508030306090f151003050a0606031806052509080715050a0e01110607031409010509060105010f0c05060705040e0f0c 76
    0x4955580e40d407031a00d1401480307040d4200c00c0c402d2403000086020013101000303000341c40f00b0f0310340d50426a9071000210240d110700398000700003d82c00d201d40e400c2002546044003d00030982c0002c5102d070780b603001091411411040001e0302946641d2045d1407040005698400340ca08100650b1452a042011a480000c00b0b00802912018800080e031a180c01000507061501c00501c5038910661804000303021302401d48948a400b440c0040004045001c0d00c00d403862141d06a0026508502d180c075007600a100003002c0c004c0b0f809003000c0c80ca44103442ca401d401020003072903c034203d600d41070084036890110590013030f1490405603e07074607a0a80d04101a40c030b000c6503514010300d402c40804012560b4484401000005100c7c40341488505905500b081c90391861078500c0e110941c0e00c010f6a242030315001da44507003080e040603005000075445404208030603d4981001144c1d1016075880a1620b40111041c0000483c00b09060040c0403204004a811100d044000200d505100c810042c480c4035500a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 813007140 1250 813005890 813005903
    0x30a081902070b0a0305090c0a083408150f06030304230d051e031204021903170d390c0b0f09010e030f0d051003020d050f100c0507 58
    0x10310412a403081001401034910503008548035008400090090001070380d2607141c6025480300982c681c1004e46110381111180c00062440c0c41000700070001c0c42003510840c240072400441410601300b48015480000c0240d60011715507240020a11030716000f01400f01c41c034010a000c00c0c00950b41c0c00200750303002da030309441d0b240207403d1400000364244100c0da8802500410300c4003d00d4180000412041c401410340e0214011141d0f5640641d6141e204400829104c01c100001107000760a0142c0914a640c4d1000400d0b82c0950b102e441d01c5889050f6410005050040001d5182c0200140c0c055104050510f4a403481c580d4080c5c03100315200e50000742000c02131040500c2c8000e2180c82850403901c01900004002c1d0503003480d10101603030140c12a0203c00139030a1811800d00c007540002242c62a0000e20903890500303003c0c1c0c1002c40034160107131101c840803220f101c011000d0781d104440c0c41c02892060f0300511444d444200c4050070035092166540620789040c0c0301701e2401ea006011501481e91214 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 813008390 1250 813007140 813007177
    0x20313090b040623030c06042304021605030306011419080a0f090c05030c03062703091201090606080d05070803040f050d0203030405060c03060f06090d0204050c0409050105030a08 79
    0x340850002c0030780350300459541c071044e545000126040c4600303d000070750942c01d4a02c0c42e80c0c50002d20442d44642d22609004038000644030001202c21402c5451441d401040985010300c0591406100382c402d031801d0361290800420320282e0741c3c002c1d4144004c0803556503014109912001c03000305503200426544180030001e0005801d04407982e03c03a111a0b070300c0020400c4441040c2c1840c0d4525509401580d010b8820521607007558a030018038640300d402d0701e008800c20050190000d800b58000ca031030905243c441404a42c0b0190740703076041da41c80b1001d001c0002070724007203074100002510003550000320250003000c00055419441401c0315406d641007007550340e4a8559103401074100c040c090010700f603801032021080340190b012008500071400b820485801e170300d0352440b8403100c3c401a42d41e40c0d403080340c0da24112002c3c00c0034800f610314440020310040c48101c0c81d40200d03040e9001159440c8080c08005030602824540d13100d040d000d044140c0040024916640d00c072401803040743d20300c6032400d5411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 813009640 1250 813008390 813008411
    0x61e080c241326070506280c080d020d2004060c03090e0c0a14090901031103010e01050a020a200307060b060415020307020a060f080c0c0f1b1002031309 67
    0x1d4420b03005041c55031490003861410303840540442900403140c80e0501502c040024180780c01020b0ba003c821000c0c0e180310603148481e240c6802e03210b160501c4d03000e00441000034004180c004001e040e003030714050301c05695505025044402c54800c0d0180c1000c9408400840215119410a4805481040c10031540c80002400c0507074030348500303510107040568030070104807040034414080d1500303582c2031b207520202a18000301c408081c0182800b81e5002040354004101041c0030405140a4540c0500002210840402407a003075074001c5550301c031529000a110740c940c59022609554000c51414016400d03444220201d45a20500c40043e01d2a17444091001c000d42c5c5501c00c680040441001030140c00560f030324069100d801600081c0e219445d601c400084640c060810103161010560b2007511540e280e80b8074880c10341041441310700d58800c030700c05a48001c108110340d14040c426035207111110005001080103420b9020707070310f81c00c6420902402c080714460444d41c0042d590300007808550407180c0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 813010890 1250 813009640 813009667
    0xd1b17030c061f09060f030210110a1101030912020114090109030e040b010203090306090a06050c0903032704110423010903030e01020a02090c1207140904050406061e080c24 76
    0x244c0100c040603140100001e04026103442a104480c801d0382c90b90252800e0030815212040322030f60740a400c0c1c01a110301c10004040c00c021007030b0b01c0c8c0e0504000a0741c03a03150b151301d007583c09400c5004d00941e5482c0d5240044500003a03209a0004210000b4030096090340e0b401401c2140c40720405000d15281c84540b030303160b0b00070320a5035084007005d0202c40702403034102c850f5a0ba808100000b56034041c0b810012420f029012422603440940c003400861810f51700141e081c0340c4c43d900401e40045802d001042e00c481e0746d60760040c0001e04200d01d0420f07840b64140008114050b0003041c080000418000f02040a030760014052800c907501030410441d070107603441c01070781002c0b0030040083d40030b46000c0c104102506000040c142103481205400c680c0e41c0c81c0a425581c1002c010b00f810706010050244030024500740d0030056100d8031685000c5205a5030701d04d04c001d226555518100c0c0d034481000301b80a554000c0094205034030080301d10f0b80409010080d40c45e07448802c0441040c22000c0014144042c1c0d51 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 813012140 1250 813010890 813010951
    0x190b100503030324030d050f030604140c09090c0301080d080c1e030103120c0b010909061d0604050f01050609010b03041b0b19090e0a0b0d1b17030c06 66
    0xc0a01901d075070740f40580d40d102c2c0e6040200040750400202440c11040d505000401003050191901c80c5e92524a2a1010820030742005212561058540794000d0455400d015840d0041030300b18441600c1d80b800c4002c000b60405d000b04480400d2800f0300c01000000400241d01c040c0051a041a261b46d45071640c03201d20a11030010140355220898000c900c044481034000c50480380512040c007000050800111600c0503a054003038000d015a00044c880480c09a0261007050320418000411241040c060040900c0200300f00340e1542000042006210062088080d402111002005036240a41c002081c0040602900300c0b4000080006030401c0b40c820080d00212109018540200f5503032a9241001e61046900700c415285148602e502180108120800d96041c2449200e00d40d0364188140d006180650a03030380d100302e60702000350100762203d04500c100c040c2e400702c6411050401c003582c2c8143e000f8100d4180268010001d4040030320010070495000101d0800c0307489440c3d00484c0005450341d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 813013390 1250 813012140 813012149
    0x150918180604030c0c0902030702101a091003020411120a020706060e151e030307080d110412050607050301060e1009051804120915030207020607061e0e190b10 70
    0x10030781050000b0700d5040000e00e80daa912680c1102019500d421844081e4002030381c241015034080324060344451001e802041b40b8034405845840c0480340500010b51f80c1c282500d03490450b2030b0011003802541000e008a2034400e06074103403e494000c800e40c4218110b0340080240440641c0072600401300a4560860380040c00707180320a40c1c06080c10f00748006080c03143c4c42150b100b544a400c2820020345042c0940042da01c6c01005142455400e0301ea00e00e20380d200c403000d03150b2150755440105030040800e010b00043c090102c402480314000f03103040c41c5400c0300508032009212040c4010421591311040074a80d200042e0f6003a4070700305050006507001c081c1a080940d00220303012440700d04e2080070180ca48034034040c0d4036500200c083c9000907180c891890168642c4400314150740b044941c0070350014000d4038800b4262a141c80020b44440c000c4806c1e002d198203008041d0700a50341c40d22580c0c00b4110b0554030741c2c0d010f820545030000301002301c20a10040102142c401c0400140e5031480d036400c600040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 813014640 1250 813013390 813013393
    0x120c040302091602010c020607091403010f020415091a1b0a050304060c111903020d2d0605070f091a16030203041a070222090204140615091818 63
    0x5081411442c3c1482c84400c000c44010f61030301502c801007510018001e030240c102500d907502d032141000c0301614060814182035806640b41c407030740c2c100caa41c07034801800200001110031180c002c40580c028519442c90780152040d5404046041a05503954100d50485025551504080ba080791005041540b201e0014041c1c2c080410000f820541041e80b80c0301c1544162000c100c02c040d00f10800c404070441d010300b0281d5040101050005007070451134900001d000d4488004800b8000b017192545840c81680b079034ac80c1e421070141c401046040d02489800c03c2e82c40c100407441010a8030000c0c40c107041c9100d040382d6613410181e9200c900900d034044440f100c840d5243d8043c03240b541c0c00c2c0a50703241c2c0700b407082c810401e481244a0f101016800141d40300207034010450410b052100301040104030b68180c051101c0d981c0e8202080c01603503139100e080b000801208402d0107901e0150100041d80428200310100d0010400c184146591465110141046e05070000046070315816184106881d100110b008070b0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 813015890 1250 813014640 813014659
    0x91b040e100f060515041703070f0c0f08010b0904260301030f02030618030f070c0b0d050718030201020c0904111509131a010c11060d05011a0c03120c040302 69
    0xa0042903040704150b80340e449002e0066690712401e100c40d111000b01507080c09542800280803400481c40ca103d02c9000d500104ca051185640381d11001400d17080007103444960140e070800c5201505080701c00148000c1c402000180440008076001e404001e10050000482d1650401420103c200300e24400c0c41c454512612903031649170242c401c0e00c0b0003070f06a03c07e1281e140010f10030510290b80c41182038810000c2d40c10580d8003003036120190440c1030225100a08850301141814030303100944440c00c0d4101c0c01007805c1c200711001070b02000074003069010003079080c0418000b40c0d0700000e0403001000292014406683c5504040c260501c042d010f050b40b02111448c50100b5014800280803085012a0038403200390b8044521001c44100c25100c80358100708141c151200d40c010b104003005207000d01013042000c1400d00010380950b202d41060022580d450b00144502c2c0000e4030b806103101e0599008515206e008245595207005041c2101000103007500003401d205150301c1517074011540940000d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 813017140 1250 813015890 813015913
    0x8150a090c0804060f020a022a040e0a020f010f020d20010606051902071d0414011112011508012303010f0c030b040501032312070c150206091b040e 65
    0x2002d4401d903003d484507400c1c000c0c40009000c5500c05c44049040c2c58001705896004082c850302c1c503003903004c01c40d141e40c110f0042d001d01d0b50b02da5010781099450044041e040d0100e15204002c5c0920100b8941810019070004182040e5000070728001c0c1900c15007004170039044141031220b2418040b00302040a07500b040030000d420394000003c0c000a0364039944e59040c001a6400481e6200003521409036182054450440c0030765446074020780103401200080c11041220640034203444190903841d50640000413011003c0c0788148000380507003644e05113007120058000000b0907030101070080b24425042d0322072442214a0141c0704620320f10000d0002e0180c0c10074000054000d05540c1c200340c0120703040c803074a1174291800d0711815042e29400079070200c26259202e403020140d00912f41822182c07045441d42d651810407040036240803403150110041e6113040c4030100c083c100f41c0c0359940c01594001c40c2407100b20040410b12a144880000c1c1c801e44c1d00310003a0004024180c5410146541d004102500d42c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 813018390 1250 813017140 813017147
    0x402070f0b160216060f020f010501032001052113171903021309020a200a050717061303120f06090c050703090513150b0301080613020108150a090c 65
    0x184989100b607000c0104080625007640c81e2241240c002804c0c0c19425000d1148038002c01606174810f07810303c100c4078100c00101c030032800c50ba0300707030400e55002500807283c141c14890300c002005021000c0c60128140484c240c51150300743c003048903104450780002c0000e00c8028020440003c49600300c030810190416503081b1645030f51041414131692410b00e4010207845029008491a242103002d0b240c0650380f400303082400a410060041e0100940000c2c0e24919401c1d0a07040803c016042d00544894640340c681186040c610360b0104418850100803010102008216079038005510044951007e42c240380c12504040c8420655003454900f01080440e6803031680003d041d85d0a8220400690101d9402640c0b1801152030041c00910300ca8014001401e0841108045203c6600c010507c4004404801c812031a141c01c072806400e404001000b0603841000866048904421401424001900020704103131000344003002503000f21b0018403498076407030110740013490004420000c811503144001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 813019640 1250 813018390 813018413
    0x140c030a06020a1805060904050a0e030a0306050a05040b150a02070312080402040614030a1707170309062a18190f0e090c1c080301030c1d041205090402070f 69
    0x540010318004c2c0a58132104000c4901043c0e680080172107040820400401000d80380050030364030084c0e21044c90251041c0e042019107001e4207a600e01041c000c2c180000e1200c0c0700c8a9510441c070035410959092226220304940300070414008232690b80d02c440304141a40b400c0d030300360300090206050340440c10080d544000c41701c5c0243c2c402c8500f031000d1039603403003541e40725040d50016686c103800c0204008005580744039081803608480040c241840850345801e0a4550b4141219204200000070015003100500c52980e00c1200019000d02c0702c04001c03400000740115510280545000241420042d0042900642207103070091540c00d40c41c22480f80c0c010021030340d204010341283c1055010131104d8658500340d02c41c54290009200e4444440708100c503401d03100303182d04120b40482d10000e002c180300d01e0085000c0e43c040c025020b241850045000c079040055000302e100c80000c101400005140041aa41f41c01428544036440c0c01081c3c2c00100203107c0c40c40014254400d501c80d00d0200101002c61 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 813020890 1250 813019640 813019657
    0x103200904031205130203031801173139031506051e01180305010c08060f01020102070f0b06040f09050607110607140d02071e1101020304050a03140c030a0602 70
    0x4e02058403015a0b48a83d0038003100c009501da00709000c40404000311501010030400145840b0106415201d41c1200341c03801500c4c03010746200c180c2e03d1050000802d40b100000000a1420340390304101545440901c400b180441800707154213075401c86164a000030a1782511800f400f45060015902c1c60310002401d090030342c040ca907c2c145070b0300207402c2c40c1400d01c003441c00321483c01111503429608011240c0c01962240e482d03144402c81d10101c04117409205503c190102c9880d00320041c1007280400c1810090900c000b030445e0f00420046001444000d014800903034482690001500e91000080107005040d842501ea44d11f0300d44d030345003070060000d0050700425058036200428050068410344425086072400041681c0e41801884242010001d01480100d07050060400c0c0351982e41400070b00d054000058003034400c02e4080700744003001c2e401036404042400190f02d49860300740843c0a10119120142c000d158000d6a103c4a44042c0000b100c500c4006050320302507050b5103400002504000e50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 813022140 1250 813020890 813020927
    0xb130b0f1905060901020f0a06060f15120c050c19020907030203091207110d06050601020f070f05060c03041a0a08060f06070b090705040c0e190b03010320090403 71
    0x200d6900c5801c00d040040386081c440812006801e0502c01442419881300e00a5411032003002c94000200d0340c240801000180b0800010541c2480c140c444a94a10340c2c0d0015401161030f2410f000510340c01044503071150450b2200821074016424080c2d405000e180d40d01e01440c0100441c5581c0707408a0900d140b001842240c03a180217031a20341c07045049000840c1d13a080258003125400c489485108013078a40c40303100d106c45806c1080440b0220341040589070741182c1054031031003801174030b40e0184540f80d030140142008050845c5010a00714210710944280c0e4000c0000103507021410307006000b100d01030610003c1c1c40700c1c004034020002e072155001030b43e800c0000c2d0490700850700034540306603140c040c0310300240b00c14100b1007962a0040c02035030107014842144a01e400c0040c050700d903801500d00c0082c89450b00880355054009020b20a0540c1c545059410f810400034001e0524140540341501d8000a0300d08050740b60040816007410902c0c5d642d17074072082d920204030400d0380c00290180d00b41d070600c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 813023390 1250 813022140 813022159
    0x60c02010c051216170f0a11010603080f0403050f060f18070e010b0a02070807060504150c02030706020705040c0203190f02070e01090c1707090e0a0605090108060f1807180b130b 78
    0x14000701103000d00d0a284203406c100f00031a81c0d906100d2400121200c160000001e007207a941d43d104803036648468200d1407a1b10000c1001c109011081c028052500c6000000e41001c0c98103641c00389040100509034007444401040c2500c4040d000c008280180140040000540d43c4807400451503403c0b00300d81c40010311600d540860344030000301d1010b084070119210941483d04188240422003c1e0000020401041c13081401c00341c2c5e020401e40000385403640150984501b07001c1130100f5102104404001d55001700f000c80b00c00000d078007158000c2c0605107404188e081d80d0100490800b50b0079407002c0e0540d1245400410a4580d60340410007001d03458941c020120400c9026001c0071108841140c04221125400c116219030340040d2580100105000290a43c6400009070518000c1e042071496503c038a0400c445046080050b542100c2c8804070000314a80d034500c1140e03540c406004154000d08000d03995500c20b16150890203210000030185800030450f00864dc0003408058440c40c400d803401e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 813024640 1250 813023390 813023423
    0xf06030d170a0507141803060709080304050913150c020c0109030b15040213030803011e030b070c050c0d1203050a0203070203072a030b1807060c02010c051216 70
    0x31410788841410402841d400303a50740b1840036000f803800412540c140007403041002c88000c030002c02049400c8408040d803507200a80000d15140a000924840a20441050a000180c40042030710211340c012120311545075546106440c4030014031000402011202400c0d240c1c00e0300705d4100115050b419402c980c031000d0b5190044078103032080d00c00548510038030000300301c803018800c141d038501c50406800540b030441d0003c448071440915a000f540e02d0030b404030051102004240e10f1080301c014116950b040d0740e040d51203503007401c800503124a05215000390740ca010440184039407601c1c5031009060780034034091410150341c0b08008040078000a0b1030320740051103403009803007070701e01455542d0300a5080c003505075503080640d80c81707401e40d03e15061100303411100d00001c200d850f006544100909a584d04040780c070482d0b403480f44500050250481141030243da5401510f007040250240307400c900700c8900b03080c62030910302c1380b60002c0040d0000080d9000110780a14140030704c1445501800e0004001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 813025890 1250 813024640 813024647
    0x307060b0f0f090405250501030501050609092205030a090518040c06052d2203021003020f09041109031603151517160501020c0901260102030f06030d 66
    0x2030350320765124030900340e120024180102d04941c0b041c490f204881e0b1542d84034410b4420380c0580e091900c0c3c901c0300c03580280304559040c055280104402e8072050b007001d09200c0000d00008000304010030307c9111120741c40002c40422020050241c00c01d00350f82d51340d803030340e08002c00c0c0041c00d0241d58022a101d02c0e802014020710600103200700d400100103069581404c00444860307101800f400e809071006a06100814062070000da898072104051a5940d03503034201d0040c0e0141410009800e00740e9910080015880c0c000e4120803200c00c80c6001a610b0a00c1c004d0000c1c240594880c10750000e242000030080040040004c0445800c200c04440c10304607c52030010f80488640401000107990001a40c110001c2e501314440d00300303840702941c1030142c40f2000c032254984038040114107507210075881e50700e00103603603502c8000d41000c0c805018465200c1d00451150740301807082c0c0c0089211a001c2094060101e10418200d504000095641c1c0c1882013140b080b44038260ba0441c443e004052007000e40c0d501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 813027140 1250 813025890 813025909
    0x1b0d1e18050604020112020d1d120703052d070f1b030f120302160c051005090102031803031c05270d032a050a021e121e0c0307060b 58
    0x10311800400c102c3d074841d801100d0f501020110072982d21340078032040459400c140590300c41d40c0508004640d405070806045403800180403441d00c0d4641c0c4c10443e010109901004444501080c0045000007400c0403451401c8480c1d0802c0b50404290302149407410401c03242c5651034024007504021182500c0c4034602107a00d0050b1000620044c0b076065602d0000300100c607030070b503140320301e0070014200a072601c48581c040710b60b454101c9404c01104000d100903d0310036010b044c03807410751412078203200f640b00020b03640384a09254003410344000f000c00c007001c0e87e0400132189400200c1c103c40213440401d00741075020300415174051030650100341c12040400303410354000c0c42d000c07848001080705200544099000301821440208101707100144803016400d224048550a4416500c0a40d12100740b10b00a04004004d1a1070460024110140b101c0c841d00242c5c100007070900040b1140d40e00503000b030301caa030030205c04409400408080b030030100c03501c0040040c1c4209806407106015462200381040002c48 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 813028390 1250 813027140 813027143
    0x81207110c01020d121409030d0c0c0c060806030f0d020c011413030b041a01061101150305030405220504060b15130b07030e030a0804090c020c091b0d1e18 68
    0x1380300c4500074401c64402c400a400c203885241001540203038180f00041c1c404802c9481c24460b40c40040d45038025003252040c0b425048541c600321390340048036525101054001c1c441e181c208058000030030101c6d542405000c400e60ba00c00c0444070000140e040103511004000800c80c00308005d5406510207105100860303904a101036905020942195101c031443c00020740705448541e1440200504902c50009160103007155403a03000600d1420740c4102d0940d0041c606000d01d01c1a0395070200001000001590180c81048506119240380b04001c3c83e40301510b131910030b02c01070603c0d05010901042e40e03c10004900242c1d0210303030605400120080c80d00c92240c040720110700702c00c0104248680d403800b904413684245440010880590000b038606141c881081d01c20a400040c01c2020300b0161007100c1410506001800103821810005010140001c1c4941124244103119070090b55039071088403100c100b2024100010329072310001e0003428000c180c001000391700c0c001a10403001d062640044049 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 813029640 1250 813028390 813028393
    0x10216060818160e07110d0306171506011b0b040b0619150e010903080a0305060a09060b0d0c021e010905010b090c090d080d0f02030613150918081207110c0102 70
    0x43d45040c224500c03140000388042c04100c2041c600d4048944244078169185c081035030041205030411040306030044180d0000016540a1607403001d00074110f508040d4001001d08000040c046040d00e05014018101401400911684204400c100090b03828a00030b441c142d03814103032100d842c25460003a044901071044200b0018000b01c00e001d20450705050795000c1890841030850f43c96403040e6154100e9074000003c00d484004000207400c003240601c0040c40700010038480640384c800d03c41c810348105602c0281590300da00000c0703807190081081d46001d071503c80d008910b840380f9a50450003009024004c882550800b081c040c0d41d80360580303801d8020b009025410380380c6200202040128101200110780340d040912055802484522441059003614003000d44e1b41e107481000c112851010003003042031207141c0480301030141c0802115a0503290703d0000002d00d08003082030400e04a05454000b084680700040b5040680418003505028448589031a00c942d95a00c06441d111800c619045005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 813030890 1250 813029640 813029683
    0x14160314180102040905091c03051b0c010e06160e01020c0108010612140a15080a08040b0703092303011b0225180506012304090506010216060818 64
    0x41c00d101c010701c030740c004600070005282c50340e0341a00d00d0558100319070700e0446400c04240c6001c035120038040a90300d00300c103160400161a0241070702d080f51498ac0071626608002113000c6261136000d5100b4071a002d43c4600b22452864914001031a10320118000070010b28080101c90440d40000b603440c034529416194075280e80c0c20400c040354081ca5060b4940e5070035868102140d070282c03d1900e124015601c60b0340c042102c5004803500140b0204590182c140741e48441ba01c103000c1074556040d5029940411642d40d038400301414220b80b003030541d4102c0c03075540052041801c45a008460510034039003040e402405000c0300300d02450842400c1d1011240036070402d0165003074a030140c1c10090520060b0700c1ca91071005032294005540c00702c4c1c0024200c00d059540e01400744640c0c0000303890840050300b160310b444815480145180d24052441405c3d041516030020908617802070099180400120140050f02d41d6140002041c0f910180d03250184450030a426041864010072080e00d81812400c02098 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 813032140 1250 813030890 813030901
    0x703200a1e0509061c0b072307020409150c0909060902032502010e03120109050c07080708070c0528050105090904020f010c050312071b030819060914160314 69
    0x140000081016038001143c5d00103802c4940102942c0904d103000345a6442c451404000140c104498007624404e014003140800081c85180f41c102c80c0000da0503100403e0b4010180b410a02d55152540c40d01602410610f5154400d54040000411640d02d400107201040d51982507100702c1c44140c401c090080300d015260164031b04e80948004000501d440000361242e610001c441c1540c0001401c6440034a00f070b0b0040000c01001c1c080d40e500060200c000c00d1a0140c00ea807045494896001e004000000108216042c001010420340c0100800f500c4211080d9100e03100c020f2a1580c1503405100e4808a8004506075200e40d0666103110b00c090f03c2580c00d526150200b00162030024502d50400030a481080001001030001d40310745913000c01840000d041031000a4904806000b084030711107000d0740b070000483e5001c101d00f50440c0f52100824006050708082030058aa150041d1a02c4d43c10400b42140c5018054200340c81344514540044400e06804000c80503a441e11003c0300461095602250 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 813033390 1250 813032140 813032149
    0x40c03050402091f09091a0105031212220302030a020601080c1309020f0303120a0506030c0117130821010915210b010f06120c200703200a1e05 63
    0x480310008001e449840c40c1d501c40c95078091b0ba134400c80445074000281c0c103134000c1038001640300c5d01414089000e405000b40d101851405802501162a044001a804103081c03442402c40d8620b8201c030080c2c0b00c03404250300c0c18082c0d943c2d130101e8031200051061000010300c1d80d9020400018024004007481422111292100702601e620442660b1140c245400c05107180d8040009200101c20261a0007440c601002c891044450050045000303411015407840c07960392107041d00b0086446d070460800292144070300c070403d0302c05925001386001c3c0f00080c1d4000d0030020000c900c01e02000e0b001c0a48441e80c83e202c5080960703803462028001345000c4102070204448030403514000941c0c5042c1d206c1d80d00300f2515802208042a8003520b5581710f5824144102030b40700805c121400e801c04000d100c8481420801000c038600500c1d402407480310ba650100c09040140308a400440d0480046119100302803c00000850800c40c154411100314000150010b5005108801d250182c015580d141e407402c270510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 813034640 1250 813033390 813033421
    0x509030a1805090106110609011b11010b0d1b1e0302060a0c080f0a0e040e07150e03010911010305130506150d12200325050307150b040c0305040209 65
    0x40090007508980441c9980318500254005e108550305d0a80483d1002c0000c0c0c24040c0180901e411641042d42200001d00e200082440a0140c1d1400100e0b1740560080d49005080720440b550348440060701c2d1005208101c8000c42400e5400c0c4425804295a050228203c600380e2909030109140701c2410070241c81c11502803c40b5020304c3c1003e2a003800107540d0002a94000b01d14280c5552021508003141640118145240c2c20261001c1100310403c0e900300da07580d09640f0926170001c646c0b42000e4030343c40c8a00344000c01000d010f0000d22a1001501e002503580000165090029290400040f907003810500c8a20032140c102020340780e1a240d150580b075000841522080e005000e1440100c00900041c90880c8007000556420510103900100d01115041998540020354000e000742d8080301158049510f655001e101112402c94203440d0450441c025802d01501651901007500140c0c103594008004040d4112030401421a24010550459009a4020350444038400015040e9180c080c5007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 813035890 1250 813034640 813034667
    0x806060705031303080a02070603020a20010e011406090601090b0703181d040c05061309090203012c0f010908030609040203010b09090d17010812130e1302030d030509030a 75
    0x60b00d10300018a4010100c4584030f50003221031280004039003131300c964107018500103092036107029441c0c03114030200203080811030201c549503c411300798443c01d200703c2507218880240e840c600070301117091801d00b642015032046070128001c44480e000034000d50b00c9040200181d0f800100c40c603041001e2600c00329081c074100e6100d803030402302820700030032107081214600120074242c0c40884168038092810413046201303580500e00030901400900001408410320b20299461504005040c50f00b07400042d01400343c0e47e0480c070b110791045000100d8070701c01150040b03188482c1c0e002c4400b220140348490b42260000800a443d188041c00031610910700304520304d0704580028000710308038815500050340ca260030307104081149e002c010300c1d80036140c000c00c4a1030b00302c2026420005662418242c0354a031164840d00c0642d001e40090491101c100c10007052010300704140041e503a80c60011030300b54000c030b1020703010780c440c1c4102d11504130302130300c640101f034030030034001000c2c0d0708011100900f5610100103194 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 813037140 1250 813035890 813035893
    0x513030f0609051506060906180901090506120303040203100903050d110904110408070312050c06270c150306010201061805061002060705030106210c0c0b070c030806060705 76
    0x418462a814030005001d104006182c0141d0318065151203410108039039030209000800150b95580401c0e80e40010083e0b80c1c4642d124021105030b00815081d001c640d510501c3c5400101e00300c9103d5100c107200d40008c0c0e0314014902096000640e883c00202d5000354154403150082036090115080070002d01d1081c1406400d104001d181803080e21558450b4031110040030501d40240e1804d4020801c5c0d455003452581e01d428102040103440301014000600010304001c04070f40c0c158030980071200e050070180c09843c1142010980030303062000d46081000c6910108100b00c0b0307a00004203001d490080c3c0104441020000c0d41842e00281d00000c0c90b581c1035541e0385000142c05034102020085200c4c1e9130f580050b1a00d0014200413910401c0c8482a00b190302c410100180250000304030390547d105c0341803c00c000d41000248141c80070714040b244204034103160150084031f40184881800c6403040520394a00d07036071b2801c12149032800e140c2c0900011034100100390326007081402020068061340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 813038390 1250 813037140 813037177
    0xa110d1e03090302060703030f061203050316050f0c0604030e0a0b0702040b030111070606050910030312020706020d0612061b0203160807060e070e09010203011404020d090c0609031a011505 83
    0x80005d511074025843c260040303515111036040d040c03103034450304001d01a00070402c6922001c64030014a5070100828958a64161041c0c029503d4003c0d010f80340c3c5038101c0040540d484500140c032644a8030162400c40c0030038950901c034086c81c90051058019652000c1c4d03a1801d008454007000042c0032943c0d0740540555846000c105100e18203001001064007466010407402d10340070074480341c44801012402046841c001c01d200007940103c034107070400d91000300940c0b00d01d40ba040c020000e20402c04009a130791319103d000200c40302604030700300034940034080400101074141c010b05403645000d02c483c00181c10812000040104548109041274020303229035003004081e5a0744022070b0201d420005055010035000c0115880c0007030100e5011045c680254255490405401901c60114030101d20660300451091904413150744000690b9400c45602203c541c3e40b100064080a040d000548004890f841c0440810500d119003074101c900c0100b4603050501c40d08012140c507000364184000802c1681c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 813039640 1250 813038390 813038393
    0x1204150501080a021309052113090b04050601031e0c0c05100b09150108060607031205070806190e0105060903030408060906180c010906050a1b050a110d1e030903 71
    0x3842040d0103440000000e20840655004000da0701c00a4040303c0c6503c1d081151002c006800459241d00c07000381d4001c007a68021402c1d074042094011b04500c1813491800400024004030f554102506043d02514200001d4482c40011401d403002c0c43c000c2151040f00c2140040254403ea010030050402031900c4410388106a460604040d0284102401c01d82ca03000c0d000350b01e00e000302130940c01250800d0041c4200c183c0d040040d200f540000c1000d03108100100e44903060600420350f02040c0c003990181003100d80f40014001d081c9400c151291406044c00504100e00c2480024903241039499040c0d420b8116844c0004100f42540049415030b0540010300c00004d00c0c440c1007001c03e005500000c054907080c40d000b2807003a8104004251031025610000c450312850b40c0081c503040c01e45105140c180c1c0d60741200b80099032031940d10a920300040c1c1d003100d41c02051190200b942541c0610412046100a00701c0b01080003100c034242026103d000750708448190340c49103092030520f40344681451054140e49 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 813040890 1250 813039640 813039683
    0x30c0604112b060c080f0c03060105071a0403120e07230a15030b0609010e09090c101112120a0c0201150603090506010f060e010503100b0f0d0606090b1204 68
    0x2024880c1c54182c482c0001c03408003c03da00a810000000d86044030207803074104884c0f00071960140080c00261030001c08100264850401c543c1da03180c02106984040c211141c83d138400311411102134000ae045501c3c0ca510380920390152042003400000106404d60810b0790601303030300020850070710302860b0301c01d907204850701c40c00a000014243d40ea100d141800750b90038090b040e18541c3c1d440c44d20415040001200c16a0030280b09228060305940b480107036a20080e82320328140d00c1012090740021000e031441c403d0342d807050411110328240c0056031042140036410b41701034014140f482c0003004500c40010722003031351503200b84180e139060710000c12200b445011407081002a600078800103921041c48c0d006011042101c3c038018020a010280780503d40b200040c0b1618503840003d041241c00004520344003440a6810050000084000d0b034408903440d8081491b03201d44c1d9407102d514204800011454024005d0f6000c4a000004691500304419807014401c1c0d001001100c0311008079007a10780e580c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 813042140 1250 813040890 813040939
    0x12070b090c100503090c0103060b070b06010c080c0d140717301501080702100e0c15120f0103124e0213030b18030c0c040e030c060411 59
    0x1d15440d10b40d50b9040103466175080c454002c00c0281814144242000896503420840fa15141c201c814240148c440750012034480a01010180286401084d240f01503d0081419507103074000703494024807030300c6540c094141ca008100c4090002480790305a4810b5000450040031054440c00125409815000c00b000f82c0c42c42e420f00038a030100c04001041f00d030384056002455048000d003000c000170b15154034025503600c400750543e0750341038a802c5070141d140c1d4100484048244001c26001b0700340d100c0c1e140b22006030400548020000504030200744900d81c4088401d0603640c00012800091060344001e0351000d600c2c50502015114440101543c2c0e050400301d142907005145681d0600c103440719510742c01041c0c5040e1003d07070078410010070441d030f20400103d80440380d004000c0c40241d520700c04a00c1c040841036401c04224000010a8036608402040826001508540400c1482032aa008540d60f016080e5503810941c0480b000c100826000310015074450002070080e01010010b01071040c0060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 813043390 1250 813042140 813042169
    0x50a020313140f010305090d14040504050a09230d030515040e06010e0c0c03071515060c1506060e190506070b011404150b070609023012070b090c 64
    0x900c00442c80007103290640d04004441002d103001d000e42d007009509241c5510340e03d4180030038010703c44440d404003860350050b600242001801000b40d40b07000110301010b0251000e040354890500741080c140d00000840c000800320940c0001c04864181710402c2d402032001402d010746410300100701c07500e10341d540d000345a081d80c0c111025205d5549807a403181050701000d80400600c4d8010b203c0740310140070000a0790500c940001e03848000440005041c0001c001880001452000c0d45e600801c2c0c13160450300745038585100306100500c20b0304041f006d404642480c02844009012150200d4051500c0461500100409141c80400c2c0e0b941c1d0000441c00d40c0040401c88040350781c040100700304003d416001c060f0b6201910107010b02401003000d4604080359011f6103a4030003000c40c180061104681c05103503040e50160032034400b002019a0050610343c0f140045882e0010350105c002c0550000c0340d455144041a0100d03803e164941d1398800344580014441c0c1c641f48201c0f800e065641d9144001c0340c0580 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 813044640 1250 813043390 813043409
    0x302070f06090210020c0d0b040f171b0d0801090b030106050909010902040f0b061b03040503030409020913060513231305071d0103031103090a0e150a030c06050a020313 74
    0x100c2e00b403040c8210524450300d4441950010181c03a15951248900d46c0c005c20f91003c4218826559481c04450300700100c5400b501050508080d401405071800c010a2198225084007180f0065a6882c6a0b21b0441c000d1140000c1d80c00d0004000b060200d4001204d40754000703001003000382e01c44011450340c400c1201d400003903a464032000d10550a262084d1f411a95440320140302c811144030100382c0030b1064081051400313600303144600c1030310000c0c400d0702c010701801429aa9200c1c1d4920824000e9046121424442c20510384802440340e103501c1001c00700da0300501005000c1014407038800040100d0070080c81040305034001010383e45440303405288a95410a071000e40882182040340ca403040c16045220740d03010241c51100c102d54000d00300f40c116541454840c020021070880c842c15030280c940c2850300101c4060000c02c090745441449031040a2403a00016140980c0307041101e5018103210150840c807803200184044c0e44500001c01c0203071940d0040364900f44190700362000d581a250301c03807040b2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 813045890 1250 813044640 813044651
    0xa060504050d09140d240903050712110a110d0204020f030a06051e04180203030a0c120201020405011b080708130e0f15240a0305090c060c03040909030302070f06 71
    0x1890700400c14201030480110132580034425000411820710203404040c001a01c10540c1d940b0900c0c4942c02540c40c10040c1c5001c1c0003800c4140b601030314507089150b044440e104900304241d03c062103252402461200341008040440141d141c404014030380740c2899404c15400c04180e80542c4482c00100081b00003612a550341789852200c04040340d2803600314503c60f82120a104040c0b0b1201042411078020458001405604450034807175035100941009403d40008600004201c1c0c00c2801c01120740c0c060f01e0f5401c82d8810b861822800c070301c918050702c3c0c0031079165001540c1082c00018090343e0705100e1005240742c0502a1a101318942120150000c000355004060003821190900e5a0b0071a01a0078021f00a0070701100040d1400907810307016000d0715a0303220030f40c0d0101c40c5114021500c600744140d159070300d02c564002000f0301412214070405200c1d0420000321400c0410864040e541500042d43c209400c1c441c3c42405030004110039401c040d024883c842c0841c03194500051302500c51f4400280c0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 813047140 1250 813045890 813045913
    0x60102030d021c0b0406030213110403150f0e010e0706051c110d0e07034d03061003050d0807050d02130617060a09180812100e01061d030a06050405 65
    0x20307182400c080e0b40c002c5c0d040100400058075029400100082e241c000801e0050781100044114011640041c15108000810003003c18032a44004481c00300100107001005900004500b44d42481c50511420307032001d4010032030188940c026108a4a80700d1a00d441e1990580540c0141c030011041610801c1d80025001190406c42c495807000c2e40621029042040c030799210034200d042c2c1400c20b0701129401122112014039003030020010720100f0030364040c4101083c0080201030000c01c2040c0e000f03202e9017003c201d940900185034001c80344c0c010700525092061541c11200e00c003001e404201480001d2262415241c83e6002500c40c10071180494242e0b070340381035802044596a0411052580042030034004240c85103052041036480346000491807650080c041d101d194000a4042d00c1d070240400c40d42204503d216800f8025031800d0311023080d00b0b0f2140502c802d550001c0c8642c001042c04480300d0000d0315041c1d0580140a2401010f8424050160300d030203081c0c880c00c85085a540d04810302608 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 813048390 1250 813047140 813047197
    0x30610060216150309020420031005040b0f0105130305070312090b03090d030e0a20120d050403060b13020d1d010e19080c070602060103060c0c02090708060102030d02 73
    0x3606980c1d6600e9002c4032490100081200c0406040ba802010b80340c20111065440b04d80145040301c04054921642041d00074100c440341e042a00d00e04c50613040c0f2800000d00e80b074140110008030705c000700129200500100159001c0e80000031707008101c070943c1000008100c061241c0802503003c0c0d4810006d58035110b100a01e81d6031140c00035440070505100f4041c84200028203a17803165400c0c20000303a076a04034881549442e02c032401c01405418054030104407034400d0028184035480948184640c0c41d011552075032124071300078100000540500c000c2005c1004c5070440c804e2600c0240000308041801c0b040c1005990240d158080019110fa008a01c9000204035030031070b14500c01e000700592844a141543c85125189400311903c140c45041c0040c0003420048903204500803044542459031400040c2d15200300b44401e076800d40c54040f0b42000c0c07600a54440d68203a500520310603442da0740403015250004040c008074110b11060289841104907440140080c16942d1695500703001c44042c1076 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 813049640 1250 813048390 813048403
    0x30f040b0a0606020a02040908090a080708070b0720180a021902034609081b0f040c12020c0c030c040e03090d060906020409091407150c050a020306100602 68
    0x40401c0c038074240c0200501c95020a4002c041c55044402140c0c0b190306040900050151039484e0b41e01044500002510180004101c4100c9280c482a900302e1603a41c4960360081c000c4640c00381403840918444504800000051f0a20000090802d4186440c01620b05240030007200c41d030f5171b00d079400520075030706850b0b041d4884101d80c101d200452904011180404203000c104c015007012090302c10351046144540080c85c0c1d007496081e405030800f10300b11840105440c042e4400d01c50310b40540204407071005d03500201034691900140c00100503054000500004000c4c540b6404100902d000d1034030144500c2e8001440307100300c024020030045080300101408d06421840880c41603243c5070701c40c0710103140070064540b01b8000b2603140b0084419400c000010f0314160900400030b80c800100420a41101e51000d4047d174080c4500807003401510340710303c0e6901c00c0c600801b40c0700e480c810040040a449442d180c90000d2260040e6400b503551a80400c1c60602c0903269550b80d0880d0305014040c103a03040014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 813050890 1250 813049640 813049651
    0x1009140912090102010b03030c032205060909090a0c15030c0804050606010f0c0506010e070318110f0409240e0d08060112270c141c17030f040b 63
    0x12085052000d8003581e6401d041c0c0c0d0560164001080d8000181e000394060203e070940030301520768400f08800e0464072907000d1011040701642c210318044000c03164544c980c064640280c00107180200c2c101c01c0103048000104031130428800e902402001039803000307c100c020010f6135580790051403540c0000c4c0c181c0b484181881c00b004004000c00000c07400001c4c6460300b00c0001c1c03c1c403030560101071104440c5141c2c9808054028030641000144070012800c90920445050381c080000210110700304000c01c418100107440300614a810040a01d001001410340c03540003440040c8041d419550841d03a00d645940c10b0704040003851640b9028031b140e024041c05400d000d40035160001030600040c143c484042e001034100b242c180d0300ca001d0940d5983c4030007089805400d002100c00060660642c202d8004001200c82c400c1c041c1001454100740701a08844150080004a440c108a2504240407588034015521866080c001824180315000114003480c1d80c00c41c150614581070500fa042c84101821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 813052140 1250 813050890 813050921
    0x915020c01050f091309031211040b070c031a04030f0c05030a080a0b030a03020f1501152a05010b010e030111041e03080319111602040c11070f030c08010606050702060c030f031009 79
    0x3000802700c080c003801c030f4040d10044c00001c1e45521741d9050106994055801c010300444810b012426100007078030049100b280710703582d60f980c4058021000c4407010194100103000303500512a4070a803034041c0c4001c2c0d50101150b10002881c00c0a13400003880c050544a09401503002941032109203202409a00004640c1c0c51001400707500d0260b140f03c0c0c640025100000b0040101008890b0200000300100307034046281143c101d042d590b080c814002c00e00200e440b408102014105005410b041c000c1003910340803141d245060910342184042c02c1c0c440c06c409003221950f100408400220301c58050340c050400c45940300890a00394281e0000c0b9524503161a03d07001c1c05001a015641e6203910080f81c640e4169404924000c0303034401034421080050421007903004400740820305400880c1d08004483c007604050703030b10990700c0c107a5900b00e4580f40a0400000c0c002c00108016040810040c60f107089068103c034030300141c0301c14111080d001075803120365000702c211042020030b0081c0102c145040f10300c3c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 813053390 1250 813052140 813052151
    0x5040e13020d03050a2102091c030f0e0d0f060506130605090c1b1b011409180711030406030605120319030f020702120d0915020c01050f0913090312 65
    0x10000744940902d903070000c00700400015400889442010f042e0708007400c14900030700902240480300042d40003801c041d4015044903410741c81031403160440e11002609900e4032554032107030349811184010031032003107034025840080e0100007a120001041d07069010700030000e001d051603801c0102e5901c0d004040103030107090100901c041d94423807140e181c0101c0745c0c46140d50345000b0a031403070021403400c0b84441c007180903402c080024420b51522820f2544030076a2541e251010010031103010b4007440c0d401d0398100a6211030b045881031030a1106801510606000d8000c504901c2c141e855641300b908a000007a40302c1800308004e04000703a4000604c0c2c2e8100c051411302c030a619804028500e0302100904258403400380420010850b81111440c03030300544a0038209809107a815628100e9281d923500040388014002100d4881410265000410794082c10305100c1d1b54004480d02d401c10307480d4000400c003c101d40c40807507584803050101c40140b1500402c000106d4100a0502151800070380860f50400307 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 813054640 1250 813053390 813053393
    0xc080706150e0709064b0c05100c17180c09010e2e0305062a07080903330c0c120705010603060908070c060c0f0206030604091205040e13 60
    0x100442d0280c544a14001c66506894241100d40c80d9000f0010051030483c90000c1d0040c2896007180450f0301210b164400f06c08603154422101e8010051018066400020007000c0d8440306807c452842c030340a00d00552140d01003040c0f12825030099500c070b00892401040400c0c41d4900f486651148002140e98a66541c0340813603900c1f642e84d0040c9812801c50902c624240346003402071681070026410705c4140c200070f49a00c1e00316510501503c000e444a40c0c0c0006a1008141003a407000900012040703460030034400756500b1256802240c0c15a0740760081007801d4840c88603c600f1a00d0859000703212803500c6101c644030650f919000b078041c0d6010303c0e040117074814000c0002840b01200c482010020354410f0313941030003801024a07410080615050261410501c03521801074003841780a10001005980c2e540c8065907207076001e09004292107100082c000c0545000c50185a1010010b8404107281d2015640d2520b44070303282990002141c400300702802010002805036920155040301c0450040d4035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 813055890 1250 813054640 813054647
    0x207050105160f02150c010b0405060a032105071e1b210804080f0102040602070e01030f020609040b040c051c05060d1202070f140108090102120114010c080706150e07 73
    0x20250803d0051102070045454507810f0803030410880d80340b00d07190001c2c0c2d401c4a0280c103280032141d110710305140205101d860902004000c42e60322281408807a410081d103080680c40c01e400c50f07010700c0350502c14400071070740da01030400000740b0003041c022a191051505a12003c40c0070326400110b45113840910441902410400600c91000c08405007220b540c508411a03204079004034002c0d0190800f004080c200540203042030b900c2d542c00b9030392483d40343c50784204c0c2440c0910014000540400c403034400740c2070107802441c8c03a620240001c143c4503451000300c1c05a40364522010700003000040c3c041440000300030b11104605094805120a0070050000343c0504c10401c40903110000d041c0c00901020700801401000300340c0400d8501900b9034518081c00c1020710410b0140c041040d540001e0b50150040c0b08580d1502e4403407480481e80c1c3d007440240002c9110172061281409004403920010405207005080018850000481c25400031030700001c5080d615801405041804024082559007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 813057140 1250 813055890 813055927
    0x41505040906170a060e1204091a100509010c02040605030d172206020906040806041a071e1206120b0406060906061d1801080a05011109060409020c101401060207050105 74
    0x1004600400c403040d8010890f400c101000c200032468050000d00013270f00c6030b03098002070200310b410307440c0d0044805014240100c81081c00e031110001101080911000d60082c840f540b0000d0018000050340340d11000424501054070040801158502c454000100354502c9850b60109441c00c44515821081c0d2960702800790800b03008015a80225074040c3c241c0300c01003940c00403c540e84c122802400c003070400031940d41d83c01c00d42200c1140070f440090005401541092015480d0118203005e40f1aa1081181c07985c01c1c0312050b084146d100e200011700c18404a00000c0928016102c04006041c1031030300c4002c8030f0056110f603801700c2c20442d04000443d00880d0115030003407080d9540c03034440011000180903840d0484a082d42000540020400c104000ad0400307103248224001c0207040c21a80d1185400c0c0a03c01150b540700c2d004201c14400700403550041d02021201004a5004d40310b207036401c109984115001c3d030310540301b0303800401c8820360410070b40000309001e003070061801e8095440c0705c42480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 813058390 1250 813057140 813057143
    0x18140a0210020606040c0f0c11042c06070203090f060a180f0503160f290703030e100506060904090302120c0c0a0617010b03040807120207050102010b03031201030611041505040906170a 81
    0x203c02e0041c0c081c40d10340f50040bd4038101c170138145450f03080c044d00c0d00d5a58001d8207030080041380715000005039864000000c0341d860500080ca10401c010500b010010340303038051214102000f011404904081e071030707403003448003605070040d000b1703001420318041c9840e11014600c0c24415800740f0000300150344900c180780080c1c0d0b840300500240b00c81d803103849104803128a031407a880600000f8061b4189a45030340440604100002540d403007095041c80c1005844055810075480281040710348894a0a1744c40f4a44441c46401520041506011003282da40c02007101c542c802e80042180a017503240c0780021b0405410fa41c10703c40c0001040d00040c110102050080c1c0210303550010101d420320440034107603000c403035200c0b90000c1d8540300c20100135151409445158055800c02003041e0540c6000700070380d040800c01850b50341050f865515075002030300c407440804152000400011a884200d40e91402456400da01d860380d40e02c6ca086500d000320365940d03001c01c41d2a1203031040d9502451020a45503042c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 813059640 1250 813058390 813058403
    0x30f06040b0601081e010602060103151e05071701030807020406060504230d1211010b011b121b05030c19230c0a030507081018140a0210020606040c0f0c 67
    0x1075540150104000324170001c80300000d00d0050002a420b40d0001d80c0e42d042e01e1049603440b90444040c10400c0503035032035401c49140e0181ca00c5084116000540c429544081c1c11700c0d103001e10381c1c0d80002c0c5200ca200c003a0010b440320140041c2400030750600b801080300038646864024130b0186003908203046000144012865080110051113496903107e000c503c0140e00002880459460201e0240012880b001d42c00040d5003019991002580582c112003401c020004058509980c0b5954072540c10001d40d11140030300c00004015013050500d0854481c400b407041008654401c0450109403501c0b414528607804400b8011280d80080c01c06507d400004004102c0d2f8410400080c48080c100a02d00342c001d034000b0808000003041c03020001c3c4900407038180070f0640d0424004109250300b030300d582015101c0d8076400b00c0b280400154182642d414482c00d848255041440180d0005809141134114800141c2c85542808880d02d0244030b40e00540310181040c02c4d0b10481c50201400101e045440903160 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 813060890 1250 813059640 813059657
    0x30903030e0312031303120b010903080d0626071a0a05130b030a021c0902010509090a0603060c050a030e0d082404110a09060e030601030f060207060c0e030f06040b0601 74
    0x11902c1c100021002202400c1405131030303181840c546030050b0300e100030030760005100c80003115500c1000e2060480c590410381d40c00c2051030442c4c1b502042c5502c4100e03282001aa1a0070008841d69200d00e94213110020b20343d4550b402c0074200d0300c076142042941020742c0700c106000f05480301c10041000c41c1c1005100d824131540700d45844038030960540700b40d44141e0350380300c0010800c000d4860301c1d0300401584c803000303482e100d401840c054074070119501d1500c005c0c04100208280801c61418226559200c07200340d070085551606ea90711031090302d100e8510301e0007041000c140c0403009a05400381c168006890b100611402d0001140200702d89400b42c2030103444485100700d42801c44040c0000741c4501c0d0098800d1201555180500d0902d40c00350f03c80c40e00003506e40e0400300d01c0e1403081807000300380e40c0024018450369095480301640d04c041180c08a4005030300300000c400140311801500d102e4100c549070040000020018035091028006060f41d042e04640f04110004142182494002e8028079144d0355 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 813062140 1250 813060890 813060917
    0x12f0906160219081c1b0206070f06021210050409050a15230a05100602070e06130e0106060207120308010e0907050a0b0901020d050403050604110f04061706060d03090303 75
    0xf0b4040c1d4800c2d04400d12854800810103034400114818802001003504982c561004001c903501c0c4445148194104e136003802540151074084054508180611020458240355507662000c903400842001c1010b5101c0c0c0801c00304014044d0304600400090380c09001030052552055200e03001803100500314240020183e00c0e030f5444c0e03070201c42400d2610203a05920388000c0b0340e21020305821141c925604e81008001080303400c9015032401110026001090341604180d120784011000500b41c41d0012441400d2041c107908a00411180e03c45120000403540d080c08002418140680c100500d818072100d11440003a42c0150001d045800c01c5881e81c1083d00c408080c035040407000c0d4085980230900341c402040c802070260051106040c01d0b002c46a015260040076034143c003035484083d101d500004002404600881c21941400000820b09000d804035080004c040f2046608020056191000c000c1010101009002e81164049409042214050b0340c0180780340c826010040c00c000d440f505600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 813063390 1250 813062140 813062149
    0x60a02030d20040b18030a05060f040501200702040e1209130b09190506030703030c080a14300105030715050f03070c02012007120c0305012f09061602 66
    0x50ba0030481c2030005558503a524008181ca8011070040070189070000302180b0a40b0b00040c208100743e60080c040c00c0c2c40d81c1c8040d011505003030010800d030360703030f548426203841c02806074148003254030180107034a40c4805950040c032044545088407000250702208410440981300703025203181074021940e034160740d498005400017501036010300542100010301805100c4450840354400340c02d0300d034003c0000307030707261010550b803a1f074240700107008609218104404550311800034035102600703082456044510350b031500000e60019401a00c94141040e48803c0c1c01c81c1950581c2c2078690406004915504020009459a0a501c20426814444002a0900d6001e60196510741d00201006074481c0f03452880a000120144801c030300051040210351100800717590a80008840d190040000c24200080c2c0d6444401d83c00068a42c0c880e441c50000c0001d070300b40148442c41101e0030500c04c420714082900302518440c041235101c5402d0900c54003e5540341d500960f1741080b91080401c13024580c900214 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 813064640 1250 813063390 813063431
    0x130309030210081803120708130209010305010c1101060f0e1e0103050a0b090138060f090a05010c030e040f0e100b03060907061b03110706020607030605060a02030d 72
    0x2e4004000d11200c40e5040d03000303c00944141401081c500c5054056140161240700744c048140850013900007046050b0700c1034801a502449103090300f8201c1c1020740025800281c26441100c40340c0d1601680350303119622103090380d21260880000e000302030919500d10f05244160084c0e001080c40440090448010b480c8041c0c0002910780511503a07503100c0c00d0140c0c0755034070b1040544122141c01c020542c543c005120300c0300701101c98400e401c819207000b504a262244c800002c084050741d00c07040004960f449000800e0901d2030003002d51b13501e40e242814080c110085600c07040c1403190401c5540b0120382c000f00480c800e000100e030002014500d56820b41c1c01407008c1500c3e43c1d40ba01c240400031400049691150072800c008504403280d0b5036072600f070076548000c140501c0001a6529825aa10000001c2404081846410300d44003180042040c2d5141600581c00703c001640002c0500c281c0940520586021740010b481582c42d00007403050103540c1e4880d04464030012903031001502070310441e55086 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 813065890 1250 813064640 813064643
    0x120a0306050d050c1009061707140a17060111100c14180411130501110f0a0308070f09061706190f0f05030c010813050102160308070807021513030903 66
    0x6641402d905030410603a6659441c0e0010300920300304007001079060096054500b15807140e0f9a986000c51410100c008100303015206405110750314034a0a9401036001c013602e09200c0070341d28072b00000440201c1514441014000d01c0c18440800240c0090000100b5103e540300400000480d141692080499400007992802400b61801246580d1400c1d190701e60206083c100b1102413103a1042c148614007030f03100b4021a4120100000410001940203000d41c1801988180694449176044104107040c048081011400104c902040004032900181e40c402811018a80041081e0404c071000d080600c0c500c84644071000c002002807007654590787c0e14180381d1201002c070547e07159969804170aa505c1e0f401001c0f0781d0182139002003550700b000901690540b2051752041d1960b01c441c0002104030000714015074243d5020003404105c071320088141e00e4068469581d0204c0d0b4501601c0040c80c54802900300710454000c038040c4064100d0300144c15400849020201456070264501076910080d594030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 813067140 1250 813065890 813065899
    0x1506091e0a060804030f020f0c04270602091305271905070503011109240423100804020108010311030f0f0102180a0b070312060b0c06180f120a030605 66
    0x1000c030b2060380c0000d01c01c1c0554866140d0b00081d18490385d003030345c54046204040d000d69000ca10550f0042c82c00c0d03008559981d080e8440386d19404d0032a00606d03184420050242c039a40c3d00050208090f003007035071821008903561501004141002083c02c2002982c81c4c1000312044203015100e0f4040308240100708121043c440e80400d400040d14105880d00c5440c8101e80c481e51070002145e0340ea440e0181100c6080300028400c3c00d8104941e03407030802400c003440352001c1302ca20601c00420301c01d0503101100c0802c18082d9452142d030301e1102c1007000c1101d000d1a04001c212400040c480140d0300586141c1c19a5031006111650f200f1b40e9002c80d103045209444101c2c41d2282003060000c200040d80204100c00040703200c030006103480001c2c050306042d0751040c0c030900f1908000ea40301080c45520001c1e90711940d0440801c04503a07840305080caa412428031005950400003e1244203071203041c0900c4001150406000c06038440d01540d52035103038420000404140004074100801c0c4264001c0025140042 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 813068390 1250 813067140 813067159
    0x4110f121e0d02071a130f03051506041802041a0d0f110301140c0309070306050106210506011205091005040305040905010905010f150e1003141506091e 67
    0x542200380303410039030750922900952040100551010034444152500d80c2014001440a03442e20903803540a5185007142c00c0c0d6080b000300e00c0e1030300d15038942c0041d03004000078650510141d40040c60250050235980c4100e141000c1002054070303004000400302d404a134001402c01c00710200c212002c04042030b00d40c0c850300401502023005101050f03041240d0290b03c0984400c0d050b041132500300c1d61800111000707460b5910010700c1d007400c2d43c4011a4450745c180b054440250352603980744107480c400e812840100d401c2c05201100d9a20f104403484002155640034802418200001b0300324041c03180a9a19040e01c0d0000150326020401400f050078003181000c03c26403900e4100140170741c009010b8000041d080c040001100c0200c0d005840c182c5510342c0c0d440b0006464181c100c1440309102600130180601e078400114a51b48641303c3e105c000c0d5080c1c8001c207060130383c0d1110780d00b0482c0c02000060641e071000b03006942511814155020000169a108072041303020030b01440300400e86030443d0780020480d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 813069640 1250 813068390 813068413
    0x18100903081b01180f021c0f1208070f140a0507080a030e0d020d02070e0717070f121e0908040f06050a08091504061a0306040606050a080604110f12 65
    0xc03249680002c94000304280d82000200b00452190024050100c074003031107900300580380107001d441e4038102c00c0c00d8445210103da5104402000400019103c00141c940280c07007c1c0c1d0403a50560f0702013102e141003082c2d1202000d015080c5140e003d0034241030300c00410505c08141c0034600f2200c801b5040301203541ca401c1c4005000f4045d00b541021803203d405800382d580c5c0c52a00014a0740324403141c81e00500000303410100580c1c00d44000920f82c204002c000758400501c11012030805004074219500c011408031940300190140d14003948c00c80c00a4a0951b90850302820071100e1940190f881402140c010104d0901c6589806544c0001d00c01c0d591400001506940002c000d01d2091405e440e4843c0750341c0c42503c1a61a12906007002c940c4403194000100040e0050b84840740920f4803600748450010408042032a00d0001c07201101e4440e80c1c0c460501c864644180980300410b240c9004001a10b003c2e6140e12500600e118020f001e90074000c220f18040c0d1380c09003c1007681e401d0100b16082c10419 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 813070890 1250 813069640 813069667
    0x60e070503011404080a0516140a020f0a0311090703020906040f03031205160f0201060f030f0b01080f0a031407240c05041a070c0518040c09021810090308 68
    0x9a1080e40c1c4258a00381008500100e4041018803482d0000099030403d11030001c280d41a6002040c0e00440a18a000000024080060700143e502c0d0308401401c0781c2e40c081c03040c003480800819465109031140c1030f04100087e5564207145040e00140c5034040745450b45003050340a406001441a0320142c0401c2c003246404401785e040342168080d0b681c0d0314841d4801c01c0b18200b203640641d200c101003581c0c01c1c07242010501946240034030342e240d440001039641c0e85110b52400440d42c0d8104039090100741a4650500c00c0d280300c5a405403074840c01402c20303026407485d115524010440300609100c61240d0129200c58814240c4d0402034110b024281850060450b030400c244092032000c4510345401c15244c649445507080e2400c0c0d44034480314120812210350b6071001c0e5041410101d0708048031030f001082c161601400e0248411501071610360701d050914100d01d0340300580d0400403400e441802100301c0b01c2541410032070300c40419184500e1030070170f000c021606204950001380c401d880029085480c0c822 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 813072140 1250 813070890 813070903
    0xf1807050c0c0a030c030323040b07110405090a020118030b0114010f020703080306040e101a120c01050304020105030a18051b0a12120519030203061c02010f110307060e 74
    0x340c002590502c0c0e046604000841503a0300005c0c4c00e0b001d4041003400001c0c09001e80d07400003c80810ba8010b1412001d0001d505c903030217904100d082010124064040041c219180780126100b101c0602c05e40c0b9201c0d049517a6031010082c040e0410084c0744502c041600c00700b113204040c60300000796250301d41e1141c03401c0080500f06880a80000c40c079a01400440d480800d0901c1036a40c003460072443c50311400c0401001c0c1848203640f0043d400b4844428010801a2043d038103503036000051440c1c5030b42c0080400808214100e44d030b40c0d1640211103129a9aa44081269445607090070119140e440d0510342d03500421002c11880110480343c020f01040c05000252640814803041404039221060818404007020078811045c508244462000016031b42030412644c0c0c0e115881c2041c01e0022600c0c00c80c0b8001e00c011050408070b0f41c00001d00507241400348000001030700e0a07803a0306902100b940005d11a9400c21030f19002c102110700c4110710b445040c0100c0b001e15810480502103011920f4154dd02c500c0d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 813073390 1250 813072140 813072157
    0x16080a0201150b0c0c0906030705060304060501030209010f080a240509070e151e061204060b0a060c0201050a0e011b0b0906010e1306020a0311040b030702060606180f180705 76
    0x15110000f80500c07160341203c20007440e40c00649035040c103040c1804035000700502900d43c540101003010410343c5880c070142d8480c5005500c003150651540c01408145441a0000f80d843c01c4170b200c050041d94400260401c2c00f542c41004494070008540481c41300c89417081034402c10905010030322104590000da07500c00d8440c81c1e1941e40c25601c503280100240038104203929001405d0403140700100d00d17450303010381c15000040d0013035291100150148251005c1110100c0d5910f80c1d4801d4481a4204a10444080e0400f400d06684d29070054002a1250040004003802c004074184a259141d100d0004048480c0d100c0c00c800545241900d449440c018023202c4280d114411f403000040c0e12208841120300540d03002c58255103101d40c540340e001c0a50711807100b036405d041d29036211030070020b0590700920083c05540b11294407030034050402410b11b0000382c9400d12400d01803158036a10f260700b03061050380190072a0341c001c4080240c80801d0881d4076101407404001715030000c1003030860304800108400d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 813074640 1250 813073390 813073421
    0x1704032708060f06040524030f01020a110118020616050a020907110c0d08040b070303140a09050d0806090109090f06050f04030f0c030c06020306120a150b0a030f0816080a0201 77
    0x16a40d4100340070884008032804a0300d0101841052107c00d050030801221840c09401c2e01d510041158099080e03920601b20040001e0010381040e070300980a100e4030304160201851300300300306002d800040381400381d4040300424407000c5040f03034100003041000641182d8060501c1005280c04200505507400f0311f01403c889000b480342100d80e520b41103004c1c035102ca23400340c03442d820035062400c6541280c004000881c140f40c0c0d00c0c0980f040d80b542e103004131482102046000305603000c040c0360042c103020700145004240040f8505105003540d911036a41d044d5441070304009654200d81c1065034140003041000f0b41003a18000030300c02e00159680e04c1c01e00c12402901c502c0845080c3c13280071912044001c1c0050700160702d40c0e0015001920b90307001560400c100070b00c0200301c0d946d02c03072084ec10308044c0c41048a168480e02c804c040010f9190140c2d07110018100ca8602e10b0503e0340e00c030341d00780d01610880102081000107080340b00105c088021125203070800c00251b00d501c0c400d10080c1c000d065100501009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 813075890 1250 813074640 813074671
    0xe0d0201020307090b160b04150e2b1e0c080d0902180c1204030917010606030507030204050d0206030c12090d081302030a061512061506170403270806 66
    0x50a170102d810350100d000d00014041095120718442c0c41001e001241c03400034680c0c458000790720701d0203040500b448a001508008684007480100a211030b0095404c009107d8255130000380c01c141800304500c0c40e81d032203207038820007901c04640c541040302004200c11004034044044141c968001c1031980c3c8284e0708080c12075085040310080b0002151115a100c0081284e6507841198a1b4915041842030602005980d02e54003e01820b41400a00c00c401f41e55403a001c006441d818001c07076400800314201180b070182008041483c9001c6240064000c0ea000004102e14090b29030442d200d0001190141015040420402c0c1d21030003d12100c400260b14100491568122807400c444d069500900420825541c0da9540303000c0d200d414200007410340312031400212010911240480c151180c4000940741240c2c51208000040b982c0065082012601c1401240034005a40030740281e09801c0a01c1140c0d00c0301411140b18003c84003000e2074405c0b45000007002c40c1c0002d502400342c0001d4494414 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 813077140 1250 813075890 813075899
    0x190f11041802041a090a0509011d0105090106021009080f030c0a0f140301140d02120106080609060c0f161a09010f09050c041a0a0e041403030c091002010e0d020102030709 75
    0x20b80c00340d8080c078011050750354011034005101000410001c10003502c29442e1954500c002076696800341d02090000c03132202400003181010800540c00360004032280310585d410850002d684420030054005010b903103081480034400071302c0544284181c800e001540d2840c2002d441e131500d400c641c0401c0b000c1001102501580d03406400c48803180101400c0755030440c4e18000316814107100f0910820b400117012059040540c84520858103c060a00000b00b00030746814149071030440014145015604654141f000243c20181103c200440034031169484118807200580d0724803d1060003040000b0030390341c05040d41c0b01c4071709061007010110000c00150b95800d010f4002e0704c40e50140180940c01114940c021032400b544a420300750b0386003000120f540c0d040d401140b17102d103494201e100480c1011041104009404064121130014000550f04504003804040c1c1580a004e2400d48968044031140e10014400d6028070002e00c2c2c200100e4055800c0c2c240042c0c003c1d441951203100185200d580404d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 813078390 1250 813077140 813077189
    0x1b0114281106013c030b2205060a0b010215250809070308210f04060b0d030e0d030c06090c080f070602190c05031f1401030506190f1104 60
    0x34101c0344030921144c0c1c240b0103004540c80748800d50f031015504100002481302154034210000c805144035100200c0d2509000c07091228041d03c040a041d03601010041035400100081000c58010349500d001061200400e00180d00345800c504068000f004080104850140388450408043d00d180208a03074040200c0c400326034080c0212511039140d440507104000080da0700004021030201e580e075052844020071140600104151808220500c81c84103000030311113541f080818000d400c0701c0d04d00d1001210781e405842c42d0510300039148960303400000c003c145802542e201d9a1140c0c400e80c10004080a440c084820313503d20b02070400503100c1e80500c82c420703000000d01c4106071001a0010026006031510b000d40683c860242102d84507051080040d460320300700080c0f01102d8041d032403440101c680d8843c034003c403180040c4d80b0542d00500001040860740100b20240c2001001012035211080300c0a110003405521801120052600032101400300945014100f9100f00307601c840c0310720b420308a619 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 813079640 1250 813078390 813078403
    0x60a1401060f0203120c09030703050307060b01230f5d09010f020f0309060f160c0f0b10240206010611190f0b091b01142811 55
    0x40b409a80104038801040f40c00b0074985910441842140f4038040601c0013007420024180e004841030385c0089128000c0100380c0c0030f035080104d000e20b012115500e400803c0f40700c020000c1132104030003400041d40340246400a003120341841d40f50b215200075812661164a0711100c0080344000043d1403010b40908000183d0310303c0b6251094a00d0800d00c114521980c0660b13200541050040c2d0759038441c002e607091140c0040c181ca031548082684c1c0700d14040be52142805401049440484502c2e01044214601e05200100400591500e00a05503075864505081081400f001d0407402c228410401088801c01c900402c0c0c400540750040d5807110a00151141070300001c00c000982c1040006110251040e810030000d089404206d8212030640c1d00c0b1240b072075440e11010380f0130054003403161090002608503290800c08580c02080c100586000d9810441920390701d01d8100030920200d5060b00c842c0f071068030b44280b1056008556000c8060031700000031507101c01400400c2e02090070750514840030a01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 813080890 1250 813079640 813079667
    0x5030603010513202b0314030601050403031d2206090b0907181e0501030506010e03100b060904050a0207060b09070c0b130b0711070b070f0b0606040305060a140106 72
    0x10b0b1680303500c0d01813844c02d41071441c0d91903a04074002c100003c00c4030b06002000380c1740070030207442000649804e007402007a80b18080802c0e40500000c009201c1c1a9034031508550840350586000c1b01c905924800e000ca00c101c840301d0003540815500c814060806002c034500c4818504108200a10381d80e603643ca109a5284a1046a010740d1080001c2d00f05405203046c0200300d0304002140c5501500d5000324551080040c6111a0f1241402d03030070700041d40c06100c1c2d035402c041c00342056a03c0192500c0000d0307171145000e00c116043c40c4c40e440e88080725112a001c2c0d881040c0014004c2c4481c1c0380000410009400c030003402c2e6052400c0c01e042003824246000410b010f03a07400c2da41c20b120b5a860b03403100c0c1c0401201600a9050220000208001c00d113011001409144956102900140e0806609107402c80581102801c03440030405800003402c101c51702488103500c41c900d0006980c410f0300082d458001d560003d0424062407041102c0204140c0c41980848646460000966210ba408480b2811740345003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 813082140 1250 813080890 813080903
    0x18060a030e1903140a140a0807022e0c1b0f02040605150304030c0201021005010608070f020609031b1908030703060f052808190201030e010e03160318030305030603010513 75
    0x1125942c1c560800c00400e409542d5046c40c00b2200c011a82500440c2e1022924070b0000340d6410901007500d5050160740a0300d1403200850f1400284c404c014400c900000c800300003000e98648400081c18054859064100f00b4500c00d061000786e035041c050800044208100c1c0319034640800442c442c0740150962006195a01d04c160550745c955071b050700d40c417601420a07415845019801300d1340c1415805080e018010395992a956814060070103070611001d00d00c090299004102082500040081a1600341c100d1203030000d07407007a03485806170404030045201600d56180782c6240d02406214001507000b400703503903020442c641c0d8450a0b02085049401602e40c0640b109881548010100c03404803107914100d20804040707960b4500052404441d0400558918a90316414040d0343c1c0500c24109101c0c64880240101445000001d031039104000a44460003504441c0d4020305108600c82420034034645040100251a802c0280190300103c0b80c042c480c1d0f0800d00000d0072101c00f2000d8208482c1d00c001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 813083390 1250 813082140 813082157
    0x13030e19030b090f120d020906030103060209040e010b0310090309050402221d0a0c0e090403110f060f010e10081006050f06070f08090324060111070f06030218060a030e1903 76
    0x30032480c5e49a0220807540e2045c1d800348044030325562044002c600030762050100607030b110304000a210940e02404a0001540d2415400403030a440106019403e44044600010454110b1406481100d0f481e0445900a4404103803205039032050080c018255041c9241c03000c01517038071007617a03503c10000241458403860000c0804e04003da240c00c440d04202c81030031321105680c0d540000c40e200500454040e400103078090004050041d05000350040c3d180f548024150614010760311113120302c018440c1c0550301200300300051140c031a40c40d4081c00340c014201034503c00b10543e80003c014042a000e900c2c407071000c401001c3d201c8d19060044464031540000300089020041d2515001900200941601409904084203804400500640c000d907000740b0b1201103800c01e00c0c001070403400c04814240340e41d44940780a200e0301c22a4020141181e5803841c026a807110a01b582040d1400092000381d0400c0c070100700f00f034000b42c16030804001402848c0890b07038a171080c41c10f0900728803140c02003d13001c1013106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 813084640 1250 813083390 813083413
    0x307050f1e120a03110703020703030f0c1707060b030709090219150e010201060f0603051f030b130203070e090c090f0105130f020903030304080c010507031413030e19030b090f 77
    0x2e80140c008000386044c002a00c4200e03c242c203070650300c00c00d02200141c200327401c00d104054204100c030b0701554071440d00e0301200c01155110300d0910100b01c0300010460001c68503808111442e003000344442c1e40503041d5034540c0d5440001c0000360166103012441500302200550240d0000b010640483e6901204100e100d06d031542d007034510042c15072265046540b81c080214100150000313a20003003581740c0c2c0000782071416021200b41c03000e00c0300d20101280c402d46420804142c00c05c2215070002408903001d4240b03496440000d180c21340c2d0794800802400070342c04200c0090004126181d080c50161421241581c4246900f82e02e1074090003002d0744107203502041400d400083c0d0002e5071a40c4134180051400d07080000003403450700304990440e4450000500889603842c203025071030b00044541014421400308621a49000c84010f01c0c85581c141e03241440424984626401c0d100c00d14050140501d843c01c2c0d0110f1007e540781d03030100381c84c0402d003003020078080f460005175440c080702c07064050312090b00e18 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 813085890 1250 813084640 813084673
    0x8011103060609041505060c150a020702090106140409050408041e061e0903171e0c0a02041a09010611070608010f030821010b1c0b0a05060d0e0307050f1e 68
    0x20300c0170007100560080e030200e80c1d622950020442036403881c0c02492062445405c421035920010b0502162900511100e4010780300d0440300c50654401741851940c01c81c1907806041c070b5000d01d5210441b0305080030240018014500002c0c020341c1c44500e821132018159070010603040700c25120300800580103200001c80e000e08000c1d04160081c00c7e00d40f282e031166584d11f0301840140501d83c003a44042002544224005910b480000c41580e04aa000e0030003081c9203e01f5140c180040003c4d001d5500c0f0300c6d650340072030f04031200c111040000a0150400b941c450300001c2a403592018004201d02c0340c1c08011403200e001d010030340c3c1255080e1141c06075940c00c6030764068450b00120200d1074036810092891101c1310041601e0ba001c3e041c400b0110307454107126100640070070003480e448041d243ca0400f44a0b11502d07903c1100082c1da10039605c99540b039400b44400c0004003080c814500b414000031408504002c0d0100c0d500304950304480481c1c42c022240c509400608104a8180350b80c1c0e48403082d5504014007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 813087140 1250 813085890 813085901
    0x6091003020d110d0501050a05180c09010c1a01051903051b211606050a120e030904090f060b100f120612030201090311030406020d0e06090a08070801110306060904 72
    0x1a009400b00da4062212031042c4160001e40c00119485d445900503c000c2c188807102c1d10040804444c4c400001120340c03809210b4080180c00d00d40705000c001380440c4564061104825103640c4055490010000000c0c2c031001321b907007809220701c560140c02d880c071111940704da070860540784c1102c090504109000905040300f00d0349d009998104105c0d100c0103039032401d0081490043c25076680584186801645103006183c043e40008041c80005c2c008180f05a6101b0080b4601e0320300d8000c00118070154090703051541c0a00e0345120790150400c40b040040103550402001c03050321600c000d11440c02d5140410010010400c99000021001c200c4140194031520328107010000b0710340001038594845c079590700e018100c00c1d403c1d40940c0d11098400201a441041c80b202c0e0450343c800742d8105414a28001d489441c01c070690003c01820b65610001a82d030740044808035000185852003450fa07401c945138403011640b044290710751901c1c0030f0111440c0408200e9128800041c0361070314051170300080200904 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 813088390 1250 813087140 813087157
    0x702010c050418051306050f180102040e010b0309100509280308060d080d090605061011191a0106030603030807030b0603040f030302120405060a06050303090603071103070807061a0609100302 84
    0x103441c60005c80441c440c3e1103001d0245000c2c9200c1300103442d214481d5025071040d00e048600c2c9a10401c002c20542c404603040c20305480c2400030560350f03a01e0f0b03403141c01c0c6440082d4881c400c9182c076140500c02c5030680000c0c00e120f1200800c602c48200c0302c1c402c445848001000d0b00c058082401c0304005900b07450012004080305102da1281420080303040741d56022039004550882e010b503078860070b11100e032410201c1318850380c049240107040060402035081d12000740411f0301c0705159903001e15000b0840340e0b203075000d40e5051424005c03000750381d111402006030106100603400309040c0d40224010700e210340601055004080d015510b162100c0d55a42102ca03c03450003034041541c01e00586802500d00d00d80e0381e00880c018030040c00c40341042c0380e0810440341b003544007a129900800c60141e040d00d0700410f50361f0101070b90070b142d0711034620491040d0130761081c244001c185010014001c030400403950300c0782c01200302091130117002200003130a002e100d2040c0c001041d031020302c0c11505800030384260018072110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 813089640 1250 813088390 813088411
    0x90b0303040e010605030609060d051b0402071a0a060b04150e0a030629030f062706040510060b042403060f32060301060f14040602060702010c05041805 67
    0x682d10405019416420f0b00003000288000040c400b507442c00c0003080340c01c501e0480b580413040d03200345d0b19140d60f0501080c0f10b0487c0e408200750703912581c4e039550503104a560031910044904003490028003440b0003c4440040941c542900415000e00794400d50301940c018909242e820704802e24281d40400e1200c0000b54000d03050b14006c0000f8070319004202001c282092090600c6070002c01c562200922103000a009074018038036052410000550f0350b40100740035460381c081e0700c2410b0010b41c8224a1000700b103410f00c100811302040050000340d101980403190020490315841d1031010041e88070b83d01c03a501d0803120031403001e40030050301c4400000446240c2800503071650781e404a02c000048960150302e2600000c6001c5560301700190301440b0003040c1c120007030415441c002c002030f070a00040c040e100820920784c0345d0403403850040d8030f0180c1200340e00d9015601c2d603641d000d00955032801200c2c4d440055090400140915000e0415102601c3c40318407540307000322600002400608005100c90b410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 813090890 1250 813089640 813089647
    0x1090f0807080d0f0b030706030c0c030c0609022e02010b10030231050319020604030b0408090312071b0312140f040b031f0f0b0901030b030115080d03060807090b0303 73
    0x3411000d1140d810f038004e81e4200400c0321442d2401b050b041c4940c6500c02014141005550f9103400d501c9000c0c0701500d903050030a52400ca010782040402000e405038001e400203000030100804036041d250440b150703091008020101501000c04030700360303030300c00c1c40e0b0310703000081d02c4110b45000340a03402804113045600d8240e80010113203031060340e08008803025403802c0e40da001030610460a0078460071717016800400202504a2a95002c110244a54800502501d0b6020082030400445004443c001c2d04000c0895036003c1500e40d40c2c501a0303100c234204072444042d403000f0b60021490b507000181120f8004541020030071107403c060700c880044200c4c80d40344143c01c11040a00b50000c0004d0006005451000c640720f107012000b034040c40780520309020340e94000c000108181c0c00604071410540b1f590070350080c0c49101000068005d0310070b000341c2c5503041d42403001d40500d034031242c03070b808084543c40e0003254094803a000c0250101c0b150350040c00c1071508549014000320740c142e00701849029028003142d26 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 813092140 1250 813090890 813090907
    0x30b01060e240c1014150a030f03051b0d02101d0619050702030f07030c0201050906030f16030c08012c01090c090b0918040c05041802040e01090f080708 67
    0x162074902c074040300310a6000c202c00850380020450229010381611080007a044581303203840e2840e0000740340810b003901c0081e405056845408031800103591020503a28825074518000c0c14540009165849841c4900051b50701180006140348040200d50098001440034070180d10140c0346035484070441891101020400740d00402c0101d05c0369446c0301200c44081820345010046c6c8001408030400c6510610001c00040e00a4045a50035585400c10190075a810b10040e40d030350040c0030318540c0c8448040200181d50708415442c511a580c0b0124900814040d20415811188825041d10000398880d0050204030340070610108070a520034420513003c03c0d2101d031805141c42c00d80184884c941c0ba029000320355038101101c0c0025019a040f441d0800c07005e000810611064003103030064010840c9d020500f84150354407482e001c1c1401900510249400c480c9803880710104203001ca010741d19142c80c3c031600c940c040c03182120071544007020703c80f030450319294034200c0e07003002c0001e450a0004001494 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 813093390 1250 813092140 813092179
    0x41115070f1410050a2a030e070f090902030105090d12020304050304030b04030f080c0901141e0d14150303120705121e070c0b06060a030b04020d140a0204030b01060e 73
    0x2003d11843d50f40101d210b1420011000986481214107a0801104205c1a003082d01207071241c3e49a1110b8a400614058011042860401d4940c403102600c9000c54020031210b045030071070384011b030003a07000313208035100d015405680380c403072881c020006580b07914260541c511a030001d640103801031045a0809850307844101a8040c01e8508074003143d408890340400c2900710340b580c4d50020200c07114604140c44030700040c04801a200c4174245450b0001581e0ba0712103485146802c660741441e080b03e8a03110251841c50003480311010310110b85c09004002000d0851031502c03042c0d00c00f00500650300300701c0c1690045040c101c014114200307006040c4006403032014490090303885400000741c07107420300c4c152254940210700c002d400202085154044640800c24151142d50003140c01c0c1c88030765a40c2c0e5500b10480c01020b0032941603030b102c2c0c00081c041d900c03d001c1c0d4000e01c04011a0400031085511140503507804c070302c614400100b003540d40400411482d03000354009501644041c203104070903d561909135 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 813094640 1250 813093390 813093403
    0x182c0c09010e060706182303070204020a030e0d030c020c03010e10020702150c010c0e030d022a09010b13171504020a183303020d060e060c03041115070f14 68
    0x710f40d44617003080750005000e200120403e0b440b0452000010091b47e96905a45a224040b030190003580c0003c0d184030154403d621115403481c0d00e10039240c02c000c0c3c14030000c0107040005460740051180d402d1200c050f15042c4190403d88400400030045440300b1058071005e0342018000340c2e401700c4009038011a0042a6004040402000000240c1c6014001c07000d044010b0003000305010707601400b01c584185400141081c8100000000c8041d039040410031000c144001e0607030f10360000c054100004680640501420046080c1564441c0e0039845400d03600d40c0d03041094000480303034055281202c050f00c8050202d0780150001c0c0640c101d2035282c1d4401d1f48003031840703039001c45000e40c0c6202c00707815101020f031004e107000040564103211100d600c1d01c0e15440c01113400080c0c03141c00d826800300100801a402403d541c2c0b044001c0d208a07281030072440c81150402c0741c040e12000c090080030115841d040d9003601b0311402100025040642c0783e201c0e00c2050352958000c6610107024130580343d2132501042807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 813095890 1250 813094640 813094661
    0x30e0a050f060106080103201309110319020904060c030f0908070215030907090e010e06040506070e2706010207081b0112200703182c0c09010e060706 66
    0x4144001c8031000a074a0b09030144d02410410800c0d01c01400014102000c1c00c845580e041c1c0c80100007000b940000f000d80e10300c00140c10130240b03005020001c004000c50b200c400114100d041d80c80c500002c05028042c2110000b0096100e0b042d0000100060207640c40b4100d652124600001c01030032203200c210440740f00410540e03801c01c0c082075400031403400840d40800c00851a03441070560034070070401552034450340907030402c094031101c651146040940c00b02d404c891003102201c010f810281032080e00d800c000d64602001400f00d0456440a08020080c005005c001a40c0070024141c403c0c1603107940c2d54085c2809046008420000490b50000c01a00e189012440c201e20800a00280054040c10076030b030b4145116420420b452950310183c4402401550a201180350f5411301464200e0710300440043d80e0010310364141c2c010230407100540c140c0c81b0300c43c03208002181c1d4035401d01c3c200e985100100e6030749000078020000d909065204a48002c041540945068102025a51a1415104180d48 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 813097140 1250 813095890 813095893
    0xf020d170426010603031b0302030918060306090a0c050411090d05101d030405010302030417040308190c0c05010516060e01091110050306010c0c03060c08040c090b01090510030e0a05 80
    0x241050540350800302c1001c28040000300f088618664001e04842c401f00b0326011000c82541031482418020300c00c481161f440103018032404d40840c0c411a01480003680c405000c4e20035080083c0781000009190803010b82c01038290200c0c01c1c40c0200b007002030401c90010f103401c4e40086c060310a06842c0c54140088851041014229117090885540304a0319080145110500301103400d40744410301000310780644100b1710740540c1e02d540300d00b03081031001424410280240c400140000903c03104002616241410400d51120f401030458100c50303503401002c01402c0c60700000d9003085203600850081605520003201084032485d01d88800c0101c624030030310040183d44407856a005c10070380304d902c00c044403070840300c090120701c440100520300c0c003000305524188041104100c3c240400010f1950086520100500c4801c3c451a0300516a4006403000c4036100803480001c20480c040340145005402c06954140e2141e290604014105400801d004141940d44028001c000710a00180162902030f40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 813098390 1250 813097140 813097169
    0x6021215010c030824120313050f0310050934080303010608010b030603010912170f06030a06090219030309060801062d0905030706030b1c0f020d1704 66
    0x3200610022054141046081006000002d400c94001e90300001c8640144d40498007024035200040000307180c107a032005005100301207441000000342120b0030100d40070301d9410740c0c40042c009040b529007015641900b1005403285140c203070f6030195130300642c600200c07040c2600c819285912060085200d075098507803504414090160f2254100007043c0840065103076600d0000700824911060042504c414000800300d10580d43c00d4002010707240c0c01100200c0782804003800076110000140070f10401890420019007000e401600d030380e2046601030003810324543c85540d407100820680b102280d2004829200d0017001080024503030107148283c842c560524281880901107140503849901005034511007001c0b80c0c004e4403a906a600c1c00328840860810302c207001900c04203101d402c11034240c4036274440024501d5040c1c0290034006003d0384d00c60410041ca007401840c0b054079003000b03409442008881c5006007402032001c240680103e86000c14940c611145440b154001d6014104c000e0104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 813099640 1250 813098390 813098401
    0x1104080a05010b09070903021c0602120f150604060c06110d09020102100911090a1e23040b061c080403050d0e300115030503130b0307052203060212 65
    0x74803c442070000d04603424180da00e01804020484002408002d0040d403c0901c010200c5a41c03450480ea070a81c440415504c4d001d25440450140328111a100500b0790301c540031400d69200c0b08c200d01e415807c09407605150030b04000056a540313144400032250180c1e100300b40d42403200c0c1c03040030b881a01c00042d00802e401c1d11740d0000900c0d04082842c0e00059a1502007a040000d20044030b04005040545900b450b90741c078692440e00410102c1344030041206c900001e0b03104040300e45e00040e03001900848242001c81040c5072040c50b00c00071100100804601c41c0841c0b007924108041c1c0d05002c82e124171908100307200e541e4084858001d40d01c210342c50340c04888804545500700400c6840441c2c01e031502c84c0540c54031140100d108103c0758410649030740c00140003544030b500390002034031094030304c0ca03c010550b1b07a40380445d5030f076019130640030032250380b101c0101e60030840d0802c072401142d15039991828004981040840e00c500c14202c0c40004010000010001d40c0b9030000e007280303070f4000c00004103a1809 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 813100890 1250 813099640 813099643
    0x11503030311190c1104051302010206010801141906180b0114030f0f06010504050d080304050607030209010f0e0a050a03030314060402092b081b0c0a0513020705011104080a05 77
    0x5020b500300915405001404501c442500000100000341c0b901d10340341002400d00000e01c500004100750028240000c02120741d04885501011600c01c1e821100541c8e038541e42c1600300d0320301640d00b8414404030700118402090500925048c125a18000210140e640c070b40701c2c019846135411145070710303180c101422807581c10008001c0d624803017403941851850010541748203500d008144442d60079540300820100d920550542e4084c00d80540440c080c01ca5905203100d40b034004840444144c440d00e00010b1000748a8000d0380c41054060311030302034401b034111050340e808902d290419008060311200080694485400500850180d02c00182d0f090200040c030034a400003d084a0080d40100712070b00441c4c0314019030350011050043e482000e1141007540d410b01020700c11018150b91008992a00820005019001650781044c1201e032601030402c1800b001c0103c5d80704081d84803000840c0081d20101c00e40060881a114100001e42d2103408844406140c2007074020040c158004400103041000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 813102140 1250 813100890 813100901
    0x30408151b0a08040303021602030f010207170a021914010c0c050d08040c06030f0f0e0d09080d120515030f07050301060b1215030f0a0813050f0d03030b0a080115030303 74
    0x207084110502e802c5540d88041c00b0110041c100400b05a0300089026082d40e1000e00d000a1981c02010744040ca0782400f9007601075003003841c09694691441100507003c0042d90f040b50b03050185a00641500912200d81d50b07801da00703000c002c1e5a211100041d080d030540f0288212542c464407034980060007026401d20301d1601090711500760a0141f500c003800301090b001b1f280201120213038a004620b20340c04105100c00381c18407a480505482c02c0040c4695521004920b240d8022440e40d50341c100c09959204103640c5042c4182d40c02d000c10500314910300285031640065500030005ca40c1c6501c038812420200e403405009040e24240c1e5042807030148500d203000c3c01307418000d11001604505207030100d401007401c050068905c00c6028440d1000c00310a403070a1040707050b1840c582041d203a071a4010304124040d07501c42c0c800281031407043c4070049268035080100310381031400031705140e2088200d50340c1507004028049070742c1c1c3c1c40304944900043c440801d000385420f045e44952100c0340185941380140070390300b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 813103390 1250 813102140 813102181
    0x30c090501032016020a030804210f12031b0906020105330a050607081804020f122a040317041d1b1b060c0c030d090503040815 56
    0x14144004881070540a5600c59a5880841d80d004da8a29107440e101c05406800d110094104c1152480007040c0700d1803001410407103c400b040c4031402003a000386a54519080d010041c0729030010000100030a4034090b0f01401e9002c03a00300081d04154000c0f88803603904405030030600052800c5024400c10b80d080c0603180d0032000684110110714074100d010800b11010481c1b0406450480031201d80c56580c442007000103050141c0556510360b2b03141080440350748548e00b004003500d03180d81454a00d06040c4200c41040115041050030310340d21400c0301e10382c402d01624560b0513695180728012036048444040c20070001d804881a5154550310304003112014585540c00030400034402003101740d50a00c402e4086030410a00490a40d595100e01802403410300d4420f651a00007007015800502c0800b8403910402040c3c0444030a96034a48000603540b0039141d110071150024000400c3c000d030207802c0b0480311407050040d2401c182d02e80d40f01e10315000404e0340402c245120202886201841030604200c501d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 813104640 1250 813103390 813103397
    0xf0a0312030f15121505070206100e0f0601051e16051c08010b2b02071103060118111209010c17090a1103030d0603060c14040e0f060d05030703030c090501 68
    0xf120316200e125044140b10b08050300052900c10402c00800c0990501d010010354410016420b002c0c600940c0c0340c00449003288042e80c103003c08903a80a000c2c10080c4203803109951651150b690400440f02a08000c0a0000640c049411440503c03c03940180c042e190042d101408801c5007414443e280c111039402100903a056000c0c1d0100c0c880d031001200303042d81c18411000d917541c030f00d0000045c1801f104001c0001174000c985045407002d045a0010320441d0b01072065081495002d60815840362000c1c07041150490345441051801000d13078111082c83c118011041b400d00d1004414007102c0b007400c4680c460b859540311000007200750003080401c401d19020070540e80794548103915682d100c4040102030301c81d101c6542501850340e420000c5845100b40f120307060140503903d2820101604051404002280308001d01304500c000c1c0c10700ba5011900c034a001085552034048801d0f86001020f130145400001007069100800c104000912805110366000203c50486c0e4000404101c400d4000f40e041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 813105890 1250 813104640 813104651
    0x10b130b12060609011b1203111801030f020d36030e0904020a15021f090c0e0702010212040f2105071713080c04050603010c0207140f0a0312030f 64
    0x440c4890364a4030751100c07040c1c541607070b11320061005860006515040402c81101e80c05000d0400400c0c09051181c0700154a0034050f04c0301c5211700c1c00b224080c07008c9503c0070941c81000342c03800d0341c401d0304140c0e403601c4000801481c00d429035440400307440c1c070718100c01c0c0500040700038103103c1d195840d46d00401e407420b8040f088555055607001808250010081841040341601007420741da1600e52030300040c00c50500060300c4541040c0040d4032441d15540e01098a440c5680343d1022040d80e00400d524140c2c011755034807815080002d40c4501078006000001150360034840b081c00b00d110a042c0e5401036000b0501c1c1503c12400e403800100a6501a40c03408180351069052175600d5004402c0d04d90305580515014140050a001031000b4000c100d801c910302120240001000310b00030500c940c12070b9099505014a0b039640d4181426140000c00410040e400f0940420110030f00d0900c0305818900184546112481003000030b10b24100c0340c0081d5403000a220045110f56050b02c11013405040141040c8403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 813107140 1250 813105890 813105907
    0xa02160501032f0d0203090105090c04051b0304050106050a0816120f020603070c05060c09120c010207150c0602120603010f1a13020c010c09030c081b040e0c030105010b130b 76
    0x80050f9451402d16424100955030709500d84660306541c0603809000b401c64a915080107114080c000580780807000e4020800b030800d071401c05028a5106c0c101e4001c3c1ca0130091032a4000415552000b00152000e559070800442e0990b1039815105c018004d2600400001103020562079482c40154401100985040a0240000c00c0d00341c451350441c4e01103c2c0203440e070750380d6407058032443c8a1180c010900d01691040001c8005180094a9141400c0d5040d071080b21380c00c00c40d9030351202d100b051640981d01c6010104140d41e175003e0311404580540c64030344e0101d03400c3d90300e01d0203981020070340030300380c503001c10400456040c01d20400d6150300d034084090000c2ca4103008001e500441400b0f40d503001d07400599010718060f10382d0301140c003955084402040707001480007004000000a001c11a05240c10308000205060001020441500c96003000015400707a4401c03c80141010aa454003900480d060030b00c142c0c0e828440c6600030041022496138403c1c030750ba91909000781c1038201543d040c0d030901c045071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 813108390 1250 813107140 813107171
    0x40f150c020606060c010e070e190225050f0d02031215010c080d090c1203140f0a1b020d0317090a0519020d0b091b010e0913080f0a0216050103 63
    0xa803c5a4155401a620704142e0840c9000d8034a1180100091040c00c400003480e0340d1280f0780b41e204800740c01908031341030701d02c41c2e9810580c8102c1c02113000f00340c203c500c2c451803000c503117244d000c402c2d220b00f00b03d5a11038940c9100d5800c0c46107581143d03003d42c00201f01da619640d1451a029440302038108403135201d002010004e414030790884809402c903480828140c2e8044d0056100301c9005410110010420b540c801c41c420400c45054412800100d4040011281804031025950400c0b0403001890600c204800211492011404414034a41d460318441e409038481d034a085017901e00aa03544800301401801441a03400003416902050b40701d5541e810202e000407401d0718074140440c01001d0300c84101c0c000180d581d03079070340d0018143c161584141b003a800310004041580700c07080007002c440c0180d10801520f114071007112444e001800da4000035002c804078006001c0940c4101e24082c1402e005c184050307132270f03044048030502592000c050314132001821403006000b8202440c3c14050b0000020504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 813109640 1250 813108390 813108403
    0x61d07110f03070c03120503070804110102010609020705030a08070e030d030e01200a0801050405060a212f031b1207050301150e0906060303040b0f12040f150c02 71
    0x20420000035600000344205100d424807a01001044a8441c10381e0f003000c80816440f8481290100d2581c041400554041c80584e48140c0d4030f034a0b0b0317240c2680e803074440448052301c0c9116107045568918001c80c814240d840a0941103000301c0081d03440324801480a81040405000f00d818820201c0c5d200701296070000d1898040f81880c40c0100f00180a034440d9405000109004140080c0b00c130941444a08498040c0c4080340490740c48035020b90380c1d1003d010803104c083e82c800b034006269900900910000801c20501c40d019458050800030035901c401e40f16851080e42000e4a65603403051040c41c0100940501441200724094044552002010342030314801d080f130780e40070340b014042c4030b00002d4050003940000c2c440a03009004040301c10717402c0c401038040c50161b80307602540300f000b2940d0241d0008078644504030180003507182c00c1c00c0c40c001103025006500c01e00c0603a4010860541c5565443c080d2500451140074039151480e0710f0300d091004280503040752a4594904084840100d90014a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 813110890 1250 813109640 813109651
    0x14030c1b031b130e070b0301030308070206011e1512050406021305011107060e030709021828060503130507030b01060f1d0f0111030a0e100207060c020405220b0703061d 74
    0x761382c41d05000c4040c00d00345580c0c0a0380c41c2c2c2c81d01000010500d500460001c0c401c16107603080d14a56a03c9600031071044400c0440d480520282d06001e000c80c0420700540060542d080c20011072400c007620080044d01d808603030488120760041406003603105105800006001d0900b004c02000100d42c80c45d80e0b032034601d8401c0b04d0070007242850a66858400b804640080c0a4100d4107554030f0ac18424417030148c0c221664440e01800804040700d0448507103203010700e481c0e400d480205600390700e404000c80f5a500702600e080d500300e904506400004e00c0801c00280254851103000540390f14050000d044188141401424424401030b01c0d20208038851201a21501c100ca4120f000c104060049403070043e40d1040982d1440001005446241c0148425080d40360032205507908581e054001c0340c032540ea902c100310205002000701401441c084d080f440c1d0104810004086507542d020008801050002058900c6808801070164042e4180110409446580004078140074500c04180b9281b600508 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 813112140 1250 813110890 813110929
    0x40f0c080105031f0b0a2d0e0606030f07090f0f0305100510061202120103050109020f0a0f180207050102070c060e030a0305030106030e0f120d062114030c1b031b 71
    0x83d0003560340c2c0c41d0381000c0603042408090300c58407d42c20030fa040450196441071850a40c804001815580e051089403041e94082c10040c1152601001d01c0560000500b01c0301c00c2c4009442e000c5044401d2110050061100095800d42da5203141489800c000d080015218541e0404082210310342821503074100329042e6182405110341d004001d103000f400780c038400c0008076102074000000c0c02015080892020300032070791a0f1001041e8810030a052210b8400c000728a051068100030220700b1400301080070510780c0000d03203041e50f00d5403020708a0b440749001302c03401c4055003000d10005600c4010051610000d4004140c40c41729610003400500051280a00b0503440d242c20000c03060040c00a804000781c100c04450403c02d005c1d611955603000300e46030606080c030b05800007604522114909429040c415580741403114951100815000c0f80005180d5030720007005203d0b500c000030000e5a06803503005004610400d484000c2506001d00d250140140c000100955045035a8030744c0c403500300124240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 813113390 1250 813112140 813112151
    0x3020a0302150d11030601020c090402210703060903090e0703020405060316120f02040627051512010806010f0501300603050102160b100b0f03070e040f0c080105031f 73
    0xc0c50450346100d001001c003803035400c001c2c04c4820191444003850082c0320076029105143c1c0040b0900840c071404842c0690301500ca00c1040030701080e8070341800d080b0030541090ba94803a480740c48003c15111210005c40004101d0041003100b4480c68001a0300b060300f9190562500b45040000317200e40c0800380030f42001c25080c021080c1000e000d00250303000c884000100740100310030b00c010480250040d21840d400b00301403041c01e1101c40700003281c050304200f5586403102001e02b002d092040d1481c441980201e502c0040100d450313038100ea007118034002c1c040070b8002d00441d8184a5908141c11403540041d041c80f80100e00020b41909503003d164200c1210583c200c00f000f4040340c1c05000c0c03c8140c2c0060419403000800d003025003d04070314460f4490080c030007034041e901d549204c4004100310784100103600d001440f0010f2004d800c079000316040045480c010140e8a05500094101d50044002d01556170381d80882001454100c2446801400200d01174401385014112007240c070804005641807080e900c0c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 813114640 1250 813113390 813113419
    0x3030f050a05041d010905060d051203091f09020f041406042c1518061302010c02121c0f0f1b08130f1505160309030803190b030703020a0302 62
    0x1003083c0c40081c0702c0020f1000101c4940c041c0500f00c0700d828010f403800d460502d4009216814200d4411031f80700e52120003400c48100140d0855065007014008442c1402900789042c03502c0b1900381c117a0741c1d20030580c000040050581c0f041000c0340343c5003003c130b42c092810032003c16520038402003d2039110704107480104400310400780c01c191007101d415030303042010200c10300c0c0301640a000a905c9011040041281c500d81c845440c0d00311840500042031075243e105000051042a024441d0602c1c00c0c03060400e10803020555001402c0c0d0540300c0c62a1009601030582c030030b000f06201002e4a2440c4480c20800340200894030003d00c10948000403405000c40b1040c55100d0b181100c4003000c5c443d40001c94244c841f0070025440000003503071301c81c145111409800101d80c641d0035640035071541d400e030317165185040624480c00c844a04001419418481060400004600c00100440c8644440f4943d14607400f03042e45144100c5010660550281c2e01c242001c0c00182c403020040c03001d5a404498440404424 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 813115890 1250 813114640 813114647
    0x315040b090c010e28080303012d0b0301180603021f0e040c0905010c02060f121b0306061e0c0715021b030d030908130f0603061409040b0603011d06070e0a03030f050a 73
    0xd684038546c584000000081c034500820f681100e8181004065039030303642e030303500c00d45852a031034040c07818642c0c42000100304d220324000302d1a80c90640b10b50041076460f42d03070300040c403440849102030522002c0d0f03400740d81c0c420b58840403600d48403400700c0d401c101181c1d0120005000c50303c1405881d0500c81c20080e40010342d0341d84401d59804e040048d41c61556030000d010304041d05407080d21861030040c81240c1c0304a01c0c0b0703c4031055074840e01015000e10300b0300065032081c0001100c410824041030701300308440300d07a1100038482c8001408803440407103007500e816000289401c0c58001030207450042c5070005602585c0c085900301c80c0348614503000c00d202d400390405101c9445080089410400d84120000d070b20000f04120008403003a42c1c0307040080b66a11508210310b96802c0902c41d030f00c847d50000090000d2004048a07810587c0980002401c106505034400042c081c00e4040c6060382c40380b8100140c05a100108081d209020349096041030b29654000d0084501c0d51503c41c00c0c00800301d0880b000920 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 813117140 1250 813115890 813115969
    0x302090901141510050a1202090604030210020607090b07020102100c0516050706031b0c03030f0e160e010f08030d0905011e050403030c0e031b0315040b090c010e 71
    0x1000c2d1580d0703a050900d40c803400aa2864600500d02949404003100b030024003500940d1034045041e10b440044d4201c0c003040c0c10007940044440c5a00100601c00400580c5817060422801802500105110b080c07010001d41507201551110304556400c00881c00142d0303000c600d01c504030105580c0070600802040c4255950302030321142200c103ca1044079042400000544030040381c0454500f00035411001040303144450240c815400810518124400028440e612140d0310030612080001d08a441603001da051116a0221480400500000340484c0c40d40011442c014070084101810700b500d003071601038680c05541c00c1c4450040d5a03060580502c0401e40202d48100711808001c070b20510440d28a000404055070103900291501a42512107070043c0d12032100303054010000c0c420b128030031f1844074000c081e08414a0701801503e40014030140a000690702440c4513003410a80c07454194503051600661442c503d04100d202421400c20792295445131900101010480c054008040340405011b10b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 813118390 1250 813117140 813117161
    0x4050f0a030206070b0414070f0501110a23010e0706020a0b040c09050103150c090b2b0e0c2404030204020906072004140906220f06141305070302090901 67
    0x40090400000c17030035007846584101c10440505521184947c1d903800e007402900d913909d892050500c00356002e070201c00303d4844180c086841d0400e255441c01c40901000c3c45101d0803102070804101103060038068414103484040007040400d203003600c0203690708141c0d00c01a10340040800410107103c40c42c24000c02030120004184043e513500c0c0b0b480008884141e0060b09018940f1a2a05440784203460800454404060503403e20316503112003003e0300034009900c82c510b1145810096101c0c02c03401450722456401d0080c001c201c01700d03c04d1050500c90040740c8103158000c44514030242d031102055405507601070b40c0040e103441c040b8021130881e00c0740b540040c0046004444864041340001d5034508403410a982c14050100185c108441c07052080e18908e54a8001d07800144804c80000302c0f120710082900594240d04905480f020b502d041404810b4680903100d2035000307600001100c2264109841c1c040005841800e81c1360592100320380d000082c85140b6001c0481c203040801d410509545 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 813119640 1250 813118390 813118399
    0xe0a0503030702070e010902090a06030f090204090f0c06020f060c0a1116080d051206091b0f18010c120c0c090204080a02040b091e1308030406021314010504050f0a0302 74
    0x900344075034041e42d984074510440c2d45403070142d0001f142281c024003d46088042c05407140c01703042d05015044d030142c81e0041540001d940d0310050000035030782c0d500a0350304050103201140c0d0b00748103505220242c100b103500b10409540c0400420600c007800000c1c0580e000c0d2083d003405440c3d0204940c220750550001840c008075114120742c440221b01e180110b0030499045804039030b0752400e42070b030075601350190070011a0060520000184281081200c0982c4900016044001044c41d4a18400150485511030401c0300000c00d003140401d688000e001c10320802400d12040514066072a80f20b000f40c026443c078100003001440f0300400500041d05005050191000c5d5200d64440c1c0c800395903910060750683c440c2d07051414200241c1400e046032400741c0741a0b40c181030001403c200030655208060040c0443d544e800c41100007040740d04e0051406188640005030340d44070000070504851105400100c680110002c800480342c0c0c100b012982150000d031100344094204074000741080c01320340e2029402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 813120890 1250 813119640 813119647
    0x2b080a1404060f020708070b040b18030106080a15051312030e01060801020a030f1a0907020c061911391f090e0408030402040f0b12071406120106030e0a0503 69
    0x15250440103c2e03d0540b0359500700d4451343c0d503d910075941c0e40384074800e10180c4141004180035510001d4010050307078000c0f968056403121040301182c21a142c036408840e141d0000c03881c40d420440e48040380b480302c800307040040c450760a01000e500b00001d03404100605125000c800c0408085c000d40200a680901d600200503c0c0c0c0d0703801a490107580985d5143c40000e24006a46000070128820405020724030040700c1d9001248109105803864040d080d8000c7d0322031542e01c90050380d290704c000c0c90401c1c1d9034464005441000c0c0340207000404054011409a00018042d817561402d003c0480e425902e01c598184118450038540c0c0c80c0c074100700460300d070000c8001c02d105583c505910403001107075419980e40003541d41c1ea01802c100d00f2000faa4000c00c011010000704015140c80d81040315680c8504400003074290809000a046103401c00105100350008103080041011000508408450503180c45107051403803100903103403410501070142459031301c416544c00b02600b00080920b040d0305c0b10803a0799 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 813122140 1250 813120890 813120899
    0xb0403180806011809050a0f030507150e0a1e02090a0c0206101a1c0e0715030b0303040312090f0902120703090b072003182b080a1404 59
    0xa0310032206060a803940e0a00c100046007040000c02c14100c0300c841071010856494905500c02801c25100251498492460600702140500040f1003555110740ca0307140d03442c2c50611300000c40140707414510054914180c5544024400800c144000560080546000400d294940180c0072200c00010350440209000c0100041d81c40c0c3c0651103c9045400f112187c1d0744404120644c90f40714010520480300030754040c917410012801030181c044010400c503d140b01056101c038112003d150a1410f0381e0b01c508020803640520500003031001d111480c0c18001c0c0a154404a5a40c0c0700310b100080c45119100c500d058000d200c3c0c424a0003170289180d00d5a0302e05c0e52407801c00d0113500b00b0222860140540d5000c03525880c003d200e10f051b101d6001200d04100c1e59203880c252501d500d1100c1c283c00303100300f101510004c40d0051004040c000d0700e6040c640400551002842000601411004000c070811031491045a21503c4070340703042075226462030364590440400319404800039080e1a55444081800728 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 813123390 1250 813122140 813122147
    0xd020306182811040b10081b0a0518040204051e0609030607090e0f06090703021608163f030e030703080103051501062001020c0a062405150a020a0b0403 67
    0x18100f03020b091000c85040d0800300b000202d9030400c0702e00303600c0a840c038207851440c0c1c069803000d540b04c03174407540e1003501c0355200c0801c0526911a03401e10700082e60000710340d0b410540b03503006c614110000b90307411401c040c2810045081c0090310704503a0740d80007019a18030310a5032040200c075400200a016030301c003030038078500140c9040d00e02e0180e070f00c400d100b01000071003450440b08071610a82f4010f100c6002605d903824142e0080d40003250300b40d540a07a1060350000315804030000c09540c0754900515144508604001d4072610030002d0400018140c03004117646151111b10301049422071400e441c007903001803003040d002401e8802d601d6074a4003021411100b8540c211001c14101d90052083d116080441d20014010302001d00640c4003213000b02d072803c0c0303928407241001484201040f00042c548030401240c10715264054608031031603a25802014804a41c6004803402a43c0810b840c07000c050a040c0014000304c042c0f01058070070280410302001c154800c01c403100340b580c1c10410f12413241c246401c005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 813124640 1250 813123390 813123463
    0x307050f13030605100b09010e040513050d120606030605030a110d1509030917210c011d0f070f05041512140f070503150907031401060f050d02030618 66
    0x100140f201c0100006d81c5548003821510240c005965840d103144100307041000820000c1c180407040ea4070003d180c0300040040043d61103000b40e540b00c010001c45410500c0c82520119002031080505148042105440004210800c01e60101c000c20145200d0404103112160070311010700207030f880d41050f200a4001c0c2d406005e50f540a5a00c40c0007840d1900f41c030201b10000c00f40e000ca2240e110726101e9010300030045007503113212a04000f10f0b1030004a0580f842c250796412481100360242041041c0c4110b00405c114100d8001d024082d001b00751528250030550711003841518001c0c2c1e19501c1c900c5504a02c59861009802c10b41c11016006078207041c524814502030001c50103030b01c1425005404d003480041c5840440320020010910058148000c05030440c018162030003e102e0040c0120001d0110368a8032640103425000050041c5010b004595a0765294002406a010808004003513100820f08030740c880403e001c000790f20382d0000c924620300786081007103006d010750390112800b910071780d042d58 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 813125890 1250 813124640 813124651
    0x20f09090a062421180501020d05060a0308070305030903040306020a08040318080a02210d17070306030c0501050c100c05070b0c090907111501260d02030307050f13030605 75
    0x80420300d03882840f004500000c0c1ca641d40c80481d010000c009540d021882d10100c0302100c030240481c490304401c1101c1c400c3d900620088400b0b07500801d002289204070b00c44c584e802401120300705050707440c648880320503200c0d40714090200180040010398811081048600942d03000700115503400d451040181000b006880440000714592924840e1007002d00080003941c0b58100035158141c0d030755080103201d02c01040002d10103440100c0080c00c4000600600c40300c401c00d43c0b110500d41840c0d5620080d400380c010401401d1505d0414140045410340c00120b055640a01b003036541c500305a0141d03031418411140c0030400500381030649080d5944000070b820b2152281c000103640c0c1d142c421070712581c0e0051343c2c1440e811604280004038011303c01d42d504441e0807600c02c10b88200c1100070310382d1902c504090300040e10064400180c110b0f001114000d058454903808003078400b2206080009449110140119082081c04030724100520f12101c02c4442144110990143c25952481d1000140404452 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 813127140 1250 813125890 813125909
    0x3060507020a050c01030902010315080109120c0b040204090201121104051212120403050d180b06030609070b21091b030d020307020915030a0605090708120d020f09090a06 75
    0x10418140c000690600040d81c0030340600000d54130200114000c2034520400c0e8101500d520001054004105203100601034801c0046019140d5003003426002c00340440401c1046a071000c0d140118106016584e00700303504071404900038000d400102c500841118000c0c20162920140200c00d882c0b44000700200d80d4141d585424130301228602640364040d10794241c02801080000f0420f00000c07030802584207100f4145641800c48070100c040c02c0301e440003408101050030154900c20b21410010030350340210110014002460103800c016113410051185803502e0001003a0141c034001100ea01a00381e0100300340750003036444d10030100b503502c220651410745910b5241f100b46030360307050128818401600a40003189000031682c00e110035441d00501c2c80c802c08410327040500c01e0341d41c14410140303070f5405000042030b41d08160700c5040c203021942d84186141e9108520006144100e201500d48070a45a580147c0381d80c4105604c1e15248102d801b510347c414940740400017201340b0395000f4000d0741d15408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 813128390 1250 813127140 813127151
    0x1e180d09030c03060b0d080f0405091005030d210c17160503070f1209060b0f030102090a0506031503010e0f070801050601081810060b04030b060a05101b0c09060306 72
    0x24400e4030191940e001c00342a011144405002040305500200c540b944098001501d0180d43c0c2c81c0d8001e1038000000c0180c00e0800010308001c28680214016003003ca540240001d0618010000744d44544a503a000f0038014500e001c5840d040701c0400346e80e0030102c158018050301100580040201008124071454608404c012036440c0144d00d00b0b4102c0c50086403105459034a6440050300c010b481030680d03000301700c1075540080e010003a501510000c07500c1114085400b081d4881005041012092102d019a1041c8440724a543e240603002c4c0480d882a580c20750747e40c5400d00ca20241c6541d900c12590158202100150750318000554a11402d801e1026602c0f081e440e911703041e081e900260f640340e0000b0842d50109504010070880521000e50002c1258800881c0e000e4000580b0310a44c800802081c000c2030400c1846901040c059024100305c0d0000c1101e07040c07800040b0030b071081d6090041004000c0542e81d000f400c0f10f5020400c2c05400032080e03c80301d566400d960000d032a1b14042201d01074180f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 813129496 1106 813128390 813128413
    0x406140c15181506041a1e01021209090606091915020c01020604120e21010921200c040501120204110a080f1e18 50
    0x503002503914a000082c840c0080e020440d1610b103030b0401d9108a07607a03420b00a1640d8400d008403000200f41641005d8201d420301417044140d0403004c0c3c0009800e828880c04e007003441c0030030700b60300302c4d40d017449683d02001e02e42c0140003545400c0035000300891010715100019055056024000c5094620152181d041d500c034694000d0b1207500c011174940700aa9814004000500001e0000380501d00b403590300c04c40401e44648a000402c551113540512950707039651300c0c804141e5010141e440c00c020405280c0d00030300c0b5172102102da99122400003c00380d999031900e01c0c00200d050701d58080c000222480c401c071005800110601a000c1e01c4500c40382a42c603031040710302034089410640c4c080110b0384140310803121285c60117560300b0130500c8407091580c2d00075080d5901150200d031080c40d030344880c0b01610a5480390301e07109400c410341074204000070390740c0303003c04031050100c400b02d607004920f0 = true := by decide +kernel

theorem cover : BRFrame.Cov 812949640 813129496 := by
  have h0 := BRFrame.cov_init 812949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 812949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 812949640 ≤ n) (h2 : n < 813129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
