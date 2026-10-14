-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2599
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:24.701728+00:00
-- url     : https://prove2.me/submissions/4125f91e-1986-47db-b3f1-70056ea93738

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 467266187 ≤ n < 467446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 467267437 1250 467266187 467266201
    0xb060a020a06180f06020a0e030d0210180503030403210906050103050f0106030507090f02040312050a08010f0e01050f0f041505150f0406052803020421050a0b060f090c03 75
    0x5810400c50351030340c0c818030b10f42150380c450101108980b8001e0102d0740100d400c0c60782c0e42c494900903159541c000d0071200b4803056060040d445540158842d02c1c20707400e0100380c1c100c489415852040f6690f219004500d195a10f481c12103200d80d055000d015104102c5c250310304d9031707800e074002c1c1000d0318001c420008055145203003031072510321030f0307030301c8408a90510104102040004c50340c1d00403182c143e80c011a00a09054043c0020300c039541008045550702000d00316001c1d4080c020304412103464949504c140d0b21412503000e1030500d40b0903480c078203240000600c11810003003a05016a40d001d000285c0d48400b40b4001015600046008185481d982c2c20030031592a01a008100110341400030174500003030703d810084244968050074045c0080040d007084c0c0007064000b036040c1c0000d81c1804a01c9402e020038001c019502234800d802c1452098041c0691300e001c01c0c0071040119502400a000000042d9504002c0882c0280550341c0312207000c01001c8030761503801545105403900b4220660b00d251104d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 467268687 1250 467267437 467267441
    0x80f0423030601150207080105041103010b18130606120f030f17010302060a02070b0a030f060f05031b041506050304140703050607050f0912030a08090d05090f040b060a020a06 77
    0x480d803959200494100340994030040740305419150064400300702c2481c4c0f540103034548401d652003070344e8640c030704002c200900000200401008400700c00038000680740714200b095000403820b0811400341c0301d5010440100300c0840702c4a501d4810b2401260055441c80c03045510341ea035902c02d0380c0c2c0020301d2000008040d4806c60510681600d4140085c0181a81524140e255030501000b0b01501000499280c140c4c000c002c00d030010020a075207290b640950a03401000382445444c0d610340c880c1001404200c41d0780307205a48e42030320030260060085416940100a00c42020004c594100b41ea85602c103442180c1041810040c00f03c980b0340da030303172410301740381002001d181d0307100320881d0b6004140140002800490b109401c000715244c00fa49544150060b02d166206030425140d22110700c6d50217407000306010014140a481e142c0340c40902d07640d80603480d6220300401e0000c400141c010080320165141240d8081c0d04000081c200081203031a04020170308582c0082c4400340542d20100400003080154 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 467269937 1250 467268687 467268719
    0xf09040f050114060c0c030303070c03081e15040906061e09140c0d0e2d01110d020a020a050123070201090201120c1e0504090b030f0d0c0f080f04 64
    0x100004200d20761400381c0c4440d001d6000d1048921890000480700e00e0540e0401086e003241c100103060769924108000b01034141120071000700c01241880c0c00040818038007001c2440c1d4100689010801640d41ea15200f000c403030b40c03e50096029980d9420f040c0403405900c00c40000d4102500e014200c00c1185641f9480c0e0b540c60750000f0240d6080800d02042e6080c4c650541d60400c2c004041c40d62108221401c1074068034884074940c04500c2001c444070029410400c05646890344551542c10351501d220803a070982c2e08120f21700800c200b0402c14801205c04031383c000c04c2d00c45042d1050758441481da81d503590940c3c400002802506000c4511800310700a901c04c0240c100035180001c01501c011a80041c181405003802c03c18500d43c0c0e244075074500d60045030608400c40e038803a00c40240d82513441010302550031900802108d10701e0300c0c5207041c05040014803100011a900010907034085210411610301035048070441e0600c0d050925400020030070805003414844007004143c4407410440070a425440c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 467271187 1250 467269937 467269961
    0x303120e0a150513060e030d0b010507050c091801140412020a030807031109100c0302071401090b030c04080f0c100c03080f0403020c0d06091a07120e01060b0f0904 72
    0x6080840004496400301d00070300e000c000001c40d01d680d80c2d601381c00049200400c09040d8600f41960007900f5400800240b400701e151050412034905c0e018011100750182d038000810039440684019021310308940c8650780403d45005c902c100c1c0540c20013050030340b0a100c0048000a54001c18030040081d4900c000000e4606031005180c0c1881ca40c80040055601804074024196180042c80448840713504490504802810343c800903501c0c0200200b0600e8031410030780c014003814802140317083c142d00030b4500d94a016550310341d000341440c2d00310000ea840604510380d40d0008020010b2484030610185c01c1002c0b441018281ca04140000d0244501c0a1f4503000300b00039814690000103500491016008000d004e0030009955561038145d00d4010900700f0194050b2003107080004203d00ca42100e00028030510080740d42203082d403800d900c80e030b03c156054004030340b54900460300140c00740d10481103062560004540b0070343e00d400103000341c0d121320ba2602010200281d500315500b0203010754503444003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 467272437 1250 467271187 467271193
    0x140103050c030f0a1b0206100b03100b090402090a060207090c02011e020c0109020303031306060506250309260c1e0d06230603120313030807050c01060303120e 70
    0x240c54888601d00b488000c0040c0e800f00e8000c0003003090200c0c182d00c140440002e40d02030740c84041c03280002039503e0101301c4000e118011a0390000c1041c4611005581c0900014410311035084d05200c0070401d246c012001141c0c202d54203100558a503550341038040000c0c00d061f0050030304141024003070010f80e001d125010081da0305000c07140c00030808040402003544e260800040c0c0341c104142a00d405450710740e0000e98148800f00600a080c9844686110342511460080049994030824170803135002e10038502e5107514044030f0b55046500d01c01c80d001c004c0d500c24908010341179101c1c0020014103840c404492856502424411446401041270f015018022580c210000051b000d407401d05d0201681c4280c09590350000c0c400801c02c003900000501c8940c403411f651000e10601034580040c0341221484e2089c0702c1e0b469102400320062003244c1c01290002d0380c0c541c41c4405510281d40c0810701034210010407000f00b00b03c811188003881000061442a83c0e1400c08000c01c0841c1e10641d01503902c4420160 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 467273687 1250 467272437 467272441
    0x7030501050d1203020d050906061201140408070c080307030e040c0c05100c05040504061203021207031209151e050c0c0307060e0705060c0d03110315011d04140114010305 75
    0x7603641e01c00c070030b0600c0d84510403401402c50840114040e001d0f140c080034019007808184044114003183c000c0c4140300030344000c0d0b040c941200405003640c01c00800f4800850042d0041000301e0060801042e03201e0084600307000c401c1e522150385146a00031b08050740011a14408842d0360f00c0c050094003d400860f04c0d000d140f6074540d484a40d00c2c0e40c1000000082503075640411851140508103840c01840010410040f41d903558958081002401601318014003400a11006102c00001901c007800d4041c0c2c0e5855440d1240c0d80d002c8014030010400f511345111250300c198030865540614981560312060341c503416044080700e80144c0b60b01804902c40039100b0b000c0442d1031100002601d55041d00400c01180800c2c190842d1824100f49400240d00244002088440d55030005060468004140c0d4200000800e40d005000c0c58001942c021492141005082d0000d40c882d500c107482a20300142441c00b19010301c80020b080310092f80c6450305c0784169a0040100300d00200c3c8420036004d085c00d041c0024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 467274937 1250 467273687 467273689
    0x703091205060601030b040b1c05010e0105070507080a0e270a06080a03030b1c030c050f0303060604060c2d0209060301090201020a0b2d1906150f0e0406090e060703050105 75
    0x2c1d00000c0c401c504040d034440000b1805c1e0f94640080802c10303c040c12110020000e042d4000c15a81140c06c01d9031fa40d03091403100c10030403505100e07581c480d0885980b490300740032a994801d659540540062400c1098200c0c0384a1036941d804a16091802800d501002d984007a00d010591180d0090040030303401c7c540042041201da0202c0c40715140d9905181c006001c1804900040483d10301980a070103442c1038120386820160000c61380f2001600420444007a400c2251040d903480c40b0032a00240c201105110070803065000e0752007036011a2040f0b4109440c88501002040714003042084101d80040c80c0e9a0f220960400a403580e821240aa000384030400c45a00003039070360a9032003001094040c468000a601c214401c401340103c8200c103000380200c000d4507a80c6e520601090310001030041071612440c0e00401c0c2032203813400712441e0f9000902c0b01206c80e0f205940c0c00188803202c0080c441c44945c1d00d00540c0c4c070b03449180040c1c01c1800c4006961140315070f0081c1b90810003003c10040c10315100040c819 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 467276187 1250 467274937 467274943
    0x41d0601050f0a09360c0e090f060c0d0606020c0a1707120507030c0503150a0f1e06060201050601080f28020706060303021603080405090703140a020703091205 70
    0x1501e0003600c0d400c49458801d00440d1540003580e204109039450500510886403610440c000c5142d084040088074030b202803040c600003c0300042c0103202d03c1440e1010040b41590908142c0e0002c4100141d40100c3d0140280c5409c280003240c4050005400240380300d1f0480c458442e00001e0b101c03520080c4a2640c505000c0390300000540200c81c1004003485501ca403840f01040175001801c40380510142c044032600d400e6645036014002210300100d00080458142000500a190300142200c130b03040a4854a1f81c0000034200c141003030221a4507540c071a107140c0b070018511492a482c0b650002407243c03600ca0020308407040500240c2c108181941806142d80380305105503080401008545d00d4186006000710094103815100b1100c1400811440d013401071540c008000c40e0700903000c0d1914032010091062140600d800300404041d000d101c00e0006080c141003a651140e9030b1304000800c0d108003200b0142d402411142d001c051074002584004140d80500b80d40000e04a00b142a200f105142c1d8610392 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 467277437 1250 467276187 467276189
    0x40c17040b07270515090a0e090705060c0307060509010b100206010905070509100e2202070501051810050408070219081002040b09091b0c0a02031c0f0503040c09051302041d0601 78
    0xc400c8000c1d128000a074020381040303d29060009040e6054150342303800f0341c00314100803036100b4114028484001404d0900d80300325500d0b10407501c0603602d0b003c850b60f0342c40010174011300b0068496580710800c14450303d51507003146510300340341c0040c09151314001004090300c40c001d08001c10018203103d05081a11107203c003800000385410f12403105000720010074441c0d07a075031280c1c1d556034484c0c3c130314003c2d1460726500901001d07018000038130a9644014005e0f92a2110911092a0741d00c0300c1110347c0b0312442940400c7d0418443c2000c21325000c41500080e841401510701e400c80b100110404006000d82046403030005810782c8001d50400c0c1ca01107000c1c5145c060220300e0b40c05403c403800024580c0b82000200c2d1024040804041c1c0c84861940c03010b0b0b56640c80e50b10881c0079203e48440c169100517030344201d03400e812055640310a842c2850404540640020b002241d18000d4000045088426400350030b1117000d00d41c8070310000c020b40340104000c0c1c416000c40581944d44000314919601d0700890124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 467278687 1250 467277437 467277439
    0x90c090b04051003021c03050c010207030f081005090105040b0609190e092a03010902040606090f05041506030207210c022805040e1509010b0108090f0c040c17040b072705 75
    0x200001b00203017010b0342e462203219040800c0d94800200041050b42050a05d034500c00c140c2e40c0c1c40c03100d965040c00381c080e0300300c1801820340c414401c0c3c00401c00b502d881d4000360342d40c1c02c010342414100440701005c2010300440946000d5450669542800b108103101011907120365424028043c8034694259030550400c520140d45c0e035004141d2102e09a601c0c2500620314135507025104010807540c2c0e14005140509a000b030080810041200003040e04e800c0c041c80890040b0b8000c412420743c1b50100c150f0096000400440c0c00c0501000898040c241d98070b003080d0f001c4a182c807821500d0f59188100401500f200413810f9030b42c00c0d44c600c0c0d280d03401c03041454482175450a58002406503820b803441841c00f03911500c0078055020b90400c100c003c84040d0012140c0c00001e894403080c0340c440007005902c405c02100e03010265444071071544440c4c50960131501c0310800720304014001400c2045081c1184400700d0f02940d8032a400e1040c40001c41e0b0000110f08840501035011036821441000c2044c04d106601c101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 467279937 1250 467278687 467278729
    0xf031a0c120406090f0b16030b0303070c090903090302091e060d0305030403030e1920040209150a0909050103140610050120011401080a060b180606030901090c090b0405100302 77
    0x10004219048444440044c2c0001d110301b0140303440e5450000d40789415160701d00190804545825a0400005441089034400711300c65400742808964401030000810590411500000010258644612f02c5000d072510f0200002d0080742164403004911029042500940040c4054004250300c50166a00503515281c080342d01c2855141d9646021541001c4131242c48981c18801c08002c4018805c4130006a00032007000d1000c80642000228021400502d4004801c0070050901ea00010010031034584c0c5400d164100f076031500c0c440e4003211800d80003116481d10381814501008020402580c0c0068443c0f41c00000301d060400080101c1e840b10707141407801c103c80c042c07246031840c29001010304084400840103d9030795111240e98801e045402a20564030b442c07a8080d15041c1038004000040e07031203c030032090ba102c0c44144201d41d80004c204220740e55031102d4503400070342101c400030004e0015040203c4c8524880c0100402c81d04050700c12051200803003010030050b1104c04105c81d40410710700c44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 467281187 1250 467279937 467279951
    0x601020a05010e0c030c0f010c0803100801020a0305151504061b080c061815060108090120091305011a030c1204051e030c071a040f031a0c120406 64
    0x140c0ca0004001002030080d403c107610040103080000da41058504101e0449800d482e03d5424819000540c2c0861030000303070112141e0020404180046802403030710101220b00c19030301c265a6089810620806001945030414040d50701c01a03400704400d646e04641440750406403104103603282c4228405c0e40240614036140c82c40b65031702615503400003134200d2030490307494110120b490380301c5104485400d00740803420308020001c2c2c0700083c580c80c05c0c650658010015100e440040d14004401400b480d01c1b07648411020090381d0001c484404412040c0001e030b40c8810028003000004c2e100c00381c00010080c80c1400401016000710180442c40445180440d500c2d140d0084011144c42480210004420300b0020301040200018541c0d40208149000d9404c0c01103d0001035280d1181d50369031650742c0e1004d0720900c0190075402c1e810441e0784140800900e0541d403030140b01001d0400707134015107120316812003503860004406401c542c4101281080c170b20b040a00d501c403031076403032010b0009040c59544041c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 467282437 1250 467281187 467281189
    0x71a130302040f0f05010b070501050c13060c15020a02010c030b0d0c0e1b3027031b030c070509040f110f090c0705010e010c02030a0c110904050a05061f05040506 71
    0x110002065824072000d00c178943c0c54090101041c1e100c1c0b81c3c126050342c07030304002695007a460400d84030f000546003800e45005240c10000c1300c1d005003440c3c0c00e50301032080b11b02c80c4032203c6543c4000e25226110743c0001c64500c100c214082e048400080f8514062020043d0150001e12841041010f42c2c5108002d51001c0e1110b0184981c103440315403090b20308880006140720310442620200902c1525080c00d840100080c18055aa0060907288040e9040c072881e0125212141802041c0c0600640e4080328180007542090310480000810202c910390000a02e840042606200780800350a00351607001407820107689001681d031482d03901401214910071304010039558000b404a0145c002420005e19040c608a00c09080c0c0c04540c086a15603c1c181000022880600a0002141841d0003660404c2ea8040042d82c0d2505142c034100d6a907c0e00304035048550f920307080e10b0390050b0b029400a1140010f5442e0240c030b0a40050a0506003d80c940d20a0585e03c41024074441907130026100462242c80d214 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 467283687 1250 467282437 467282441
    0x610080c21091209060d0c020f012309060f061c0611041d010e13020303070605040804030510020906091c2a1a1b150405071a130302040f 60
    0x9034402506006150261410407295102500035012007042e20600ca12180701101503104011009820810502845c80104555404a081003001c1c2c0103440344480301da40403070700b1143c907403601240d00078012445044840b000320070309510482c0b00740105820304000012400303840e8018946031040c600d000c01c01d4500d50480500c01c44c0180d11000c2801441c01d41030066216030024021a030800070313a0014a1070501070399000ba41292a4000d00c07030300544400c2d02004500440d0602a605444204505400610340b03129451045010740c05081e00c03a411860710a007003103080100d15894034014081c1850940d9901c0c1242d0b903078a0104d030803984001541e800036581041c510005046640c1006a040f4107000c14034007208400d026500030050240c95030403204500510001e030460180c07061084403401051029205890b40c2c1540495a03113000c0c84100f01c419080441c1c04a4103504203400400c42c1000d682c54188200c00c5080798a41807912000381c00405094070311020348196261400c0d402468059 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 467284937 1250 467283687 467283697
    0x30f0e0a0b041506080105011703091f11031303120216050904020126041b140405040f20010206010e0411091005040c03020c0d0201020307080112021f0e01090b030610080c 75
    0x20f084103000940d81c884066000b00024400c0030382d0160108141444440080204d44001400421300c80c40f0600300303071407075200101452609040c0403050100d101c10700b0040003d40304100801d00e0b5401614218a40100ea410301b4812010942d4012005d040310450342d500910103030780c01034030310101990311800101c498041080340c8041c00c4000201c580d8158001680c1c0c01c0c840e038000d011400c52540900800742100e002841840c071005c0440c200d0f540c50b4a0719030000c0d50014081c00302c581203000b050b100c41540700c0d089a109103601080c603242c81d9041d60107110b1a0700511010744050510b28043d2036039240c180e4042030721031141201c04e0000e5141c0403070718035840181c00c3c0a4810468004030b0080900203500c25640080c0d103104180603288804d10500840b8440d003816600c00c2c0a991802c010501c0d0f004d150881241c1c4107400000301920b02000b0b00e4050b00c600b0343c13940c40002c464070200001d0038030340140c0c200031122023040007003144917200c43d02120f019195600e0600c40b69070707800d280c01500e4003076 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 467286187 1250 467284937 467284973
    0x6090b0406080c0906180108010b031504020f04050a0e0f1b0a030c031b02030a1808190303020f030f01052d010e010e0a0b0301150c0f2904050607030f0e0a0b04 70
    0x100340d21b0301145103d5000d9030302072000c2e200d417030585c0d8a404400c00f96010440d808156202140301c2c5448a0a2079005000b02023051602e1a08240d140d00c0000d09c108219004500c181c61b8080810003011281d2801039080980642c0407540c41c102c1da86c0c10000e620a64071040305054407a00300d194154469405002c4101d03150f103030b07500c540310490740080d140d5014008190004a440c0c0c03000324a91a0128443d080352910801000e211030202100800c0d11010441a010b25a0901076401e66540703540041d032040080c400105490343c180000c0044012050100e03030001074107868084000460401c8030340107400c1c24240940c2c1c4601c28401225400c910854184d0400c030b080c64001020610079000d181620146034040b401841e03609400c43c3c88803403c020142c02c544661602e540812040c844420340d0301c0c0d90381328880501c410801601c05c0c40e00b0a44084075558400010045101d5042c800c001407800340c08000c0c0908600c10b0801e55664951200c0a80101e480c5808101041400e2100c045c034041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 467287437 1250 467286187 467286199
    0x2120103080a2c040b010305150d03110d02070501030f02090f0906060409021c051b04121401051e0a0c09030b060406050d050d140c0a0b06120f011506090b0406080c09 73
    0x1e0043e90340c1458444a60914051400e0611031680b541c02400780364071030b80c1c8050b1902000007001007045401c05070904203070300b40030b450804c2c881c4180d414440c00a003e50250010f002c241c1c603050004007103844d440c4600c42c0d1240f05004101c0d9a03035440400052100045803102e880d0744645c07000a502d0703ca03d900c0091507506c0024100000c500398280d801e84412402403c0003141e4401d0f40c01c1200303808080007540a240100000c0c4400c03201d01640b880c002c0d002c1c03030f0315034602540c905950b4215002070710300100b101d1700f0016854101d10040c01c1260b104900c0e820a010116a25002400c2c22200f400020030b043c0e1840006074250320b0342e90101c0300501c001000e44c105903501c2e050054450750513410041c0002c40045000d84d420b1081011035111815074002003400309240e41328259041005808113510020b070750046050f40e601002104a01c0c4841000002c41d03010300c0c00712000d4183c0d980e220106109881a0400141003401c040e50120390003810409542c3e40d51441015003441501001c0d5480f46c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 467288687 1250 467287437 467287487
    0x30103210e1c14010b01021203040515070509090a0606090b0903010e072c0402210a020a0605041d0402031e0c040501090e06072c030f01050106030209031002120103080a 74
    0x9440702d128202030078020148180c14074500c4808600fa6160102454050f901208040507100180c0004541c03280c0920b00f51428400c1580c601c2110304829285040015000700304034000c0c1c581081c2aa411403105402004468640701d00a01080c00e036202e05a4184004a0508280c0c1c41c2908038081500e00d6105a640154448044001c848515a07111681e0102041c10551200d40016118011034004200c03170072918080b110840c401e0440c0c3c004180500401340e00c00c00589505000c1c1000e48180c0d1200b03a140e50404111201400c0407180d210740d464000390900015071030206031610065800325005510082c003511031450204d1030384440e07402034a440d00009580c01c45138004079004203c441a00c40075284c411040329088240351940300d4143c60312009141a1051940020020708040c06039032101c0340c01c0381c450342182e00076070200000c03980010b00ea80c4245030610296244040081045007030403205001c181c20000140001040c030440054542704060150f51042c1d104804600e00710340c4c91f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 467289937 1250 467288687 467288719
    0x120c15020102130e1e060409141c03111608160303060608060105031b0a0917010905060f19110912010b011409090f0403030915051b030103210e 63
    0x3540040f001c45543c034140f0380082404031800080782e01620704d001c01450041240407460041050203808035a0040c0d40304400c1c0001a0450082e8a054110310042c0c10302490551410380b80d41c01304c1c404801058680350b1005080072030b0b10700355445003007131940c203001c2091030385010040da00c0b0300310400300d044030019058020164960003200665049580d601b05d50f403604801501c07140400d031107400e40c80071141072554444100e40302424403200c039840d0030300d2003503aa81508580c80044251441081c3d440d030a0b15000c0c071008010094105004985919543c41c040d110480700400d0001c1c0c000e003031502d03200180c0ea241d42c0c0da4281d0b044010001c2c0b03a03445032441c440110f8000e050000000f8082a48845d004002d03c12140c159122501c015007514003550703814004c1061100024030842c10706658001c01008100d01c6281c140382000348800c0000d090030484a0360040c039042100030510303c202000140009203c0c1c0d001141607034040c4041d5910101920310583e03c4481d00410a80c104a4071444600c030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 467291187 1250 467289937 467289941
    0x140c220324020405031f1503080c011b021504062c010b010815010e0303040b0708072109030f1703071701120b130312020a0305060907080f01120c150201 67
    0x20a5a030000390503211081c544045059000e580318055150304100207654803210410442408212a0b26000400002c081b10082000c01d26070420348407040045030701d070a40102403050240361009034082c0c005048488400940d503203104118940080e403203070003003002c10145400c0510384c2007096070044a98603d0001d40d400c08030901410062079800c00c00c4c0380e64154003c0008a019034070041c10003c08603402c0c001502d0145516507915094801004001503841007100500703040c611510815076038a20f1410311203c05071030252001c50764000c0c007c02540050700404071030101c945c840c2012803028001c0c140b00080c00e0742c04c00c01c035000385e4001081144aa0303000b802071940303c080f050f08910356625281d031038a901100f11002000c8400c61070108004414405000c1c0c0c90500c207241201d0f50b01c4105501e5420b0307800850386c0102194840090003240c1c83e2038003056a000d02c0c58a0300c00c190b482c05c80459070360300c0010310403070740348203241d010342801e22400c0d00c0840040c21004a200300303140300c442c0000b80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 467292437 1250 467291187 467291213
    0x50d110d0f180503090d08190519030203060d02090a0b0411040501020f150109020306061306050901121e0c0c080403201e190801090308100801140c2203 67
    0x80585880d07400d040542000038807540780b60f0440c00941c20039031a1010702c100840031000c15a100317281031003e0905a82c022004000301d800c1aa10681c0350550304000d4403a107420b6540480500d0b005000300720313654403003a03a515981038040301e25010503103561401800070145141a66003003030800803035010303101541005008444003a82210300b01c11a003403000380c80d42030b2509501141046000104541700040e00a1500404010b21142c075207200351488502100c15940908040b840209060040d9a0084c002c0402d905604078107000c441c030903940b01440204290404501c180d42c1d000502200c0c4d1064180c03490455004800791b950715180e05052040d0020340401c0000c1c00721500000c1c2541c1007558905002142c166401e0034503041300410000080b581c130400f40700b6050100030028600b80240100c0d41d02900035111055503041110343c25240c240e82e9000f002e10340c3c0c1081d1280c05e1440110a041d544045c2e000d180c25241e55440e007003002e14501e000080b82641402c2c02e03000c0144441c00b130090b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 467293687 1250 467292437 467292461
    0x7080d1214100e01050109030803040f06110310030c1a120903130801050a0506030f1513080a0e09220f140f0d0e01020c0108070807140315030f01050115050d110d 71
    0x20300f03aaa03280c00441d9900a18080145180020b202107800a440140341400040c0b143c040810400088640e0325125001110f40070440a001c6a04000303021000003440301500b850040d0403000300b2100d41c50056440b841c90160010100b120000d002481c0900a070380043c03120326550200d1647d10310505002e04025514074030041c0c41c00c80032946d40c1c41d00081c400b5249284101030007010803a01a14003040c00c00600c2082c001019100351400200e210340108001c0e032498880d03400e44a1400280000050028003030341049000b0704012a21403048681940424ac4c050701d11807654880746024100c8880d000d00752080c80c17060325000503100002160b400c2c542c03115a0345504188154000490f40d8181030f44000c2e02080508000c1002e0b00d1082c400240d02c0b040908180383c01030f50413001c040b07141d03004031404441c5d5841a4815480fa00d0b0622201d0010707148074000384520350522209102c14143c0d1060603061240c0001e2154004906801440b407041400d1040c98585040e80b1000e000307429008510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 467294937 1250 467293687 467293709
    0x201111813060f1e031a09160f15030204090c0804150506060306011b050a050f0f060f070c0201020f03070b01030201030b03030304150e0f2d07080d121410 68
    0x3580c050702a80c030919040f203502d260aa003e0030f240500c000184124030603a500044000d40020001c5001c1c115151905003005001008500c3c0c03d000d001c1c209040b211802c02c80fa218074408000459a1446d103001f95902550b0187d005080404290004d1103a03a001c81141410100001c00407900803800c1c2e0710950181144443c0d1119009019007290310840760b01d9070000061012562652140024050080c2c0000e5007000300720994035105d20b880600e403011183c9034003500034803070f0008007407001c0c1d01c1810250703004003480e05220303403150306950300108a0000c22072441205170a5a108001104c46200300b81d060f60ba90300c801e0300f403046a001003404180d0219007804001d00c914100001240d200e41d42140b011114003d00c0c03003881c8042e1800c03d40c40600c40c0f041c10880408542e0070300c43c00d8840412100c0c103041060384140092400380e15449101d80d15080340e04104410075020580001a15441c500200300108035107100380108440030b4099074080300d407401c0010440c644402c2c8003d40b03281e6605 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 467296187 1250 467294937 467294959
    0x150c07060e06040312020d02041d180d0e121c0503010509060d1a0402150c0604050609030a0816031506050309071a07030507150203040503030406050703092102011118 73
    0x1070103560300000d0b1030080000d01024101042c0325003a6028200150440703102500c0d15130b84a200076404844106080c811b002c15038140011102d261603c0001006284007400c1e208000080c060071862550304030714080c01c9030700c07030b030035622038050100d0403c507140404402d40b80caa007460f00410a030024040e0314000d05150010079114a45280041c40160b400342410452614410031154403034800b500498004e0201200c001240807044090410891018001c04451174281825451300304003030f1500c0545d802c01c201d0259640d03170007404141e02540440c41858122840a0202c0c0207009000c0101e0401014030400300754541d000006500030702d0302404aa0031191200705581c3c03001c3e10304503c0c0146a404002450010f07001c0d0014124103401030442d203802c1301c100b6090f10140d038011642240d464100004000030804913205007900010145000c10100d07a4590b41c0d03010041e4101c140081c011040c95803005085e20035000300c0480189600c00a45079602604680038004584d84854071401445070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 467297437 1250 467296187 467296211
    0x7020d0207030b011e27060918080c0a0b1501020609010e03160f08160c1401050a081f0b030117060c09210d05041409090d03020a02150c0706 62
    0x1c06400342c94000c805062980d18140d450f865011400d000e5030001d4190080c0081d40700341c0c45020041040c411600c049500d44844030034001c8a01c0d6412441d0110300d0a10b14064450120f4580340d03260341e10030384590b55500180f60841c0740815000300104200003c208011b003040707410707081d0700e801503003a002c85001c0e8031000700c103500b690704102078040700380d1041c0054500032461890070240c3c00c0c00750100c1c0010071203a8070342c0461035000d603180403064203019051004002d00303550b80d94010b100c4191900d80c580c0758000020420310030542c1d400100310419012600401c42082c1b810743e05410314110213080b07592100f0b04107031354109108030030107640390346a00c4011001c04100d044c803619882c1d0034149045200400c010420301c0316090510403440e541c507550382001c03003001410010aa15110541c075145012500409021038540180c010a86881070101d0704500180215041000d42805625141144000c0386003110b040802107044412100f40b2030516840d000815016008e41e000b40b1003090450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 467298687 1250 467297437 467297443
    0x9031903020a080f07090302130c020613050c010e1f0e0103050601110601051c150f0b0109061704080903070e04120c02031e010f110a0306051c0219051807020d02 71
    0x82002c00b01e40380d1400180e640c11440450ba42c0b205041c14086001c5480b5000705031030140340c425005250f50303580c6403180b01c107404001c01035009080682940d041412030b40c40c1a1104291482103061091001140107540da030b84d40141520500d80d0070700c5540600c40c0400400740d0081d52009030102e4986804100389510989958100010101c02020f481c0d20700340501030109030f813a000c2005040c840140354009841c0b8501040e10821400b4013041810798007400b20120b60140510a0521024803c10000681c004800190410303d16040301c14a0f6544d0800b50b2051041c00526030789409500c0c3d01103031200e20f02840740e01407070190322650440440e48009613581a00c0d4107001c0d5050f4025500811442030b4040c03204507500750280040b510001900c400400e0328407041d000c030301800001c2940d5808903407511038030740140030407910300020303140e0181d195248842d10100a03014110000c81d034212180304605840041c440600a10342e0310141035080c950b40002501d0000040c003507080d80300500f42c400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 467299937 1250 467298687 467298697
    0x42d0e271c080126010f18050708030712030513020301020f210705090613050319031d0a050411090901061112040e180a0c08010c020c040e0c06070213050903190302 72
    0x4200b80389840b1300e035284a40102640d84680e2065640b50700c046031880300c9900503c00c1d030310515001110310b20074503e819030502d0000d40002d20030340c1c002e01100005c11548691001120b00c5810001125110150300e500c0d140e0f0302d1030002c2d4156000160180210070050f00420030400300c080545014018034200399044582a112040010f9090101c5d03207661400e40010625107200e070102500082e5101c001c01d0a06510f25045100c16030f880c10714a080c15007190550342005c0c00c04000307041581b01c0c00e000400e0781a4034003806000d1a0344618006e0000042002c03600d10781e800074000e822030740e0b4401c002070030031030200c1d40501d40d800fa5080380c1d451a24034000792001d413210708010a0b07066070b8490200c8005101c8650b4800715100d4510701001085a04a00310b0180072180d0020a41603410301029103004407200c24140540d2921106083c180c86c04545e402c50400211081c43e41c8100900006809600201080014034a44810710815240010003050031601c8200a0341e003028442c80160124002d0f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 467301187 1250 467299937 467299949
    0x1401050f0109290c06070215070f09030308060103110f0403170c0604020d1104020c0d020f071206020c01110d06050306010905220311030f042d0e271c0801 68
    0x800d0098002d0810108240f24000c4010490f04003441d10a1051400304191592405a08080615404e801d02d03e98a0341e030220302c40c28045001d103c000401006101c0f240704c007404124103240030a10726803083e000350704040c60040f40581c0340c1c0315043d40c510441d80213100440e512501c0351500c4442a052070144e59203242801c001c2c08040d940c50f024410081c3c00a44115410000d0b400c3c891a0ba40d0b685c0301426284441c14000e019146034628064941112403071003030601c2c1e10036241003102138540051611803d600140140e00c07080f12031507a81c0585000c4d03600354014003002c42c0364a41c50802e94444421910304400302c0b040d90b6038a8802d01c048610654000c49a850788010083e045091400d1402c4142d12a01d001c00090310022203075400c680100f18081c460500c0010100180030401c0048651380e45842650416141e01c02d032090400b400c81d03c00c849241e00003800060495980281e07080046000102030000110034511168442483c41d880c401d050407074041e0380e02c841d0b20032145030b0305270340b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 467302437 1250 467301187 467301209
    0x90a150b0306030c060403030e09061c030e040207170307080705180d0c2105010b060301140d0314120915060325050d0c03020306090109030f110c041401050f0109 71
    0x41811200310403a40000e00040e094800c1c40c0c40c0781040e07100c00c80140019802079036085007200c16841042006000500058400d40c01e0705503201100b4194540e00e190070354141041c81e1f8401900002c6130107030007119809030000b05044100305804c03903140002c603c0f800c2181e480c4040795072008800d03a000d005e0280021a035801880707822070a41468038040d05080d0140700e14410403554bc60792001b11080b116032042e41c0c400c5000d81c4400704242409411401c81c0112007060642d0f0403d2043c04412112804291103086481c44420030b240c0158020300c005903000c1010b640c0c84d0003902c80905044016144210640305a4080c5609018204a00d501410b0018094022003103a2402e100d022201d050702c815000c44005d0001030141d80f040c05d8421194801e080c12842d203465070042508044000b083c02009904101100740000e81c0940b100000c070300c0d1418021401e03154220b0542c900f040a560303142d0058074017601a14510b4184043c9812194211103141e82c10740e6a1004441c2031070710388100d441d242 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 467303687 1250 467302437 467302439
    0x15090605310807051f150f031e0213050703140603010c0c080a050d0f0c080906010612050c040806090a0209090c0112271511040302090a0509121206090a15 68
    0x360034200070003c0500030802c507480b641c1c0740003045103c600c003400d1000503a42e480e4580368880e2012030f0b82034020032486843d040c4252075074485c0100340c00d400d80568800e0103030b9144c51086544071102e07884503040e400802c10031440c03d40c8001e4018000c58a858031620031407400200035190501500f03080d540240c0e10b15075528500c0d80c070f5401036007003040c91805203c01032000746881e018601c100001107000e00c6000c105003c0d0704001819820000d010030007250003140040c410759811841d8800140303418480081c1c160b0321188400781c103001c0c98001c28514018482880804034000446030610307070007160002035070b46600145035034800c3c8400480740400c0060f550007035520342c203620040d0040c142041d00d050348100c040840c940b00030011400c58900f84a4040498504024494100f0241c0386000944c0f8190964000071121301008040c07542d041d450320005207102c0d80a0020b013807210034841809442e85a0582c1000d01c60104a8007140943c0c100000210b0f05101c40c001d80d03030040d2000c0c1320740d1051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 467304937 1250 467303687 467303693
    0x105091303120b06211e070903081e03180f2e1103070807030501090504110402070302010609050c120c03062407021807020f0a03080a02071509060531 66
    0x1410021460b2a800701c003d001713150600802da62817038522a54032070907a0b83e03441c1692241460402942c05501007090352801c110200d84c04c28086004d4030f400c0800d00c0d0f15181c0e0501c1e4000092403510048000c90400300500a4414044003d21050401d01080c1e030030201202002d07076512611801e040040e400b44901c4158082a04010801904c42c44500030030021550b002005190b4019030786e02d000240800100301c0d40396814801c0a0250414143c10310007420f0a868904a2810310240107101c0c2d1342c0050a0401c050003540150001c0949180030700c0103243c00e501c00c002d944c20004241c80b0000924000403000484001164800c910080000542601c03240014a941c2d02c120f4420352440c00801c05c40d8050b03664695030b6a005840c0000d210018500381c1c90007030408000404001c1e07164490440d0b000001c0d08800030f141d0041d0f0711600180c0345c1ca005c0c14030014050705000d2090b802450404070b0021700425070003592080034002842903e80c0d500c020801c416084441503000c810700c20640c84000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 467306187 1250 467304937 467304941
    0x100801050418050d1e0201090506013c050a0605160f02030f0f01060504180308040b28020705011d0304150509062a01150b030c070812010509130312 65
    0x400d081e50510307101c001005070f4036945800790b40140e10000c6100c1422052554460343c200d41c080c060340307100034800a05103a9400780c0d2054180994200101d50f270742e840032141c0c1c001d451000d03100c1c07503000c0d8007464103a280080742d03904070719000b01d03401518000408145140120b040300d83c18841e200410003605410745514045804191049903d80181d80307012071080c0e0200802c018440b6000d0001822914107020041211000956540b005a0501c0c00c0f0001c2074108064581c09900940b600b5883e0361021101100304182c03014a46151024034046000719085078060b041c054401d1000700147c04d0000c1d80220500d061803112005a40b0400050058070a80c984410703e000f030904026003400e41c072400060503508101c00c92100da030040c189544102c020102d1059402c45280002c00c424203d40d09000c0c0305030101c3c0141c01e405c40c00040402c011400440890b4080e5411200307064540240c03641c0c07031031584000e104282c41402e0b2003000c241c8541402c1a00f1032141c5d459128201074503188046200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 467307437 1250 467306187 467306201
    0x1171c030605090a02090306180a0219080f0708070b280302071e061a060904091415090d05040f060e010e0a0b041703070201020705010503041b090e010b1008010504 72
    0x1040640740c180018260b01e401c00b03c20700802c42c071200580c0358101c14061600d0404002d1040404001c411495035503031101081108686806981200c00020241c00030313132089119501504051007249010012400301040708800d80c0c01e0362088e10304655480301c600c000b6002d1116199041c0b400494006550b0807440c00d0f0415010040c107015082c403025450b0011480c0c9140c000142841586071010104922840341c3d02a40302c60102110300b01441d000407a1450144050143c040e5550b84629000d00a20803442d06921407040c007117030303102001000700500001d0107407074491340c9200e800b2080345120b01a2060b074094a1100c16203102e0903207000821946021101100c2e418030800c8030302c0000da9150542c044c030140964040c1c0c00e649918003803100c402821881c809a40c0d039001485000e005030f902103079110407034400b40790407900ca4645040800b4004500503000768280751001c00051810302c3d0b41c102008070265070307008002286008082c4088103e0b200c0761704000410005c010b008610b05644145 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 467308687 1250 467307437 467307493
    0xe0708040c051507120906080a0b0109120602121b031501030e0d050414180f06030f030c0c010f050304170d020c06011e0b0a05030114120a0b01030303050117 69
    0x10459659001080504038007000c00083c072000022010140848244010362003006841c020064910301140144200381c003900c21000c1c40e844d007071114001d81c841c00c0355201408250440400d503e4a501d01103009601c6000c22069904000700042c409244240700b025000049840c503600e981e48001c0c0d8010141e040d024860f0500d81d43d084c00389144030301080b00b0b00c42c05d2a1504d0321584c51341001c51203180c0311908100c1c2c07441241403141160305c1c060003101080e04500c8158481c0d800c2d4854900103814150158029a224400442c41240601c400141c0841c80707e003c0e280e241d03541403240021201444100e8001d009014800b443c11500708841b0000c12403207403288001030804c06d11265081c04e03e00f00707034041650401d10414010a006003020980000c101c00641c517031521080540141c0b85000510074070302041d444120075204d0303450b03048004041099010681d80751495900d0010207000c800c2c001078000030325140001c4bc81d0340c0c80010015450340c2c030700c004004005825440d100e0034024603040c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 467309937 1250 467308687 467308703
    0x20105031e100315020906040317070b10050906010e011b02150403030504051011120304080702060403060e12030714090a03080c06070f080c0301030f110a060f090e010e070804 77
    0x8400e058a0a0700100d0050508014500d005841d5040200d00400c43d08002c806242c070403c10f044c40c81c1d131840c080300e080b25804422400c00000103080c0403454010580080c0440d0313500f41c01c00504100301d40101c800d94404484900305529800e00442e10a0007800401b80030841c0d007042d101050080d03405507440580f000f00610300c8c4006418034880203401643c070807004a0030200e82440285400c01c03041000c07055034a0035611040d4000001550b40000070041a814100000880d0a208001c01200c400c2c42c0c01030700e410b565035940c1c90140000d2444080c4c1e20b6280c000d04c1012a40d04945601b12401010700b683c411050103111500c0421503401302036070940c81420ba01d400400500494060024040c968000c1c090600d0b110401600e0010410340500410000c1030400551840420950741582e400005a104141d4546485900c940350181c0c52a800300490000041c000c0d8030032465807610303001c1e9a03140c8410b9900c8a40d286050310a000700c08500c02800c8c0041c00e50785c030801015370b0160240c445 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 467311187 1250 467309937 467309971
    0x70203070302121c02090a032001030522030809010b0d080c100605060904020a02010b03071e06020a1a090c0406030606050a05030a0c0e0903070f050703020a0e070905040e0c04050a090b160c02010503 87
    0x40c80d03140089c10080c40c004c0704500440c8504568142c8680790303200c120380c600591200301140c501d0b144001040c030000c0c02d00c181d401c0854a0020258030141c1e000f0b0b4054205411300c20030f81041503c40e00801c1ea80110307407154800080300d1000c907004000440b0800b0b0b00b190f003840c003441c0420020303400840e2900210342d44c9290a542ca550100a0100140441000003124985488803008603400c10303040b0100355031001c107031400060800d0380040b80f0300d04507210408070b40d00c855a60700d0500030220b100550250800303001000740180c55000d442103500442c0c03200e80c510f546200385910307448003e101400001e500c1074104501110708410ba42d00c00c100d901070724030f403404c59030b120b840d50328040e90141d80540c0850400d1003182082d1500c007005d000c0d0368401c501c1e14904000300074580780084c05440e01a40d105e00e403a4907503000c2049404400c4100420511007440c00d074031b064004007500e64003928500210b80c00701d01da0301d00502505095103c15074691142c601a500192025400581802c80c1c180540c50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 467312437 1250 467311187 467311193
    0xd05192313060f0510170303010519120b150324061504091b110a02013e0c060906040e04050705041d10110403030309080c06070203070302121c02090a03 67
    0x80b402031003c03a807400004031400c02480064241a40750004907080d540c20b450640528000000d50381181c0040310050143c404018160000c62380d6070b4003840c0c5451034500c08004001c41c464007507204620441c842d020780c0c1d00e01303020950b5424102c4003001016074580404072030035110404140d44108043c10342181740403034101ca4103503a030040d0303c10081c49586000600101c0040f1620301c107080401d1901000d41c0b441c803c0101d851b102d8021009040c48801003092104401c10002d0040011512009030450b040b4200d69408180e20f0015504150285400203c400e152420a807440903001804c5941054103203941e1454152000c1e0054455100d116000a11540c2d00e01804d4038428180c07044102c0900301a80c0306c2d00e0500700d245080300c8681482c48804440f9064000e40d07040303075094074020503802c6883c20207465502c15400d811034030340030b11820090300940002c004c01c502d42c0320b82d0071914840405140d40c8070501039a013140c84104400c40142c0c0b242071003074000d020400d000820100603196282c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 467313687 1250 467312437 467312441
    0x190503060307170f01150b0f0304050a0b0a1d01060f06200102030103110f09012312073507050f01022d01060b1222080d0519231306 58
    0x4000d22129030b124103135461615400380036818a81401c040168002c0341851784c0e0001c030f07014981040e50f800c80084005000d00c40304102c80c1e504141c008500001500f17000d00d103440a40100c0705d005001210704003810341c042005215080c1143c02e4017002c00c0040c0c2c20008115524446c15030402c4800c46140303c9071100d042d083c401540214440c489002c00d01c15014184024800188000e500c1049410010042140e24000304900c18100402c581440e40300c40000842c0c0000c008010301080c802c242c00800c0c1210049400c1e010745045c04429882082001e48400c0b5120002101e00355507085490300b0442420300e115024240103050040e140c1e1000c0044080300040440b0106500a040070900090f42080038031580c8043d28940e81d60034513000d8080d9450a00040143c6040c40e0f0ba0b041010305204410244440291143e0040030140d0754002c20404501510040d6280f90f82da0410f0144802520400d11480b441402410b480000d070717200c24000c840d90050700a00c401961001d1a4802000030014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 467314937 1250 467313687 467313719
    0x80f0a200c0d03050a0b150d0e06040501050a0e030a0e0108340e010201020f1b030405060712020106140f090411030a0312050c0702010903080f07021201020a08060105190503060307 79
    0x2410007884040b00340c420040a0701c10280140351464580300e0b8034196920340f20744030450203004200c05a5203800a0407510700030308401e01100000d0184c407041c0010840e0640000c1d01a0307085007410710100b0b0b10309400b5070326445400a46408120140021200365006804440d4098036000e6224040d040d2407684848043c0c50989030301d40a4030b060021034806400c0241c0d620380190a2000f141450f103007451010940c800e01840410220100d00c84e604a020b003001160301400b809003001d5241e22003460100c41c81c10b821400c1002550034034101090f441c800d06041810000d004100188080c503c2090050190000e001540d8414202d0b0304603010f0348003001103550251003560380401c000009603044048520140119102501c10401500980e0384840c0e0703801500e4100d0740380b076070310f6203003445582103413140c041e00a401084821045070320b94010b5001d000d040c0103588800c02c1c1640c441c3c004540902c10920080b1184000ca800800054815000b40d42d000c600642180c0b03415454400425003a854 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 467316187 1250 467314937 467314957
    0x7030c06151212141608040503030a0504090b0405040209130c1a09010201060801330f0b040306050615030705181507170c0a0f0303140406020910080f0a20 68
    0xa82500700007000b40f010030282101c2c02c0b501c1d007000d42d1030070011419500c1c41030414180800030402e0210b4180001b10088400a0100804480c0d440441e1480030340f00790018481e0706501da2600c0201c0103a400d240c050584a0795004010f0510703a528600c8004895081d54019100e140341c2c1600810001c802c814038014450340c482d40342d80c80d916143c000a0075500160401c86503641805e0a80c464000c031384100d0810007108410701d030743c44010016101e6800d2503e03440441590800200010584c0c0b4400043c003e03607004000900c200e54500c0240700041d0880d070300c3d44c00314600400000782035500c60805000b84010845c03d0000101002001691214100c403406031500390000c1e95000304a41c07036295000c2c10200302003490a19050300320a5880701e003004005000080c5002030070040601c20391265604007081000b0b94541e0605040007c0217410260401d03008a846140c0ea200c401d006400c41882843d03500c01c48000c6a80381c004007009400710422802107180a40e420385210300603c8054168418 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 467317437 1250 467316187 467316209
    0xa1b0503030114030102120705030414060726060d021504090f0506030d020f060106050307050d0903020114011e0512070e0702032a031207090b0f090910080307030c0615 74
    0x41411545440d100c060000f20380300382e20401c0070081d1001860005688201541000384c2c50360344500344100d4035070100c1c0f003003e0340c1e01444040140246d0805201c000300a001d01c000e00152344203110b5002080f00030b40b5000d51010000b0301490041c40d01000200e0406049283d8604003980d400ba01016030b1154000444501e803150200602c6060401280305420441d200509400084025881e2242018087c0c58104100040022403841c020b0007290404002e0140401c40030402c0c0c00e0080c02001c10800d01c41111904800003d03642002c00640b0072420301c0c020002410034a04801c002c54090441e44440441c068250700080300107008510034440d40898010f10366815046038503006880c9003141c40240340700452047c2984c1003000040d1580400580c844400365107814070166002d11031a0f118034400c03580000e03145141034482016003800c0034160b46100103503c030812000007541640c058800180d00c18408080880d2103841c50b141c49034050540080c03299182502c504a188141e080910098 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 467318687 1250 467317437 467317439
    0x30c06050603060115030b041d030703080f010510110114010f09060e190c02012403060f0204060c0b0a0b060304080c0f0a0c091a030607090e0a11030c0a1b05030301 72
    0x8402405125407200c02200505015814002c040a62040400700d990400d03030380340400174041d01c03154003009103c0800c02d451271001c00c07242c0c409035803640312400840000320310001043c0060001403056060f91001030844c0150b04100f0021100001c0c0c8490300d000039929000e0700840d10b11200c1c01c441c042e090a00c0c80d82d02d49070811100f8400c1e103003035030700c800741490b011002c2103400030144071603c800c90200800424074004c006070407400340c610b400c002d024060348628a00246d2104520070360480344642001c1c02651521a201400c134015480303610b001c502807140506c0043d8090384080e030301c81c1c44810000707200640302000c1249600101d03001c84040b40000744201080b04d040000e40303045806a0010141d001c0c41f40d0b145100551180314200078140c541c1c61400c074490000c00c141e040d10401030121082c525045000800c0710034188501c0c0f400d0425200801e48030282400342d01c41d0180310050051031034450703070070b041070581c8048009000c10492007030380303104040c00c900049107c1e0700441c015500c1c0c0d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 467319937 1250 467318687 467318693
    0x3050f062826070501080403051c0515130509030d2703020106061209150c140f07020111030a080f070509030a0b0f13050709020f09090a061505040602031e0d09030c 72
    0x4068094141c0030b160340510b0b0204036580c1e002d1401e079071140c0d00d45881a00e03a80031004201d80d12900340c0d0f480c40068101404c002c00d0070040c20b000c3c082c4041c1180d5415a03101104030000071a4015035521030f00c1c0e0000c00000c414104c2030f07040594039607041c008600d03c02c180d541090803000c0d02d07a041140180d4450404101d0f41e80d1110190100170035020082010303040300e58074403100400017a901d6860a448903883c168041c041c1c00000c583e000803080c1e00382e4600c1030342181c1103a030b444228203e010544840d510080c1080000c02e5902c1c13a80300382c8072a401a1140a5103002c0100000c10304000c1080c01c110981c1c07140c40521050312203901c0350400031420b041005a450041000800d0702a549581c00340765400b03c1d10006400701110300c904401a03540c0b085040800c034910403080c51503003041d07505c818420701e240e003580581c00321168121813003114103a40e00100c540c0d00c601e1050000592050080810400500180b580b203081400345c0c441c50b0a9440c4400010343c3e0342c889068000c9618400d000d424 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 467321187 1250 467319937 467319989
    0x1208070515100906151d1003060302100f0512091e010e150709050105070c0504050408030a06051504090b0109031407050901090e0d0822111003050f0628 67
    0x2500c0d511505012441c2400000741c5405c120320114010000259900203400404070525a43c81c000035081c4031018450110240c043d082d00d02c4120b01840140341441d4080d4424250140d0711a00781d80c80926108443e10b403540040000303011146079026812840000903000c0300240314501e080400801c8031141e00050904001c22000b200301171030f4401d001c005100360303c10b04140649509007491501d1700d2080c1031a0100c0b003140d4129a8000d031526040c0320030f201002c00994400e5400002c1809229107404c11302c01c0c8045040810015054180001d0180c01140d40285007502018981406a90b540344c49500e91487c03c0c1c641001107410000040c09503003842680a4058090281c0038000f05241e4141582d40c0c0304d01003000000c114030303200800c24407487c40302d00c2e1036000d03004003c1840401160420400d0100c3c0b800000e4071a2440110015415020f401803600c01d0b00328408140300f6170b5035082402410561440341142440502030701d5240160b086108030041d000011840ba00c507001c540800203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 467322437 1250 467321187 467321189
    0xf060a090510110306040f06050306090a0c120803160c050109260412080307051303112701090f0f020d09231002071e0302010c08060d0c120807051510 66
    0x45000e003082000f5078902c190340126500000700b0f8400003584a4000d510100910050701b01030f074140120014011051000502003103498002d00340c422a5a54a401c40028140300e900028600001400058548104444144000c6846080c080151040f1780d603202d007100c43e0000c00300c2d4900450b2046180c0100300401611030082d408404919041c101081c0c1191415241c2009140990000000b480144100d0554804000018050301c030b850f260f142085103034800c101113501616a11180018892409400402d504401c5184100343c3e402d02004002514818542d24905c0751a0140402d88078118402091000c0003410002082c01c0d5074980507001d014030b90b166212030480c00c42c131807604020210740380b0907603c500d0700010b0307031000946007180e0100140d02d0144140c1d0685060081803603019004448503004c01c3d61121000c1c0e4400d4108034a40b09140d10103090303031104180a1000b048160710a25000d8058a22241000007a0f5552860140025481e8441242c0201441b011040001c1a08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 467323687 1250 467322437 467322463
    0x609051c05150412030e150615040303030c1e0f111e0102030a0e060408040905060d02060c0609070807080c01140f040f0602060c090108130303060e090c0a08061b07050f060a0905 78
    0xb0200c64450169103640f41c03588640c04101e074102e40c0110388c107551149440d50320040000101c80c7c40300c1d501c1c100517006011060741800410116045040c92406041066001010300d48901240c4440d001080360385008580da490b0303442c0700c0c40240109010291008d8602c1408036000942c0e2803519075184d809445080c031341c401d060751000f402c0c8000900443c0c190f409480c0b00c003200144a9461034001030306134110000294002343c0000385034110100100320380e441541c060b41100c102580d1820702590301e0000e482003015541000c45080c0d2198800d6a008007400c40d113500541c10b282d030380f070485211f90380154081e10010115080412006030180042d03540f10303908501507400c1c601c50f100003a10f072440040c41c0d0342440d00106124000c15000758415000707020035100b40f4042e031070260072440e5030305c1601d50050310800f294003000030a6000006d50b9441800f281c040c1c200d0342600c0c10003c2c0751075004480110307454054070a147c0038402003000124450b00401b2404665034403941055410701c1c90300d000c82 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 467324937 1250 467323687 467323691
    0x1e0e180106170f0706090e0403020c061201090e070605030a0e070503251a030126060906090c04020c100b0d1e060b0f03070317280809070609051c0515041203 69
    0x10040b01b60000241c1c8100d07041454035500c50f0303885103800c038242107900c2805a400000402c42c5a040e102000d010781c16502c50b088104561020081c000c2e503580a00d11880303001034030400010b102207003d504060084008003040380d03051620b6600003803e0460036155030361030058441d441c420801c5030b21502320041c18880c0b181c500240720600d502c1014881405800348010718100030001e40c016080660081d8043c840680d18982000b4810944550042d03641541074481e201c5030852524061080744c1c078402c115802001030a100f01010400b90021a0040798400c070422101404075030070100044414005c0300000041c00d10768608070003190702c0004038600840400554008503100068000150307608050429290228034800450310b20940d501d104520304004503414450300700d030030400000101e82d00c6004032903441461050340d8000c2071007010001128100f0810442c2410400c441a1a110840241d40854103840c0e1740c0c0b4001c52140d04080c651909000c00040c01b040a10000c0700c0c0b1410721302 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 467326187 1250 467324937 467324939
    0x12090f080a060b180a0c0905060a0e15070512041a160b06040f06060201020d0c260703140114010e102a0227011e0e180106170f07 57
    0x24403651034015030002480c2c16965005898036589500407400400c03881444d40a0b14a0000885405407034006c9205000c510721000c0801c1906c0d00d0003d40740c600920b56510008803c5031010000c24844180000d602e40740c0401003500410414080140c6140c0d2035900786039030f0351030b00c540d010005208001541c0c62080901008034003908981c2108001c80c0c1252420341c0c60b8075058005001414540c00d0102164030302040011000d4064024107002c59503060204000c012403001912803030030f45d0755450304000c01501010240e000d00c244090700034055140029440c807851245081c040303000c0c1c001290000907084003503115a4001921000c014096801440350120715601501d034118081929129215038100e000030201e03091000c40403e50014001c0e491130712104030b042264a4103034003005c5084585c600101c1c840399006040c41e4a035007509984186c140c54401968190314000d002100328200790b0780b04102c1010240503401c0600621103816200c641d1440c8140c1c54801c03030710383d210450340003010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 467327437 1250 467326187 467326199
    0x102071202210f130b0a170612070302090c07441b010e0a0609020a120302070b030a020c0604050d02101104090c020a05061f0902030f04020418080712090f 68
    0x4207660280000302d4007144c0740c0d50629814507031091140c10840d00740d000400e0010040d58041401d500c25034200140185645501041c803074000050111031210741d010301401c000605110080b01e500c181814074032414501c040c0d070740182c1070041c3c095003001c804500341c002c803075203030074102c2030042030300880d4408907000c100c50b249240e82c02002ca005040540b9140001c10074030b02074008a42e01c01c0c02606907020301506141500081503001c0302603010341c0000c038020a05a070b030920390700507454068004140d09440c05028000c654001040100115003d012445480c001023000c0d43c0a5403048001d000c400484910013442d280e64800000da0107404c0c1116000496085400c4a041d100b040c0ca0200b1491180309043e0b02e80442d01c0700080c95807050100b0010403050301840050030f85103040c131628021b942c8119040c1130380020b545240e045112000840e00529043c0c2c024136030500c0d54116030220614684070a0078a03001424281c0e030903d014005e041c80207500019250250038015620145141800303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 467328687 1250 467327437 467327503
    0x90b0301150e03060421140f040f1d06060a03090506040f06050a060509010b091908030306101409040504141b093601110f0913061208030c04080102071202 68
    0x70821014480c0c4511070280350b40b180107030300320070302007c3c0082e83e95100b00c50310065190700920440b82011113042000c03916200b80d85940d40390000c045c0010f82c00b5102d0008101e182d501006240c81410ba88800307403030008400740400c03403180b800b60781d1400d07000b542c03403c091095441c0104481750081c500b96040c001a998580414155406070664903100c2e040c82c0040b4040905034181024a0204000c0004140b42c1c0080150300c035a80c1a1001c0c207544034070b8030003030710b030500101d100c40030061003800313044001d0520346d00281d4014042d00d48588050321580590b420001c6400200c04100702d1302d0b480d00c45038104419a5500125103103003c040c02c19104520b00e4004003100c0076400d01c00a00e4140004100003504140c04120000d210642d0b940381c801007291141d4000c61440b4020094100ba0341c4508100c0c0c03044808841400d0000303100c541940d550f410680d40000d0242030041c4083c040800e40540910140400510860070b4110304500c000000c5e00e0034070b9a060700b8415001d10507050000d00c0c0c4803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 467329937 1250 467328687 467328713
    0x2040b0906060a05030405031315110304140f041b0315050904020d0f03020c1005040501110708060c0f0705030d15210b070e130c1209051903090b0301150e030604 71
    0x31320340152070b902c461800509602c15459002c0381e00b440664089140c0760716044602c9a20216101ca0031100d0b21001c2445d1640074600c13440c0a0340079206058084da00340002c0411015400910002c0c900210101d94455450340420083c002542c508080c801c200036162000d010b00300441c0e41c0401c5180c2540040c06108450100a080714041c04105d0209402003015410740c1000800a42095541c9070008007603411500c43c1030f0000742d076021480140c180128900069840c66400f62801d0340d00d00ca80c41265502084d60000c85500c03c00c000000b0503400e0026200c241050300c008213040811040d400c4803001950486680b060403001c00489a03086070412130f0515502c40301c607240316903910200780e510401900c0031940082c0d064004409034082a0300066031204e0603202c2c05805058001e258044441d07200c00104507502c101d0f2050350582c0c1e20007007220080d11078030300104034549402c01c00e55250403c0e8420203a003842d85021008164000c9031400c01050f044c0c006084d1840c2503100d0321868445 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 467331187 1250 467329937 467329957
    0x503010e030702060406200106150807180303050f1c0203060a150206071d030a0308060a21020d050106080703050a0c0603050c0924161a0402130c02030d0c0c02040b090606 75
    0x413a1680801f10011241c40703049009144008104059a5044002c075441c2040b4002c0001886000000c10460050b21102030bc01c524109504603141140c2c0c0030351300340d400800d00d100c007030905101c0c40428000d400b68400603400001009a01ea0511005000140d65940c008910500b07041d91400c001e02e60024501d40c0c8070909241c4180141c584d42d100801070b6240004080d0035008aa901c40140b6030030a12080c01040203440014030540e496803907510b5034442d20310140c0d85c2083c0c242e104000d0328141ca461851303240079800004e50346913161016840c05107a40c2c011115a00074042c04008d01407030795420001400241010700540c90003001c10206d62107804440361080c84200811241c0008003420b17034a40b0072000b4285942c0300921000480f521004410071a004801088071026020f03c0440040c02241c0c080c02c4003514080d5600c40344054030030b03a0164400c51000340180c040000250040c808034a440c0d4442c140c0d40c05490050005413a5013001407805a0002c0c4244481c640f200411911140f030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 467332437 1250 467331187 467331197
    0x7020d0507031b03050304030909020f0403020405060612130c0b0a0c060e0a050102040f17010b090609040f0213090605090601080d0c030c0c26010c08040f02061209070503010e030702060406 83
    0x800d0340360030344071000411540b002c3c00c46651150030405400400843c001da00076220800700d180d4503612001a40303e410012514070b101440b0400042c01d064100300d401210007400f0038246005840160f00c078490440d0b032006000c0c1c0300b64244081c04000912407001d80708c4c403100710f032a00c4c0580c3c10240c41d0161002000741a01c0d91403880c102c00003c288203200401d0341c040c1c0290358496488034040c00007011070040510346240049010321400d0140300381440104080e1000a1540d0f1b003404010340582d00a0060310f5450b0006007500040e5102e880300c01440e200d11000245000d6641404800c413140181101c400781c0c01100148950300000950a0900141c0d1810b1000b0911500d802c5550340d00301c079802400702d6104540031407109962000c0c034007400d403d0b0007542441c5082c00e40880c00d0380c1e0800000320100c0c40b070070b0104004c213503480004060580080d20243c07902e0904d00c078803084184100c8101c0ba8075008030109216516003801540b0314880da410085082070580d40005d03045200b288500001e0003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 467333687 1250 467332437 467332447
    0x304181a100512010803030105010318050d08091219030b010c0302060414030c060a06031106180f18151504030206040905070315030807050601170a030e1504060c050c0907020d05 78
    0x5118504440301075032207075406500c3c1d5941c0d1000c2c80d584d4100f0300480380031034104120020070803040c800c2000f50741c2d00b010003000031243c040010303102c15030041c00700f0b0003a000700c4007c07182d0500c0040050109814140240804200906001342140e07580d010070340c10091201c1e00440865400111160080e40091300d800c1c2d01054201000e10f1403245900ca2049402150100451011203504ca00d044074003c030200714103c1140b10401c041c0f407103428000c240c452132180c00ea07112801c2990382090b0030000500101001d10b821203c0c21410b240131a0070080e42d02c00720304c42040509000342078176061042d54180d5030506007140d000031242d001c0c5003e0084426076620000d44445d1282d004502c01c90382e140d46420a041d1641051250707548141c409492610036040005200c110084001054041840c042c050090481c0e030129400c205020241d40d04c4103001015100c8418410000d1004000c5500c5c2c80300004803a1600500b03002c2252110b51240041d6003c0044441d0007003020a541d41462030425559 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 467334937 1250 467333687 467333719
    0xc060f0606091801031401060e010b0d06030f06091101020c0d02061608040e101a0a031802040f0c08090604030504060f120507030f050a0e0309040f020705060403020304181a 76
    0x6401180380440d400068001e003c400d006203540f103141a00d0140500c40c0078107000b40f010380d00341c500324441d0104d00a2408010030a442c003040103859800c8480b035010400e595a034490108815901c00241c0d000d5685900d06c0c3c081042ca040710700c1d1103142c203001604a00d2141c00c0010b010801044002c1d004840c001281c0c0107042154905250f403070352105229499a031078540c0e12180300c20844d501008588400000710b40580c0b00c05c41c04000c041000e00b95494144064021000342400841b0b000c0d82c00241e6990100590b074600442488107a200c030005094419980000e25080d8003820205054209a09010119070300600719400d95031982403c0540c184003000c206c5846004140122040d4942014029108e50581001c0c2040490240034001038407040f8010f000c98068614284080d40100300308241801c280e0006a4044290304005003001c0854070780c5401d100c011501100160000503007441800c0d070301e0300e0800300c1001050003042a05c06503615008260100c203055482240161a0540c032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 467336187 1250 467334937 467334949
    0x3020d140d0e04140702191e1101170f010b0714071701060b041a03100902030a0204090e061312020c031005010f0e01030f02060706020c010c1e1403060609010e0916140c060f06 77
    0x400123011240c040075034446d0034401040d030001c081944c000b03001c4000d088031020500c1052402502c440040e0070303072030b4685060341807194040c40044a40410325070000070100c0040c423098000300007254ad109035070740212070a142192138503000700706141004d01081c40919006101c0c0d210350750320301a556586e0b0b240c2207500300c540d4103190702c2905d03154000000c2181c074001c2ca40243c4201c0700315043c244500d410281406840b050107c8910003c1050103580c0004940c2e90b900342800f109003401510140c446103008641850102103881c0c04841e11900104980b01078800650010500740c07140720103d506550340c1d60000c00f0080000303442030901150b1402400f010764116521690040001c1100b802d2200c4007500303070f9006901541500300812401d104140c0110b1801140c007645c0d03190946141d03501340801c40c494120850075410013468900d900c40e96112210510f00a65014845480c100010800103104003058000e1031040d401c14400e403045050001000381d00100019a040242e607582004a82 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 467337437 1250 467336187 467336213
    0x130303091b031b030b0f0a060815090705030d02100b040b061207030b0603090705120a0204050117010c020a020913060e1b03010e070e0103020d140d0e0414070219 71
    0x1044003034041c0d0318140ca034600c0300c803001ca030321030703484000c90102a40381440070030f2140c400a0180c240c40e60000c2c628200307001d00340f070340709081c1100069015102c1d8030561170403d01034031074076014408009000854000700302071002441c0440041805000c0d0a0000b920b5007461070300340840c16210b06a60115940300e410600b034409002e40040c1e203916403960303024004d14007954400d01084c540001c00702c1d1403d00c40100c9100d01c1c0b240c1c0041090034904003e0109259240d04030003600c3c081c0490301d2006039220300030f8600030301000200d40c8016030303402041400c44060790b42160555004011000058a402c41c42c20380c028000c4100d2a012042c07030070072034050001c5803030882881c0030744001c0c003900104211400e20135001c16002008042090321f4002d03a201643d001c1c2d40000c02503400100010314103000489031480c4507150f025143c90107030658a20f060700700e181c107002040d2501e44001140c2003510600058041d80000030340700e1f040900c1b0194503600d0640c40040c02c140b0792140745080c41441814a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 467338687 1250 467337437 467337443
    0x40801090f030305070e1c0203010b28060e03150919052503020a0302040c020f101406090411040c0306170102040512030c1f0605120c09010807060813030309 69
    0x30290030303818501041c0000003000c0440c0440d10301400f1500d0540b05c0c1c160341612110103003c950714185610b005500c00032080340c01721f078559200c00400b419601ca04481d542a03100002515402582a801010f00440643c0104040015240c140d0540c0e03540061050054a01c0b541d50342d40365110011641e0602c0325490a070015500c1d984150b02c01c1180000305010304003081e03003802900202a050725000c030520ba21029501259112041c0058a000d80c00041110703954011074101d20750f14240c050428a40082c114030150f951160401d2440c04400010f50014080f503400c819450259916a00518500621030256030b41d6440c5912142c000d0307214001404810150110104807281da143c040d40c0107000d401e01440c042010110305d4030000007071f40d204003100d8028000401d10340426800412580d1003141400351100d07000902901c074240f41c4081c080380c60020f0848101082e080c440f1048060b0300130100f46d84000d5040021a42c021803e0342c000200111361004030099040031000ba240d554409 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 467339937 1250 467338687 467338691
    0x803040b1017070609090b030a0b060102190b07030f09030c0308040206040f140a050415090902150406021c0509031f140705031801020405010f0309022407060501120809100203040801 80
    0x240a111400180340d40446145a0b41c1d000303600d8072204400147d4000c528603d40541c000441003001406c449a400ea0010b0188100c40326007804202460b500000c0050035103100c8112414440c200303626004086e122241200d082c4140d004d6545c00500d840c0b0380030805020010440c0101d811903641100300d400030310851000f00c20311303a20354290b5655400002903c07445842d0003200010f25045c280035881d02d403801e001c00360312507600e4600d614010345400c40040303900100040400c0142c0a002c400350018103d103600810300c59105034451494000c0130b542c04010b101084c07041c0481b070340d00011038890916003400d601080c8414004004003810300650002d01103c200d00801c1200c650001c05184a00200b08000204070500180f0508070b03c214000e440c0020020390403010701134025040061a24805000c444120100101c1036800106042032100c1c4c001c000208001480480d005460250003083c1c25090300360709a543d422042c1c8111a0101e004002e0060070200d076500034410b41e07004084041c02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 467341187 1250 467339937 467339969
    0x61303150b120f030f030a060b0a0809010f0b090c1b01050f0f010f0303170403051209010b040b030111090f032503060f05090d0e0303160c030b06010c0803040b10 71
    0xc080050451a0300481c000c00440d54521030a140000b0307003031a290b011401035440d015990a940d160b952000b0b0156464503100c14000030207a10000c000e01c1c1400341682c0700017150400229907400c3da10401201c0341e8682c20700090100c01d580c0d1a240d03039080411507440d269200c4a40030421290000360450300569440d000806c104101141e01239481100f099a010b4400e0fa2541c0980c2c012101c280400f42c001440446642150400c2c4402d0303e030002d009050450500611001426007000c04803454203960b51100710841080c1024044d071045440c08030020f200303100401e1090749847c05082400b80c892907520058810a44041c024200c0e0440801d50741c0200164541407440c69604c1d51000700c0c6d2103072819101c114003480078803d00303000d520540054410511302c000200c2e004024040440c0d850b00042020441008a2034016079030b00341714000705000c0340d1440c00c1c08030f918500245503c0c14030100d03810682c0054080800c0304d510560121800e006600c491104c20710154440c0c00c031311515030a4440c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 467342437 1250 467341187 467341223
    0x1020306090105030d08070c020f04090515060102120d05220605060907030627060819140a02090406150902030712060f0b0f07061113091514061303 65
    0x154450318099480e6181660380c0c40600da91034406074100b400185c04500864081c074031a41520407400d000412209450300058001000c441401104440d02c1d4030900c10350000c1c2104846d80c590140c400d00251080180b4011031084c01e00ca0790b140541c0d49a0b8810000e6400a5403920407468000da441c19002160010316120380101130550f0481d00c14010703000064401c40c0300f4001c0d00c0c1561002078002d28280543c503031b0340860f0f0f40020f50b600c81040d1210300c080341e80e0b40100210140038140c5801c070544181030b070500c2c440c90820002c8081503a08907100c00b8000d41c807078000240d00284d1295001072000c120031100034020600da0882c3c00207a0000051100781d69020303220030b0240c6050391007003091640d1161400803c420b0f030310501124030000d20680345070702203090142100c1405010045041c405042c0c3c1d00720340d07a00003650b91600c2c0302607a105001c64441446508520740c640140102558104088940d61203200404284a04000260280c0c11010715000c8002598020f07400040284170079 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 467343687 1250 467342437 467342441
    0x102040b0a121a0a0326160c0506070c0303030c11010e01090201080f10060c0c0509100924090b19060804030f020f0c0d060f09150b010504031518120c0b160909020a180801 75
    0x1d1058030002c0c034009009c1654903200c01214170296000809808203451039030198042d003441841c1009000c210342400c48141800e008800c1c8291082c4000150181e0a2001401074240640132070b40000f451420007119071b1040c12540305407041c5003095199511a0f14110a0b288a60b400164215032081d00307201422041030900002d071208030360305001402c0d140002c000e1b800f9040d900641c4601001c4000c1051103010b0b403298514090181c005945007020340000903844170f035a48800d001949020801050550000c01c0e00b0b400501407010b0005080040c40ba40e0313840b0340190800e8411002600407904100c0710358030250003451807020600040015041110844000c4031031f010300e0500b01141c0b140c0942c400d10440d010340f503000c000c00c43c450000c049900c000b803c0e89100e07418528032a013600030110750041c00d00035442c0e40726601c0d81002c10340c2c0e140c5004d020502406990584848003c0180010b40060a083c140c4a01d81c00068071600000707021658030346000c000c12203040040902103002c15040d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 467344937 1250 467343687 467343727
    0x3051b0405090102130b1c020726211305010e0c010e040605090a05040501110f0c0c01111e01111804060e0408030a0c020102040b0a121a0a0326 63
    0xc80e4208030755690210200e01340e01c0340b21060941a40322540070f20515014401a220074407200000c6022161080141c2d0201d90100200743e445c06910182c1c00183e480c88140340c05066405011b8500b0040c1c9012822181c940743d659000507940e00100140d558100c20078420001600280240500800300104030f450b4240981214000307418500c10050300d0905004000807194003420703401c0203039203080c032003801040041c06c126030554070b403020035002c45941406460400020310082e80c2d01c01420a80714901045810701078140400964000c4418a0100b10b07a0f450110040e0740d0324001050720056401460b040141480c08200443c1e81e4241522050304016400c1e07050754100855516400c0403c3d5400c1d0440f0010722131801040000c24909280d007125401140b0b900016007082c0d00ea030031000c180c0d08020241e40000d099a10441084621401005c100590328202c0410010080c00462024900d5020142c00e18108180b403502203800c803500c0a011000c0049442c0c0c807020344201142e246051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 467346187 1250 467344937 467344939
    0x30919030e01120c120504020d05070b04090b090f06091f08030406021005090d0c06060b030c0d0b0a14040e0a0c0906030317090a0212030913051b090a05120703051b 72
    0x240c0f440401496000d0320074000d501c5542d0b21040f1012100b2180751000d03200c001c208a803c05980708070036000070000c018800c05410f4854031241c5880c14540044100c1d00b442c2280c41c402c06541043c00b034032880d0710b25416008a029074a000c283d540d9100340c1d100902400b403100f1a242d074007600000c0c4074107012000d04256510b80c0d0035101c540030b03054100403e48005440303149481d00054800400350707002c0c800350620b81c0d11070300b00445c0d455138615503011303560000c1b40c0751007910380000340300c04122110744188040d0ba8004c5038101101c40c01c0c12140ca03c0105402203841c01a99145150b441c111401c0000c400e00d03c0e400000b50014541b103200140207003450b071000310041054050700701d56000f903c0706003a2185543d4802041d002980c2d0b000c01c400390024000444046c04104815040e685502d40074401640c42800085440e041010a1004811400101c40d01404052002d0b40c520f076540200081201c0c8225982c041c081c000907030090074840c16910003411481120b00340e076050350004a1490200c90 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 467347437 1250 467346187 467346197
    0x307021002030103020901050f012a170c06060127090b03010c090b030f0a110d060f050f0603010b030901020c0d1106010f032103020405030102130e150d08030919030e01 74
    0x16800080c140d0000b03000081d8440f46081c0188428182865404203200301490702500c90a034040300242c03c104201c043c14005021103103040144164000014003904070003103842d1900d8074074607070180c070f58802a10050400c0410b1098008bc0c08109a40d2859011182502c0a40304e99584603400101009000d05000b542400000040b00d40110207003011250404100b81c9542d840b4001408030180c02049090030715a1410010401480c0301c0280a448110103030001e115400c04041d02843c0d005580158880c1c3c49524101c5100d46450b41503a044400e1880c426849480307440c501400b81c0030700004440c41788038a0b884110700d294403203203207504042000207407401a43ca0741d51100300d070710031800043c180f1500005005680c96503959071082003816441e0040c10103484030f001a0aa0780510403003511800c1c503001c02c1c08081480d446158110703a58036030071086041882c0c04120754001900340903000c0d0101000042c0055803c1c05207a581006000c43c8100c215036524005c1d01c030a00c10000d07680051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 467348687 1250 467347437 467347453
    0xa09020409061d0a05100906060206070914010906051602042904051b0306011709102f0a030b060708120f0402091501020c060d020901080c0f0a0e1212030702 69
    0x10b203083d0168001403003214200d0829a1403019610160002820080041c007003190300250b400b0b0107108481c09000150f02034105030504503030091007025146c100c0300c0d54581800300303c0d40580e049820700c4200c0c0d019007421030b1221400381600003240038003040170b0741150526030015181b0300504100d03d14a00c40050706002e40714000c090200b15032045603000703510b10008140b140301c4041c84024550204051410000c1c0c1c0b41c2c00807107151100c20a4a840545900440000d10019800c0c003e41111b0f110101c9003440302c42e100702c44181c400c140d10600151100002400c0480b45119400c88000004003401d802e035a50210324066040d0790041d40b2007901800e801c008070f10390482c0b82012130b0290b900241904002d40700c254a1004d480d02040082d07041d44540c5810510701e8640f08003600c810640c0b041d0050b203c91140001610698009015030410720007001400da5011030300042d20700a08603817400141d02c00802c80030a1262554041a0100348111244544a50240300c0254443c22980c0d0075640d0417 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 467349937 1250 467348687 467348699
    0xd05010f0c09051503090601050d0f0f0605070215130f2a050a12030815030309040e0321010605071704031a160c24110a0801031a1915050a0902040906 66
    0x40c5c00f00b9150504503810020040105107084241c807412a4001c0c101c0070013002242d5900c101810f10800c1c01c80d01d079034070703082003200040e010301c02c005050341c82481800b050702d0406405080468040e00040800b102c2500143c140032124400704661702c0720307000060030030000c5803000d68180e0145c0304c0c2c00c0c8a6040c84001160f00a280030b80160f805070715440303486090315100010b481c0c0c18807a0450300d415101c24040700c580ca603918050843d402e8a0031010790313514801d503030b641c148500101503e1140050000010000513a20108541d1015000f070048045000c150070303242410b02c90742c2c1c00038007800800d050340300e0001c02583d800c601410101c4d10142c45800d489205884401d008000541030840207040d1024005c10240c4d000c00d82c40d075080380060304208058100c0c40a8000e0918040007405140060042040c6100a5036085c189131400310418505180d071002c02c030400081c0e036039259840d128800e02d4079140010040190800805000d6699190b56040000350042d125140c0d0041c1042000160 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 467351187 1250 467349937 467349979
    0x106030302030702132702270610030e01020a120c0201020703120b040902120616090f0611011d0f060c0f07060903020c12161508010308210408040302030f0706020c0d05010f0c0905 79
    0x558085010108040d0380b900100400cac001640b402c0c03801d260f101d00203002200000c0c0b00900303c400d40c075100c020495440c10090000c5401149214003503a104012a03000320380c01c1141d814108440c0d02001c03440340f445034003040c0540031403e0001d4000c4180d10912147c0c1902280c907a208034000c1514074616400414111540c0c00340b4842c4114002841105020151180c0390f1102201019000843d000c950100c115400c08546512004150080c1300303401c107844018050f20790030592280c0340a090182c1600c214016100c0c0075001000190340d140003030100340c000c3c0240380c1780860051100c550304c0024892151280c06520b0080b07010301c109600400d103a90b050400c042c2c2140a941c2c2c000e61603003599600700e2607511504040a036107007802c1281d04030441440c52207102d00d06c00e5600303944440c03a40c4140741c6806420965802c441d007001b40c0c28858031307074001030f1800780e04000c0f030f8481d214100d00e0500700d0060624100c80036801d4200017044500c503410484130001c40d04283d84440c0000903601750510 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 467352437 1250 467351187 467351239
    0x1201030807210e04091a0c0c0607050a09090e1c091d090318011b150507210c0e1c0210080c0f2505060f01080106030302030702132702 59
    0x802c3e006106011242442d600c640e010600c0380b4143d5804111741c0d0f10800c2c40210888115603442d0700003411a00510003032003c0c40d007000355820144d052a50b1740c035000e880c0b00c089001e0f501d911507517485a000c81c2d440402c503614040c0c50303801643c0107000113030f00000c1070768a05003d0403041d800000842c581d44480816050f110300c500c1005542080c8070816400405d040344151039041000041d0050700704405030b17075092840d921840000c5550b80c1060501002d490b0300804001c244030145100c150511403040c1c136005d50900d5040d00013100d0b0009482540c9421205c031106030010001c0b03840c0030541400c070310340f02c40450003141c2c110891504400c04507030198086544400d0a030051180b000c45c3d441c0303200503020400440c9001e40151440e445c0390542c000582800f40d50329400b15050191000c840c00007240901400c4c0000e1041c80c0c15501d000c3c1d5030384503140b4003d0080381100d1001000300040d60100810303200c21051900f06000c84c050500007031100f54020703403007400c000003625105819030361000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 467353687 1250 467352437 467352503
    0x10c09050d020d0203010e03030c13060801060c06050406150e0103020a150f0c0302070510021006061407031d10020a0303050c07030906050304050109080301150912020d080c031201030807 82
    0x24107010301e41d00f807042030f6190542c1203802d9906c03800503950307108062000e184030b40507101484ea00c6405074801c1c088203180661006003807100902c010f10a85501083c41c542c4160402d5001c80c060b00d40d49800760003005a00050309000100600c00b00e441080460054101d90007207a40148281c2c0700d4910100c103442148000020407010080c100b2040d006810320042c090003401030740c900f0781e920300c007003024030200d0b480780c60050700400120070310300c0e046114070009009140f134030f48585044040c24034010b10540d00040e091018101c502c100c90002d0340c40024051101820000d14840840e90107540c440800000700c021a00706400541220300c0b403010b80700d2140d010b03a1412700191074100b054816034030150040e6030342c2d5214240386003ca500200218000c3c241c401c010120021a1a00100324841e00e4000380b0791405143d900300d0250b506e83d08440040c0340c00900c4e00d82d0b0380e00406161440c52050100d0551224240c00000043c030801c05c001d0650b0364001c0005c4e1140444400e48c030420194000114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 467354937 1250 467353687 467353699
    0x6010807060c02090711011406040e07060522030606080a05060f1005010e181611010203040b01050609130906020909060f01020a06051302031603061b020604081602060d0e010c0905 79
    0x960244c80c004201c0307a003164040c1020315403121400c40c0c03d82075401d2488205083c02c16141480361034201403060715200800200980310b002d040c40002030032407140c10711020409809000042c10040031085900c01154001d0042103903e81d1a240c0356107a00c00c500c405e135400e000740f04c00110344000801e4254440e50203088003000d520709080041d01c1454100440ba904554400070a0310b04041d0b040256004040b01c480100860004030001010152a1441d885450340140140300001e5001b00c41d82e419250210784554807460124081401d5614003031100840b103003404032801c00d018031a8000c2c82040d80555520362941d503000244804110840170050059010181d00c4c80410496031003550440c14800d001d41c000e150030b0300045e25103184026026885201100f08004000c0721b4032403584064035010010104003010000a0348500c4010009810900d00041d543d07031505120180c1111258001c0500d5200c0000718020001400300c8550a01c0940c80c0090400302c40340103042c0c000846800401d9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 467356187 1250 467354937 467354957
    0x1050109032117040b0114010219061a1e2e080601180902030f090a0b1518070c171303260f070309060305070e0103020315150a020601080706 62
    0x215120303010322840201c02c0001c1004109688840450101e018502800602d18294142214200e0a00411000c0c230b040d075000b624400d840e0011406034021f0640c00050002e0a1030f400380c10285030a40101c5070641c0911540988198000e1281a9001182d0300384c80b4086404c0102c50000c0400704010541402c0740c102c01a05c0b01614403807031300755074490010300d4000c150040a0a03c550303000e64a400287e03038941c01200300403034210f01c4004294412f80040c001c02c00d11035a504c4900c0b40303540141c40300d40c81c044284c0c0d000e0741c41c0d10382c401d0380c000020b90b0610700442031508090052200070208012120040042552088800710605450a8800008001001518580d2046030240342a043d00410985030303040f00d1508521a00500480e0b040707030400903a0340445180040206846800610600d45802c0a20864603400010390720110001e01b0016525102d0702003030740a480c621030b4455440210705c1000706a444511000e000846400d400702e0307429980702d100c0182c4a152a004423000140c0740c0700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 467357437 1250 467356187 467356223
    0x190608091f0506220f36030302120a0506120d0e0f0d08030109061806030f030e0d060903090f1d1b0705101e020901080708060319050a06050105010903 66
    0x401203801000041c0006205600245801e003408071400e0004140c0d950354418800d950410f00850034100380d10700004805030100190103403e85040c1d01c1a80f09a4062540780c010540254101c400654040d0006030ac01d14201340b5041c05008129070250080103a10100c030325543c0002021051500d054072000340008a10b020710529103100450740354450700004078807012480d584011406041c2108000c40c840d07081030115540000044088034001d86040b0b001c00c0412041c0e1002851158145428904803046200051100040c144060290b0b45008550f00416410810705400c85220a0713805040c240d84190010000d4119850022080c502d0400610b01941c0070203290300e1200000c032400d05100c4a0f440ea1464000c0101c40051090303030324201c22000d04200800d43c40802c0015405610301010040003d145400143c400000d01c0801c101003416640e050018103d1000718003e2294a0101410004d0342ca4013000f109907032852500001080c1944160312580949800a520300441d80c0d0103c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 467358687 1250 467357437 467357441
    0x1206180b06090f1203041a0a09061409090615030a06030201110a0b1504060b0c0d0201110309030912010f0f0902090a2003040c0509010602010b03013605030405190608091f 75
    0x69184185400200b0010501120b0b020768018561130087c0c80740d4482080020103402e007159900100d0038044101031480d405940c141c00c68075000c4003038480d1350150712a000444e18001c06102c6081c0c007400e021081110341081036000c002140e000742e84000c20301041d29489926210219009000300c03803051b00103140114200032000313a41c2c1001d0800942c1039540c100802a5030480c2d041d51400e034204482030700405509029190b4003128026200f8510308041148640d20b120704040e8030b01035402181441002c02080d40040390840103081d09100f00003220350464028111141f04a10424407013000c40c503e206284038002c401e0328910760000c0721801c0d5038020140e40c1c1009204644035001104045981c2d216039034991300824464001082105030b00c020103013512000c0b9132042c0008880e0b85600d2560440c540300d40e80d612000f140c1c242c01c90407a801c1650661045400130307504025041c00318040313401ca014102c811110299034850847c0c9070500115111120000c1140808a1110b203400403900a0703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 467359937 1250 467358687 467358709
    0x171b101104180e030904060617010609060e1c120917010e1207111e03061602030412110402070b010f0e06060901260a0516030207080f0702011206180b06090f 69
    0x701c90a00c01405c001500350382c01ca070082c40c006903030350046d07000b941c40081005015003c4c41c1840c8000754106440100000c083d0f8044a00c203c0200f1519008003451111006c4038a03000104844035180100015060742d005110354407480078500c4121000303800c11302c00c02035118206000b07044504a600501d0b071058211001c00d1f204038020311031745100c541d00c040c900801128140c1c80030130034050000c05c060424a00400203542840b1050088412650110440b01a5101c55100d0312250f803003400c0001d00510641582070f00617100007111014020000252412244610500c1511a440c1c250382c982d11801504c4240c1c0003502030050744110360180c180d96003201c0181d066851208005010504084015500c480e0341c541c0d00c00174001280550310071010100c1550905520740840742c0c0d14101e8a10441c00044204c0c0f00224040046a02ca40140b00b80368058180c00d211442d00c8081c401c22100701f071002c0200070b901c1c2410f90340a60410106035030700c4017401000002d440c48148148280c0c1565 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 467361187 1250 467359937 467359961
    0x30304080d0507140601060207090b0907020c010f09031a0604200a0503191d0606012a051e0d0201061406070f020f040c09030501110313171b10110418 66
    0x50021004d42040100b01e41402401306074001c203050761400e0034003400c860002101a0046001c4410005c100c0c5d00000d025910400c2844c0005c0b00007c0300340c040700d07a001e00d40c000400c006c40c51400031240c030b11880440c42c005c42040307800f0455100e2010040300c0740a000403a40301c24074410b01c141c0c2d01403402440030f190b0000309107402031001c0b01d28003103c00890f50801d0580100101401080d01050310411000e1360021081c02e15261040c0e04a40b8400c00b6501c801400c03403904a2025840d080100c1402401c2052221609040072810100b840580340c0c1000c2444400540ca00800040c40c040d0503a001d8440200241c652490210562640d0240c89840306090b41c0025106c0761005c990f468520030800604681d82ea1710300c20781d0075458291b0964920300d51070031410000f4024443c1c3c105043c5200141b503a44500a00401c0e081c0c03001900583c00b40d2160604405103510940401c003c3c041540011860400010400d112400919102d1401b45025071002c0c0a5240c29107440e05400d9030003560b11600c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 467362437 1250 467361187 467361203
    0x6011512020a090918170a1209140a2306060616030c0206030a1505060a050f0a020a053f0a0c0203070b031e0702010506060d0b0d0c03120905030304080d0507 69
    0x10311424480c0c02d1700c0c121080e40400c0d19413001101e0500070b000884801c460201000b1600c2d2100c03108009000a01c08900340d810540d80745034050400a0380c8952000c44000e170801e69114491170309020202c4024110f65110a030752907800701c4207010707010691a215050091285060243d415403562240420380d60031014484070188000141c0d4440c03010350311079035014502141c00044407118000006c050303804580180000d02c80489410340017004c0d2181c0304007404a2a0f26100142d40132031800301662005086030060b42c01c01c20101c0814080d801c040030300c185d82c0300e0211100c1004040710540c031406106074030038140b25030000107105070031003c0310380d0006040740d42150300d0340d06800c201d41c03081d40d503040000c006040580400c0102100b103680825940000c1040d468003c1c0414520310400b032a84681c66620402040340741e58042580407031980084080b94a03540703030719103403203510084000840440d0b11400002040d142c00401c5a0954480da00a0a079101c1d000d041a00e0740d4008030021a00c0e11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 467363687 1250 467362437 467362439
    0xf061103070c15140c07090b030304241d010801061404090e0109020a050d03050409020d0f0e0f01060f05033f032202031b1210050906011512020a09 65
    0x1e09425840c00940351140c8400b911458062010348440203138080410108014005508910742c003044a500302c6500c40d00128220380d00a0000c0d05501c140d03007006041100f040a544505500101c0103245803c0c1615200d40c6070000d0074024200042040d0610700040c0180c1c0140000d510880184107404920041c0e0b0707040645501d04141521030075141592281e648000e0304040d071801e0342010004000030b51302501240c1d0591002015403040380940c41003250002401c40b0b0020403940108905224180100700590b5140042034035181c0c0000d2290856003040d4004c10034407111050304085a8000b4000d2a51864130900f4085074221034000c200c242000711401010381d032600c510b419010a840d9941da6883c81d120b614030844c4103014229002d171085190040006132800510000c0c01c0c01c3c40140d24400290002c002101d456030b05102d040e941c007504505510610650300300d0f5000e96440b40c1034401580c0c03100c18030510f5080d0500c0600c002103c0d90aa26030000195005040524251810308021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 467364937 1250 467363687 467363693
    0xc010f020f011e0c11030301030602090a120f0b010b03060f091e040803040c06020105010f03020f150c010e070b0a0804020d03022505011209200607050d0206070f02070f06110307 78
    0x541e603481000540b03041041d0030300340011041c8a00c02480c00141481c050140c60700c5d0400307560303000500004011a074001504a01a40da4000020081000d5907104109468600c0c2108805030071001c2112203079004800810b02d141c0740d0341500d01c9480302030b04011400b092042040801d00c4003070450305240001c00880d9100900d021640c500c0f5600462060b03990307081a02c0c0050303444041e50f01140469250000500820f0500b4139840d08680c0c04aa9080c00c4161404c002983c40c105420079034596100081d5402c000f0406410940602c0d1080054413529662000458440e110708900c00d40054040e4001a0051409508241c02d0901901c11100466007014151150850745200f50140c0b2460820400c100c0d039010140710301d8245800e03400d00000c0056038170070114066400071000340103400c21001c4c489888120a1b01c1555800c02c00301c90718581c2403007020b034440b0801d50700c09001441800c5a0480c0e00e0000440304116548001170b42d40c183d117000002c4074803406010101108d400100685004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 467366187 1250 467364937 467364941
    0x60b0a0309051b030709271b0506030402090a090c0e0c030103021c0b0a1e020409050a0b12190602191e0309240b10021b040207050c010f020f01 63
    0x2040169440c000740303554103070500364580209210b0b84040502d8510b01981240c40200303800040301d400d0440484c08070a00350610381040403090080000c040841c03020800d0103210460061000304e8119414a2151904107102007407200700c2d000b0790003141100209042a07000d501a02185010b02004d0100c60b48601c203003041514161030411455902200600179443d0641d02030304550159488007031000440d550b00c101d4070360020b1582c1c03605a6a400e6001508006d118025540c58a0f038004540c0d980e01d40f080325008003010340340101030a203010000d101c181443c1203100d4180b005800200243c0749800d8001d0450201c0c0d6404032107558082c0f00321117070940c00c7c60f4a1258960300b40c07a00010f4071140f207000c150070318920321440105418865150f011480d40059903607a01c003800281009041c2c5c1c4061000604188030000390002c0c849405840000e501240c00c040303210b40d0100210603407520b4005c000a0307020711180034100342c0181c00c40340d00c15030151004600c00380ca0b0b80150b0b25a20480000e16007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 467367437 1250 467366187 467366197
    0x180818030a06020c1203070e0d03091205061b030702031c0f020414040509030f0a180308121f05011e111209030610060c0f1401050a06061b24060b 64
    0x40e02c2e43c1c01041c0200e208600b44401c02111a5682c01e85066140c4601c0c028038080d5141c016078000e40d040840c6030141449120340d075020344405003040b07010441d035103003c9541e05c0003150982010500491942914048602200d0250a681d8011400c0c03180c00d00270049514000034401c0d9096903503081040380a030141c000342008040c410148408480d60a0501c81554002006104e0302c1d0020041503c90502680c103540c8503122524000c2c41e04000e4141007041c480160304080c00440340850818101005541d207d4851030841540420701100d801c12248502e07000d0107400d010904034600d0454039507441d03400340d1102c4400d180410b610242455910704213001c0f14119800c0340b000140392151403d0800c00c1c00c1d002100c05454204061070f01c10000c1061716a0007000b0146180d1154140c2488150101c07008240c40d0240200b04506100342c850000704994801c44001c40c05141c40080b600502002200405030060282c45241d40359005514400c0606000308040e0307543c51001051107525240900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 467368687 1250 467367437 467367443
    0x30f0907051507051b0a0b090409080f0c0706110a03030c031d070906051503060d05100c080114031f050601090b0f030a060f0602150a0e16060305010801180818030a 72
    0x140c0c3c407000d0f070512504028805a8400313a44040742d010840d1916841c5001c3c04840840b20320f10707240c6000e4400107019021070200503001090100b24481c5600b240401417102c0b80d25002183c80080da1a0016035030118200020b075480e401644803c804030380650003e21300c050300b918002444003e443c44014140804010f01801540030b00414030115645200380006001c04071a100015120100300f20302c14440100142d01498920318002c0810000f08131080610342c110307106001d4540c0000008002c01c030240b1485080c42c0032035225400d581000329454a0883c0900520841c1d040207402c080068000604a20f0400c2020f07a00010b642c100c0388054030409040c10b01c90b40c2c0d242030640380d400170b0f500b068010058825244008200300d680000c0c07030755034128052040b032150780e80e120040070081080c806110b409000c0d585000e0f01c0b10608000d40019a00607840800c0144d8880e0100c0e400ca030440e07000d0400e01c0300192440d13800300f5009000307000804003c0c105142c8428000010034100b00100c5030803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 467369937 1250 467368687 467368729
    0x608010c4e051008010b030c1201140103110120030702090402060f04090b040f0c021915020403032319110708031215010e010c03030f0921180b030f090705 68
    0x2002c3c10f1011002004010308240300244000a4a04002900d6400f1005c21314864010000c051090341000c0d000091100c8018000d00300a42c0e40c0c1c103010010548082c4520300183c031003201010707a45180d40380041c1d00701e900e200450034001c140d824804c1c154005441668004001e20900c0c410086900040024004905000c101340e24a0401e100688842003a10800103003008007134038540c0d900140340c500e12084000318020751a401c3c14250188154250814000303800050f0100c02d15030880060219402000e00d05a4809200c5034044001d01480503040055440709403401142c0b8030070400c882c0c2c0252002c00781d404140d074a207061031071540041e104039442100f00301000301100058160f04028082070802c00c20310100e0ba030000340001100f000040c2455030b90908a0a08030391239018840300b552007040d8070340c522562010740d00c2150400080800081c242d8080401c5036065850000c00c5403c4103a03014150b8a0b00300ca00070b40790500519101341482040c800059980c2e801d603842d4580c0340d4a80c61 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 467371187 1250 467369937 467369941
    0xf2c0a06030311030a0c1214040b070327060c020102030909180d0306060f031a1815030309090103021c0605040b1e13150f06090608010c4e05 62
    0x405850203c0c0a468052903800520024140a4008080b8603105a1182c54010f8074920002c007550a29516850308101440c04100814055804030051080b1030090f12030480511a626800360714106d000304684940080040c1002010f014031000d2002d40c0c41401901c6c1000700b4000492091441198209489284981811000e240070b11210651421f20702c1c0520800303080407801741a00701c0703002164003017556071613500791640e20010035550000801803c14a12800b100c9504000010580e40c841c0a000c45030a08041454001f046411545c070203003d0000310382c41d40e001c00440c0b20f1506e000c03e1402c0c84070b88401c400141c4030704c1841d204910403410310040b03042034602c040d4900352102c0c980c0c01150003441031250140b0340070200f0070207550015005c00c102ea80c090744040034007109040014000d0030410046034041e526041002500e050304000c00c02e1154080003221040090b29040020900d0340760003008102c404106c0800992162087c00c1000d1000c0b0741c40f4825003c41da094104242d942d2003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 467372437 1250 467371187 467371193
    0xa15060f06020f03070b0402010e09040309050405100807090f11040b1215091b1909051e13091707060e0610050612042604030c050306010f2c0a0603 65
    0x109503800350100b44010a924900180000e680740b103628030241c845008600043d0440e8070400e184c1c0d1560320040c0464009003024540540042c5c641d008203031259080c500090340068010b002c03403017128808001410038034681100b140c01051090320407180c5a444034030644481112400410040c0040301d4079075510f9980305010010200c0181010100c440c0c15081c144480d078078a00c7d01c5403c124009a010b5443d440701d1810241485030800c0c5403030b012058a01e03d803106400c04003075021034809840b0000100322040317494034600300d007440e40340c0d0086c04c0c400d1141500341c45521050344544150741d5184400003444464195400000c002c403131103901c038410f020803154240030710340d000610f80c843c903481542002c000444030b00a1180240740c80c0c00c1e4100140a022502c180d075084000e16020703a4141011070440b188050b03001c1e010079205101181d00000d1745080c0050103504a625003004010300034104140101405880340e8942c040c04022000b03460803803215000140680da6002d000140c05145203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 467373687 1250 467372437 467372459
    0x4050c0901030b160c050d180f0e160c02061207201b0f100503011a030c1b0a02032b09080c06091801030606060306140f10020a1506 58
    0xa60140c050505400100000b0315888885a044031180800c1c884100d500201210117a001c1341d03001d8054450503850303e0105070040d886030710701d94814415005560300d4903902840810359204d0880c820004400154100459072500314a02c1c1103490300703010405d2650002a800c0e04851070000c0400c0c911000e200c0c00c40d410142c1c1d1400600328074000e110070044c0340191521401500310440100411001108a56440004001a6800c018000c19203030142c1e4200401d250400d01421940d420038096a42d500744004054034480d0409080c1c2c0d80c50590f03101102c181141c2d080b07601400c10320601c0420001070b54188145407604d04081002da410310302e59000c4900e00c08941c00f44005000100c80103104461011840d5142c41400391401a5103119600104140800011900040c14101c00000c030030848183c02c50011101540c0d0300740415511000701040d00305007070640036400100c3e10704880c489c2c282101a1484000c190064840c40711440d11440e0403e0013462102d21107540e00c000a20480b0320030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 467374937 1250 467373687 467373703
    0xc0405070c0b010911092223162d091a071e050607020d0e010f021e030405060d2913050c0d0f3e03100f06080405 50
    0xa01d091101c480740d07920303008211001070249100c219140c5003440084a8030200b22400e07000f02030548000780310081032419001000307040703030542ea5080400d14400105d031890b400c00302c007901d50900c1103140c803a1412000741421545508050240c5001d420610150b030f1010781d61503042040384030250300d0325000010040c00342c9400c0003180c0c031071045c1042001d07044602600c084590000034411b640d14040b002d00302020300b5040c0140301d80305950400001660105556650300076035110103948a50240c015a542c0c1c2d0401c00b100c0060780640d0014200d1045d002c41d960384000c60409891a040e118400705000d1360281c11968205030f1a01e05819810084000299004901240d4208842e42d00c9000070050040501843c079415240e030017190406140104840300c003509104200003031284281c4070350140c0b1007031744034034400d80009078a4030031948500c00c0700d204103254420403541004d4000f2100c4550700003400700c0d00d203210803c01c08203140c8271030103500300601490b8440070310514251504614144103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 467376187 1250 467374937 467374951
    0x50603120a0c151e0e030f0c070e01180b10121814070e010b0c0604150b0402070c08010b030601050102100207030e0306010303021509030a1202090102010b090a2310030b0403120c020c0405 82
    0x940035001098880c01b20030b8070109101c81610740e036a01c1c8814000c514104442c1c0015850021000000406c0351048105103540305a0400c288039620082c000c1156503e0106281400325030b4040d04800409070301e500c0700d460b041f0441c81034a40008251100340c400001c40324591216400304006202c1001c544020500604121400c14500700070311003015203a06001c2c200505401000c100000380b204180c000e00d08000b0040e2045464034003d0400c2c8031511b0720351203124080d5182c807843c8035007410042903150603601d040e0000d0050f07001c074250035002035001107015010010000c84003402980c003800450300860007030f03008001911182e00c6203202c0c07a00140040000c3c0e4810402c20160700d82220310402c1240c001e1100580358403c050042c2d026000c041e84850703000c0690b50801c14508503a0f440740364520900c80089003000002080711040b241d06450885055640078000c00021b00c01c0c01e2516800340c840d01c0c0c0b03094119809844601a03c50a003401030141e00402e2480005003041d119183e4401c03c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 467377437 1250 467376187 467376191
    0xb09120c100f05040312030605040c0f0801050f06040f1d091603080d06080a060e0606010c020901050607140a0b1605070812101205060405010b04050603120a0c151e 72
    0x40403600160400140d440410140400320a400076201d01410a86005541000800e55040c2041c03100400410250260718404e80c601800c3c0002144180864a030700d0070035450b55141ca908050410803c44154120580e109404001c0494401d800d8456030780180910b45140e000c40ca2601d80002110b000200004020780c404518681150060800d10003201c1c0c00640341c603503404408000b50b016120b03c2c2c110491f00d1080340080f4017004029400940d58259400a0703c90700d4881700011500042c00500181d8003500b1180144081d140c403000500b4014440d0b0b02c4e04444500e0300d0200c07410b0400c8414103661000c2c18104104015051011030800542c01d45056450700d605990f868000d4003610420b080105070032000141c0030440e0403e0305002c0e04448811504041c500e01d8065620f0100b03c0302110a9402c004203141c0d1750a007800340c01d008100c014084c100500758a80b58030300c503801020540d400c011003021010045241240100005506e0200c00b003141c901c0c42038628111000b002c06006428 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 467378687 1250 467377437 467377453
    0xf030b132001030213030506040606140d0204110903071710050f0414010626010e0325050a0b040b1e06061b0705090709210c1503150b0912 61
    0x440c5045807400d5421903051180e520011480120300a00460040700d001e0104940c0c0482444000640e6600c503610501081c09481d898420030b03004c0f1700d456003855400c140100c5244005107016040f5071030039450070841900f401800c1c800039280a8266004940200813024070b4110f41c03c09019070341a80660701000d001500b4080298502c1500c001c0018096500340d44802c07046003030a41114009140c02844008a01141202a0008200710b207075600c840d860609580e008200200c2500c000d038078601a40c510800116900d07945c1e0a0020304101d4240c00b41ca9040f800040100d504540070768004d424030a07161402040641264040d0110030030081d15500400a182d03464004403010000403590139042012003039200d80c42d01c410740e04800c1d4001c0500d000c010030b495200401100321013540100d080039640005042900d02c1e501c545c09495064985018454429007108048006080740360004800807800010700d06805180c000111040c3c0000e02d0302c040d480d000c1000d4016510305c1c0e0190204e2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 467379937 1250 467378687 467378693
    0x708010902060304060e0c220f06080c01050a1101022b140103110d14010f0b09090a110a17161d220803011401090909080307030509010b06040f030b13 66
    0x80c04000c00c01417130291102c50401c2d424509010203060303090080d0141a00d400000c4d0300c060304418080d00411000c0c41c10340d0440c0038100c2801040100d480840140c2290303400380c0011102c030341c40080d247c01448201129004826003d10080c810f0b082040e940c00e1b0a141c100701c028060311203044100034200d08120035154030204040c010b03070440c1d500c000c0e414030003a00d100109200180608014140700026005540110410740002c2d8405102403c03c01c885082c420400901860640c0c0ca4491a840021a840052006152024100b0004045903441580d420500c80c030b1001c2154602115005401d010041030341a101c164080c0c00d002040014409c5504644080342c40c0c0100703140300d40c80d00404121041882140b0240003950441c007010b64035a140c4034903540c40c007480c410043c000742c00002c00242c2280c9901c01d200260341e0207001949140c0341d4620071406084003401400707055603540b4941030641e668000400082c444d0008110701c151a41c01e002a4698006110403460b1603c01203d03000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 467381187 1250 467379937 467379949
    0x902040e062202070b060a06030c0c060b04092f010503060d0206130905100609080c0603070f0905030106080d0e040c0207030f06180c03020310090314070f1707050708010902 76
    0x30065090380c2c82e240850004080b5003082010b038030340848491000071040144400310301810321500f8195055130406d070307442c0c90071021500c030b0b03407688000100c9142055000441c03540181d11008401480420b91405645511581000e045c42c0d815540200d80d5108450b0003400802c0885550700342415410341c6000d0001c24548405610000e1082800180c82c10b81103000d880f011000c5c1880d29410406850803d20b480e4a58090f4040c10b13002c610705010015648100107007140c40907802a00b1581141c03903481041d11010640e451403414405422000711300c5840911500c402020000d00901c0d5412090320050020076503141058007031820f140c4802025070f000200a01240c0d1b105c2d0100003a40c0403420310100901d128421041c680c2c1c40c1507200400d104080c4e0040d015a030003101030700d06105081c820360b8104d418956008003c19aa00d002d0746801d20500094502c060240d000200c0511099a42c402d4400340b10040e40095000440c10909200c3c040100074042c0802130004c100e61540c60b000211 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 467382437 1250 467381187 467381191
    0x70311090d05030c0a06020a11070f030204051504110406030606020f07170307120c110402120403050c030f0403050f0f03070c0e280c080a0b01120b03070e0705040e010902040e 77
    0x20044041141c580c0070003004104441d810090101500c685070307460702e03002010754030181d0180002036165500c042e80d1240820003501b140c22481c1007400c0c5510b56800e000242c500140b40c40801c0e4a80318001150fa201c502801c9100010030140d240c0e0381c0d003400d10240407580e240d0440800c5600610039540c05d001c000452500340c44810b03000e80040051603526a10314031a92200030003079100510419607141c4c0100144400d54400d20030804028400001c0c0401ca01403cbc510142d01110480031a0109000780c0c002c0c030181601c1c100381c91800d905044220800d9100c0c2c1d01c00c64941c0d1082110a0a0301070500580700001c0c280400780d484c05400381c94618100c0400d00400501d07510100211b010034100d003900320907060360704204c4440111000540341c01020805000030104901030002180d88450b42300318071881074140c4801c106510140c1d2400018043c0c00038003905031103034000c00b0460110000085201d034280340c0c1e4040e980e034200310100403070705410b92200e0386640c01131000313000e40380368040c5c09a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 467383687 1250 467382437 467382439
    0x71a0105100306051503130c031208060603160f0504171506030d08010317090a081b01020f071e0302030a05061605070c03030f27060e0f09130503070b0a090b07031109 73
    0x15840e41c494211440240310006001000d145000328000b00b04503003e086035131041c9041c1c072f0300d1109d0343e02c0000340905480b0445214408000e405400848540540f00c3d0807001c2c0050715000e8103141d141c025a4040e00038655507183c459201c4600c00d800e580111010275400384c000d034080c20700c12503520b001400414060000500c410350f990144501142007100340c50031400c00400d600d03c40390740c8140054031811310b58540d0303402d07401d070a240100550001516604144025005040719450a60056820701140211519800c281400000036940070488500000c0c01807001e00790a00b0804048070070300542c5a007020034000c2c00d01231000881c100121709001c50b41c06040ca80020040f10f101281c14080440101207002d0f28404240b4800318a000501305840064451114640c103950421007d80b1017500398580c08407600000034100008000c01c842c02d5842035045070300f4075001d5079440810f6401111a00290f941d108040c80c01c0c800d66810640d000281400d0410a100d00500e050f8030700d124a009107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 467384937 1250 467383687 467383729
    0x207030e06030c0706021b060601020a050d030c0306080a050102130f14041d1005190e0d030b0a0e070302030709090b0a050f031519060605030f011a071a010510030605 73
    0x800504483d0300302c868950317122004550f500c041030001d601040311000e91084520981c0000798055000041d0740e85440d400100410ba412000902100034004240c40d020400d07460b10b0700020016820040085a580304d0400907031039030702103040c8071084103140d03001074555450071303004200130481e0341c0303850704054005d88011414003078507050409854604161003809100d02c42402c080500190b100701e024811410b40320084404070322811080d1341c44140d051030346130084a01c060219000f0750158202c120050501c00850382d441040d030310b069904513003200109400100308490703164008120340203049401010010800d14501080010780940a002e008066010b1307001d03601e0f5400c00c1149041c03902100c04580c0340c64080c2c10101f2206400981101190902002041c0b640c080c409a070721401c10704d0018021a881c122030f00c2c1e0089140740707080742410020031107070000c100d180d51080c1c40107800d124031010384c6d403400007400700405265031a80109031070305009220582e2042c0b005600c60b5a0000ca03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 467386187 1250 467384937 467384941
    0x3040e0606032a040506071209060203120609090c100305010e0601030c020a020123180405090601150e01170c0705150c070201180b0a0206090708070f030201050325050705010f0207030e0603 83
    0x180303c151040d50043d550002d00070905d4170401684d440014448929030f620301c08460740c0d40100760f80d64000e40100c00d140c0145500010b43e42e0a02200e01ca502c142800210b5481c03c1f14640810b612460002e81440001c0c0c507400140424003101507081d8011400380780c20020001620002901ea401c4840c009040028280417002e01c8200d030b480141c880300c2d14596041c0d54414038601d0800c070000c4210f0840c02507040c180024100903001c52920304854545044d5040d44c1085682106c05901c044205418040070010008074445030b030b002c17103104036220407100d1703a81c100d13038204030745401a850000208020760340100440d908030402500d00055080c24240d83c0000f0002e28445100905e410100000070042040301a0990002e800703401900c00105a412168490b5541e03038403808240074030320110003881410401944100000c0d03510070b407480c07001c991401c80400c246102500c0e124803c0c00080c0c022503428207011007132282c480640c05000045141030800d40d00500b5015295021603c20140440 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 467387437 1250 467386187 467386261
    0x2010525080a0f1b1101050a05120708010e161409060c010203090102040314010203010305071502010b04050c041a04180e150a02070b0c16060b04090b0903040e060603 73
    0xc422524541c4512426200c500d0000d00030000855041c00f40005024014102d20702500c0d034100b812a150803103c101c203c551034400646042e4018034401d01044400c210815100440080b414000c1d82c05aa46244c694501402600540d00c041d00c12030044106101c02c400164100b98a050750320340c85500c40b510354060740c0c005030080c0100e001d24003495000004100b20f10720190700400551780300e12280c50a01040d1107070076080307001c01d0000500583c42118140b09080c058103c2c0101c0d08100d1001154109078a8045815581d0075a03503035018800200e07040c08074188812100000040c451744d8141403501e01000c1e90b8180402102007440681d49000c81040604180b020600118848000d43d03014102100280000d500901080c4d0b002d0164001003140f00103100200d80410a1400d15100d210714251605402008500d41c4941d03c40c1c1d0701c0150070006001091100d2050640b100555240c929089501030310072402410a44548420130400c4104030785010a48140b041c0b6120300c551001800c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 467388687 1250 467387437 467387497
    0x20708010504080a0201050c0c0a110402090d0c0501030b0102191e080c060702160501020309120106080d180f0303021009050705060c0f070608071418060331020105 72
    0x500012019401e000411082c00001001401c0411103a4001c005681c0c46030780c04e454074041c0400280f15a0480340340400850b1024907800810f01d0020801407402d04000c0018841c0b0b082c5400c00c641e0100360b203204020f1903070988500c07103000100380046d00c12401d19201c0c7d200315692a0400500407c00c0801c20740447d500425802d600d29803002c801f56075079000b40801e40c0e40e0380f000c840c00001486501c0a00c900b003c0c1540e04c00c81241d0f8182c00450500000c4010840c0d0500f100e80c0c0304143d903503589400594003c3c20011901110500d03152240500c40354050309440180c01d800c42001d00300a414108000303540040e56010190000000141942d40c1e031034a1810040745034442940040041003040d118070300803418003208802c0708110350100f980e03402c0940702030320222a100007103400c444a4881c0c000c48000200008154154541e92400e40e4100260b41c3d50403d0b0380308540a041e0520224510001c0c421038440c02500380440d400c8030b8019030000700b103446005228041960070607014001d0560f24 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 467389937 1250 467388687 467388689
    0x5181504020730050a0507031413030c1202060a080a140c0405180105010f0c020307092f070506040f02030c130f1401030206040b030606160b04110301050907050906010207 75
    0x34425960340010b418005900368560029054100240d03a501112082c2000d8402528110381c9800341044483c5406170f520360003071601902480080c4519131030460103c0000e00545001903191113001d130a500f08501c2c8060550450946100003048003405a0358800a840c0715038440d01c1c08a40941d90118000040c01c1c000142030308000c10318003031045210180e40034005a500c00e855050400002d00c1820782444000c0c49414040340f00140c403000c4071846424000041400941110f40303071503079031a00034101c03100303150308602240c1c51891411251113a000c501d1183d40c040b8050382d04000386a1155511000f016000810b02c4100d001980219102400350a12001004120a5803d098241e101e0f001c0c14440d41c00c24109072034240c0030001e1000348142241aa5000b90000c0d08060a06040b84500d600203041c4982c040000e01c4480d440c550340c050040d03103042c4078031120907180c00d00c0c1c0b070402124031070900c6561103030b4141303020000d00d09800100394045401c1182d01d441c8032340b19600140e00788485 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 467391187 1250 467389937 467389939
    0x1103012601050108030d0c081029040b130602060907091503050619060f0b030a020a09080a081309090b0412091e0f0605040302010203033112020c040501051815 70
    0xb0140001a4441c01102070014034100c0742c000d001c0044403040890785041e013201e04000c00c00f403101041c07161222200304850f1001c150802441102e0312030301c7d00c281c00c0e0800c2d40902940380d40010001000103e11b0112001001300e0700040c042410302640071030b1101c20b280518250a6920000103213041500b9061400554024065606a0424410000100e44480d10a001d04ca007008000188209900d20b200300b146d55242241d42151078802b01c0c07002035441403540d081002a543e002054030941800200ca06a210b0b00006950320080243c0b07040c502c00640c0700d065410710303003561100030543d980c05296000354011a04042c000380c1c00025101311450341c01c07a41c5070740c00220719038072000d000d40003100c155440700ca1040c1a895403110202da0902c6107000090043e00b003800854010b00c101c514122140341810a1451001911704007941b81001450301035611035124056040c4064040c00744880b12042a00d05004647c180400f1401c1c100c0d01401c0c10100e021118002989540807030300c0d042a101c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 467392437 1250 467391187 467391191
    0x4060c08091507030e1c03110c03120c010f0209062d0319110f071211120301140415120c090906090b070f080a0b060903010905060a0e011103012601 65
    0x805482402c250308022411004540028040f6201385082c14800b0407440309a828000000b9503a98100d64140190700b00d034200384581180c030f0001d55400d200100c402c10032403064682300c0c0c604540a80c291080001c26185052040001d40070545440c0121900000201003038107038a46e403044118840c90104100c0070003003c002c811b00890410040702c0b170111031094030041c800c41203030f1454404e2911078102a800740300c00c02c000340710008050703104040b07000b0181d003050340500f04404160307800e000018031043d103030b02800001403181c099407404145603c001038904010485c0d02c001048501c00300c80c029034400000000140081001c5010444041e140516052055070340c1c134500100500000740341260184440800940c0c154814003200d0500c1c0d42c25514000c040e00c0e80101807008098441c816504514108140e0609440901801c4881c9210310010501c40c40e1050510782211488070090155074185100000e8090413541900e05484c03180c030080c0c100c002642080264080d00041141e8194 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 467393687 1250 467392437 467392459
    0x2150906090c0f03030a0c08070b130b09010c0215150a0f0f06080708010b0304030c0203030a090e06010e240910090306050606190c110a290f04060c0809 67
    0x11a000c508240112501070860341460103280400c0368440503c01096050380c014450071009503c0340c0c0045021030f01031071075940341aa454880944c65041210224145c004a0608004115102d00400c5e8070204080007045803802d00e240094a03071040031550314803a80c0080106009a45d0a0440505020010700d4990360300e541e9500000d000203240b040044007000c0c2d01001940500030242c09118425030b0f0345400050b0300b804c00e4080d40f0307080a80282c0c1004008040b900050328104010b01d01c05a083d01d41e44805450036400c0000c001c4004c00d81030401030f562100500030745030007100304042c00c08101314402d00c5100b4039100c60725001e04014141e02c50f0559445094454001000c0070a49000f03d00601666450b003040c00020305c9800040c03001a0300b02c814030840c1503c00c8100030031041c0300f4820072103525070010020700c016100d81c004913280c050501404102c0c10424203500e10440e10f07070f400903017004c0302c00d0995404e43c0100d01c90002404032140403a0100481901125000500240024400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 467394937 1250 467393687 467393701
    0x171b03070c020f102003040605071212140901061512021803060112050f0604080a1809020c15060405040807020d0c030c031a0907050303090f0d06052e03120f0215 71
    0xd117084c030140c0d40d13644503444c4202891004c04400c65043d1030b1141c4849240408540c0d58201110401180c0010403903001d1340908441903d0250280000c604c40103040c450801c4d0340041d084402591000540e1011399a070fa04101e500012518110f01c00a0401078640d0b81001c4052001e001841c1c4166060103180004548440211100c0b4000c40c000c01c1100c03031107030550b9a4540d42d0b15007600c02801e401014060101040c0c45042c00985107040031080c100c0c0c03d40d03200c1b110416a00f04107a45090358005803400300315402c002c2c41c0c1980c040c0c0100c5007030209040c241c07143d10703041c0b24600b40030b4003410002003050184954012000c00543e401807800e001c0ba40e49050241140920484103201c0e120008082030000750002450780c15200010040d600d0714212004200c81c064251201c2074014061301e01170004140d05110b0b4602c00d5030034441c840c83c003900b500c58208925500340b07024540000e04030b40030301c0410003000d102a4000d01070308001515001075241640f030084012605509006014208864 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 467396187 1250 467394937 467394947
    0x130507090e01061704062d0e070f03110307171c020a150e010b04140702010b01140301090506010c23060105030f0c0f061306171b03070c020f10 63
    0x414542540c0e05804162500044440000c0a2203600b001580114500c04406034070003c0c207801c5071080400080c80100c00540341d034500c608211003003618075440007071261101c0c41c0c041d543c081007038900640419030402c040382055046a01002e0310312808104007a490b610208164030141114503030011016131000800f41c1c5d039010769081d01450f88a151100220207000040c3e03a41e01c0c5511100d0400c445008070f40007170003488884030891f04c6640301d44c088102902e592043c06600d55003210000f8103032800000203800d560076214000d0422400b03115403d004103402045d02c1c15220080303400f00d802d40783d150049440d409841d034060042c0b01314040740301c10041e0341809018941e0042c02900c03c540e80c3e42081580394141c0003a10b070415003291148201c540b400e4441801400f00040c003540c1000004075601c030030030340941c0007039021a91903500f4440002250042aa10044002107070901140c030912154060101803c01c0082c4001c100a1404560b113003400401c29079001740864110070a10540108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 467397437 1250 467396187 467396191
    0x10302070c0f240e011805060a03050a0e06240105070c1215020f070b060d05060115020c06070f0615030503130e060909070b0c01060905240a050a170a021305 69
    0x140b200e809401c0e00c00c0c40c2e20f009810040d1a00c6036118a5030403444180151502851002c0000003180344180100d15035a0724405401e540030b80c0e40e00041e031864843c00c004110744481040c4101944441d0401014030844107011300d054400c032103c03801086081006a600e4021184014440828400c000c10b0400044c18207121b4140518210b0001018400c148002c074811000300c050a60740030043c000200d06030000c440c1d089000580f41c00d9030400d064a400741840000c2c1c0091003620058444800c03895810000c081c0304040c11589107152008568501c00541d0f800c4400400c0152905c50318200b445c8035203440b9000399000416280d984402a01080c2d04103514026242c088011001203075640c10001541441880c502c0000c2078064280b030544031581d005a001d14101b9905c642000c2240c0f00c090054900031103a200744249118002c003046483c2c00e09900805009903a03140c020059983c40c040020708990080c40302401c01c2401034001803c000b40f04038080e4114102e54540383d0080c0050740f100b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 467398687 1250 467397437 467397449
    0x3070e1308070314040b18040902012307050d03021b0d05180d0f080a2a02151b01230411040c0c02060c0703021c0503190e030604050c040501080309031b010302070c0f 73
    0x1f002c8846424200300c201c0c5c0720703070001900082400c0d00e0a02c0300d10a00e0140e00c42003c0c401101410050329656851034000030303007040f20002c1d401162503d5030806019003c1d400d100d148014008142701540010628007c2410072040c40303521703040e91806502d070b0241c501c0c912a0003000d60324507246e403401c14140c150300040c0c0e0f000000740a08a01e518204071400700800d040f4000312090885440784d000c00c9000003030501c51a01d1030104020303007401284a034520fa42d26152480000c1102c4003510b80603140010306039980f0714001c11800c1023100152078001e621013112000c480c002005034400704d0032120706100c500c2c025000345c00090519440d1a000030310004a070300c2100e1211b1401e038503d080c000715421020004019a00170b111103e810b0300710071210304540e0004d1400c4501c001034540004d10b401d2042c0c1d01510540c1050700381e0b0500b4140b9000c0c0501503c00c68005520f018000c41c0880d0752071072442c030002c0e041c0b00f5241103141d9503032087d011220105d403c1220180784d40d888217500d003000741242c400c078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 467399937 1250 467398687 467398717
    0x41e0b010314070303090e04031413080c0d02090402011d100302090310091e0206090414040201020c060406090b0c0709060b0319091205030a1d0a0203070e1308070314040b 75
    0x1202d00340b800062403905603541aa82c03820f6291512070052148000600120b050203130000308030088440700005024410800b601045845107020f2080c2d0400b003001418074000c0c01054255400b41e03d50100d210b400660a10703045190840d40380103050f0308000200c9051b44540800804082142d03d80c025140922049040d80c004100c000d86207811a80510310081069100847d0fa1851208801960140d140043e0803e4035049202000034100e0b055203828000362180340060005550781001031801ea0b4200350b502c0c0d49064180340c000f030716495445c4150b860405000840307020060043c4400e9004103ca000240a001d49803241c03010590021a0424442c0a0030481041ba9004e1030149024442d00440c9079a005421040102d985900080c5800c0031a41c503021070464401c21030280c0c4100d941c507080030303009401c21881018200491a0b0007544000c0c03a64042c00303184200030690180180e8400900350f541d001c50702d002d40b240080310690805130500070800040c0d1070000c1c1d0060955034207000f40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 467401187 1250 467399937 467399963
    0x14010c090b03010e1f0305010c1101150f1401050d090b010329180c090c04260330040c0501090602012a0c020904080d0b01081905041e0b0103 62
    0x5a07207841c0000d1150341d007100380510204a24504c6481c03c02814854041d910740d00c1c54480d218a429904c003041c1a00001e0707880c402c0301740c11f0076084c820000c7c0c0c007103011180034803030749410200060540680256610390a01403c080e1040e80140c0446103200b04010050048078800e0500700c0355980d0910090f0380c0c0907119003100403505010f2190715000c41c0880180320007610ba1040c41003541c2644802d02905200340c2d10f02400715921301d50360501c61030360000d009035a6414403140801d10f528840c4002544254141c88450465010007600c95400000100c1d400c520b090301a41c1c03640d00043c40414191003d10000d200034008080c000714166402a00c5c1d2a440a980300000c0b401c84400721941e41a4444500c0016a07080d43e64054107150721061400590f241f4080c0c0024417007002c19101260600400982100281401d0007220380c50102401c1103003031407400c10409492042141c0603920856550030010701081203100c0190076507a1000120030100b180c0d071410425034442800252084002e03140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 467402437 1250 467401187 467401199
    0x1812080a0e0904030807081305030c0c1507020d0209040204110414010305070f1b05010f060b1c0204053a0f030207081c1404050907020a060501060c0b0402090a0914010c09 75
    0x40c038180079960580e5040c0317075941d40c00803c441742140035101c1d60300c5104d00e604100100300d04101809111244030050072528465a0800c403c10004214540b4400b03820f004060143ea17030004400d100a4050720818442c0e130701c910006000f4180080d004403101b034003281c00b0071440b58003040703615112401c0e02c04000f2920740d280c0035942e030f01c18000040006112082018100f82000080e2150707140300d503002080d61248078070321000340ca61903045000a000041409000c0611000c40290030451141c3c003103252508040200e61280483c0500840c0f8942801180f88640304030b00005011034841480e44001109506c2c20700c026100d00581900144031782500403990100200d0141d45815540c0400c0182d5000d40c03c3c00e64003505002c005c84949141400002001d4845440080c414282030740a804500b40900e0071004654060704000d00f006100540000002c6040010300e401039011101050580e1f1452401405407924860080c503544c414407250303400c070005401c0f804a8200c252101c0b084136031164 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 467403687 1250 467402437 467402449
    0xf130605031308070201030f0501060e18091c0c0503030a05010518070509102304030515070e060f09040c09230f01230304050604030305011509061812080a0e 69
    0x65902c2000415640c0c52100081400009041d030300d1040c100411000044c1d00800f003151800d0384000d020a03840c500344104d51503d048408444070340403d0b0b038403d504000301c28130303550300d02d0040050204c00f0600b00350030114024180307003211507071200403240e4130b2500c607a40201504c42031007030700d0050502c0340020009405204483d071003100705a603060f04201b12142000f0011214080341000d104142c002c120020802103400d9007a07100e100b4085a0340c0c0d1039440d0491400c0c4003c6d0380210800f031000240000161320046081001070100d45064668082040450b075901c1071110650740240f030284ca04001e907402580c00421580001c03403045074540c841d140100180c156681c050344c800180c031200c580540c00790b90740010f004049003164842e51901c03206030006070300540741036400c0d90040c1c0820007016032500819003d405041640031704503002000251070550380380994014400c82441d206444010462400002d001e01c171044001c403403440c2014031280c0d000388800300005e5180c1d4a00f0050341405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 467404937 1250 467403687 467403691
    0xb04051018020d0303020f090402070f030e0604060c1b15020109120c030c150905030313050714030c040903030b03030f04030501060504050705182d01030605030d140903120f13060503 80
    0x34101102c143c0041d5402c900030742c00700c04119809101400801660784640c03002e032040a104080310440c4940500b005021801c0000d035007446031404110500c080c9038414a045641503100054019803600e4a41b101d0b00c8004582181c4011440740a01450320740e415084005024000e400d100a09258410129060300c44904050013040307107182d0003400034003030104a6984481a08000030314442d6036682d54195072050714850108001030611b6000d010050010744002c005c250310030900c2e10414004a0f858044500d6460310481d030342e501100070301d40283c001401c1d11800400b1f4a0f40c480c202442070700c241d005404252003941c038050000c00d240c00c0911449005180c5615100c4c2132480d00e0003200000044180211b030849010407a0044007290400c0c1c116200c007880d40985412042c1d00c0004003165541d9110074840e03841134a520442e6500b1a58841c800300b107000e90150f4510040020915000e20409400c500100018003440d103c014000907015010060440241555a50f0b908503124001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 467406187 1250 467404937 467404939
    0xf09060f020705190b0c15010503010b220b281a03010302060d0213090f0f092004060510050a0f030b0f0904030c02121b1f0f0c0b0405101802 62
    0xc1d50622140c50705804c0262a001c48001c407a900c151140f00c15000f5030010f08650410340c0c8842c1051005a5080c0718403805404141d00030040200c00c080014400740102c0ca5030508403400c04120100320003940c00c141c0705c18001a00c43c82456483d10700c0440401c0405e4030081200d01e54400100e01091404012005101c0480c1140c1c2182d0a6408001c3c2c251700204040000c40c0e820003802a003010051240c07001054488400107039507000381c2c409006d03210743c1004818010320749a03440c0c00050b200c134490701801030221384084019405501040040a0541100e980018807482d000d0040e50701c079004258000301030b9181420b14a07001029419580b02031540d0703a1118068100d5111410300100d00c44c3d01c50300a20704003180da001c6030007141e0101540b00001100d50400f201200042c0d800340f0140300104010b803100740e005400c3c07000c441c4141141d11a582c00b002007080310092030320300c504106410f454000c6404119410700340b801c0745d59030b00301542402c00300341031008400b00e00c10400303011845550 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 467407437 1250 467406187 467406193
    0x702100b031b06130605040302153108060a05100501020d0e1314090c0301151410030603051203061005281830080a08061f0f09060f02 59
    0x7040b00d04101c1030200c4903444075003103e401c0c424001304074050b415460003401d103a00c0e0140d0b80c034214018084551500d20000f4440c11040003400a030781c1c0c0c13200c0b6009000440c141281240080d14900d0354000d0f840342c2c001d400c541b01c0c0320140075010102d640b00c940100c4e4648912440907603500300590321100072050150100300704071031480340c6040c0141d00320040014404009a0b03003607503181c3c641c201202510640c00303542c0a6540c00c0c0141c02c00344074201384030381d60400b845d2031580b500e070f881c2c00b1000085110501511081004820250290f000390002d19404004c0c3c40b488000056442c00382d4204840903840b444201c4a80080640039008885c4000c0206101d202c42821128864400da043c403e0300c1d000300b0100810040403808a10740c1c1d600640607003400ea0b1000394040d0807081807484060341c582513450b103504081000a400e1340c01c4079242c0c0315604042d0450760b41c0c6070005010400815050007440c14880220385116404039000d074001ea07103502c600100d1615a00101e6088200710030000140e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 467408687 1250 467407437 467407453
    0x10f18020102150c040e04081e030903090409020a0302040524150703111518010b0a0f05090703020409090b0a0c080c22090c020c010207140913060b03060f0702100b03 73
    0xca80851160340c0202d800c604130f80b41581d01c403c00340c44000111410b42e0781750001310301c01d00030280b00444040007840d1100317250b06508203944020f4891180c40359030342c410350b40c9400d10011529011845402160020002c100302e1038001c1c00002a4943c84500d9146030f00c01c01c504c00c0042c5890103000d038002070301610090a040c0103035400e687d614800c2040d8074542c440d0a00018400781c0200f0740078845d1901481c240000348640802909444822842c9846070386060710a200303000189040108550040b030f080b00075600d84402c140d001b80b1440e0840f0705024148100c0e44d00340420141704c1400307102c416008018010042c2c1d8211415107003603403410720300002001004400c00e8407800440400c0024101d0000760356445c3e4850040b40e17404070710000507030411741050059680510411000b0320981d1104c0c00c0c4002c0620000d40d0b40d03607006000160101402c1e40c21f400380451a0312200c62440c0280840c4c402e402c1040102d6110b500841d10400180716401891105554500808041c56400790003040d0755 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 467409937 1250 467408687 467408713
    0x3030103021c140c040c020f0c061e0403030233041b08030c01050f0708010b0a03180807050c04050703020c1b030127020907050304030e040b190602010f18020102 71
    0x10500e4158003030351040c8500b0011020409554140c901c2c11103450040c944010b00100340800c3c0d80e010802c103410f54008040325070811002040329820180e040b01c0342a56942000b1a00d0080c45d074803000c0501c14a0041804400c141c1c00141540d50159800c0e002124101c40302d0300301d01c00414500c2c500200c1c0c3c400c1408500050200f03071059404d440e280d070b01100c60540f00c1c0504c62840d0024201d80706645e444a0074005182c26a481c4941c0025842c5850142c41d0b0400803140c040b84240310050042659a5101c1d501d5080d40301100d07080182e00c858515960841e41c14100d40e100e1070003003094410340c5070001084035180603200310703819040648040c1036070803449034006200e00f00e21600039405540314941d103007504940c0030760340814440c005840f400c0d00c0c8003401840a0848010106424031104100b48008070360060030809607444116400304002c4000c2c4046154080405841461211b8215020034626010341000303c400056400030441124002c0303000b00103054008010b805078100368600c02134 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 467411187 1250 467409937 467409949
    0xf0d120f0516030c0306080d0804020f090408070b060a0518040501050f061e0604091113080a030e0409050a0606090f11040501090506130815012103022503060606020c01120204080303010302 83
    0x48a9505e00300001c10a503075901d0b003801d0641441c0070314001950750040208500d011030321030005a40072360312400341c0c1c40c05170344210710740c850260040c0290043e10000b8a5907542c4050f07010282001070507400d408200e80200741d8602c1026601110254244000608800040d501d081e1003004000c0c9150f204004d908001030038601e091881a0b00000104004100340810b800391414204582e1076035a074035229800403048901d6660844040e50b0403030100070f000300f9440a01e042c5200c40485000410000c00e19180703182c41c0c110711004000034240303400000c12068660026140c01c4122400380b09402c80070030416500d10943c05494041a000b80c800d010908061000e4400450203082c00342010340c440151f58900711a603900d28010a010750300500c40e4811640c10424203c000d20b0300c0e100c54920f540d0b4041d4039400c1b0449160b02d94040140044902c0302d100c42d04a00542d0010ba04209481d10790700000e44500c42c842e541c0380410005000a0b5003a042403084804a50170f500246003564250380c20008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 467412437 1250 467411187 467411201
    0x306010504020a03060b03100501091401051b0c04051009060b041a031906030c031a13120309020406081606020d02100b0a0e1620030f0c0f0d120f051603 67
    0x402c04da590300740070800c1d4101c41e000354090304148524003510791070040010854071040c0c00845071901c46c03000d00c00d8140d030802c5c252428140042d038801081514039035003e01e0705080a915a070300c5800c0c801402803040300c8100010543d50000401d2090036103500030030040344200c0c41142059800c503100303042100d580c14086c54201030381c80d142c45101c0305034421041c01d41d00e041d04140c81d4211590010020403800d940d128080d00d9441000780410314018560700080b40d402c0c000541702041ca0749520245503c240d100c00b40040d4010402c1019645036088581d07110242d0043c10340b010290304000c44d10500005030401050742641c001c1c071041001b14103031005801a8402d50f5004200b605d0041a900c48425016214030805030482c0300300c0c000340b00024a00c3c0c1d1070251880c0700ba000c801c0410300c1448080200c4e1280311644090503038541c80701ca0300358504141a50b000d00301e809022000705c0000d90100c0c4990b02c003d410102803003d00c80400dc540e00b00c070300503a2254145c2564078541c1d9800b034002e0300030403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 467413687 1250 467412437 467412457
    0xf05070e040b0702010c09030f2411031602010b06031f090906021306032f0c010c020f06060f0d02010e130c110f01051012050f030d05070e0f030601050402 68
    0x1980480e6035500d41141500151070440380014a04100a686607092059800c0f0100070314002d1101861758403500003102c42c0030005080800500001e0a500d40e424654030041c208122042000c00b40440c003a1a003a0001d0342c50146402c032141c850040309205000b0050340c10402420030785161510303080d92401d0260300040c00140b292211b00003901010a20500d95a54010800980e48252000b4070f0484111117400010a040c0b0341020501a540c01d40c0715013036880c4400980c1030000b807045903240d040303004032800f0740700e80d60900c0900c240d100d40c040350300480602c1240448480307444800801003840313031208085800003022186540590305c502c80501c1c000c80302a200140f098500541e05023a1000c13590f9603c00305102d03030341d08403071000208032020000c07035441c000700f0441c1403405050629003040d00c01c00650030031f900c411034240041481003c43d03222018003100d0f85d4060400384132020345012108900820b0360700d041c03071080c0c2c03c0049060510034001400791900745c0c24281004000e42101c1026 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 467414937 1250 467413687 467413693
    0x200703030e0613050609160603020c07242003120a020d050a0b01121a010309080c0706020c090903090a03080c0a02120304030506011e090c030902030a0303050f09030a0c0f05 76
    0x1c0329120103002840c00384801c0c2041ca41c0c041c07070904044e442c11801601a02d2035a205d200e072200d4000c12042490140c4a1074907015075215441400c0074a041d100c0d03002a440c030311500428145400c00d4108406602c10280c8a9001d44080701e01c080204107101c84410140307406c02c22803003120001041c3c140b83d0006c1c21060050030a400c0807101d104882007100c0604071a0380c1c4409260305903801080042ca40700c0d0443d0140a5001c42011500120319540a80b50606484110100400c004403064860b030301c0b100000c07195910360318070009503100794101e034040c020781c22500400c0900c0c1c008011214204070142c00c2d1400c080c51031342c40e081aa4031100f188584ca0040010710380040c1e03034403c100d03c003aa400c0c00003191510b0071400c1003800d010040c0d1042c0741192600840502d0584542d100c10111141d00c84000340d28042d000382500a0207903104002d515000d80c14201d0201501640018050050302d03094240355581c0c014290382c2c0340b18541000e80403600001110000038011a104c0b101c0c64400c8044d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 467416187 1250 467414937 467414951
    0x702151005011206180c080a0908070b061c121d030c090411030102040b030a0506090106020a0803062b0309050a260a06020a051c0b012705120102070203010f20070303 73
    0x201d145c600c211000c81d00c036907502c5264401186502854150308140c0040080101c2601e0f56941800762113262002021001b0b0040080e01e01d80d520a003580016139480102c0e6002c121b80e1a107181e181d0392115150000c1031034900c00810b49000d268212074101009030091880f48000030801c031403030b40c00070412941c4801040c0060aa62020f002900007419030020881c0c690070200c0c0e1240c281c480c0248283c1c000c03400140104581680044d0003c1c002c1d401a034031a03900c0d215507000c0f5054003072740820400c840c41901c0c034080c9000105848401041d001c8e5549000c142e8440e01048040145d61251030700041440e003541109490544010821018010840c1d90911040d611141a80c0107266201c000c624042060381d04000e11803050600008184000c010b08010b0f040042d100112102c0540f0440c40e00c46105081440c0f4101520084c2000a0900c000c0c44141c1800380e0107035100b203200301c1c0030b0b508045004200311420301459594000291000c0000c600ca1000007142c0d401c04c10041c1e08240d12648 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 467417437 1250 467416187 467416199
    0x90b0d0206040b0c060f090c151201030b04030206060405090d1202160309030c0909050304150c0501060e06010f0305130204020a0903060906050a1a13021803150702151005011206 78
    0x28002826100e50981d1901c0842c0049401c014008000d81c0d00c008001c070401260740c7c0c020405100401d41102e2500b0051407502040c45180140c00001d404018041d0000c0300348501110038920441c401c1c1c2c220740c00d07070b0355410901056883c1603820032100d1384440c4800384014001c6c480d000031a1a010801824084005400540084100c4040c0c01044502ca41401448071300301d201006026280d4080c02a06000e9541966a2050703200702c01520400d2110307200114402c10003036010507040402803100701d44405495441002c207940ca9408240c41110040c1124000c1c040c0600c60584a001e4028049841d001c0c403019500c018040030801115180c0840003c0d0b0a00c40c1424a034090040080e89180c00c0c1100001c84121016031408600282c901d400980e4503548035174400007414001684a42c03406403240340c04802032030915894000c1c074020302c0255422401e40b82c0709070140d034200c404100c1a080c1007a02a00240d402450440000c1c4040c0203550050400014015013102d000905542d588 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 467418687 1250 467417437 467417449
    0x90c05090606120c0901030c1701050d0c1502010b090709050120030f0a0201090309090203150d05010b03030f0903010f11040611030d02030408092d0904060219050705070e01030c090b0d02 82
    0x1e81303800c04440045852462541d061260782040503450401280c1d65140400304004100c0500c02d01d480382013590500c1d010408a82e01c2c510040401ca1128085103140d0f01000c1c0c042d00d40d0401c0180507003050800a0f449900c12201441150010303101d4101c1c102180c0f0010252440d007032030600042c401040402e4a4001c4c410040c00c5a0745241d00001d40b400043c6801002202940d00200c403190060041c080d1130048a086441c04a01c110f0306450440218988580075110154030940d243c007022801d240b040304c2e080c00030440c089040f00204144049680450111050106d0b80845caa8081c40240b06260050081c4c5482036100f40459040181e40c0e44400c099034812a01251180004903101c805800c10300c81c1c602d9032800d400c0040400b41c000302c001c03100b21400031040303a11540c50240401c042c00120350480740700c9c017503070074854602590401d07020309554003c0d8401c40f080d05c1100000034940681c1d10181d810313240e118154560a41c50204c00b800a4000041c46691006205100c41c0050f40c1380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 467419937 1250 467418687 467418691
    0x10908070c060215010b030f04020a0f140108090114010b030406020706060303050403060e0105010602060a020f07170c12070803040f0302011d060a200904020a120f0204090e01090c0509060612 84
    0x504007249030316051580090a007140081038028460210f401030010100705070030b036a8810323541d511404107a0f0381c03400014001c010315803005402d00c1c9090404500350030911448403440c2020380303c07900c00380c441121250032661072481500f1a465400700501c01c8600c0e030340c01181c0282c000d845c0541885c02c0c6071104401c40e001a40101c0c040f803400103041041149902502d05240b0440c0b00801156140000107900c4500080c03516181d40d038005090f0081610307a070b082d290400d4001e40010140e0a24403040c1580742c0c0104080c01c42841410b80c80300820050400300d50140d680000700b030381035890300c3e61248449440100200c003595240c104d00748141d5101c0c0c40070842c4100c100c00528807420602000750072680c484002400c02d2040d66801410840c00b1400c40e82c103c0b100f43d500580d80c0107004421510600303504034404140b4182500e80345018403940292007610304040040105074200b0b501d5600321482e101c0014442500041c2c00c100c18a418005c0592101000c0c02480c90324400030301e0038900b1801 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 467421187 1250 467419937 467419943
    0x1e080c1c0902010311070b0403080604091718030708030a080c041203020c0f030708060c071a0702010903030b061204060b01111006081524030705040e100b0415031401090807 76
    0x744406800c25076906001740410308001c40091031030039190340c4503502c48480c0240b01800344800e86003c02d200751a99800540059041041310180c001003418458242e030010400d90300560022180080074034001c0ba00c002140e150400640c40c00291405c1035640f9000200400c03031003c0240400176030300460704a060012441781d400f401201c0300074802c004183d0030030040d8500a503c448024412034000041080e00854030355066510b90a840c03914291a46543d20401440c080d298103000079960150040c4504c1d9101c0e44051281c80d1400e8180405401100e4080d00d03100b4407070020a000c68083c0d8001407807400d06141c1040040a181806440d2039880c0e0600b00d060b07555503100300103106040c80f43c0c40f000200003070890002d0420180c03080d0359103a9020504441008455241050350302005550000c10340603105015865070b01c48000d454103d00e0a80c5072526007032110030742c0c0d60b1809100d01000c40c0440030a07802910b003161201034820211a2908015658640004012480440c05081d16501c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 467422437 1250 467421187 467421191
    0x10618090e01020d06091b1107120804080d0e0904061a060310090e0303070f12380d0503040b070305120a06080714060d1e0509011b1e080c1c 62
    0xe44c820505086908941c020b00300d02e45010b404458000f00700405c40024821850805110702c1c0d411002402e0081c030390b10103440c0265803004001085103080150044070a03d43c1540c000382244881901d800440c0d04500340d01480707110010b400644a540181e0000915001d0101e02d00c091002142c1958410345040c820043c000780c08210100c29801840507203606030f0007650850030702e2100601030040d14010481031199803c04007524a400d40d200010001d60311240070f51640c1811211030000e001e0f50600c103c103951031a03100700c082c00d1562001d8100356100b0000c1d45440e1a200c28160141c200c12022001c004041040071744010030302c0c070224000c0486010010303080c1d00e09204a0b203002000c1d07004000203804003028440d265695015200381065a4501040d0311100919441085c4807400070741d0b159524010074403000710815805801c0c01c00605607030002c94488900150780701d210f06c2040101800c0140c015090142c8244806074000d00c0a01c08241010207550590000301041a8820300042e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 467423687 1250 467422437 467422447
    0x1203070c0b0409060504020903070e0415050103081b01180b18010e0d08090a031b0804090207060c110307020a210804081f09080a0c14150f0a02040e010618090e0102 72
    0x3c5a684503040003130208480841c9408064004241c48900030300c00c01110000302000902440740c40620b00c03c83c82c03080d0340101700c15a120700c0c114405411500001203128400004120400070500ca5485402003140608108010a5035000106000140721814916000400301051102406441011314090020f0f140380010103400078940d40006142242c50782c0300390780c1000483d81103002081c8000e4802010342c013180d0707503090562003031040d5800300e50711a20029500c01482182e42c0070f100307000c1151b55041c40340300100688940d00d0240d000c020f0f5101540c0300040111b0f424640000303030302030400310401400c42403944510003550455440300301c154100c9000d82c0ba0754185210320f4070065201c01ca00f00111040e0b51207514490140d0941002441078201c40103003840942c550111440f0b03102000c440c2c000340b0919071000f04110580382c0080301d03901030003c910000802c1c02030320103441c0c100c0d4141096170f1074104212624907141500040c2da10854901143e440041c4c00383e54401ea9443c00090b95036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 467424937 1250 467423687 467423699
    0x5120a05072f0a0b0912090d29040f05100605011b1b0b040603060b0a0504030b040f020a150e090c2d0f09100c0209150a090203010f05011e0903021203070c0b04 70
    0x81b60701c03107580114501040002445d9035580f4001c2c41105904007617000340c81100b00e10b2440300308605281d05143c5101ea00304120801c07488002c0364085038455810b44450b481d00009a5064840381c0c011540400d20f0241d0581082c58188030f200602c1e400741d5098818070703c1803401d4500803000c6821400c0c80650003e01400344540501071003005001d8150824505019201c1c010000c0c01140402000e2555140110b000d02c142c100201000da5001400040400d03038440d80c44507000321a401c0f44000c20110a0081100d16005000c0c6109007405003c0e42c0c81c0844680e081100c0343c203641c1d01701c040780b440c552500303044035031a40181920104001d001e5a40ea15202c1c1003001d901c03050f08941c0c0c2000a8080103c0040e00c0b040384694110f9104d0005105892140d0006082c0a40c19040302480b02d1000c40005010901120f85c002101d49c01e0303e841640c103401d10031a02d40000c0c20b56211010800703c00b800c000604000c6411402c04040f2426242050140e548003075502180e580302c2c4d446804041424001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 467426187 1250 467424937 467424943
    0xc0e0f0403080708100504020c150901020a0311070206040509070c080708030708010b090d120201061809020103050f0c0a0e1f08060f041a0d030203040e0705120a05072f0a0b09 77
    0x20f4a94140284c0c00d15051030030f016801c01c18041d050040b03802041070203400720204880344160280800061091602100150003900201a00f800107400c01807209090341d05034003166122a009000c5600c3c0c03a052a00b804400c0c0030180c16802000f550800541c08542c4103030251a8092054042d1641e0307003001840208a59410f81060702c810508202520300382d60f600f1030030310000da44038002e00704406001e5002c1c1d00500c2c0b03550003000c0c18003030010442e03550303030159001d001c00900c00d80b030030441030321008902003041d5821107501d0b685035420411448401c0c010b00e404059882c0c000c0c00480070319070b035011502e042100c04900e50b0100e210b032824400185003620105000180541d81000781c40300c1080d0003c001e148000c607050241c0e80713425849003494420b004440251507043c4c600380c02d50800c00d1000340381e87c1c011043e9a0700c06d103100f40419403191036801928094207059440850b054812403050baa1410b2401d0343d000c1041300d8923085205c0d4801031101105050041254007000d06d030200060341 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 467427437 1250 467426187 467426191
    0x60309020a151d22091a010b0a180506040b090109090c0512100b1b07080703020603040b060a0504050a0b03010e07030b010608090f190201120c0e0d0c0e0f040308 71
    0x4402034411010400664001e500702d01038550088403c142c1544070707000c5001401040c022084240160042101001c082d41124085503c100031480500080708204050300383c0a0040e5107414070304000d01200a445080007000e811004400d0304806a0b40383e00055965100d82e1004d00440707c041403503901582c01805400080c51520000d000c1c0100101d0001d0070703846000100c2c000d2000c0a004039110b23a200610050180a103410181d81d554044821680b1005c5000c040c2d0106120748600400c00013404154801101d501030400c90444e20740307a68200300f03100300410700350308103135420300000d91039071903004480c010b138110f620005640d601c450030f1500b51400c40a01d1844d80c3d02012041001034501c2c0c002c281100c00c145040300c4551100c1940c00d040c403e840700032291610510340e40003404403d2180a01d11240300f6203c50f0f010035080ba10704816500034040240215041200021403401c0038001c90030300340e104a0700320000c581c032140d803000a02c2d030a450340740c3cad032032003420801c000c25801403242030b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 467428687 1250 467427437 467427449
    0x2031b09010e04080a0f2f0d0906120e0705191509050d030e0103200306270a09150e01141e0604050c0409060308070b0615040504090c2309010f050a1a13060309020a 72
    0x1452711400d104000d410b5111280301144030554621941d8075000080c480200500750040140003042004201c03401e41580500031030303448807100d8104400b918003441d0f038001103070f01c0a80901c044024075102652412400705207641419100c800240941900c506100416460451904e86078205101401980e9034401d01284010f04c954040940400c0740346c0c0c07155441082c0f0000850252030502c0c140c42d0f25840c0c050300a112600b0040641212a81900042c0303d01e41e040c105a1090b60322680404a001c4c42084031110003016000414254109a0000f0b40d001012041e410300d45030380d039400c540403500c0a03881902c0401001c05d0103010011020b060541100b000c0345d81d50f1030680c04210001d894450b42c41024411556512044d04001b0b20320340000003080a407102603840d04001303101c21007102142c1ca4091041040b1300002c02e082c105034540b0070554a018040c2d228203420010b15041c40800c01c003004108080500003041d45041c03000c1c08a000c0c0c80f03152f90105144e40240b060000d03400c4950018 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 467429937 1250 467428687 467428697
    0x906020d0e030a0b0c090a0b0405090a0b090423070801151707060e150c06161b0f020607172d160f02031b09010e04080a0f2f0d 56
    0x4100715550004201c0d544070380010380c96480b602d4184d1500d020f48210f41c5915000140034000090b0785d030a42e0040c6c411201c003960b0b00760040c1d0720148180206c3e441c01000e20791141800d00402c000c54100c00640d440001c0003a40b000c2a5120b20280a01d04060380d400444117a449071030304040401c0c0300603804002c0503400100109400d0300c0401d0340e00e4038070078010201040150f900d104190354500840741e551a09100210b6030740c6036000171490301c0e0013080b10540744e211390810150f06090710900b1074041039007410810380c101958a544441601030815400d076404001441031901141080f1240e41c0541d070304841c055910300e114402208160310982405000d0710f107013100c02d60030000c03402c126050400c8000c1204c800321014a007540b042140c2c0080a5090720854040b08505000880e20b4486003000302d03002d50041e0707602c201c10f201902081b14014130304941484030295944c000c040d01050b40f45a81400c08a285001408040c030f85041d010781c3d00142d01e00a50302c0d20f4540240030450920030740d8504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 467431187 1250 467429937 467429957
    0x1110909010b0c03040b0711090f2203030b3a03080106200f010203010918051b0d1703040201260105190b0301030b0103051207031202071a070906020d 66
    0x540d518014410303045044000152040c00e0070083c0110b8003d481e65406440e01c451680c1800100686858040340c0035400c050003055845540c12071040c403403c1c80b01d01580e406c5051300010003031301c10f17086012014151660500d910603035990701d060103812202c28107607010020721407010b0500d606124860a1510032540c2201c0400d074044401e42c191034013820000d030f0860148824521118240e0302105032401a6080401e0461064009604880d800309043c001007440d0a0f036040c0380403109000a0a42c0e0003080c4540325040100ba082001120017400305c10b01c4600e41d101d1000e00481c4080c00a0900ea00104000c11580c006002c0507405507103a1040c1400e80d05070440f080ca030b4074107000c0c0c0c40c464001d40841145220801e4502c802401c0400620b58481d6944e00e0300180340320082c007040f145c5000384280700c2c0100e58020251207106416070358450510010143c218000d45c00300009688091b10b00044413001001c4e40c3d00c040c0200456502c0d11240c5107400c40090a01c10806240c0d0100041185 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 467432437 1250 467431187 467431189
    0xe0a0605130f0e0915090d0c08040b2d09130f061205010e0d0503090d0e240d06052205060f1f02010e06070e011409030a1505060117010b1e0c0f011109 66
    0x440001840d01230070550020700d20790404002174000d40e40f021128100008002d0f0b07510840001d1b050345201d1200d02548469005450320406018480c0b205400421628021624408175000b0ba40c0c611900d81d400540c0540b51407055540c120081e1045d14030307a4441c4480d01001008208002041041340b80803800c0d410302c4002540c403202c0e8000008100407002e4244152a950100b9203080041c0450390440318040004c0106510340100d4401080b00d880c103c00051541040f200804c0c1e40070150342c188040c811b4a204003801040c0152030550010103d4490015030b41f980041ca00c035038481d00e0840b010307981e0b8070304000b1b0a481c5140702d00c4040d0303042041440304080c1c2182c15001d4000c400d0a210f035002a102e03000d40c81c0c034003c00990383d81c9446004120018800500300c90044100d0400c424400303036440744010340c0c1c04041c4220321580c260400340100300903d00c1c040903180c030b03050480081c02c0301050b0405660a64000c101c43e515250080262600030750341c00d104001443c0c0110201c40d0030241c00c20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 467433687 1250 467432437 467432443
    0xa12080c0a030e010e06090a0317090303180705030105010e220305090d03050d110705060a14010312030207050d050301050f0111030910091809120e0a0605130f0e091509 74
    0xa4001c20074141c5451032000302960a40000801107242c0088502074506040d0040e500c40c0544825004560f000c0c409040d214801c03090180b09000a100944c55922000b00000c542400b0380800034250092316000f04242e80d0a0007140d008050ba00100891400d2030303107441c0418103940307038404840954040040c0020780c001d801d1b1117000d04101e40300c0b030400c2c01da410251a61711502c1c05052003527242401100140302c000c40502030380ea0060044600320768170b044000007141c040a003081480510400100000b41e020700d070144444140d490054100107030760f50b400f480e12908110748400700d41c0100040c4154148080c1d1044411001d1174022056001d03084015103d100d01ea008502a01100a44030040d40c095113560323005002d082045a0a40d40000440006000c080d0084900300d6040c40852503551280110807813161000f8561102641741480945160b40140391411171941c0c03814000034082454040f4200a000582119015143c49501241040e0441c0400c0c525403904806003c00c0641c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 467434937 1250 467433687 467433697
    0x120604050d260c13030206040806071803050703080a11030315010f02150f060d0f080d1401052d0307060302041e03081215040504061406010912110409020301020406020a12080c 77
    0x100c003410340c4e204109010800051480d80001c0d40206c0b0010300058250300028109100b580340b5565004010300088e140d1058100f284030150180d80810000d10109006a0050407903403214148000701d80000260301c2e09503007040790418060b42c5503840218039075800c042059070249562001d083c100f8510b02600e54a5580030f45559005482040051419194103000807102e07a00800b80390341c0c1010341c1c6000f10899002c0030000c0300103800d20860035002c241d1140301c541a58002015041040740c405400c00e00c5140d8500108a24000940450401d40b418450b12010301515580903075640c3c240200c01c519121260541c1c50341080540c0c0400101740501d0541e601034440c040750480c603071200343c0d580740c201000100d255427051404042c07100f0003400d48c2c044440460b20942c80e1125a80380700055554030340c00d00c9401c240d4441c4000500c0015910004009a400b000300b000980b10129004203089800a8100c1005a4040c0c000182488400d003004030f08040e06280081040c07920341108900d90041c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 467436187 1250 467434937 467434951
    0x309051e03041404091a0103030e0603040b01050603040203011b0e0405010b090102301315020601030b0c0c1606030608060a0203062d13050a11070c0311120604050d26 73
    0x51640811a901c6400c200c05903170300004d160f6009400c01b04041c0888070280700890202ea21b141d601419824841c0503a4072a54000644110b2a03180c44284090740d40008e0040762301d5540c0700100c1c0c840f19100901c0340e0007a421b41d80c40054001ca07581c00d010841e801a040002c111030140030300b800a0382e0001e500d201c80394036024000701a50034108280d049000d03003c803844188201040c150030004440500c20101e4048489410300c2406041c0240d0300c0c2c40b0f080c080940129074180028103400d0030347c40103112200203181261400c0044030b0345094848001c2c2c01110019031039010030008048100515604414422011840e504000c0000fa0701c200d06c243c1c0301c0109022140307644a880c80e0310340d048089607102400c01800c9243c412040c0008040440d001e02d0741c2460400c0081c106860b840c1a40c480300e9008060748203082c00c5446078071807107016000c2554081131008908002c184188016800f80f8401d000400e20740720920009070115151403c4080b03505804031550115041444406da08216 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 467437437 1250 467436187 467436209
    0x180a03050d11031510051902010209010e01030515011b061a040b090106022a0402180a061409040f09150606030b010c03020a11030c030a080c010506010503091b030a02100309051e0304 80
    0x105d0006640a0080514081e4105408983c1080c903603010b40060614a074261b8504a24002810040d0100d543c1950102a032140700684040d0360b50160301c124913034140c804203220107000d483d41d400c0c0c25030b4540d40b007810a5005110016550741841e0141440403d8100c400803007035070409000035617900e0310030700d880000742d0801e00d01112180514602ca40d0385202500a40d0744401d40c1028107090300040e69881e0241010500014034944140e21406401400070360507440d00400300104009800350003141100c10f981e4240490020301070324590407100c2e08180010541070b19169019007100c10314a041c90600207103502d442d0000303a0100e4002c4185074800030303000c142c0365480c022034905005151060f405200b40300441d8140503504004c0c3c400100002c0084c051980c946004503098001039a00030302c240c0c4800b10040514040051005991001a003210107181850b00020341e41d00c1c0510000010903501c65104050240c1880002d0210814180211009010340c506969a11603403203101110302c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 467438687 1250 467437437 467437459
    0x706150f081515180601020d050a051c02040518040b131a0702070f08070f050a06020a0b0406020d02040b070b0a09080a0f0509040606020705010807020c18180a03050d110315 76
    0x2518404114809074002d04113052080b200030401d1000c181c20f8a03914054400c950920040f40d03c40c0c8211201c003180c0317035281810300264a101c0c03924004426210044541c00340300210b03c0e03031561400d02c0c186c006207080711480c2e42050300f05501c1102001d00200030030103a2888810116468540d030210000b0380c400c03424030554590404a007084080d030402511184c24101c0002c42e010002044020344144000c143c500c555280d0400090344020722072030b409a04040c043d1800b041802d42500e5200b402a4405481c10f182800c6010807644990005205032001080100070300c140100ea8952081070300008110740507068031410043d020b0030b04442c1c02c110710007160200c024411010340d14030410240c4240003258480d5400394540140340107150000b2800320005500f41c2c1f0000d64403011000c05055280c5d00b2000302890007460700c00802e10017509440a00181204104204100001e40295142038442010001007011b0300c13910401204002018001d0021240c0034800520b41050129528903080d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 467439937 1250 467438687 467438701
    0xa15120503031305011407050901110106120f3e0d030c06020a050d090606090c0f0c06020315100f0927090314121b070b0a05040201140706150f0815 65
    0x500f08075294900900c80c51b2003448081904a405003a4544090300c0c1c0c032454502500700182210780622403d18401e80d2400c1c00008142e6801258028902502408240d0712030740014035030900c80000340d003031104040f0764a151001c02e00c10710001d07440b5085030000086138154400414205444c403028121950004d1000d0f00342d402102100d080c08071016040c800100b03541084002860144a0458410f00345041400308520a03540c0d0000c2030500e4039900e0981d05943c42d440029000101484007160840d4003003440c594492360032013060301d0a90f42e20301c01c00d0003401380205802c0c050f5002c03c1c12000c80e50384003101c1c0340a4001c20b68039940010400074420200c0d003012100c1035081e02c5810070030040007a112012403881e125240c403514100c403161040002c0d114002e00300340700303d040140c6400e04200201d1200190f03a080260414014075110220390441c007981c1d9625070044504691041c2c1da28001000e0384007860440300204031107001c4401c202d1500c0701c0c5035110f020080701996880701c2000002d0341 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 467441187 1250 467439937 467439941
    0x20d0f02011b1806030504030519090b12091011040501051c02070b0411030a0f060506120709150b0906031603090606170c0f010e130f050a1512050303130501 69
    0x6156000c002c00380060003146400340550301d61408000401408000c0490010300a000301405641e05568552601d83d003014904111104071f10380c50100061103c0003d501c480c248050102001c0303000724041c050401d41c0c06a850321000020b00c01815040031455007801c076080c3d0980f012104c0c20b091444e92008002d100c2c04040c03011541145503e07102042640c1841080002c1602c16441102401107184c01c0004156482e25071441c01802200ca04601c5800601c15030481030708488007500303001505441640c0a03042c0211600550480b6a44d501102411440d1491403402003c0c0185100d1401903a000480c04500c070052002071a2196008044c4c1c0340c1c2d100f644600b13401508004100b207001d8441e8865030115003207406642c4940300d00003100000b89032030711642d80140c0050f103641c03400000e22410f001070700745009400071006070340c2c06500910458a0083c1442514480800244241401802040d00380b06401c05060f50400c190100c0010300000b044a8010300009110003009032289000c41c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 467442437 1250 467441187 467441201
    0x60d05010b0409050a03020706170a0903120c020303270a0303020c07030602040b09010801090e060103020111100f1b0804030905040f0b1e0f0f0d0f0201020a02190801150501020d0f0201 81
    0x5040b0349407105090a10001082202c819807291742603031030050703540100b16440e482048400c40c0003203822000c10307059649035210806451090802c414090700c2c40c5c18003011541480341c204090b810010801c0b082e10040030b20303020f6a0703441d412a202d46c903982c002c0b01c0741d84a4581d03030001c0605900180d200f84940003000344500841d80401c00750340e20350701c0303181582060300030f40901c601103000100049074a54260080444110342c4500400d446e03131031900119485c150002d80c00400d40100c401d44040e8280d64051199980e4100b5004580c8400840381481d403130810400c0c600c1045084418003001983c45414281114030413500410700d2545e003031a00700101252601c50307603c880c56000310310340750b070301c03400100e08044040720b8010244007800c0520400c0300101c0c80707240d400241c003000711000440741361100b50350f180180b048417401e40701039004c10080342d034200c100c02c0100c0091804000540c42400703107440c002d000104415001d844c040020390385114012142081c01001e030654007005100350b000395 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 467443687 1250 467442437 467442439
    0x912120a090f14180c040b0f0913020a020303011505040e09010509010f0b010903030c17030705030103140d090e1f06030b1504080618010209090406020307030b0f09060d05010b 77
    0xea69411001028104038202d200364960441d40705400251a00b410403144401a0f000d8000464882d0280e4410307001d100007000001000000e1002065006210002c1c000d40019108003680d80c1583c0410070101c2e408001800c803040d401008951025030740030042d60304444000b16210b4040040207400e461900403030300403210100032501001405032054120354000d80306040204102410080c1c04000d49070b10f031007120b000c1941c4000030800281b083d41e1030320240c4e000b076180114540c0310340102401a44240c07040f6001650100041c0b09120308100e15500c095641d00c000c24415100f808081c0c965902441a00c050300c8804001400045848642c04401201d402400c08203a890b001c014000384001101c05c0c1c000c10b5503000c6400e1524a00048030241c6090350300501c055a1601590310000700d2220103400a55024000e02c0380075142e000700f05018500c00c903005030312880c0420006040b40d0500c00c0c4c580c8600d112060042c020b4131a22265a0401010360308094088403a00b0500d01400f0010002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 467444937 1250 467443687 467443723
    0x203040303061e0f140102010b03100b01180e040b0a0209040504050609070506030903041205070b0403051e010203060d14070819290c090a0b12040b090d02030912 71
    0x806a055100d1010f03074101c0c481c20600c15842c0740010350300b0852401190424051010140440c03d64028055030807401440080380c0d080412021034107185500c82045071964445840200c19a0842c1c04202440c0e242c5040b00f894070300d042c0550741046406080501280540b00210b1200709032501203070b4402074090001d00c454103040c80c1241d51082d08403500c607018062214041968545074040700d0046503402d00840c02c260804480700c41a040144085490307201d80741c00011581500e8014200070350045018002c14039401c103410052a1242e25540b071107901c10000c20002c0c1e0b5407900084020303031300204013449001660300c03110305d40301d000d070043c03007551040300d040d4021301c241d80010280b900d2040f85460528092001000201c1d00d000c5000031752100f421000072500b4904401a2400d07a2005280c04200e603952080c07035619130700a480c0896042003100c10441441000c000054001100d00300801411026081c0203440b0702a503142580305071040c06c030004412404102181c0041000441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 467446043 1106 467444937 467444941
    0x8131a010e220b0c09100f030b0109030312050c1303060b0f04060e011e1706060307080318060d14010b0703020c03011b0804030225080105010510090510030f0203 71
    0x184140650a1105c0c036415990f100200003a507201c2c0d112a95003c12144000742903c030380510f4541805610281040040c3d440213582c0d8800301182400111030f142c050703003d101445801c03480c103a100e004110110074801554021070050b03004444954140d405002070100b0703a0581d101c3e0824441600b401000081070500003c07040b541c03504800382d103594641c0c0f0300e640000307000342041d02d041e4031240810109003002c002880140040300d0046080110444503031807145441d451083c000c00d4041810440b4a14640255440d0310106030110398039a1202c40c45803960708450405d60043c401c1c01000c1085d403c06203d24400072000741e6a200e100e031130001003503c0140000e801103045200d203109880c82c4001e500c1c24403408641800b250007405180a0186081d1001030304000e110f14044681c40880c9600924203400b00d450644120700c04844491054008045d00d4801e20081400041 = true := by decide +kernel

theorem cover : BRFrame.Cov 467266187 467446043 := by
  have h0 := BRFrame.cov_init 467266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 467266187 ≤ n) (h2 : n < 467446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
