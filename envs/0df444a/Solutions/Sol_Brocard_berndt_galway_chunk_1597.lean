-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1597
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:46:33.506194+00:00
-- url     : https://prove2.me/submissions/3f3a3255-8dab-4e36-80d0-a1baaac24a47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 287050359 ≤ n < 287230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 287051609 1250 287050359 287050363
    0x1206040b1801050a0b090c040807090221090c010311041220180105010207090507020c011d060a0c060c0c120815060403050f071707050409060b0409050604060b090f18 73
    0x442110441e643c80e200c00c0000d101400d90103200076800c01c40c0c640420b91a035690081d0785000d035004602c20f82d002142e04004500d8290300501e040c203010402882c1d50002e5034400c8101a03011502000250446228401d2541e494803800907060320714010706007003509102520050402c0b0450040580e600182260300e0a80707807051617072510380020705c40100001c811602441400003842014054890044003085004d0300340038135403241100c1c2c0d0080c0402001100110740b05a0a1061013901d0703141c40f101d080d080d48801d8010541d104c815101c6841c181d500345800012503a0001d104010808200125000100b42e40b403071004030115407522800c02c1e03d4061088080b42c68001035560300100010b0300100b008004540408081000411f880030507a5403101c41103c1a004016000704d6000181c00b03114038a080e0f07004203002c0d400340c0400902000b044010800300d9661b81025a2158003070001c0200b00f0105008510400005607060009802c007000b00305c88460020f0700a122a11490403882c030fa02c402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 287052859 1250 287051609 287051641
    0x30c011b052a011e11040303170417031f0806010e010b07060212130203010b010806010206061009210507150c060e0307050105100f050904050303041101210501090b1206040b 76
    0x4102c008009109040c0d503204111440c0d00350703420b44141402003100180340d40c0c006540450780c064590100e80c0182000712400035074010f00c101d03a5805103221176022417000001440c8502d8403c9031208642c04e042c0502e170703031000050b480a24694840c9005224080c1440301c0c080c111901c2400a40d1110031614040c000f0780074a05891003295003030f03400c001c82c0030002ca01c14030446000b60001c01a405a102c01142d800804444541c003580c04540401d6540c28442c41080400ae81c51270511039441e11004c0c0300982440c074608580f04000f90800321402e210050202d04001e06603824001e0680f0003544006d0484030300400c001e080a56104070300800b07081e0601c00c85950f1075211000708120324043c1d00c031911039030f010b020712a0340182c4144080352909203e02198082c83d0440e00450542d615a56452000a0722040041c1009141c089500041c6003002c00802151590300c0046059810302059904a55407030700300c1485450503101410b41c510012a01c40c5e04540c2020340003145684a020444203824 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 287054109 1250 287052859 287052937
    0x31c0e07080a170922060e0a0513021003021e040906080712200d1401050601050c0a060b0d0206030f0403300b0105161a0106111c120c02030c011b05 65
    0x440e20000500d174642a620003801c0e1280c00c06040110740784d01111008a48017101c1c182402c00600412001501d00408030810341c210a2402610703004040e40032916483c00c40c9040d2080c0600400c1c103204070307030b83c90140c5006000a100202400c41c5401c0c81c4598041c41c0c1a80075103403114824114410500c46041d909243c0405403560fa9021035610b00100500194128110b1a52a200118890f580304804484107411a4001008500c60f40d4a030500241407041001d68012500c803460f400580340c0034082d510640000380880c5091a040c1000384c000103840c2c0e0501c078031404241c1d08004030080c1c40094103403140c3c071075000141c035542000181c0f074611401015010f407010012541007004111010f0001c40710030031500120503681d5540980342c03122140207038000da40100c0c40030003101410030b60a1611402a141810301c9113034103071460044481100c0d0350b400507000040c619800e540d003405003890304117094000c0c040c0401000f0000708580155100d41c2000b41800225442c812a40c02421050300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 287055359 1250 287054109 287054149
    0x20a0306060e0714030621031e070c1d04030f09090612140102030f01030b07020304120b060102011a030318030c040c031b08010518040203031c0e07080a1709 69
    0x354440014018030b1004445010024100345500000c0401810980340203400c050410506140701d41e000c2100014040131020b9980b00501c042001d40342207000d179040c0000071250013035840710541425030b0f41c0200d03504401c80002144d0080418001c9004245030310139094a460700c01345da41044101c4e5045080d900020505040240c040303501480601b1402c82a403107610741803280046002904d00341d000440e10b4803001d0307141c07200400100c1c905c610355690000403031066034070741612580702250707040c18400103581d942c0440e420440e07a540c09104140b4150b0400d0800410f804000001a60301c1c8160a202d40086107000c1c0308444a0f11b04020851010000410500891452442c0100146916001c00710302040d40840106540c1c00b0b1102c0ca0f041c0d41018000102d000c000c0c09003c21150f0020f4001c80c2c06200030001c48250020007070a50b52150619034010a03803640000d2068500b460a8005421680280500034001841d4010714812040407080054440201c840010b220000034450b0b95600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 287056609 1250 287055359 287055371
    0x6031d070503030f0c1c020f0d080c0702190e04060203010f0801020c060619050d0f0308010b030405071e03080309061506120609100305070311090703140403080a0f1505040b01020c010206070c020a0306 88
    0x294012810184001003002209d00d183c550702001c5071841c0c0180e0301059510b40030040200903041082e03c08141c40c510304080708107240c0c0c4040100d03880700215001e5a10316404001030020b081d200c400c02000700075000080d800e04625903041c9403907540c040d08440c8192641c0c6090040c881080e024100280001400f0000491581c103007101c4400100304101c00140c003400010606410070802d0b240a42e4002d80140705240c1003400759107401400580c0040c0d8061340361030000004004100851044110b10003400c0541808010700c4550000c034212903110746000d0180c2e4034031151002d0074035880241140c40345060340b41c04607140680d40ea2038002800902604a010080c0200c1c070fa544520b5000a07a0329140903503a04004070100c40d010f050b2164070340802d401040120340706820a40d000601c0302800202c1200c8440362008039121769a5400a800666a08010902d07140c410a8240482800549401c8401c200003d40740c0074000c02d030740244580c162980044d502d820b60ba003005580d02040030040303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 287057859 1250 287056609 287056663
    0x1008061c030e0a0f06020601030b0a020f03010b07030909060506090d0807120504060809070303050d020306130608010605192628020907020a08040501030b1203030106031d070503030f0c 81
    0xb103480e041c01d0709001d4880c2030303400218001d40081020403a0001e5001d0049a42107940d80e514850b4041c110359840c0d5000c0c0804a850100880114000d0040741421703540ca80d80d41c507000d0705d8111140d10032401c4901d4003100308419200d400c11a218031800311102e0148688501d45900540075174900a064030106d41a4a00307015000b00c01030040da040d83e15583c80c0d964072644003039602d101038080180003907424460300502c000c1a4014503008040204110324140807680740138204c0315958010780450703443d102c040003d4140700c0b400e00c0c20350010a14646041e401c0114102d074030036554800d03030030b10b0040c411800c03145001804403041c50480813840410950403a00c04021407403044209038452440900410f908038000218901e81d07a51261032a0b0515142c90010f40081c4040e030b44980e008a160801c0540c0d0850600085020b0211620b000440c2012a4045100c004120051025560064405100a81d8000140c0380f2203402120f805940342c5182c0603050511903000000c01070040111364210f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 287059109 1250 287057859 287057867
    0x7170f03010314061603090f0b0f0a0617190309230918060a15050301061806060f12050604020c1c110a020f0d080c060112020a0b07021008061c03 64
    0x3040b00e004060000301d0044410703000d502c0780001d03550700c90b8680381c0981400c0e613103009800001540b030264248402144a0707032100030881208880780d5017120301541c05c000c0184510321804e80078140448480005030042c2c100789503180c102d42800303413180c80514401020103101d85c0c2e1070000b52901c224100c08030502404c00780525402100a9840761405a00003010060031b0340d00c41450101e10f40042503207032602c1005400805400d42c42d68054500a140850191001d00949004212801e6050b12070001a904202155000d4000b401003200707408074002420381c0011400140c0f0950b040021b080c0d111440000d001b485141d003a02502d01840718043c03c4c15002d0318110000c461940c07030380f04540d280303130030301523110404030328000d40c010b4407080034111900307180a0410000c0e10809125191520000a581c134040b42640411007200f030b00e84c1c4c003400310705004ca6800024a04200700c0390410b01e040c0e00050740380540a041c2410040b80740d00050744c40d5100c10039413001d1b02001c103180d00c1000850038020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 287060359 1250 287059109 287059111
    0x6040509180706050405030723090601090b0a0e100503010b040905130606080d02071e0e0405010f06081c05070b0c1c050106030b01030b0303030f1303050403210314011a07170f03 78
    0x140c440d01904000144111000c4015035008132700c01d100c1044080d280c81004444c2d803000e4009810069903200c00b1401c0c4c100c1c82c00401c20300c4995265020314140179010030102603440c42c00c884c10030009000410055050f80150780603140c20f144041181e5980302d11296405412034000303003805007860f0002410f0700011820300c01c148055070968100302d869003080e10700403402c610301d02184604d40d5004c0118040004e00e240e041031003200041541141f607448071041c0c404a03080b04403141c00100c545224041907070307000b41951100d030500c1d6080c5882521808140e040040040380300c03a400150341c8106258400d003403100d4080b0000100023558584a0080042425401340ca001c6843c1c800f000741d030b80c40c0c000190703440752000d40140169541c560440585411050348100c0c2481010b1001100052449101400d800d48003a9001040c810400004003940c4050042c107800007406c00060200e90203494003800806080d864455440200e85010308900c03200c040c0c3d9801002c40440d5449103422400019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 287061609 1250 287060359 287060369
    0x30403060606030e0f0d030b012d080f041101110c0d060506032a01051c020408010506090a0e070311060403060f061a030c043506040c14060405091807060504 69
    0x82040d10501407204e03503242c4008411140e107900030611903401600c650450441c486c010314008d03030320f2080c1d0502d10131918003100c403500c00310520040e100381d0f0560000c0f455520080d1051042141d04241e20b84070070724a4210346090400903124064402d03080200078121074107074068054800700076141442c41c0200025142188a802048150160305082220820000c1c0c002c9403440d81048240f001514154800401390990810344c0e50f18651000e018401340c0000d10b010000410309240180800030b550100130b0130030302c25519180062201e10f4000910b0002c1d02d900198820f134480c001c4000883d64000c4d540024425400c0030220b04640a854000c9401c40d82d408038203000456401c116008140400c80b14640700b1003051004008042c907140c2e8040c1c121040402a24840205000c2c040480fa05a280b000041e030090040c081040b01d1034001e400140103005030301003650320520006209128910801e4400d00c5200c010504940c0315224407113901480c0c0307048620099540c8409007040c3c00c0351242d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 287062859 1250 287061609 287061611
    0x405060f07020c0105032a040906181b1d030d02010911030106031a0a06150203030403081b0f03060303130f03060f060e01230907090f120b04031b0503040306060603 72
    0x11901c0d503800003e1031201c9400c161502d90459544071100d0001d1301404c0081a40d068100b80d1024201001000401c06420030383d10106d4068106104034030005a011804201c40d45010400d4584041d04603030029491410718001d0440005040c1000c0720850300780e01154180200041e28183c40e40540c0314514140c030810040302024080703002c2500301c41d028030024100048a0001910400d6108038096002c90181c90025642c0c1e2901b521903281c48400c8640005a0b1000080c04281608048807581c0302c11903e25000c03940340e40c8070743e07810a40204415030b1803d44011011a103952f4060007619103441e8511522800705680741c000e450043c645105c207440f028a021811001076805005110070f030340d000d40d1640d032184d10b0034444e904510034400500104550315a40d4420300c0d42c4e1040e0b82030141c6a03a0750341e8900c1c1410901400030402150703001807103ca2180000c00000341007500800d911a0309070500c404544550300b81000846d0150100904a003c00240441081a1a40010140c1e045a90 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 287064109 1250 287062859 287062861
    0x6050a0c020d140c0303040b0601020c04060303050405040b0109090207030504180e211c1b02030301031703091005040501090b060d03020c040c0302090d0609110d03090b070606030b0405060f 83
    0x8040084414100d10000141c010501541400340107504102140c40742400c3c030780c80c03e005040035030304640040ea02124008078800c00d10081d9a410000d50040f001c007100e0401c145861968080e0541c4941d105440c080c940342d030359590003603000e00704490082c8000d1100395924005458002e090f030307000e400b5001d0f07405120491400540c5040c400c40e40c12014a01c005c054004401403c0300641c070640d403100714945400c010540010303a80c440320000409402e0b40104100380098003500380200200c0000086500a200410100700c40d00c0d142d01105103a04a1243d84c0e4071025803140c20108901c441c039401600308014802040f00540c040841c0a000307481052480d20b070360003040812414240f001c6d006a0010181103210302d803941c030503111500e0b141001858100c40703901113500c1c40780d00002507031f078641d550070514140a07040c0b03654070810b2800c5680e038004084558002d410784025008245860101207410700c10840075034812400341d908508140c282c0d1a01c7e1411682e2034408550750410010301c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 287065359 1250 287064109 287064121
    0x8090115080c0423070516060c080103030e030f0304050909011104080a0606210209060303090a08060604110906030c0a02011509050406060f15082205030a020d2a02030c0405130605 79
    0x12541c44401c04c3c0700381c0c411456881d0b9480071640d41e0800c0b4807881800d150702251200060981c480c2509100d07240c1c9400001d58914240505034180c10803810b070103134210040d0324a04100201c2140c0c1a618100c500c40501e4403890003190041036000070702e0f4098000000c0204c2c0a0300001143d002c50b17403007641c007840f607552a800ca03940d05040144040c010384c11600000c1c1e00502e040e0b80515800900901144d08000458002440c450740039446015190000300900101e030070203000d645060b000145030f9038a440c0c0700101280d00f0740b1006058005540001c15600041e038400e4104035002600720013841c451759103644044009241c280c80448007145003000000d03001c2a040d2812040b101144200c0d0100c640003942079076042802400d4001c030302c203201d40c0b00c200c481d6400246034465008a00440d01c80c2c07c0740c8800380c80c2000e000c41200512894201a40701e00c00c0880c01c4803410a9081e10203034442c480c91000c24a0010300290050340181004100700e001425007030b44207481400f90b8030502c1651201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 287066609 1250 287065359 287065391
    0x10090617070506090a0513090605010605091305040f03050a050d0213181104090e0c09130302240a0c03020c0a0510180f08070c0e040602090109051f08090115080c04 72
    0x25504c2544c1002c0c20300c400704190f04d010f44000400c03010a540c042049800c5598120484000740c02540c00310708041480708607400d00d003100364403901800d00c08201c0c506064441020740350f40072000038104600010a101d0052061090350803101c1221070035911f40b1038441201c03410501c50b006510340506500400245060f0030302420000810780100340c0c0c40d1a0901800d60050010b4194035210382c403411340400415110a24000d200314480007850a4030305207482c00038141205401503140300e000058020100c80c058941ea00d4001100f80781c0000e4800611030b080d0b000c0c0c040e03410301010714000d0890203024001d021520440c100e0701043d040103600710440e034112070140040703400b420103c640d217004800641d181000b0444640210750310341c20156a6402c403da442411141101e0321900414252443c4d40c02c10300c0c00d4003600c41110034100e81c1c3e610401075504481801c117454100400f02022a0454800f9400402034010400c500c4034001d0311988845d030f403000c078041d0880c0500e02c0d00051203604451 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 287067859 1250 287066609 287066617
    0x106120c0e06030a18050313050604080c040b04230f07090605040b07051207060917071e02014b05040e062101050a0e1f0510090617070506 61
    0x649076129424608000d012040d00000c10b8110f0701c0d555440001c0c03940e05152a840c25040c0300c1c000840c1e5170802d0805000000b490b80d8815809044140418402d2400215815490b442c0030f540005002a0030000100030348011480341e084200810322290100f0640c4424600c1522004076882035038035a84c2007215010018030900340001c00034402448559204c20060443c68054401c44c0c50101025019001c140d000c07050848966545183c10300400001010a0348511f214001003414130700340780c80398482c03002c20280d070703060b031040c004190030031a8001c034844061001481440c5640041d4180a1011541942098404025540201e0030144040e0002c94082c1c9020380d12a81002c3c585603d0700b0903904003522a80d401381c0711200035182480c00c54420a0b601d0314800c0041028148440c0090031240e620001e5903c0350006044908080303043c0c01054000409054000360382d581c0d244003151100b482d508a52101d60420100150481008807040c591001d00d80c1520940c40ea140300300070700b900c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 287069109 1250 287067859 287067881
    0xf0b090c0d0e07121103030c030412051218041d100905010b12070b070809030d2c090c0f120405030a02070b04050a0e0a230106030c09030c05040506031005040b010612 73
    0x86180d001c800000e403440e17018110b0030f10240071a801c03d20403100710781c25a0400d4200140b0441c100c0c5849041c03107420001c150020f00104000751030070002000365103042c0c41407980207001c0d5464800340d44090f450156054581c240c5001660941012410300c203000d407800080940c0e4540c241001201d0501e845410121745544200c020704001d440c0407402d400c150418813051710050341c04d010301825510140100d580d0802d0654441e0201400408c0c240c1170a010b480013410034405140c030645054a45411040e00259003007403440d117030070100038150340c1d5100d540d125144c01518001403008005000015050f10442cbc0d40030350f5181500c652000c80b9070302540c07080c0c5034004001181040b83c2e480c017400c03490708160a080046010038040501384000310591899490a00ca407000410040380d141c40340c2c1620140302d161844815241d80c03a525504425030095074841c0c0d5440e4080b4030a99000c02c4440f0b42185052800d000d01d250a08084c003038006e0903c52480420b082e00c0301c41100712030610840798984 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 287070359 1250 287069109 287069129
    0x30d0201290901140d06090803070f08100902160f110901080607020a0f0204090813030c0602120405060a27060212090d06150503160f061704060f0b090c0d0e07 70
    0x68648050880784501d850541170b000000a007281c0c02080d4540100890103001c0d41d0301c0c503075a05003054002d06620b2026002410012400203100325a070540c1002c40483c2c03120413000d0b0310340d1400f0700d8200309002c0c1c11100030100038803011454100410610140321007001190302d144680c0e66043d859441d44012502d820040c0c2104003440002101020080c0c103142c006000050400501e03a0785090030382c0700c00c940340302883c2000c508004000c1d100c0001d40140c00c0320302c0607021818860584e02524051030242c0b5102d046c020034400303aa148a26030700324030783c407070328401d0303200511314000340d610305401c81c0103100040c050016940b41d498280300c200e139903160000d0b10160354254031ba00c861004203d550500c00d8003106125000401365010440c0c84908481801944034440c9001039281c1036021682c000d80c1032000900c3d0304280d004248403403e9025400880c0480c0509000c0c2c48440104944422613a0104c0d0f81e60601c0041c0040d1406441c0d9070607030030010000320504500b41541d40450b842104101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 287071609 1250 287070359 287070361
    0x308040308040c03060f4a030904020313050f0118080a021e151501020a031407020613030203060f10050409050114041b0b0403031b030c02030d02012909 67
    0x740701d60401a03005000d049014085a1203507103c030250303002110b00841c505e0300d6900b00b0305400304141c000740420213404030b070408951224180700048980707104401d80d0180c1680d0000071103401403044507811040288115030f01d00d000401c03040d03a0188841c05480c1e602c21495402100d40c01403060102210f9a11b84003484405247c0d1044060390080070044110b01520242070f202c000900728860307003075201c28003800003920200c0044000d01c00091854003d003803003001c1101580d0300071481440c0c1c2c82c0c16140c6071400c800343e200c42085c1842040b400130340048002580070214092440d9110030b49100314161162503d030040d003107564000541c1c1a00031300003200010410b42c41c2c40e621001400e489880007082d641e80c1844c41e1002010b085400303641ca03440321103c83c0b13a41c40e210170b0402d002d045030002850410f82035803002400140d4a0f6500340000408a10540603d03000b4011441c1c09a402030403a00b241c0c50500000b03020745110300b0000092a41c00112031080c18070b040101c41c1000c0090f00e0104c503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 287072859 1250 287071609 287071613
    0x10f05130906060620031c020a090e0a060905010611100b0a23040b01020d020703030c02120d0f0e0a06020c1512010b030105010e0409030c02090a110a03050603070e0103030804 77
    0x5040d100180324a4041c0e032030000400242150255a000b07003116160b00304450000002118154040711009605820422916000d00450080c6544035400b00d07400513100c0d00e100d0700568098000e9001140c480c4405001c0058041d1950043c02c25500e003484180170603665900185d89002c8829030080c1140c21606480360500c00c1c40c0d1001d200c11000915501c0741c0c0da5280f001622078192105120301005582c408180c0030f09182c000c8007100003084c402003204501082d0001c1d1948240e000007410004001500390655842c40c884400c88040c3e0740035552130410440d0080c05081009410740085070007030b60b00542502d4500c2d81c0c0d0080701c0070364003d0500a01500300b00120b411304017031034007000711080c42060380a0710361412540c040c0440d02040e603641d50401c00003500b0000140070f100d128071f003024003000c0040e40c407030320318031440c2da040c5c0e068090354460b200310034003401080d454000c5041002c03c0080920f5032542005010b82c2096007940d10041c1c443e901814009400d00019022500341000700b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 287074109 1250 287072859 287072869
    0x1b030b031e010b04060b0705120405011209020d02060a051801091503110c031b060f0402060a051b2e0e06070c060b090c0d0b0a062102070f03020312090303010f05 71
    0x12148641d000142058114001030101c0750141c010741403c40001c1400e80401104100102850503c3c10f6443d04041c64000020651036540403000d003501d45442c01c030b60464071046011950150300400300d90700c2e0502c14038014041c5c1c0141640101c01d04140946158a5015141880584203140d44015000c000e000e4160f01604840000c035034054800c00000c0e10005017400a0580c24404d03803819002241b80346003652516002a025801c01900c444c18040140d4424040f1345101c682424015240c901c00c10d000f20f40343c141040c1540b101d000d1036808980100544c0b62800d80401e60090580780521641d800c0011126088642000c84e0320803808220298020b00616800341d101d804c021a0100342358001c40e000400a51303884213141d001280e2020001e1046c0190b184803801500c0300d620291601e80c2c02005101140090522007501c181801458521501112101c42c2c20080c440d03c0680305140003944e0b41d0240c08901003070250403010400c00034010086034101c800d902c0b42d52944d5410001008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 287075359 1250 287074109 287074153
    0xb0903060a0b1522080102070b0903040602033c090102010e010207020303030109110717041503090b0c0a11070f150c03170601030f0c0804020a1e0b09030c12011b030b03 74
    0x107452800e203c00c00c4c1001c3d405410856000e01140c000168031200d032841d11252205010f080c401190b00240802d114841c1c0c0001070b81d0079002d008208101e0003001080400300400c2c10320804104d405500300c158010100303000202001c000a900800607040400f600e54201e019880c8020340c107800c108010032140c2e00c1900500f40051054101d946003400541c0d5004450000001d511000d1001003000c026403074a80c2014420501c0508041c002d844075540c9002d000c02000704131209032a00071545107074461040000d40e4495040000b10340c0720035103071800c80642c1401072080078040c80d030506840e030106100e07008c85d1240d1513043e1244640d14101c1e1030481d01c4007400400c0c1070b0401d03580785070b1401048468043c400c01400b02d0f444d048d21900f0b00d40103101c900c0340b442e006606940c50505d540c1c0d0941154100e0700b4122042c4500064460490354006400c00321003e4103298040000020080100301c10b502c0004001701d1b000e03402c0b18000c0400001d4045d90740a40703007940d1640200e440241c104c00005060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 287076609 1250 287075359 287075377
    0xf0d0504030f02010e06030412030c0504030203030a1409060c01090203010b0105090d060e0c061206010206060405090c040b030a170307081b07060e0c041b110319120b06040b0903060a0b15 82
    0x13110300c6905c9040031500b2030700111820f0729511403443c40400401c0d050b00c5001044107080c038085280034215000300c0e949101c0e01d0746160800050302c100422440190b0141c03504500001d01c1a030b030340d4205840c120701802e40140140d200c1e510b80031039080190f000b8400c03140041c40185c808030340100140c0b1980024003c0b50200740c5540500c2c00d4046441d903514000b071604294092034022142041d000092030810300400e454003075440c180900008010004920540506c100d82c082a080c0d070000220782003803078400f130042409500c078803802c07025000400990320030b040a0740c8460f05030b03076000090014100203040080d0101000c01c03079000483c48a4001100038540841101d07220324007003010034121116914011441803c0c10a4144442e03030045084894151a10080d824403070487c0704181c000e50f1280e83c00d414408003881003191414075802070b50382c1700c1c401441e01c0d032510707521541d0000315409440650311a0042d2400500c6002d268841c0141001024107040e501100030b58580031241d2110840c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 287077859 1250 287076609 287076617
    0x910090609090309270f0203010e0a050606190207030b0a290603010b030c0702030d0806041401031a04231b011115130c080115170309010311041509080f0d0504030f0201 74
    0x411700580540950390400700140c10040c0d50350f24003140f4010001c80a00040141801c03c400d2000e150f442c00250780090080079000c11031440900c900303901e00000c0745c3c40100960307829400c22007440309aa001800c04a2640c02884201075541903004420f52001140c541c001000c0c00188400114a0701a5a2050100001a140c005640c000920b00602d85841c43e0002d2512020006542020b0190880d85070284a603484a54110703074030b00541c505440310010b01e40b242d02000030140000100e281525001ca4288800d9410740304a0080e1296000400d0602152098085413a05d5200390401e0018038144405008844103608a224900c00051302d09441040c501c0a80c4d00840d0a0f00c0c5084020000540001000e042e1607815004410490f440b94800000090034228601804811100b040e2403d280000f4184600e18003014a130040c1e030450030b40381d650001c503e2030180e009002c041c01c0c8c2c2c814074103c3c1d403d08903000300c0d19503401c0c041c1924000920240410000a840218141005441410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 287079109 1250 287077859 287077919
    0x30209040e0322050411030a0902150c0c0312030118051504230603030403050303010b1c1a010305150d171909030c080613020105030402040b0910090609090309 70
    0x15100380365070000443d144210b00c114881c1c08048044400d600700403c402e0700c042c403e95079000044000b9000040c001c0c4076098858905404540e00c1400070800c04500312203e6866104075802d40c0d5854035100c0c00035019100303400044501612140949049409900c1d0403800d00c200c61181d28050301300a003144c500e01005020f048000c1d92180a02038642c0044842241c1f600500010581960340c05040c0f18080d0300204028008180007004587c1907841080803281d540e0035084c4000c03a14490322805a4865107020521005030761000940740980380c099809010a84400c011410207450f01042c26a1001e81c0e4141a0000b5410a41c000c038003414008245041c03000c0071a51001c0c4581c2c5459400014000c804144104034000404001a100702e03c020003051a01c0203005841c4481d011011381400408000201156500d03042591701c01d1000e80800224141460700500d031000380d0181401a605100001c070b0600424418055419015901d15881030315010110150408003600c000c07003068400f03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 287080359 1250 287079109 287079131
    0x130609031101020a110115060c030f0e03030d0905100b030d0c020402072112181104020c0f01150501230c100912080f04150515040e0105060901050904050d03020904 72
    0x8800f1340b4a510050302c03a265800c0450541500311580c5107000076100340c031071809000103070307102544ea23032041c0d40b6042440194040c0a000ea0f41e100d61561b9441c0d00d032100040c0e02c45100c4890700126016841030081381c4922444880c41001c2e504c0c0c5402040d055840200740c001c042d441503005601090002d04010700d01480344d06c0d14203541c0d03080b8841ca90301c4951001c2c00b110070366100c0200d40403407511140401c0a00c2540c04404400310f880704010302682601007920405942d2a8126040b0011540407240f40501009032030f400ba000300c2e0859110403c406100217015400f8201c86071600165120030321a51070051026070a0740c1000c40e1000d1a840f5054010559070000d1003801c403600c4c0941000703001e00c0000e003002041c441008000c450744036002000d2200180003200041c0352080c41c0900401c1642e245aa286900d420f515212a446400c00341e16082c00c14042d808940200000e80e40c44c1016a201c800344110124292401002e41d40000c6020041510030350103040e550500910100b0f01f51300c24 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 287081609 1250 287080359 287080361
    0x50703020702060d0911010c0c0612020c030a081f05030604140705090c0702040c480308010513090320070308070b1503010c0c030c06020f120103030305010e130609031101 75
    0x402c00142081d9540181c5c0c0309115171801d2245e01c2940904e031030010309105941350080019644101b0f014450088504103500d1003036010b07103001016010889458400c1c1e20401084290103862455001d8201681d08480c280c200c07100a040d550003a004003129122035403400401d010700c0801c2c0416008a91002c030b0315a48110001e8004d9001003580d6807186854010001243d81c150740a9051040f42821602030904180c001d040d1a024080084802c4e02d0041ca684082036083d07840c6080b00c0c004280f420101500501c00c941a2502039414115821389001c001302105d010540103408980e4801c0107007604c901c0e8582ca81ca5601042060f1803505030f595445880d01d41120100302c0d2070044a00c100304c04d90309203ca4002504000300e00a200301c0d0040740d0701500e890032500b40682007201100c0004280900c0d46c044a108003040307140d05948001e40100d4400c400020301085000908060000511001d01c1c0c6074035002c1c1d041e041c120360000c0996500e84004002e60003040b4180800130406a00d0203500b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 287082859 1250 287081609 287081617
    0x40803030709060206150108041e0606080a15111b0304080d03020307031812050708040807090b10030c09120f12020c0103111c0b1203040b040303121e05070302070206 73
    0x1842d10341120083c14110041e00f000300c010200d04064440380f0040c211070313034400000c82c1c06c2070b00683e070917500c18041c26802c407240c0184c980150119003008400280c40c080050440b100b24011680d00013020700654070f0000340d402801e0030710701502041c80860b01d4401950402c040c01401d44040340d240c00ea1703440390a42010902c0c080030b0003095021003009001034150107110700384080c142c41300800710640c0c1d9400425800f05420401080000305050081180210407107019003100f40485001c2607564542c034001e07290009845000c0e805010b02080e01c0c9019020b80a00e00507552078040200303007080115a11510032110668500b56040264004281000c09849074004181c0c05001c2c0c10000c030300050141c030184504c0d0300c411202000240404118141d02c064030740c65200000c22542005000101c0e41e442c004c8205001c2d000000d400039071000128000c20840707110f520b0301c40c41c0c0820b0084400450b4041c2c0b5034180f40d041202c4a5444004840c3c2c401c039030021050400504146c1150046a403a0300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 287084109 1250 287082859 287082871
    0xc09180a050c040b1c061d060906041403030709150909020d06080f191211060c0c0c010302030601050a2a0f060f020322020109050907050d0b06090d0b04060204080303 73
    0x2000486540d00c0c03d05018007034800c030b0141c1d030a501d118144409042101c440c104041c3c9442c2da50100c4100345403c800080d43c6407612001200c00d0703802c2c032200094035500b00b5a0300b01e0f120010503404001d6190080241c1c0d02c500159102c07500300c1440d10040740e5101180842d9442027042d0203e0205400c50311388090001004404130008034182003583e05440c1c210403070b0700b4003025803003107181c454110203d2441449036035000303090645030f41d2910016203059844920310295070140008000d60b01c1e14030b40c00341c45c0c48000d0b0b0040341c41079102100190120300c0251080f40c00610700300f0030046c1c4140180011245050190503140760407042550b100e80d8105240001c903503141189880200740a45030003a480c0c00600007600f18594203003d4008151071011140c20741864021100050035a0f000720360900083c03001030002c100b14589484000d01c0c0e68003108001400c1494180309c00304501700078065030354520b00941211101c0815846070061030310b0040c0100c0b5560380810000c0b4506d4018005503018103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 287085359 1250 287084109 287084113
    0x2030618101a01020c0108130609050c100c0506010603060608040b090c0a09020903010614010e100e0402070605160212040b090f043206060406050f0d092901080c09180a05 75
    0x900c00b9000282803020400c90103040103141d20034030110500c01d1800d55103c90780010000741814441c505907081c000400b8001e83c0c0a070850051400654000c840991500d219105940e80e507a01c400080c1d08546440c01440002100203000400040840c027502d5001040c0004035820200d90304009210300c00241c00007110710341c02007445907590509002c0c940144c8180d42030b500c401344112000908902c0f0209a0500c214820216406914000e0406507d0303448050000d5603510030038140003024120503900d0300c2c021401000c9218100384017183e8181c45210380104a40307054130701550707540345400140b40d6a0303000600890040c101d81d00c038403642501e0800a90100031000300b2103424251250020303410802000590100011039882400310740a441184c00d140303480b030720003520f5a011406001084d011203441d004a0b00d0a1084042034488030b1214450070420940030658180030030746080c1301d454103a903c801d0f0104113900d490410540c0c0000140c041c400f2603142d60822030301e02070800409407016 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 287086609 1250 287085359 287085401
    0x80d0908090102011a130c1e0804140604030e01110c09010914061f051305040e07030203070503011103060d050a0c0f051005040522150e1609030203061810 68
    0x342d602030107492a00c01c03c0012189680307071000701180900708107001d5600c00b5540c540080340c246000340000c8040341e50343c00d540e1400c44031003d0041d0000c4400d84050b41e259085d00c22051110f00d001409500c507962603524000d8404040d030055850701288603000306036002e03d42c0700700c20b20b803a0420502d008100302a4041800c00440c4502020140b000e04800d0084605100304c107400e0140d200302e60502c422a01c0c09981c0c8207442c00d40c00c20004900d4000d203034000d0421403c584401c6000412400b43c0c0e00031019200c0003680e6034101805c980740c41300030300c80d01141400011441d28084d01c0c4d07003000500031130650341300f898541c0d20142243c100b42c1103030b02c0b000115103040c0020b085c8101c0c4240b0103401820450700d03203402e0070002400c0c4242c00d048100c1801c041d10000704804010f0b0040c0c8510301c0070903030780031101e03803100c1c0c01d075001d51000c0301c19264000606045500d420721480e20b000031240c0260180c86a0780711b50258005201e911201640c1d039120302940d028203001241f082c1c48072821482104409 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 287087859 1250 287086609 287086627
    0x110c0a05070e06010210200f03040b060a05282408010501021f02071a0c0a03050f010b07060e07170d030f050105150d110301240216060309020103060314010606090e1012080d0908 78
    0xbc8507102404441c0201283c00f0103203c03588401d440036038150180c03400002c15100f0305116200300016500400400740c000000030111501d09401c83d03494100740d803a800990b81e2079500488c1c0e90340311104060008040712090074940b042a0707005020880c011582c0e02c07641070703001141c9607c0e020141d4a01c294404001204403032164140308a540056404100540c40e52500f400072407a03000f801c80150410f55079000341c0b800d041080180100611100c40d08040c0a00c900c3e5041d91144242030005007c80e05180b801c0388107c6103403240fa0f0680d140240215404414648040c80b00e401c000e84c500c0c00d450340d80e200341110a1440024600a002c4000802210f2107054560307040c0d408440283c405551041d5500400c140d0240501c41c04c1d601036281c000364034138840c00128050000c581c0041c2c200160800c0c2d08908101c10340000c170a9494607120000380507070391005d20804010172105150030286812003400003403002004600b03028000d29034981008040c2c55188110740d0302d035178116900b9500040c0c0d511 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 287089109 1250 287087859 287087873
    0x40b150c06070512270a032106050a03121205090c040f020a0903020f0f0a03050f010501060c1101230a080411010302090a0b0d110c0a05070e06010210200f0304 70
    0x60b01803800d00d41142030504400051003a4035000c0c00203409218801458883c1c02582c039460a15400c00008031540e42e0000c0c04c0150800700780074070401c0e00c0c51855000d0350303240d11a0302a95003291406480d01e50710514580700c08080c1c08028500c0c10801203e2803207200900400d00a1034041c486c11000f40c5000f040d40c2003080701322400d4110202e01903005000094001d40c0003034100080301d0f0107440b00601c07a06408005030714066400030050340b003119840048140500041c000044061090023040740da601c0c2d03031041d104072100e0b807801001c400000300c0f039041c5944150f0714006988101442c00c694010309010303181e4a03420210040000a00200c200000d11540880c141c508210a0030110f240c445810f0100b080701c6802d000e0307074408040000b5184e81203002c82d802007107280d2480c1021511043e0401d8070503141c11100100741c90070310070007401181035403d01400c94000e0205030001c2c94007a10200040d005000100c4030042c0d80e1004c41183c403121807900d0010316408110000075a501c1c41c0500e0844 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 287090359 1250 287089109 287089111
    0x20315310504020d0605040206040812091804151e020a0509010305010b1303031b050a1b0b040e06040c090503030a0c170708030402090408090a150206070e03030306010c02040b150c06 80
    0x506140c20a002e1101507181e40740035941e0f41c1d42114010616070b0360780c000b00ea07030341c81561700c100190703c10138115808100305940941001c1c071b011a078000482d0a944016004600140c1d0068030078034403c946002c140c0c2a5500118100301082daa09038141981c001d080200d030055000c0c40040b6000003070300041703580d151188a01401036811b4a41c10001e00180e0904490080d003c000d080c0020030031400307050180c0c6015009402ea0000495801c8a203c0c40c190030000d00744420309408245c103c1004c42e44500748420383d0300344c41c001441030805903140000c0102510000b689001407118084000c44c40341c4080c80200b01210540d26501740c000003600c2c0c01100c00345504c013040d1403900b05021080004100340d0880303401c1a01212400300c50340b5141000240d51140d164555442281e064000074074040f15000710342e0440a68095405983c2c42503010b4401e100000c100da603040c0c0040000400c1c541c0168078040c2d02034006000010544c0204006c11540034107107101540040f00801e090303401d454204801 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 287091609 1250 287090359 287090449
    0x60602010c090f1211090c070506010b03040b040f14151012020306060d1407081b010f0207030201080a06090212040204060617040807060905060a1b090513020315 71
    0x81c0303607501e006406a861030080c000d0403a1488004120307000c3c01381e00017188131802c42c0207216810f24200b411000220783c6c0700000440361805400000034401a40c00d003507901c01c1d42c00c1045c0416030342d07844e621030030883c610240c00c0703a00d8810300354031001c80311080140071101d0202030015429428111411403240003581d00c0710840d11200c201c04c1c3c0058030081104c6400078020744140c84101d00c54640301140030150011400c09100701480028010b0300000c0510452280c10080380204161400454400035144800b8015030b00410081006505c00e000b241d9214807034030400102a901c9280305002d9074400c20160b414205914207100c1986414800e00000703140d581000202e04006c08241400d00304018400707084018042000014080c5a411100385181d01c1025500b071494542801c03001806a220b10b00c48840e05c6400b07600c80540a040540c09950340100844070b58000380c20007070003075440107020307000a40003105603070320715101c00b012409008800c11120102441c20034941d1180d01000c145 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 287092859 1250 287091609 287091617
    0xd15050c09150a1106041709222403030c0b100506070309030b070306080a0213020c010609050108151015020c0402030403021b09010501140706140702030a03150b07030c021203030705120609010b030c1308030d060602010c 96
    0x80002039080010300c0703703039680f0401000345039517441c0816445003115400550004000941c82d0200365004421a065030f00c03032a801101c40c2c1354220200d048948901800e00240e20012900002d450035410400300340d403e030180545400041d54285096489a601101000e512000140100c1c8401c0c010812800e614451300d220034506140e112550074036910542004a900004511a00c0e10a02c4000310b41c207400b4006564074202450020741d2a010a010607160662016218481e803400d54103203030403540705a40e018292003e04116442c3d40d48a03190442d211551040305030788903038205041300d1062003960003641c1c541215003c054240c074020564000740d0101000240700881118055a500d80e80514006044186030700c003040014003444000d501900c408401c2003002540800108080780003000c0c500d980742c170b456092090603d0280158806c26505100040c00c0d13041c00405000d0059043c030291001c40c3d40c52025909650160500310301c1d0701e031201020f1004903024015050080d0103883c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 287094109 1250 287092859 287092931
    0x105060c06010608090304030f031e02010e0304060e1201050403030504021003060f150201150b09010f0801080a032124050d15050c09150a110604170922 67
    0xe035058a58405000300030038040700001050403070004000f540c0c0074550145200d9600169810060302801440c0340ca41800101110031701d030030706d1040c01005512481c0c0e000541c1414240007040d00e2104400554580040601000907800a02400340900440c080c0d200011142018010b02400101c521208024503041c603600300314501380100720b8401c807a806004440300d0600140100e001d01422542041510742502c0086200744a000082501d11802d03200c00701e00020415094807410403d200d8481181c101d0f20504001c203005403030914078071032001e00c2c000661034442c40300c1044400e903480342c5149044480c030b00c01c0050f00c02401c1202800b0b0850741c07501e400d040b690721984d04900300003101c800d1030f803284049a24415940103030380c500c3c03038004c08075a50b5860380a160205034000322036290004011902c0400c10800114690340151b030051080030b0300401024042d03506030b01901c61039401152001241314051041c0c41005032100100e0310201c2c1202c1140302d401e140b00f0b1410b0030b1300c8008046003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 287095359 1250 287094109 287094127
    0x10e010f0f061d2a1306020705030a2f0a06020a0201030605040b031f0f2d0b0306010603020c0307082106010e1e0a2606100506040306020310091503020108010506 71
    0x41e454662007200d00c00301c03c4000718500382c2d01100300781448591502d6000031070904100204240f000c0b01b5640160301300c3e41c5130340e640d0b800c03d90741d2100303130f00054a101d134000800000070207554800303900859942c80000c1c4000218012403140780c0f5640c40603006800402a44c0110740e4940204801000304903018005142c6040000c1c1e180c0b500140103403649140003003841d8101e4041d8114444504503000c00304041d0041c02441d1004c0d00c82c00d0401010084540101c8403046840c3c41000c45429024009100b82e030709010050b0025888504078585601c0244840800541c41c1740c000e20b8400c01d881c1441d00b9849640e42010044031000d000780f41400703108800140f0729100c19140b880b043c60b207161400100506503000c180d9101d815080715079060700341403858458103625164244c803040900100c4030300d079860400c03a1950308101c3c0249548150200030800c00302c3e07807035005190000d1046e213140362855034400c1c100d002c075030a40801110070400c0d10300c10415984c1201016006190584845103051203030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 287096609 1250 287095359 287095409
    0xf03060b04060e0d0605090312090f060106050c0a060c0504090e0106080309061e0304080a091512020d0216110418020603010306020c0703080c010b2704030e0102010e010f0f06 77
    0x50b009400c208480705403000d42c2c03a5039080300d550314980c20900421403030070304a1034203441c0d41c804031405822031000000300d80f41440004044921200c010040c1102341d00b050b81c215003507441144032000170701c102e425070341c00710f4458420040040f429481c0c0d16500c0b86002c10340c0f0180c2e01143c0415031564500b5001300f002020103c1118119801292150740c2c0d01110107444102d405400c41c40c11000d4008402c00c01000b029000404000341180c54003610703140d07298400032401d01990111400210354010000b2403141da074000e8800e1200c0b8039009130030041048003080e00070800c3c2000761490b5500e03e003d22114146841200d40310310418061500c06246500800d40710310041c032009010582c0000d0149040d0400d210003c095688580100d580b074103900301d0903001e0071000386c0b40c601c100e06141141100c64040241c0842d00481d10000030b185645030385054500c2c40200c60198159502c80c2002661a0001c0c41802c10038050040001541000d80c110f103022113005410a1141c41100031464002c0640c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 287097859 1250 287096609 287096617
    0xf0513050f0409050a0c030209010b0a0c061a120a0b090102090d020f01030b060d0501031509050c01030f1b080114091b0702010507020d050a0212010c052703030a0206070f03060b 78
    0xc2940c02901e41c00100010030010101202d016004d801202c131541d003000520054001101e0007128442203d0341c0710101440140300c0ea4100201180424107142d0008035243c204980c030b81812401c5440c1c1e0240c2d1000f00300841100c1d04030220a030488608403042207200d0700e005400c089007034001c5040241d10000315142104640d0040c1c411030f000e05000e006684250011a10840040e02c03507900c07082c03d0340c40200902800e00003216035a8501036070741c1034240b20b03118503800741d03400400511940c0400d00c010340080c03005100d020085503c441c502250440b180c00d50343c48034000c50b0f440440c00c1d031601240e40da0316250b08505601c103896103002c1c80400070070b24098600c20b400c10554540d4803401880180c40c83e02c1a030a00039000700c400c251110900c580406d04952490081d500c0000b108411a801801c80301320a1500001c00c0090240340c10b164840c00848114071000c20010203c0e11140c000a451600244002c0006900a00802c00b0305075001c3c98071400b00100382024481c440c1422540c041c1c1e409 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 287099109 1250 287097859 287097869
    0xd05160e0d061d03130803090901090f060504020408030901170103050606090702070906180b010905060d0c020304170a0c0803120a020c011b03021305010c0f060b13020c0d0f0513 78
    0x32808180090000d1548007454083e000c00e07035500d21030018901d01d0b49940040401000d45c10780d126000940c644040100c03a18040300510b0b1343d106030308000300f000041000d00c40c0c15858903a01c5c4c0020500c3d0302c40d0710003071001e0488031008581310000c10000401e8141e0000d003001e18107201c0401040041d400140301e075002030003220907090b203541d8450101c0c5484500d41c00300f401c1d1400d149000849803603500e44082909103841050041c82e1360340c001074a031544188901608450304010031619110b00d40d1000040008600c1a28607195aa0701300c2d4014000d10415004142c204280300410844644994401444208042c600b401d007940110b0103180c400601981155800060300720110310290310254456400004500c40e07000038250040c0250043d4828013041c02c40348034003068541c042c7ca40c031034a965001078510320b540b8040d5910005440e40c0c4240e1a0000482e8194030709800050001e018400f04c1080100720a50705110000c02089081904409001d400c10070322210f081840c5428003590 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 287100359 1250 287099109 287099119
    0x150307180b060712080709061814030703051605090609070f0302070f0b070f0e010c0206040504020906281205070c03080c0c0d030501090b010314130206091201020d05160e 75
    0xc1c10a4046501482200f4009003801005212141d406130010b4103140511015902c01d041e00e40ca40c1c40640c0c0003800e184609944441701101045440784105904644410142c299001a40d480d80d802d89000e2140b05034440440d000c1c5818403013418102c0d03841e0f6005004881034402420103c4010b03196200359807030320b010503400085810a100074030501d00301c181d50141c84503c1e60b25048400030070203910050302000086922149001c03d42c41000301d00340300c98008000910b1719240804000003548502c1d030b4642c114405000480304951140d01048104a4550070860f400b1041c81004181d4070303460503440440d500d0403007031243c0c4540c001c0040e101654942405109501d8051800c0080d00803034400e0012440340f000702005155241e000340c0c0c101c0388000c0d418000b0440d1900150182c0300100d100d442103150480029400999200c2e52900c1c2600103450a40b401d00020080b4104002503100c480440c1e40000d80c6c81009022441078983c040001303141254541c56801c1c00a044001c0406040d102e2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 287101609 1250 287100359 287100371
    0x1030c030308090118030c050d11070b07110a060f030501060306180e07170106031103120a05030709050a0b0712030e121c05040605070215091e030d0c0815030718 71
    0x11800c254440000d040c0304958504080b410f619001f00480c8240800b03c41c9401200b030219462409810305843e0261140040d00c40a07045c40305480740c0b90010b810960390210040158900798032000c0e20a0041c0200d0741d1041c9010b103480e02c01a00391079044c1d0005007014900702c010001c131140718045004908048030007180e640d2008501e42e02d4840c56030400100040e056002d942d24140c154416011248180d00070700c0003980d4241019140e0282c240810384400007041080c3c051031046000715030000d624185041040d4445000c01c0c107542160b040150400e5000990f00d080c031011504c1c0010b41c0f24607103014401520190440b035212440041642103030034010400002d007080c2c0c841c0354825401c0d8a03400708118038150803c1c0000e4007040c2d82040c094002ca905200c52100c8040c001881001c40e40c006000544442c074884070002034017210b404003408144144007207800503000d40c800301d0460355508403240c284047c00c00c480c00c9900c1c1000f03200b544080c034100001c04042110240802150700000341c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 287102859 1250 287101609 287101621
    0x40c061e0302220603150b030c090904030c0b0108011d011505040f14040b04021503100e040305091e030c0612150f0a08010c030b120c12010e010e03031b0301030c030308 74
    0x81c002d2804028000320032010f0007080042d4141e0240d61403403051b001102d8600e40d68001d04803188416100880d042c041004084040d040100c2d0803074100c0e22a04d42903ca41010361121684e8850070380085603503945030910100300d001c0b01030050910742c0d4000000c11448030583e8007400c4403a61032240500840e15100000c9c03414242e40e102150503c0c0d8400304204a10b8a454401c0840004903030480c8a00051100480c1c2c600503041a41c3c41840003201c10042c0e1810500120702c0c820004000b01c08000040003041115100c101800407a43c6500e40d13402c44400c428000c00d410456140401c0b400341c00705103c82000794070b03100c660a402030303142c07040300e0130540140300890210440c509080d0341007110f0380e0001940203015400204511001d80c0d08100c0c240d500401c0003100ba488165600c40c40e40000082c030401e15000e0140c50210702740c2ca0000918080c00c042003801c0d0b03031541d4580d542c150008400c01c040c2c80380050003000c4032058a440c0516640c15075640e601e00051500028013049135840000f50 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 287104109 1250 287102859 287102887
    0x16110606120f0a060e121e0313170304060509030a02070306050606160b010819020d0206370210090804060f1103121806061f0210060806040c061e0302 66
    0x290006000082d2114642d00b410010b0217001d980c0c1031000c007840341c140d041c010324001c00c01f52440c903941c45000401c0c140d4142c00a200310341000e81390411220103d030f00100021000040041c10340000c12146480c0e14080c1050b4080707800041848015400400820858a5001ca00001643e500140004164440ca4081585401041b07c5a0504500f4203006401d019440010303c0c101c031080001c5449035103070740c868124525545e031320003904100280300785801450180c0140c6900038600d01c0c83e13180401ca070003072024903001c00780c00341220480c2c1c480c00d001d901c3d5051040f0760140090313020600480805a4882e40188298400d210420100b903128040040c4528402d00c29485000d02b160b8072400c1403e01100152403d40352400c0690980c010811003240205400e485020000d2a102c03020100324824401c800c40c10003102c0c00c50249070141140760140e881614098403003a0002c151501d89443c10440041d51034202c0000e11680c10301004c08215880b030559a85805841e0140e00e51b40260310700b80c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 287105359 1250 287104109 287104123
    0x2306190302060f1914190309021306060905031c0f09030501021305040f0c02070612020909160305090303100506090d15090c0b0403030212070c0b0a0302031611060612 73
    0xa502242c00105100d41c40d400c080030700b226403c800000540515401c0040e01c080a03800d0381101a00d2043c0b00b50b240c8104541c103071100c0b0346128240402d2503441c0d40d002600790025001c0c2c204425035034010500542c0d0f4081200c001408040e00100820101040d42c4012440d03402c03002c404120000031441074452040f40000700441d484402591200e44c0700d44e02c2c041230841c40c060903006500d81414406501680e000d120b10011240e00a0b200b0103062010844034141c0052081c190f0740e808000c00e00c0941c40c1c15603d14403500176442d0440b071401c1007a42c020b090360720281503580594024802c0c4108801c4407000079048507012a030042c0d4078825600414039000d4150b10290901041160b40264802d03103400208046100d099070421441d100c1c88549801c0c095400060016448480c140c0380101030030009200050184030041d84103a543c01c43d800e42584802c01020010390003100380401018030911307143c011002c5d41070500d200f140840780a070b46c1e000020801846012202060103041e14240580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 287106609 1250 287105359 287105363
    0x91406070803070c150e1606170a0204080a030503061e0a0e130f03030504050d0201060807120c050306040302030a1814100e0907230405090c0c1504110423061903 71
    0x21000002000780980000c20f0000000911402000003038500e40c103460410301c048d200c05448502208050340070309601c8c014002d00c80c4016560800020801d02d00402100160611981d40e540c4e40e45080400c0c0702040000004035403039654510419075039559079040d17000c04c0d07410848000d0300c0c3d503482e5142c01e03005030701290010341002c14450068050541c5500007a2050340a0720841e0b096000b406403ca08a68441c0301d031036900c4d00000b1044c040700703a5021841011b903004010020625865800003800c2600c1501c084002d07070700008114030041c0d000380520324104c00120681c3c039054036048002c5001c907070b0644800c0c80380c6002c600720140035006105402044002402c004030074036020402030540b00152016600600c2e0030b0b241001e64900c20320895081c2c4101030100714803034458101c4603540c3d070001c0000800034050412030350218947c800d0401c2c4964010050031a14029110034401110380c0c0c0302c2d404103142c4400c0b5469980304680c00041c2c0e0000380c1a10711200c0d0000018212910224607000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 287107859 1250 287106609 287106623
    0x1c0612050c090c041e03050f0a0c0504110702100906181a0d150306051803070c1208070b0a020d0b1f121d0606100c150c0302040b03090a03091406070803070c 69
    0x710400070002c0d0f6004d101503d00c610125211492041070b0989c3da04601c0c540201000340000041c4528145074120030f2a441c00d0b4680e080c100b210a80c0010114070b690000b00e000a5005201040016840080c074034018070b03200e02e40c0790642d0400018240002a0045c90030741c01100040700d2941511035800740300b00711004007071042426200d01c0d044000d000150b40c81c401a40c8044080030b111200801141c0e49103034860444c0310441d01e8429140200d4200719419600c3d00811f101e0100881c1100715a948100e0800300b0042e581c02856881e10300f02e52420302c4060160081c0d00d945480c2c0760395a0034a102c0103041c0d040904e844441c500c0b070a0040d0158241d40000072414418019a0310f50000711103000360021561080f1120700c020b01160000659030740a02203e01c50500c0b14010840c640c003601c1c2c460f1203803070058546500c4d0008400e8079403098a45036115030100590400341503114603074101500b19a0a8081d00d841d130b181c0080c98500540402820061002010600f140e0151a40d00c1e0901ea00c419 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 287109109 1250 287107859 287107889
    0xc060624030f07091d010509010b040806011809020901120b0106110d030f02090d03020a1401020f0313050c0918060906060a0b220e04050f012318031c0612050c090c04 73
    0x1240c005c2500b428446c480c02410602d001240c1d84040c41c1c20364094079051401040e0580c80d22802e482140c507041d00c01c2000d582d072140e608000d40c41c0c15034424080c1061081d403442c000074525180032540c505a002804000c01403c185400902c04141c1e0140059285000700700342c00c0d11004080244550340078540d00680c41e440007820141c000c100d0040007030050070b1362189201180c03081401d034400c04000b07202c030750000c00000e203140003000d40f030000d410b01480c02c951410311640c0102c1c084075019500034000c002d11114a0b00c100408001d6030394048113004c003070403440c1002004078a402c100c41c020200704e4280030900613502c0310601000181c2e1071541010040142c0d4408070203a000e002568196624000c0038940c01004005006082441c03400071200021001c0f01c002655096401400c141202d40c03000c0151014102c080024065080c40d0046407103400b2a80b10052044914941c0240050070301040010003051020072007003400202914035000c1a170b100700f00d19031540300b503030021020300c40c400e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 287110359 1250 287109109 287109149
    0x30406080703290118061d030c0603071407060203040305030405060a0902010905060d15151404060203090918010e03090109050d0807062a02010b04060605130902130b0c060624030f0709 81
    0x202d42c440c00a107c0150391549450700d0310030305440780401c1c051281c0100c001c20104a00c80d2103828580c111601c003140d038505001c00c543ea88030999005890540c00104040244028004144442501702c60303007000410503400b132076002800c410b4880c82071033304c12840414140044001600140b960b01b01a07902c00710410703203c0c0d8250f4150340b079040000b00059044810740c050a880034040b6415660070360011410081e07410308210843e10010000403490200c0301800010130070074011000d14079201c00103180c031106410001414006513600007841900c00303d4506021400c807004a0b0509a0030030720218058100c1654980c0c1c00c40c4085841d042d46182c0d03154800c25690640c01000541002c84061104580d92002210f590203813248071403024440c46000c00818109900078140c41e003040110b03008940d03540e0710a02480d0030070080d02d00707990000020420586414a030505840c149810000d038a101c0e4441804418000100090314030000000424101d034013070480300340103081c1c600304110614566 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 287111609 1250 287110359 287110367
    0x31509050a02040f0906060e01080f030a0e060a0e0303130905150d0f0305130308090103060b030f180c1810060c080a0509180103150f02041406030a06090204030503040608070329011806 81
    0x912607100c00e40601c40c0cbd000398102010080350b0303e080340c41d6191408212900d0130006194030400c000c506006c202c128511035600c0901c054204903480000488419160a40213020b0320002401c01c40540d0880c03002c0300700c0766500c540d0894040d400440c0e2884503621131605560a1050444101c0200c14404002042000404c02010350544c280e9040c000b0319503420303180d1443e010a0b5030f013010304178590303002480c520700350010601c40000441c01c0303030400b01c0300c2d1000c606140c0c40000303800e40e0402c4e85070801c820303002c01c090414000d11640c500550b00603c0764588144a01076000e403074003013090015010409503034071496540619210390100055507540c1c030b041e00a0040c03d1203448071082c04c00c032000c0c4039810b052090b0742c02c950403c840e130302100d070079001004059030004101d48003840c1e460030086107100007480608091440741000750b17950b81c1841c402a142c001c000346000201401c101c2103940002c401030703050180c1c180c8400704101c4c0010362001621400c00040000825010040300024140c0e44 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 287112859 1250 287111609 287111611
    0x301030506041103030304030e01050903482107081903180b16050f01050702010b0102120306061801030b09070201060501180f0b09030304030f0309031509050a02040f0906060e 77
    0xc01c103030403242c079000f1030289034907030200703c9002e0003080401e01010b0465002c0c100a24020800034103581007000800c5050100c80d120400165801400e080c032100381400305064126001071900b0400c0f9a140840001916403121004918525001e04000015400104400c001030080c12095607000b550310f15038201d0f41c10b0740c1001030b000916200300350742110120f41c0c0b403202640c502c80c41c0907207007000c0050380303402424030524200c54903c10001c074480000c4081c8a440c0c02054680d0010485903283c400081c500804031511000e03140c020000d1210039030782c000032580503060b075014140060303000c0401a0024519440b51940120a842c20010001d9040d8801c0080e100c090f00c0d40c0319000300f8490281c410056500a02c059111186418086204110044c003031007180101140d2800d5100da8401c4944c00d00d541c01200880e28602c41401001490034606021031000d280030415040303d80c440070b5449403207800203030185544184c1d00101c10300c0c503000032000c1da8100c2c806100c129691003050900b00304c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 287114109 1250 287112859 287112863
    0x3010303181509050f06041724010e04150b03010c08100f05010813110d080a02061302181902041706160221040504110a0e06190c0611030103050604 65
    0x6184011542c0c084204011400c1c050039954600010b0401007400343c0c2401909160380c2c4464188400501c4098940100580b02c0004014101d1041d03601c19555041c200c4140ca03c200103903100c01801a242103104440d40305400c10701c4041e2103025884640b0041580c20590303601942000700050f1b00b5900300710b10074040d00301858000d8140341e81c1c0c5090300079001b180c040c3c1030008081c40049103000c0b1420208ae40514020390b590340000941c000081e002400c0b6070821109540046107401c40c640d0140100d941c000290005c10791400c0d025400542c0e200503051304a01c0f03501c3e0100201d452039121500341d40e150800c082e011941e03151601d5000c0c45008072180300162074412080040c0042200711a240300c40b40c4075070001c2c1410705048111584030b0a40b4100c00010070420700002820b1380c0c0f1070080a041800c80c0845507500e05079258000c3c0640c0d0100d0400e402150100030f0319510101e026104002001c0c41d00d800c9401d20300c1c61400f040a0480c081160500b41004030011090150100301a80554 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 287115359 1250 287114109 287114147
    0xe0411091c06090c12051507051b070819060b0409030c03030e010b0603070302040905061819090203060a09020916080126070305060105090a27020619021b030111220b03010303 77
    0x40c500e05441b402c0720760031234010300020f5042c003980034080c40703078042c60404840315019220055203074040d082c641a21100e00f214a41e400c0001801401f202d403150564004c0300361001d1110784580d442c003a000e6054018002c00f050741d6036040003c000c40070351165000d064014483c41c0d99050420f00103000e500603000d40c05034140707440d0209419180054401c15040d4180740020303050f40d43c0580b03c40c0c0301c920083c0400426500c880d4050010303a000c2c8041c902c240c240c44000248030700c10b4014440d010400400b000c2c400d0030701c445180d28080d04071251030b04450a410f08103400c45045c00f6021900d00c98030000307003d54800d404000c0304012010513103e0607154151420005556030010000640754214200e010b80c2c40d072064980f0420060148844980e40094241c40c50b0881103952180314242d03502051005802146049080c4441c40311401c107004003c40080c40342ca412040f007052980301d5001318524112800003032940b0310264483d04001083d01e8180380783c9030769403414054540490425044403507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 287116609 1250 287115359 287115373
    0x30206011d0118090f0c0e0109060b0306031513050709050417030115031a061201090515010215091207050d0f050424050405040c0e0411091c06090c1205 67
    0x1d81ea0211a081c100c03080c0c80320f0b0219006200c06084011305520106071558548455980081340c20480321800420700c03000d04000707035850500100106c170241d811840c11940200b0a0080c25980003403c4031032492200a40d10b4079840c0c000354180c0c200c001345001000d60081100014a00820b588901d204a00403108840041d13000d21b000300240c40240505001200c50440c4210741500c0395101725506a00d10070301c150366003042d00c0081d0382504055880c00f10400020b0041c014a0a58012590401c0d4511480c6a038484581c0001c2d494200318802065811100300000c1c031800c01c10403400303440074961903400740e5030311917030500315102d200444c3d00e080411108030004d26080d114104843c1120b0311100010030303041c55590540780c6142110020301c1004020310012a603661a442404003c160546604030616054001c0c07000395447c01320071400681060000503601e46840d4141a02d051040b0391800708a401494040001c25190802500301c040c4004041014445001e05100c01400740d021940c00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 287117859 1250 287116609 287116649
    0x3201b100314010e0a020d18140706090506030a020708070305040806010518070e010315090b030c0d0b1914041a0a0515010e03120a0527010203040311040905070303020601 75
    0x281d82c038101e40c003141440e81034010460f5000030103950350040750340840503262505613040102500d00c450103140140003100400ca081001c00040c07600c0e0b0841c0040949000c901e803c401030003a423401e11a55000301c80010000d0745007d615070403141090340c0481110380710081d40c100140032313030498010b51600740318003400400e20380b0340301801000300c10100388510059511220200d40303141160243c0d906040d151410307025025040418200600320382e2100107600c40425041600d029070242455010b1002d4001440200d0fa0b2004229440543c0c8a414180c0b2500145044020b1002403610480d070b600040500040107000149100500058010030005494030200102290802d03a0038400c0c0c110090402d03031030b6501803103050340c080c80300805076465403000030791541850b03010280308000240300140c80c680c51244510101030803400c10354030441040900e070003c1d540344154000540b9407410310303400d041103544a800064849510006031015290f880c50048c2d6100030a00031f040c4502001448249 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 287119109 1250 287117859 287117861
    0x1305070f0e0a020901110f0616080c07060216080d0501030c080105190b0a0806010803090306010b040602100f02091c020906030109110609030f0708030c0c0a0803030403201b1003 78
    0x581d01d0100c01c0c00610744a400100b002948130a4206050111841003c150500c042c440f2440c1780c4400d40243c651441c00d91950702c00b922250390780100b445080070922050300362440c00d54078003544c0440016a40d080c10006070648209003803008149210010703145031070800d9a08040e040300d102c1d46945109a0b1900c3d440c50032f80b40225041c0c1003020700402200701102140c0c0115203d440b01901c824106525140b0b41ea082540980110059500000d58007001c0e00341041800d004001c0c19081d141442e0070910001d44400481d80c99444068984d000441d09600d941e04584a6050040c0140b0714001e401c584504407002441c0c05900c201280030014409040600840500c2030b800121249181c41185c1084134680000e04003507014414024401c0c2107050030043c4c240034014082c0150307180d038040d4402a00d02a04071801502414a040042010f803100000b1340342c015134941404a5050558ac01c2400c0c030549403504000d551181494425009074003001d80003600c54281c0b03040c0007a400d007030400c0e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 287120359 1250 287119109 287119139
    0x150f0408120402120a0c17060f010e070201060504090f02010909020306030c010c0812041b09020f0f4504090b0127051006021b0901090b010e0603130507 67
    0x901210410000c040c1c004541a080d9544588028190900f4482c0d18013030038a0310443e0314080b6010707000d40314184600740303e924996880c428044020400303858801c44d09440e0f41018815041c9101182000c211002d0003904034074094031010300100003c008904120808000801c42a0302081d441800032501040314000c80784203c01c06401040d08a100c1001100c125011250940c0c0d0039800340007251000810518072806240100c00410400e14105c245d5895100389901c8031070f601d0300c10030840c6020740200d030586a00d680c1d00c080c419100c0020160340c10041070103104003030400604003805900c5940300900d80404201800d504164501c1100500c0100c40c88200c000d0102490b200041000c2d582072071120404038400103102654a03001e11041c0140d51080d00c9500740415140c03000e00496604100060440d410704050b00c04105189011402e001418052241401e03165049038841e80d00403803121040750002f624856492808281000b00d06d06101002c80c0c1c24080c3c01000100417100410503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 287121609 1250 287120359 287120363
    0x9210a1b05030f070309120501050601020d02030304020901090e2401090b0d0b04080a05071a072705010f020102070c0b04090b0604030503040608100315050a0e010c0905100e0a08150f04 81
    0x15443d0600c40d024081290b0400e000440800010f01c10200e403100154810350190340c030820021800f030800d80000383c00e081082038010110b42c4144100809a50341503001811584060000110074a031070740c0950415031a00c41c0d40c1d140c03c420700d90505082d019011890304843d070231441000100d41701d80410822050b2000c01402090310400460041a4004028100c0d5507090522901c1d0182c582e459004c550000100846030003c2c4004110f1060b41000245410505074002c4040712400e450b204000318807140100d41c108a51980d64030180c60003581200c4640d0b401000001c81e07135903110343c944a150b00c1405600c00c0242494600e200b50305201c81a1010f9980c064003541c1000c0c20910100d0f61003400603e500c000c24021070300080480d04100902041320f1102501048034641046180c060301c000c5502c1c40066858601d40200c0990300c071108000780d410440b2400c0b103d040c5807800300e42c082071120980d64044001a4001030300c200000d00102c0c0100444550300c0d55544159851081201c11600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 287122859 1250 287121609 287121613
    0x9151401050715050c090d030201020909100b16081308010b031207050304060e01020307020a03030c0c0b0906090d08041d18160501121b1101050603010207030f0809210a1b05 76
    0x1a420b003400f01c68124903480590302221714201a60800001d4545100c0c1101780c01603540055090183c2c10f2030a103203a44810091803e450480c40e01c610304140780300c0c10340030507012500c21103407508020b00780007104c1c041085c3c0c0100c10400fa89584d100c3d4000c1c040100040d218ac0701b032103165000d4100c194240e4a01c6030f0013002440c109494100165940200102c0460440c0805c11a280040c1c2e40c903600d00300998002e80d24606605c42e00d141241844002d038001c230303581c50000c1c04140007590360f040440740d01483c01d4891a40c5000c040c079110303005009070f401451140d00801040000100c5e8087d05c0c0d03100d00401c12050303001000c0d0000054881c450f0806008504403001810300c2194005e071801003041e074502200146000f04c02d8206510203a80d0300c48580010b064400c407100b01c6c182400f8043e00104118000c610f000001d80e4003a2104544608000c2400040000203100e84800d1001141e0a144c285503140081c1c4030501c00442c039441140743e0004194450080c0a507524100f0003450400e40c0400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 287124109 1250 287122859 287122883
    0x80d0201061505040e10030206120a050a060803040b130b07080307021504030207050909031e09030d0e09040609080c01020403121e0c061d07080a0b010b1303110a091514010507 77
    0x1c01c0c0303441c1540046c52904154640c15000005071a01b00007024000040c007c0500c407800c05590074005c0c0d50018150416071810403400381701e0030340003101300d804031008001ca813551240c0700003100d030fa10403042d0b10030b0a903180b01050310010711400c48010740c4142d80c1d40d402e5401c0c030641d640c42206100010b407805030060388800b80910250800b002d0903038100403078408403401c2042440c00580689c1925405014240d80429a081a03040401c07401200101c40c3c1050b0f800000440085640010000e1002e1714240d228070104060000c40421a41203c1c2014000c0d5503450700c80c1000c4544a060180b90700009002c842840f0103195104503005101c40660b03a1203424460030346a540180499603030a410104100c0300c808864103040100000a01d4103d000d40074448041c282914034800590000000d001c04000c0b440916800003041c90580380c0c007540c1190a400c070740001c14061031507900941003061a00c00800300f00046150100c0403200541060708616480600454040c06083d4004010220b128 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 287125359 1250 287124109 287124119
    0xb030604021804020c0c0f150d11120106020601030201120203041a0603030409060314060c0a200114040f020906010f20010b09040c0e0c0306011706150301080d020106150504 76
    0x41c0050250078201160010300c054240c00040c12a0701c4810101400c0c0d22030500070722142041551107035209070450740c4002038100b9048030b8495202e107903000508650740d00070094050003007600366203a1640e86950b0104640c0c480310060368424003800140c4c0425070111201404030918001c481c400d56115152181043c070070a45c400c43d807040a40b810b41d140c00700f07200c046003030803041c13203a007000798095071201c8800680c03610f010341025800740681c0c50451080049035200e54214803000c0c1240760000402d180c25031068030183c010180350f0203020210480405000601400e41c02103202d20780229000c5003144c85510045d075803d4901c1c00d034407020640c19180803a905095241000211110100204d20300030000c0000d00d282d001241c044400040e0301d041030001090240c00c55510a11366400035245051201c0040e0035558081c031180d03a060321845c00500039071180c1400c2d5a2003140c0c501c05a8607540c44804060300c44aa00190000542ca01140080c5420211048040c4505135490b00741c41c3c40d042c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 287126609 1250 287125359 287125361
    0x6080705010e13060e100303030f09050706050f070c2606010e0117070e07020f100504020d0f32012004030f02180403020a0b0112020a0b03090a0c0311011403010b030604 74
    0x30460702c3d5a440d04002117400c09150030a10440c95819186083c600794074002e0208c590301c42444503401d250014082c0010000210340081d40c00d6810302e0b548503451588128442c1c0300d010301c000c24904d019030b00003c4650b00954541000c3c444502c0040006040d40d01c0541c1c0e54609110380c100078042c0d000100449141c00c0002035032a03040030190741e011900d035000c0801d1510b041c0e90010060740070103111140307407405001c1402400f01d6040140b0603802e10380c00003406000b0405000c0e01c1c3c110090084001c03c407000550417140032141d12040311a80350302010b601810f5034130610b49083c0d4200450300b0303030000c401c403090150750720340d00080c60800d030442e11002c8080050080032604205542040c00d4040401c4018a110302c0c4a41e00524101c81c8a2500c01a13440069100b4030840d101003680c080180d649014040684400c010b065840c0d540300800c5510b0f0001c0300e00054003244075603a01000384503584c01ca4418490742038903a210403050440c412003192001340300d0400c5107034007031002c60b2061070130b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 287127859 1250 287126609 287126629
    0x309060606160c0308030105210c0609010c2a0623070609051207050c0409050d230417010605100f030b01022107110102060c090f12061906080705010e 66
    0x30700c41c01803034282c8030754441c9a01450f0350420343c0c1042020004014914144440c7c4c0720401c403035010310311218211800540c3c0c40400000c0b03148100070225200583c2d03485140024041604010300140c8840026481c10100c0744a0410f0910305600e18000700c2c00da402911100c407001d41d48801c00504c8000c60703a203800950844081225020749a44c0c0c4540400d0f81001400b10740c0c80c249501640d1050346d40340103440c202d030040030310340942d0814000c040851404240d010500712a410726400c181c8580c1200400d82e001403003024241d950100d40411035001100542d03601d41d2084000304145a25103041041d05400d20848000140c070220101c070189119400014100074180115007108111413501d0f110305c01865140c80c1c54410101c0e07034106010513a003120301656028000350086003030104c5007009034402c0c01c130101e0103851840740e08122515505130784440d951100e409d81e101801c002800c58110015110b000c41840c4c1407540100300b0f80c2021a1440403610142c503a0742030300300e6100500c00e540c06 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 287129109 1250 287127859 287127877
    0x1c12110c060706110307110f0604080304030503060a030602040b120f0405030712090807090c030b01031104090b0303040b0d05090708030405060a031e0632060909220501061503020309060606 83
    0xd21004413664401d26003010b0760041c003441d00c9a03c1c0000f9840d03607032403820300f0b1700c0025843d6501c04024003000c282500101c0e070300b140d0145841583c9550b08004500d00e0360b13040d40028030141c800130300040d9540c07230780d405019050f644c1c00302404a910b0315605440120030035200541035420401c0804d00069803074a96002d013100ea070030009420ba903188419030801c040740e4000d414003034440141c0c00c04e5950500c00c60100c075000b4201007012035443d048001150150f4010b0a000554038002120969010825500100313030110200380e85d4841380001e40041c04054840080611407080049000744000c41914250740018200c40d0030111048812009018000400c110742200403400c0d003d0a141400748a000c0c10100340d080b004002c80c180f0010041e070060b030000070150a00043c0344020343e50042118411704044480c101103441c3c1e6510076602a044469000801c88004400c20070844190403e03000c0340c01c4034010007c0071004070019000d03840219902070450b000300000134a0b51400030041c1411107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 287130359 1250 287129109 287129111
    0x60c03040510090f060c150c0f0e030705061812030c061f080604140601050301020918070216091e020f0d0c18180506120a0f02010302091c12110c060706 67
    0x20b13544130744070107019007a90424400181041100420320100703190400380905401801c11985100850003440020743e81c62a00812840c18652101c5640410122020b800024030f0340780d803120034000c0e004104840e030420350b00606440101c904035401c0030064030184100d000184c0314a07503030b4500809954150286c04680d81c0120b110210704041c0401c425841a031044244034802c8648001c0b441c5028816840280b080e070040200c06800d4564035030b21000c4050300c15416a40362160001a400c00d11890b108004208490340005485a01030300622100e03045002c2441030a0080f0702d4540c180c1c414840318141e20041005a8250090144d01c03040f917000e818a040d032070a1410881c0e0107101c054951000345a207100081c80c410b0340c000d501c18075030452803c44140100705031222020b500c489030704034003814902c2039404071070540e4000d4046850b462801040c02001c8002c1c200e001d10b01402ca90000d0b14030070441c0596039105802500e04a50540c0e01600420440409908002603984001e85c12121a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 287131609 1250 287130359 287130377
    0x60f02070c0e06040b090115050c030d09120809010606140901020c12030703020c0d030c080f0f0706060320061c020d051006080a110d0902030c12030301060e060c03040510 75
    0x100346070003241406808214421007103401c10400700010313140c40e0a00756100d40300090042180c072a036090000b0402c425420440d44a0088082090950103902c24040c4110f00f030034605820801000c0d0412690441074072001c40c143c4442150500304c840c58004c41010404125a1300c1151501c807014101007001441201d59640070a80072820f125440c1d6080500c5030700c042410400c041d014424150380d260f0a5880140403c11a10002c2480b40202c402400800b800106401d0b034a039500c0c1121062825850a0b994641152074440002d180601c0151484c196542408002c4100301d0070860b800e120081080d41800100480c1030ba003840041c03855074002d9401c02c480104045980245171280c140d0f503508a02644c0b130901c02918051005000411861902107007408440d81d003400d44282d5894144001a404192701c0032034686608100c03419440340d0384581e440c08445002004505a4900c0e07501c204950360080c040c0045800b8001201e81e20f03030070a06c014800340c1010800142c00140c149070060300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 287132859 1250 287131609 287131613
    0x12020f03010e010603060e15060d2a060207030b0604021309020307091703040f0e0403050304030813050604060606030c090b0304060b1804030c02040b121c260402130612060f0207 78
    0x31a04c281c0d004460154488062800d62802801000c40e0790004600347d180764545640020646800b00c2c400400d080a2a5074050300316186c04a1000001500c8240c401d4042c0c071103070042e54803c41e030300c801c0340c150304540300141b102c1c10a0700944e00c04290242054020900f085c0202019400040a110801441450003d140d4a01075000710150400002443d9124200455190041c07620b4001d0140120b990083c000003036804030803650b100d0f8141c500381499482d07640c002d00b1315802c8000d0181c118400c1000f84401d12000ea8071a05c1102c0441d20b007000325940480d020b5940702070324401d44003030690900005020a2094100b101c40c0e030720040509182489108c1668900325050301e080d40094441807441003141024442d034408500e04883c01185400003001d400d0703071040c02030040c91102c0d603102d0b840d0000900a00c00c4900202d40d04544450307a104203e607a610040c07007158241d204103043e0b4080c0c0202d02880c410401500c11401440340e008400da1149005040c2c241921800c00e03500300300d0800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 287134109 1250 287132859 287132861
    0x103110903240108010b01090306021623010501150f030e0f03071203060f030c12060b10172505132301030e0d0f0f020309150c120412020f03010e01 65
    0x8260070320b41980030506411101c0d280151507058024401981c5081e03003883c070a0303070000c50703810450b40d02a1001d0b036189209070b03075081101e21030500149151038a07412f210220520f10144903210301c501d0006c02450381e950110001003090121940041030300f49500d0703165144250030524511000b1070480701084c40d408091465503220350000c1d106404e540811620b01a810b00585000b0302c40c036409042e240c4d06584459030309508a100c0c01c003501030030402140c03c200c00c54004050000c00100a040000a040301c068070940c070182d065940b2080007400130f03245466480424038508005100d0341c502d003030401811340e0039a121816001100d44043e43c00070710200c814601c180380c40c2151661502d1414024005415160b28042034038658005500026140391721104001c2901c103e490300307007100740001c641030381581f003060050340d08a0006502c2c2800d002c50f440040c003030301141e002200e00d402c084041d035800c070340a2801164035280741d00581e400945401c3c0d0300301d9010200100001088000000064 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 287135359 1250 287134109 287134123
    0x509120303010b190e0612090c09100906090e0303041b23010906020a1a0a0b0a080c011803030c0b0a2405010e04200711030a0b0405010c09030206090103110903 70
    0xd401001c00140000111441844250001c141350400318100108240000c03400d0054203804c00c800400c0d48002210044100100a080e14010706901c140d030a0000c00021340d9000d60040800c280c0c01e00380d0000c0e501c0c9603449407080301e0f5404400b40d4150785441d900c169016000742c00c0380102120380300000c500d50305941c03d84003450381c40d0000b01c4c000b66000340016003c1c06055000105541100340d001e804070b012018400d00d07582c8050714142040c0c4d180700c0b124004201d140c1c942504402103c0010400f141c00040d000c00810b801d885200c848491424030b04080b030017602001340001d511300f150000040c0f27410b00e22030300300c00400e00110b90510fa10f00c8800001801056075104268240020005560080e0212402c0740b419034083c00b281200716181e1001240550803441c2040c0e00041c0b000c144008980d056140c0c0c100141921685d0700c050800103001d43d001c4d14260750b5035182002901361203000300c014104481e40949002d0401c81b9100054005201400050292250030444402155000c0c82a5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 287136609 1250 287135359 287135369
    0x90c180902091810150509131508010204080708010b120d0809030f070b04140102030106171306090c0612090c0608040c03060c050c01050f13020d050a0606061706041407050912030301 80
    0x140124504800301798100895000035043c020104658440350b00c5040d90903c9945144101181007000c1b200310f0700645030b1941c0014000e52000c40e01080840300810700700c0407511803c0007402000341d80000c10801c0c0262100c05c050300d601c40c001401000d4040c11420386c0c080005800d4900380a8840032490083e0701c203000880343e0001c84000c00042040070a030b864803513401d001c001c50031903041c64000b5011500c03d401c107040242040000cd0350a6040340a418030803540480c06104820081c0781c0101c00e1102d901850000c940d00c1e00319441508680d10034900c4a6070410383c04010b00d45451002d45a1000203001981d040f4002c3d040800440c401d4001c200110f02e1556400317503920903005c54242100d00260583c0c000610719810311002c80403c1d514421111b404907200c81d9000000c3c82c0139803810790302041c01022903081a100140d9075030000c012001c030b400301c4e00502c041603444d001040201c4682d030240500701c0c441e8101003000380b031180000e00004507000e0700c507140508003001e400b0303c0d54100743e00c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 287137859 1250 287136609 287136631
    0x11103130302210a0c15020c0102030f07050702030309040221180f070f1e0e0f06180f07030b0607020d06020a02071d310507090c1809020918 62
    0x800010554104000f07840501611000300008034240e5550031103100d0124070000f0010002000000d020507407082c44240310a54008555500544091707078042e42080350340e08151800f400004400c0c5005d0b50484001c0c66000303020314500301441c0c1c00c00c030082d000602c401c01d00243c8040c4442011880010a50041e02d403500c26055070036000c0021440c00171a40000d4100d42c04c1a00100249901010306c00281c918103c1c10f4186000c4020700c0d14854141030784064210741e80c2000303005a108084640c28040c00c3c0c1581c000004240008210f000d8020030ba50300c40c40340e6400400941114480ea00101a01c080200b10030718000c0c2c0f540000e00120060751302910b450f1b500140e502003890301041003c0040c10707070a041d004400d4464003911075440b0010180101d00d80008007008804c0c0e0301f0243c04103250b1003201c4009a6505ca8100180d51341e14500803100850b1410002060b52303030161003440b001d0240080b0500e0440c3c1071900040c065001500344a030003071070707981c60106406884039085200c1d00b540c3c14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 287139109 1250 287137859 287137891
    0x12051b0a0201151205100e0312070801030c05150a03050402011103180a0f050d030c0606090614030d031b0c11031e0114070c06050612070807030309080d0e0909011103 73
    0x740c0c1d00742910783c0104c50750800300c101c4e072000034008140b840a080500500040403880c0d84210707410b503c0360320140303801d18403c2e00c02c0085154109411606990160300d51310801a00d8105000e002003440c0d28248030035000740211380000c0d11a400441d4054410314042074103503402011240385410032619041c3c80020700020402070b04001004600401c0300810b0203094610746004503d20301360201010b020003132451052014440c3c0341d0052401408003940c04c2054907519005440c0c20f90440315018440d014000d014842c091181c05003240300032000614010340c461100054070740840d01c8100302c408080d5054410b07010356092000e02e000301050816107401403901c9140b1401c54010300540000d03d002c83c030500860b580d0103c00c1d0b0030300325441200010140c4070392000505d881c12010030480c440c45940404200c400e070125901040300d100786c403203918480d160700040c2c0c1c403141c00301400d0001a0001110b01550b00d01122401c0d04100b545000040c0100d59a00803055640211031444a03012025 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 287140359 1250 287139109 287139131
    0xa1707020c09090f01110a050901050a0905090406020403020f0111190204060b0a03060312050c1209040e0604120e0d110907120c051b060f0a0209060c060f0f0906010612051b0a0201 79
    0x8081c1b49191155a1041450002004406007160058850b464100280807801202c2c041c020031480d005410010600c042901e400d00c0d110004e540310740012070113a40c03c1c04652010754000d18018414640000107049240b280701d9001c074201c0019082030780c3c4a521010f0016403101c0800050108100a5402160301825401c01380c25142400604804214040081c010a9440070508400481c40c070500541d9405900300007401920161907a003005008490a0104000c04011040260687c54031b13142e04980c1c0300c07020801d140c02c6140000c0c1c12518028a0780130585015022103503c0301e05420035500183c82580c840d07044901c44d14042000c070784002444d0040c04c5416641c40e2204208100800f06450301900b0a84417a8001e440b20903003c2d0041419011540e03000140c2e180103540000721102407600c40300d404007011041c2c40c5940500f00c1c490115451000202d1558140d41c0e1685902c0d00745042c61841c400142402018141d0701d4000f608071100b81d052400040240f12000e500108901e00e02d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 287141609 1250 287140359 287140361
    0x9060e060114030303070206010b03040c080303070e0103060f0509060402090301023f01050d1202070504140f10030f0b0702070302061b0c041e150e1303080601050a1707020c09090f01 80
    0x4002c40d0740700340e005208000640340e0008406054841440305151a500e0318a801112031219030840c016900011041280c0d075903200000c5d2001200c240e0382403080b1131792440d060001c030f1040d001c0c040d0000f103d0b10010780e15007095002007a17845005000145070135004070000102d40c48540800454029802d1000f0304000c25403400340041c0709500108682d54500340000d07148409a00d0003c103055500300c002354245000b03001c410001c00c0090024840e0184c814000e5200300000c4418511400c40c2c031012441ca1400c0d9911501642d502c0419480c40700c41c55129144141030081002046201e102d20200050b161900a41001400381c091071001010100400b4140041004400e00032071818a40603d2450f005010024043e5070b180c001032038450249032003026000c01d4102c8040000b6250030301c206004004051a440c42c040e94403150652a20300044801d481403012010000d110842c604280d1003030304151076000040350044070000d40c100c074003048030074104981c00100303900310100c0009401303c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 287142859 1250 287141609 287141639
    0xe0703081b06071d0103050f070c02040609060602010603150c020c06031801020415120e031608040f08030909010605040506040b03090309130605030f03030402300703121403090606100309060e0601 86
    0x2013400c6c140030384d240c8000000001400240800c0c01c02070b0784120f5100359212a48554050a001017050001c1a12102d01034040c040030310045030302003840980900b6562261080030a01403040d409032480c800941c0411040381c00140c001d111f404128001100b52010034130003040180140c4040603c40e9640e03d0009e00721341040b000c94400d482c100f103581c40240f030f401300c111031144024984800c5131442c2810304000d03a0180b41c00c11030003842c60300f00c01704000d54000042c04031418219800724490b070303c4040031201c0303000c0d038401e481d0804001c3c04103000451038440915131020705942140c0c00d04120030000380190201d001d17a00403207981c5583c1400f81c1d040c2805200340c0c044021004502d90b09255000c2080c800e880d0701d4448000c102c0240443c00380d4a5202c41c0b00710200d0240858111540703a06101c0301a10310000700e04c01140c003525440c00394491200599115520000c05402940c1d195001e000e44004010b90034020075a0312400c040004002e40329640001d1080b0000701129130421022084c00740c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 287144109 1250 287142859 287142917
    0xc09060e060313030f030902120708071707060f03020f070309090f0908090915060c0f0106050a15111603060506090a09150902062a060a0e0703081b0607 67
    0x280420070405880b03c110900e0410b641d041c0340540210241311000c50003070600040c002d6100c402c4521200e041c3e2400100c5e0380c1507440e28400d454050350f4800e0b607101080a10000c0380480e0f082410204000b070b0107501c1c00030460006003009840d10b401c0d00142401030380b02c1d6404801117801400c042c848102d11b44100c1c0400045c0c40400c000022480c1c590461600a509143c0e200e00107280003c0e0400558850041c12030344003411050b03c410040407a15154094a425002c4e550319002000469161401c4800200c840ca0710045d5120b0464140448138400306481c820039a128141c10000d01204902240c0d0065000d9900040e441c01c0c01420010815000b5007204403203420040400046041c0608603440f0f0700c0e041c4c078000f070544414030115415008548400382140c000e030743c45801c1a50034004500c024485041911219038030301211303001f220614402c00c80c40d40c0c080c01003031002691103070040a0384c482030f0b403203001081c0c01d020700b00345440c008a40a0001409865550b0100c0034001c0090b20b03a01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 287145359 1250 287144109 287144119
    0x9060c02071d040213021b010e0a120c0317160207050301090b06061305030a060504020f030f030f09030a0c060f17060916031407080106020708030315220c09060e 71
    0x9840c10070b00384100e00d90105064294008100450308540c2e8903d074215550012440554940542d08020b03c140401e94000c503682d5428000c0340003042c5c00100e00b0707503811a0302c40b440340204280410210b40d1001000300880c10b1150088084151441c0074030750a00ca0b00d85054034042c0b415801c08c0c02400c1001903403005010b81e04002c200f10000f4100e02920354408003d441c211385075104d421800c410503100f50f02564040c040c00c0080d00610466400071031040303009032841100e039803418007410b45e00c6e58010340300b4442d07800c10b0200d031000310384050090000480040c100ca495a102d41c03642200c290f180d61140020401032494810b1340d58209060083c200c2c41d90f0440241444c0c1440801c40b4a41c00500c402010818030301491290b501035406000f806818241448507442c03d40c8018000c140c007030050070054466001c1c002844400081120722415800351415005200390060107800185012400580c0352120030038000c0301c81705d10600340031078099552412111700d0080003030a10220f22108902039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 287146609 1250 287145359 287145373
    0x60112020f040603020903031e041a0711040f061802030f091615050d0e0601080616050d0504050f03030a1410080c010c030513060206160f02061603090804060309060c02 74
    0xa00403041c159000c4030340905015a03036070b2550000038194402d04e00c291030380c0381200031a1800c042c00071001e00141c07807003400318124004c0c0960410740203018040008202e8180d04048103107030705054102452401c60f1500105200392240b110208002c080308070b884801d0380c04810003031140001c5100319003000b140760241c40500c4040110300c244a440c0c2c003032501c40004911006212900c81c070100ca210007a143d0302005099000344926480742428840d0000b648201d8002c107000b2b0482011403442c1c10400d40b0b03054540b140d90040d60740500710080042d0307098000c05034806003152003400254802d0718810342c0002c0480b50b41d2031411400710054405002c4d01e0094906014246000400440366102420003503030204203450121468400d00e06044988140f0480025555400045007402031490030150252111626400c4234400b2a812100c001a841400490301031043c50030040b06045040ca004240b40c4040c0e1110099603100790b00c26400070f40c0d100940d00c14082d0074416510416480d00c040c00032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 287147859 1250 287146609 287146627
    0xc030b0d0303090c09020f090108070e0d0b060409051509121204080318070b040e01090504021f050c060708010501110d0f05091c0c050a08030f070605040201050c07080606011202 78
    0x209808203038010149580d404505050221908503000142840d400541da604070741c0540131556040302c185140841c03800c0c0c002c2060130303004004000401c41c000d1304050100300e5546550102c284045c0031103030440e90b109149408200140204004040740d4003204600d410f110500d94988481c2244903030074020148904012a140410310940054019152680341c0c0c40303000311901410541c040000361482107a2000940a070440041e00c22030f082c00540e08071603030740c03540d00c1c406480f0101e400960011028114030442d002036011000c0610151820501785610300c00042e282c0f0360295402c0020a44450041006603030000420024205820107844a80a10b10f406007046a156105905000c000328844001c0c3c2c032016507641401e100807801d035140d02040e0500c8800d84100380607181c06011661004241c01c200001218071141240c0c10703042c6808681d0300c400f001008094000ca0401c0000c004030592203030b0810070080a09442d07800780100342031907c0050208610b03049a102c01d940140841c2e00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 287149109 1250 287147859 287147869
    0x6030201080c031f030321020c030702100c06021216110706111014010501020115030807020907030612050601170703030801030f020a0b04080106060f0305060928021602040c030b 78
    0x1c0c010145000440d12900e034281d030b51034004c20880808084200b03043c3c0c0013051680c0149a41e451401c4161001e90244801c040402a84500b0180509035481004410010700b00350714414845181850603005020280d0b607401c090360b2201010002074031f242014001c80c00ca001c0701040303100220381480f1348501c51050102ba00c032001c81c4201401c0c001c0381e042c8165038100078820400000b600301c03010451840c0300a81458910428021540103620300340401d1555902001154103483e049440e181c1011550360822406c138400414083c109503e49100140c4600154440b200d0944a40c01401c040d60400d0000d0784040c0c07410700004102c0e48040000c1021a80068640781540e42100c03501c0e03030300c40244c00403071b48004050340180030130000000e001a15203030651060b8140c1c0d02955410341d5140c01480120280c50303055802aa1041100340492078071801c0000c00c2402d608000820400f10420682490407030308041c0304501103508aa895204600d424810455002e0444c2001c00c1460030300c2001ca0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 287150359 1250 287149109 287149111
    0x4031104091112070801090501050f0c030708010b160212060402010e09010b070f08090d030c11030703030f0f020a0b09030703091505070305030a0b1504031a060603070f090b0d0b0a06030603020108 86
    0x5004070b03e40350f0b80072424002801000c0151000740c00078403080c011850424000c080491700741c04d0508484d804074000c0070700e400c104c1c1d000c1c00c4540e6400c040c90f401c2031410351560344542405043c4680c40013034500140c030380b8910314100b0448135014102c645840c0c00054941030f41e43c1c8807144100c0018006101c0f400311801550183da810034003100004082d40340481840c4910301805502c081c0c000c0724641010b5000851043c1c2a10604824003082d0b4100c080c1643e0321003900005022030025240b580180303210744c080c405000c000d48100c61800350503032140742400f00300f5100802070303800c001000b20602d50402d520900801108040381400f81c000e01000b0f103a4000d4102c004e00708000040420304140740c42d0418101a0310041c445242102c034030034080e513254400d100c01c542c00a854240710642264100c001c52240c0070107444a482d590300d900d0102c1e5401009241a01030001000001c1101c50807640502013054420b2000220780390700f0000c115480d803142e40a0002c16091000c1840181d900440c5a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 287151609 1250 287150359 287150393
    0x70c0b060d15090f1a0603120c06060405090309100f02010c090807030f08041503060e0c07020a0303050a03140a0510120309030609110402220f06210e060a020403110409 74
    0xe52142d41c1d01e011454825a80000f0b003852039651007090000002c071742131034000c04044084402c2003e0a04203100e003401080040b00964100c400000e2150905030001c5a10000001c103891030032030f00300006540d084008500c0f800142d21078910701d4003590244184c808a62150600102040c0750a150303030798030002400010f00c200000c858601c1004449420760b00605440701082042c8414120000d004150034440c0e2016070b003800010404c103010100840314a0341e0041e060b203489600b151403c0c0d40c0c6511a4620504050380c44507450001d00300310030243d01075200c904000c962800d140c1a00c0103038007510303040041300c8400180e000c00042e411401c41030489500203c00b1030300c134841c2c2c200004c001d01c021000903041400011100d50486222081038003490f00e01d9403c1c0c1346646c880ea03944140c07030300c58001c481c0417444040c0aa88a005482c1c100c2034601c9081001041c0400250071050400b0b4040d00d290b00c19507004681441001211500f451448030295410803110050381c0f81d502d10784c0d2a103502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 287152859 1250 287151609 287151611
    0xf0510080615011b03050306090c0711120c033a050d0b01030b060301080a060e0309030c01110708070e04060f020a050a0509010c05030313021e06071415070c0b060d15 73
    0x70380116405101d4032a01110581013000c1d0080355400d01038803a034400c0700e01601c1255107000103020214448250392040e030b0840ea001030340804080134086075030780089518109120399451200309a0741040300c02c4c2704d8840b03a481c44140c442e00c408191071032800c030256404502610020810281d5010044e40cdc2c0480b41c0d20001700e2213111500c0183d0040564042d1640c008600200105c1e02510019104200c5880f40d0310403c034241d000703483d1940703a00a41c1e101c03980c10b40000420105540c030401104120240600940b50b00329076805c01d03030386824080d9005003480b400507410402400707014441d020103034a48580a515150f92040002c0c690311440d0b815400744007010840344140e0b44100403115190761b004040344e80d242030060310041c04034000c0104904c80c2810002c1d54241150000c058a00b112001d010349080800e0344e924005a500c02c510010b100340724410002590301c95a80005014001d192514003254245051400f8031280091005001e5402981e1180000b00940710303400f00c100c3d203008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 287154109 1250 287152859 287152891
    0xe030702040b0d1e14161701090c0603110f04120210020d09050d03020a0c0e060f060405030a02121203010b0310080a0f03080a0f1d0705010f121e0f0f05100806 70
    0x42c2c1122000c5e107003e4021010b21803400c0c80f540d0700c42035031184400c0c2c8968910002102c041c0121460a0381c00d100c500411801e0302c008104110b50094100c2c0440e848250030103410040000705041168100750300c081548403012002c082942000d9200d00f41d4840303140302501a5550184000c0c08001d4503104071800351001d0411507050600c04c0c4448541e0030751055042d40c600396a41c0b240c040c40c69095034090b20462480140e0741d011b14084084404581c4081c2c09055a01115003c05c418180f0b840a1480c01d800386000c0440c00044020095028101c2c640d10750b0349038202110402d20f110540c0e0031919030360f40b00780c41280c0803407400b40d1000c59407545031400ca40d4030365500b901803010f00102114003044600f400f450b446049071050824007008002c108407102c5075903d00c011261031125405182c0441c02c407005c0c0142d840e81d04d800500d6800d24009004040b241d400001e80c1c200c8001104480400750f882600880c0da22181c001c05801208503401050160b0401c1c0035a0b8980c034019100d90301c00c0444003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 287155359 1250 287154109 287154113
    0xf030c021512091c12051e0a020703031d0a0615050409030905030d030b0625120309061a060d0911061201090e0d1b05010f0e030702040b0d1e 62
    0x8014401c0035021505415221001c107100e5810000c0259650000303030090907640742c1034521039200ca052021156590340c000810f0000c0003001400042c00b500034043c003508140a52049440489024070805800183c1c2d40d070032030078024103c3d410003805010242244481d12100140003411040f00c0f80c016600007402014941000e0086045070b0040350840c0c18403031781070b042c140c0100143c42115015426220407a140c1c541c22000c4030408a9280e505c6042840100b0380803040b01c070300b11301e500b04e02000c0003010901c0d503c0d1640181d8590100600081d05c5207800010000a03006007a50aa0b02c81c425552192007040000c41901650824a0f0820342e1004c0803810303c0305a0411410701c980c050200d543c3c8003511086171400090034000c0241da98100295010400e9002903060f0014806960340d1343c1205146208032441c0b1f181182c00e0b9155902c50041c081c03a070007a44513010700c1c5c079040c00040d507640029205202c141d444c09071946224500522084002c01d000c100148200c6081034000c8070140c03814 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 287156609 1250 287155359 287155369
    0x20105030630010b0a0303021e07030606150314040203030a0c0609230f0f0304180e060702010b01030606080c0405060307050f0703080a06150c060c050c0111090406060c0f030c02 78
    0x28002c8911401d198415503001c4945203202c0169000700c10700034070004904100740a07000b1194880100140d0007100c0e007001003002c1c090170070b842c820b05009403a0025a6600c81d0000d03524103070010f42d03071044a050510b00040e01807088001d40c43d491980ba4125103003a40000303440e0b018401e4804184100d042d281c20030052168855600d00c2c3d44500d524029001c0035481ca001c414881d00c9000080c41000442003110200041a400d420b202c1d1000b9484e00c5d0500540543c6036040d0340c0c0e40071000d500c60100c0342c2d00306da0902c88107105082d90340c00011066125000103090783c0040c2d0199051000c89404c1c0b119880b014012034003078600541d00183d582c4c40b804800c8801c1d1284200340c1411070000b040b030380201540050b406000e00204076007845115103d482c020040c640c00600c240100d1403100c04800080c00f10b0704600c00749135007405d041741040d1401e8880d070b0a459425030011148000024000707851324052040001401261810102d4144155502c0341c4110f412400a81032100f01ca111000715611 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 287157859 1250 287156609 287156629
    0xc01030218090903071a010e060f0402120f0a05150a03080a050f0d0603021008010e0402041a1002030c010e07030f1b030609050c090a0c09060e030708060103051b0301180201050306 79
    0x40540028803d2504003040ca850b0740004c80c084035001902445011421501144581039a5400c84007242c552600d03c00c102440809031082c98010b034083c00440c4000c41c002140341d1091a1040c501c5496107000007240084540041c82d0450b811890018411641c40d010242802d596019000c5a070b911400da40584090045400c46400e5000028078000c91390311503007101040781c2c03003034401d044a803580c0e14050300c07043c10074000c3d0a0038001c014001400f40c5090b0708030f50f4a496201c019000b06107625400f04403641d218a080001603171001031141c80000f001d124050401ca4003002800f801030640d5a1860044140d1501809000c8101c02d0003007103280b00341c00c050080d940701d07008020244561502030f8880740c5460320a4852180d8800098064400f80107105025103036903103c00242e0b051081c250f5084c0042104290940b00d0034038045800340c030030010745020b07502503001485900115203400b01448400d080343c1d80a6410140302454100f108140280c00f039909003012610307603072240003195403440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 287159109 1250 287157859 287157907
    0x319020714151e1905011511030901081f0f08010e070e070903030c030e1f08070215130501020408030d02130b0406050f03060f0d140c0d0b0f06030f01051f05010807020c010302 77
    0x120304030000030518020504100f00c519207848e01c803003c22200610305d469028211299012600340700000c3c0140c40000c0710741c052249a500a2444d0b02d46415100b0a206e4450300000207036035584071940107a8008108001c0103007c0312071903041614100744000e0015409100007014440c40728906e004141c001e80b0314612004001e400010300b03906110013071204074145200d88000c05d12140200d44158808100c120b50750481da1883e03001610f4900c0e226049429250081d074030740d582404003280e1080c00744020001080020310243c1c840c07200d8164140741c4109940180301500013004104441600901964a2034007202c40080d01e0b6940c040104407100034003002640e011540b0704001e401c01c4403411807400314651940482e142e00040c1d0080c840c1b80c111400000e401000014000380d05d030303000c0c03443c51580801d016055499404070040700754203442c0251406a9039214183d4241c000c500101c0d054001131009282003403090401c260701035282c40c00a441917041503000108441706182022000e2580341c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 287160359 1250 287159109 287159111
    0x3020f040e090a0309080c0f0f030705061305030c01050a080604090303090206071410091a04020414040f0314030c0d110910110d030b09010b0319020714151e19 70
    0x450300703290b03094849000400444c0031802042d000f240c24000042d03080c0d00d01c800544641004001003007003000d07103600001c007258184034044000c81c942c1c40f060040c201401c0c00070202d0501a0801c400c01d400c20442c0c640701c0341000014000b455816074801c0707050382c000c030080da000182e420040c04c0442c003900300040040d421503000100d9808201c58007100c1d622150300102a1550030340222192020b440b80c000c0040c2c1840183c0801c0311110400171201034101d48000c200007140907508480420602d800c40d01502c003a81d04041d4070051541120f03039941a0343c02c0b5003080c0e02c0c600c0c180e11345840900661803110310103607451588007a1800d140086480034140244030702c0c1401360a0600401e000d0204084800034050ba00b4802c1543d4004d000700741d040b900c000c19820307150b03091650061142d00010002800448035a504103109802440101119405011062400307100380d0750741d40c940820a190340d0040c03060034040001219020b0a00c2c4144651078010b1071843d1039801c0c10410384407031200b83c100b500d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 287161609 1250 287160359 287160361
    0x30902031b04090b27010c0203120c090901120c140a090c022b03060e1b0a12090f0308060d050d0c0203100606020a0b09010606020304050411160308010501030b04020906090103020f040e 81
    0x4144285d078440f5112111140800c920613012244d24241c5074990401c0c0096070085c003820b80c0f42801c680f8407650040c060240309041c120402d00080a0b11000c8c0d000e41110452001d006051212419564024020090005500d071209901240080500d0310820303c17002c0c1c1e1030340d902c13149510a000d0203402c1c1c0303003003041c45003808040c0d80381005041e010b81904000c40c0c9407540000311501d40d181154030440071364000180040c00341d0a0741d03005030f000400c038504211a40300e07118111800351148055540c005c03155064001c2c030a00c3d010780201d0303010f000f00744546044902c01001601c000354030041c449003840c294403201128808285080200218078401c2070404c0b4012130310540c00500a8000e82c003a140e010f1013600c0c3c15840508075582802607400607042000140300342e007040d401452991850418052821003c0c0c030000900003c3c946e8100c0004a041c0300402803983d00d0b016002d44135404640444c03900d24180001000e9104d2415003d042c1070700807403d032140c0000c04043da001004141100030031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 287162859 1250 287161609 287161621
    0x3030412030e19051e0303090108042d1202011b030c0302040b03090d09150e09070c0b040506060307080102040b0909040f020303040305030c1005131103031306030b0f01030902031b04090b 82
    0x10383c1c074a03070150b14060b00d00307000e940e400020001e191201c1a83c010f0007642c50100c000c0011a88420018003e44074080d2580d1201b40c0081d2002e500e12624030600401085180300d4900500c50b40c084141c0401168184042414010140c014036811604181400a40c0704481c080960185c003480d44400307400c00e000320812000300d42c04148801080e600b030361101d60b45038881c00500515821102c3c80d0001801c400036401d01800d155064a40200b03040c108190941d2095171401180d14048508441580081d0705004480c01d0030440e040c094003000000303508181c1040e01e102514010400c19a21410008004c2407c0c41101e404440040742c001e42500d03641c1d0f40b41c0c24107559982c0b1000e9103400c0c41c410701611001c0f0384601d208044c018038100b080d00300c6807252500d03102e094410900500e54980400c00c46124480c20b8010b43d54010180f03901d0200b60b0f03004000800c9500c40e110040346041c5800d01002c0001650041200f40b030b031000400b180b00f1900c0070380307000c94000c00e82d000c0003c0141c9002d50034408 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 287164109 1250 287162859 287162899
    0x150f03150a060554061804031106010e070c0b0613020c1c0e060301090207030e040218031002040e010608220305030a0b180a090809030a0f0317010503030412030e 71
    0x4640c01007894a100705001400e140200e00e886003281c22404c40b030300c4039140c18403040d000302c59003003040200994003c1ca0100c405100000064a044010441d00c0001d00d4840005003c483d0040ca401c0144481c0d61502000c00b601c41f400c04c0e10f009101516807000030b005951401446191a804100c00b1915004243d070426512000901d05500301c010200880800502c501c0402581403070180405040d079180400220103034000d11401c07010b03c2a280d458660302c1c0c0355032000d8400e058020000c1c5800c180c28409041c1006407400d00300c150540100428803c41c52000d80c468110361131490201d1050f81c4001211040c40241480604c020749200c29007814550f0001c090b5001c0d00c000d807001c000d292004000c0000782c48a0304040c0410b990518005801e40d05240d0241b2a210b001d038004a29000680001a0070600380107011220b843e803a82c1904140341e800300e13142801841355009140294100b10000b5a40c0c091449030101aa10380448a401c01d0b105900791284e4000c043e110b903403c4008030041c48 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 287165359 1250 287164109 287164159
    0x20c01141e0d050f0f0c0904020c150a0f06060c050d08270610080a11010807180f0e0f04110f061b0d0f09060c061503140303150f03150a0605 62
    0x1000320403100485d464895605880b400758900c0060300d41381151903414040130307400203409038009000e0a81d024180307402c00504513106100e503000004080d0101e1a11000712080d40c2c12400400542c803650b440051000035070020189028200001656a44503e18202104000860b0408070030095281d080400c00111240078540945000724215214542a0356076074910101401c6c100240d82d0742c1042d940545161604150203140052521008410351101d21501b6030000716080300e03020003009891083c0ca8a0f541015078192500b215003056140d18035502c0402044c94442c20352074807006150f40c7e94004441030303401c40e0000701e0042100c035006103032615207820724600440c158180da80f0f0410b1080c0c000205641040d02d800c40592060f40f1984000e011271801e0383e0f1188030340350002c00810f20031216514100c41000c0103650702e150030002d00c0d81000c0c00100c007130702072000c1c0c5e211140d8554022404040307280d03082c000d1003016556501c01d900504140d900464000c002c02c03044120740d0b11007030004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 287166609 1250 287165359 287165371
    0xa2318100c1e0f12060506180406091b030e0a0f0b0402090a050c0406050c010209060f130902090f0103090c0905130201080c0f070227100312020c01141e0d05 69
    0x15041c452a403441802d00b00030340c04058000074420a0050b408a809218141ea00350301d07000000408a03211030100c3c203668007409078141e00010242c12300409150a0055201401c402d260512444000340320440e42202c03444140000e15884080058084000b004100022500554114407000c000e0038502400d4105030350990280c04400c00140210149015070f600510000b8000c42c50315283c4441110b80740c000c03c2e6560100e5400b00300c3d2900356030703907040589100308450352105c1d03644225080045004d0041e40c4510051130040c0018001941c072588540740003842030a001c2843d1840f440c009454901c5904901e070032514200a0001c0070301ca6104a2007518800c4e03e4800807a155071009503000c0c000d0310712020295000708811030042c201000d01100c1e101c0d11243c280311140c60702c1075101400c01c04648100c1c00703803181c0b80100306126101c582c0303001038141400907182d20241800004c0001c0100d1500d125801e200065003401a26104216070003440143c8400383c48080071000e08014280130703141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 287167859 1250 287166609 287166617
    0x6020c010c0c110d0c0e01030b0f071b020f1207060f0e24091f050316030e100209030703050304031202160b042603030412080a2318100c 60
    0x1030840301e40c0610408100e40e9000f102100383c603001802089200381007401c040b11804010740000420300c204c18070160180d4895050407500c0e1401c44001462004000c001404108644081400c00c0d0004240142e000e03405a8001c1449036400700401c2c0000020204800a8402d1410024000c0c0d4840c0e8254841d50f015500d01c40100380c585c007002070728902c01c0341c0c690050b12085081104010a040106103606c0050049443e100b141c06d110000305201c01460400b182001007000b4503007400580070416401d09050070040c251401034406c0d603480c44489001c4480342c1c0018580016541000741500540d80441201d81d115168074000d40c1044400d0b2082016200304000c0c410224a0203a030315040d648603104003420146480010341c00d40075454400c020f0340c0f0340348108d10202d010900007140700f24083e0200700c0811001c0c40c8000d100100c010b1101d1907640ca08510404192840908116100c40b00f003800150741d100ca0045418075102550f15038918440c40003208410045500800704026160311 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 287169109 1250 287167859 287167871
    0x406080d0c06052d06010c0c0806010501020d03020307020d0c021311090a05090702030f09130606080412082418010e1807030f0308091f0905070902040f0302101b06020c01 75
    0x103401c90034440d4980d1380c03480250408000304020496000c41d41c800303014036201c00e60102a458502c840c5902d5004000340e0f8101800502055030104070507014030501e480e04600d189845007000b526a582d1022040c108881c00390400191b40d41d842e0700744090000300c40c041040c4001c51498a43c180d015080c5240a40f40c0c40c1c50020341450031200300e511480c40c9030084d61809440c1009202d042c2d1020720059440003144050541c0e1003c10302c24000680500d45450000b070074541464451144007001c40401c01101c0c4041080541e85986000c81032403468130341c8481d001d61640000c2c4e40202e00081c01c0300b0003103042c00000e00841c0c00644140600c0c081c0e40111901039894040c1d5032654041d0002034003540d0145a66000284075005859005820609642d4114000c0030300e440080d010260054480e5243c0c40d0a0080c490240103890080906140c01c41c5880d01d80b8100b0702042d610382c84060320400700c03c0342d00031010b80101401074040c030880b90507204c64074145c900b2100070740240340341c108250300e402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 287170359 1250 287169109 287169121
    0x1509010e0f06030105090709030c03030507030219020f01051303060e030306190b0307120b031c090501090f0303110f0708010609051e0f0a02041a070b09070b0304030305060406080d0c0605 82
    0x204600340007000241c4414039503800c100501880c0603002c0c0201c0200300c00000700102190b020740b1450302540c0710b40c0e509990ba000e50f0400070302c1d044614040c4000007d00300060380060750380302d00303500c9901003e0070442e8980c400300100c402e01690f5a030019040704d0a2030a01183c04601000441c4203400c121b416020342020401180c106480074080e50400b02c100b080802c24040c02013041500c0403001000100d84034443e000402d0515482d10145103c07440b581c1c0300b0310709060300300d8a050302400e02844c00d61040b51400d40a0210880c440c8809030030300c206110300f10742e024414480c10000c020441c040305e0302903030f44401c268000c100d644614038200e89000003103040880740560300901c2c292440f0b41421292501c2d84200704099010b03180090495081200040604c81c9203000b400c400200c0e0040d40e196140d0b170520540101c002003080c0c2044c0c2000c01e052000749046c90650781c04c99010706d4001413954458000c203001305a1604100004d1140b16881d1407015803101c1e25100751485110180201d0700d1b10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 287171609 1250 287170359 287170369
    0x11101150e0702163f0302010501091a1c05070f14010f09080a032a0606180902011b1a0408210c04050609041401080708060c07020109231509010e 64
    0x207401481017440440452500000461007844060801c14091440e10012540100e040000440e012800351b510313036004005600f00d03813040c148035a19220b1000c6054404d403000488141c1c0078032180c59031840322194081030110405c102c0c4042c01c41d240030303031548584078002d9003038002000300d12900055a100340c503068140725640c503038120f640301e000130040900555401e0fa9075001111040550840000d0130660400e240d1078551241340c0158800201d584c18444074460050401541c4c0e02d8450070034280f034005036440324102031000210321401d01c03d5045445c10f80016500d150000e01d00c400100280701c1400301c00c100821034118012a101c51035010003102005403d0b08458580510106000820990401000a101e40000248002030266138020f41000e1020280c0110f40d5070b17481404207004c400c1041003003a03040301e03032454000e003401002d80c0000c02e800c0b594007850b6140b0101244290040c04143c006822250000b0700c1420020100b0302910410740104502d940051585110340e2810300341 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 287172859 1250 287171609 287171653
    0x4030b070c0b1303021507030603060e3c030409140f060303030a09060213060f1d0d02060702011e03050a0c05040e0408031803070503030f150f011101150e0702 70
    0x8800341d07030103a50399040100407000d118003c042e02980520000954a420450b60f0b103841f50070780da1400a80c0e14217504103402140c4000c3c0e840c402540c807401e10041c50007120105983c141e521003580c50600c0c44054800191415044210395481c88081404501010385411602c8450961030b400e44040e0f8400010880d0070409403080ca80607082040850943c0c0b8454205400941c01508003601e040718200044003840c5c074603405000012015000c100003241d000c030190401d8080c00e00300012007845000001c002c6109410028400c080000b071860071640200380c400c2050003c2c07100d040c0031002160000d805440120b07416150503192034140d821407401041501c0c151424014154001d580d0780ea100442503001034400000c80584980c0e000c080101040204000f0b4442c0700030796240d007030005907030070b0140014002e100d404181c0c1660b26141e80f41c445284013002024a0b240030403010800d00f15004103d0041075101c808907000b8080f55041818807040c0c010001903084900483d002c00e46071008000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 287174109 1250 287172859 287172863
    0x518010b0a260601030f121706041d101e0911240406090e0c0301034d0a0509060307090c17330d061503140304030b070c 53
    0x2005400070302c04100c20702c24504101440d4802480c2010310b502d0110710f03105003640204d80b00074000454604210883c2c031841c001301603a0500a40c800710075660320b207803001e005004c84c0c080c56a5450300c02e02c0c0c000e200c00c0c034601c02076903400b0345034116003c50441000d8559842807403042c1c1e101c1185054040301a00c100040c2c02d8200540b40d441904490822030641d00760811900038200b04c0070b0183c45020010b0051000b03090301d490ba1550b10780b610820304442000101141c400c0e0f1000d00040000c80c03a48094800410031244940c240701506101801d00784142c0380315040103074141c01c1e0031084122031090351958200215401c11803190b448080042e0700d00d0888001d034140e040365000b042600f4864020051014003420300e00c0e407445810441400c400401c46a41500340c0d00010a94900142c0041d0300920000c014a6101502240310116546003540c02004020564403045440e1b0350b10429512800f640c2d00900212012a03400d11003540e0340c22501059840f000540d01043c0360a0081c000c4041c841d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 287175359 1250 287174109 287174119
    0x30f031224050603060112090f05013201350601081b0f0109120512070303050105100c08041404021c141e0f0606130f18020c060c0a120608010518010b 66
    0x6031101f81c40c40054404544101d0f0381040040714480012002c6c0070b0045840400410b81310999000c01c140040ca6105002d0020000810401400300d403c402ca1502c19103200c0075050a0384504410003280c44010101a841241c0116400407500c1107002c2801c5001c10100c001540ca22403080d41049940406100c0341d42c08284040d00401021102d0182c1000703490044064800c403800d800303111201c980c400d03001280042c0c0d80e00c0c0140310916014581003a10700080c54a89000c19965403525064807417809070325890014087d95180701d6469804840c80040030b2608906200e10f40a000300140107241c01c1ea19107800010700003800c40010000040758041c40c0d030b03155490b903154103403207254107480a0f00c3d5075040041000b1028001d4000f038501c0000305404520706111a140c0b0b4040615807061703850700d100c103a004010b6000c0e11900010314540080d1a116420f0341c44401403401e0790014000c0031104c064034241140012560f4065004504c155107840b215011250340b580c1c860300306c801c1404600c2d806 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 287176609 1250 287175359 287175377
    0x20303060f0f0a080d261603020d15090912020d120f0207080c0a0c060314180a150b0103060902040308070b04081b030403050f16030f0312240506030601 67
    0x81e103800380010101000103002d0f8107100361100e07407075403c00060010040c0810003480018101c0c5150519043c840842c0300f10464031400c1c4038034500407501d41c0402650416402040b6407080440d1580401c20401540900c1e014466807a410400074141c0e4040548044100c091803410050012880002e981920341d00c1b50321440c00351150000502c108400c10040d50b0b800e0040ca0700040e0150002d0403a036034040014010784600d85000004401c454100704109410028150002d030840d51515820200080f180c0700b000111130303100c40ca00344190740060014060380c42501140241ca81c4501002ca0003aa418003855880750309800580c425440002d10320744040180c880418074002034035403c240701e5100d0a1800015255a00000110445110ba2900b00140400421204026460200c40c041020303101b4030009411450151391301e03200c082c00b51000590f210307042520455200611b01d40c000001c010703114400128000c100c000100490f0600c811820100702894510309403072003040142c0d80c101700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 287177859 1250 287176609 287176639
    0xe070c080708040f0305010e0106061b020f0312030f0403090e040f080a030b0a06030e150f070c060e0d090303020f0a110f04020912011e02030f011203180609090c02030306 75
    0xd0354807801041c0c42d03903881404086000011111600c00030f501860020440c510b0041c900f078211015948a40d041c0042200d01c1c081000283d040201c44540481d5160700105046011030704041c045040d90315540800010000500c5822000c41e000b103003e6500c44c084240c81d9454000891401e031005040300310004290300c0001c1901d0000c007030505107482c000c281000140702064202895800207004641c640100d070b00300c0320040082000006002055044038100115240000100079280f507040028901076003083c804550040f8454004003c12100c40c02c0748004010010b801a02040b00107004541440c813841034001688110a5040500c40c0341b04600d40d010400d403a0030804400e85c0080d0280000315056480220016808a1800020442c08200c80014030603c05031880082968414014000c200031080544c1c0d0650b040d140d0024400c034000d081c02c2e140ba030312502c6131401c80100c42e80c02288566014010000320340c80701c1030030b010a8807010f101b0b0b41c0700d0004580c01c1d9002041c5261440c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 287179109 1250 287177859 287177873
    0x90f0d12090201020f0601030303050a0b0d0804030f0309120c030b060105071101030b0f03060901020c010c230904060905190f1a15040e070302030907050901180f060f1409010e070c 79
    0x107005407050040b107003414990300b9500e0074220709a0056000c44d564900b00404820309008405503c5030480e20071100c0c0e011682d4900309800b542c04043c2c810150000e13880d04041c003e42c404800b82c0f50282107100050306a06d0655090026400210b071501c9885000c145c840d401202034603685607011a40b131082e298401c00440040c24001d0f80113500502080050101c0d0314240b11241c090712212001582d240880d0003541d003513600300304040c0100458444038800803c0004603003122244588a1039598410060014010741125000300c03a80d01d02e004203001d800000940a00103902c0c803003000340700c071241d5101c00408440d40d100801e882c0c560388428807001341c50050301c0300d0122034992048505040d142c0c030003030b10f480008562407800700b41e001081c42640d4200b080064020101221080750941c10711944140015018050510040d1100c07014003405880390003601c0600600d591350002c10342e03140e00d00c541705040c06140500402c07030200040762540b501040c962141c1c185468000304200d050b60f80d04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 287180359 1250 287179109 287179121
    0x50705010e0604032420180306010302010c17070218071409030d030e0a0605090a1a1b130b13061101020c070e04080c0a0c05010206090c030c010f050c01050f090f0d12 73
    0x113461556035400d000301c6ea5114031101081100448000303480c2d034100c10101900007080c0c0b03250ba200341d01c80801040180e0b880768085081e1540101c00e490071950040504041c0d01401c40000d5000c3c0001000c0254103108568070f900c10080c6948000c8002006020300446100d03440400350550482402400e00d00c0c0241c100c0c91300c1d01c00034800c440041d14241c035442c04891041d109842d440d00106208410700003080002d100800c0c0485074000f640c18042c88a0100b5404009200140c99021071000049180c04808100034007410018983d039813944010700000039640d0041e03001040c10080d1120b9110414400c0c0d9100701072500c01810102d04007003135155210b20041c82110a0074041002c4002460180300d03000103030344a850314404803800c0400180c00c260008094805560000007922800d0340c002861201c50b0000303003494aa00304900c482100c0c1442140650022076003040305020088005440d2548252410303c2034444030f82c07900d0046607e6010168503100020014904441001c0285e4801c0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 287181609 1250 287180359 287180423
    0xa0c0206120c03061e090a0908130905100803040305191b06030b13090b0c0904060e090f0129060d14090631120504050d050705010e060403 61
    0x960601c0203049051030582000c84481c6240e00303003c42800b0380ca040038102d403401d102042420402c2500b00e030703011814103c8000d1114001c207480d00020018048403004030b40070704550010500c40241c6507039080d8003609041e030741311050b0503411000207060140030007502c090700d03401406888000c000c1c589480490280d0507068070070703035928070000c0c200c111040c0c001402440182c41c080b0b07070761354500e040014000420881d83e08880c1041c029800140144030520303070001105841c0c644454001c800324004000c10b801000005002e40c1c01e1100c410800984500d100040c1c0000b4442c28881202c402d82940a13119403d40d0004c0340c45503030001d8070f045030260198034480700001982145500100108520a0b00d000726030741c001e801404060491442410911941c0e000c059803042c2070356600744405012100050710041c2e5480c21490110310542c1110700400004003400c513154914107155440340c00c144191804249034031507604c0e050402c1002d4404030780d0068140d0683c60b40203407004200300b1840040f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 287182859 1250 287181609 287181619
    0x7080f0c03130e0106090e16121d060415021201170c04020d02070b0105100203340312050a0c210f020d02070519050a030516050304061d04110a0c02 65
    0x600c0d07982c0b840081610040031280e1000340780b5490700c00c1c05440c90344181c02003000301803d40204000c0b0111020210507822183c5400748400d03041da0080d4001b0724840d030014030003504804011710b842400040042c080d500810f0031880c100c0041d4106001ca2240528802030701352000c00421406040e07454410a040f1103c3c1034403980f110280000d4200e074003034040c8901c4c0031350102da541d00b40900c40200901400c0103407081000c9983c81080a5540d00401d050301900c01f060190714144c14450000300c00140c1400c00303000c0349000c1d90703140141214161501c200307001480c004c00110040c0a9001300c0d0410821a11105025443c1082e45080034040510034010300e51142101c80c8440268801000240c540a10040e112000d0b0b1404905125200c0c0034484460000c25886020807c00708a0340400341c0d1500304541c1ea21141c2e04d120802c100300c0700029200380408600054010b030407440d202d015645a59010800c1a800d008100480b072010010030503108091007050456809024041c001d1400180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 287184109 1250 287182859 287182867
    0x1103040902131503060503030f1c14040312020a0801030201080c070b0916050a030b06061c06030501020a0806190612060b180f1503041101170406090201020f0307080f0c03 75
    0x2040c8090741c0c030030030b22202c82000d006800c0100307004142419014040625050000c50b14290002e5528055520408200e500026100741c0100d1360f41e440c0360301c2c80e0805805000d5070b00c0d00c810401b44002c0c106d8090740460b085407200c2c1c0700d05e0002c0c030032160707808815201c00055908580045030030039070080034440501820442140482e90030160244500182c000400401d49060b2101092180a41c040d5002e220804c20510000d03004001c11584200d01796031054586614140085026103000010200149004c1011007806011740041450001030340b1114566101c10003800404501040032000503030b00101c05203c018410043c2c95507615031150b01003101074030340f44840129070001400b5001012240d8401e449410050301c81c80400070100d414100c281c5002c05410200d22004100806400010790343d03400e503078041c21411f1204900640003204525043c50b240c0300800b42c26000340d001d03104205541e2050314001040303c1d40158001d40040c140301e040495a005508100e0b882041804140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 287185359 1250 287184109 287184119
    0x10605030c160f02100c0809040506010903120201150f03021311041d160801080304030f0204201806030925120c140d080f0a230a030e150403110304 65
    0xb00400a514090b088001c074009007807040024910340c01d82020180100d50400070007013402a02926031030901960042220756519004035102101a04010308600c00b422110b0f8516905500007c180c0340b014046101450303d4590007000001c161100039032090600500100c00186078120310b11b4100c104d8201401d00e0b4031803550820740343c81c1c41100503000309c044007004200e0860050f0400825041e0600c51f03802d5041c0714115450744a0360102400354000c011942c0b086490b00d03448000441c0e4582e4411407041800d49504041b0703800051441e000d27100c21250210306107000c1003140d000d4260400100308124004003214004e000c100f001250407461400c00040d5100a5411101900d20038003e2900480c04c12040c1d1400d210400c4440b03008201c044901400034040f8401c96101604c40350203e929051070140072a002c1d65407213044000360110203445499210741d02c02420111120351024401c1c40d45a103045540c40c440d41d07203d8000d491850b404640072038050451408a81680390030f8a00c7d280d210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 287186609 1250 287185359 287185387
    0x60a050c190c020d0206300115080c0d020f07021e0109090b030a0c080f0714010801090504050f07030819023403050a0309090509030310300507090506060f03010605030c 74
    0x7c1403192010f40d50b4101e215000440b84107140b80780e491001c0f84051203506203042401c4031000481e170f240501c0042400300d4041309003102501e000d4001300109544d1a070b50034503640751a40200f04203e000d090300c0380c00300342d2411f0841401811807006035250390909140c4501c400261070100e05560300350007460012404942d80d02030103c00343c01044020101100310907030a038608440b66104080d2800101241e02c003d80e40120828112451414003055a880e2803c0650502c4105007104503c0c0c42034000001c00c001400e00642003000c40b480321080100d00303180050340c80704502c052100c0858810302e202c2280078107a02e01c0940030b1034070115447e05241c40780e03505840d0584100094010035800c040400c40e1201ca402119803290f8403902940c21030402d204c100c2c42d400040c0c003030342503031400450680c0303645254801030b0100160404901d169951803420140d03140e5805000e80c241040c1010300213416070418004a606d00085107124170700c1e581c6002c0c0215000c3d0000740407482d19000400c01c01d031541c2e400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 287187859 1250 287186609 287186617
    0x30519090507030b01121e02040f090f020103051609031502040302062101090b09040b040201110a0305031501020703050d050901021504060b0f030111220b040305060a050c190c020d0206 81
    0x400c1e0014030406003035040c0703070f9800c0b441644450a041c145541e07801c00505502000e00d0700400c04038911100400303a01c00580a0191345821b001494074107034002e01444200c180001e2003038003e80301000700d51110400d58500340060020302001c202d804904000140c45215010309400c0b4055006081544030390010324140d000d0208503092107000d440824440d005c840c0502e00400a040c02040401020b0000c11030b48840204040c1c02010004005015a401200d00c0c0480704600c200380c40c1450303110719000c0c0c0960000e6540003541080384c001c28010754000035400090701d4000b0001c02c41308503241011103196003e240407074118019003004003c3d00c0c0c54036080328042d61207020003280c0d02c074441007070040720302c3c904444603c240c0c14807a1b042c020b40d2403401140c880020340c001000e01061105100742c0001c0c440d074400300c040000040c00009106002c10f10500940840109000d80d03203412440d402140196440d100c0c06a1010301c0200d02d45001c0d290340e281c00351024100880c42000c0d50009036203500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 287189109 1250 287187859 287187863
    0x13020c0601082407050d1e020714060705040b0d0b04020703050403120c080d020a03110d060806090703020307170f070b0d060b0304080d050402011710060905010f0f03051909 76
    0x110031401406804801c2c0300c0d0565036043d4406601d05118694018001043e001c0c252000f44280000d030706001014507000082060003a41c500501400c0200300c8100030362000310140d6500e2081c500c60040010080354041c0640615540d480c1400e0a103040020a03601131030070b01031007030750341c40203003156440301d00151140c80e00a46a090b200d51441c28000305140c0d1b118198410000b150240f000010840350030b40d02ca0508807000140c80d821184400d40041000c000f08074546d500106101041a4840d044541034030b201c0400c0d91129180c1c4c0c01895901c1c040742c0002903164200c10300034000881c0c41540942d41600312030444580c801c841b080d07142404c41355000740511450000b8200314014250040800611344071501c20710314034154071001400d01855405000c1503481d032011074156072044010120701003203c1880030b000d08040e03038036040e0b005103486132601050200500003610741c024842d040440209454141c500001050100d000b000c00070040085c400380403940d810307400c5c028403455040c94 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 287190359 1250 287189109 287189113
    0x1020307331518090c030807020f240702040b18090601050a030f060e12030a02040609090b0f04200d021201080d0c030c081902011d061006050913020c 66
    0x303400d40c116034092030024140751403150910700e10041c00382c100905031044950000600500b90a00e22a12000c2c004950020f08a0f0b1082c0340b010040c00100c00c014480c0a10031a9100740b50740071034050100741a0790708900181221340807003200524004100410110748010f0000600542c628001684180340031300213056488844108102900c0800c10035000d001d0840b910640d0360f1441da00e000803414100d4000303041d81d4070b40018850001040120a41880d0442000303070b104e140c03442e2058001c0d0484d104510015000c3e00700010108043d1045020800014101c0040184003000f0302024140031424000d095005070719891a001c0f0110184c00340510175080560b0700c0440b40640c6c0040c40060300600c0c03041c1c1022110959068010f254554031070340c1410481c0b001c51140c10301c8007190240420b04000050b41e154901c054540c1940600080207540031140041068445180e6030f6050440d90001215910315081c40541c0c001d40207081e852200402c2e1005101d0348101b25404d0340c0040712416103603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 287191609 1250 287190359 287190413
    0xf03050309013b010b040e0d0e06040302151809130201030b1005190504033c150b030c06070302010b0102060f0903160201050d050c0d0f0506060307050901020307 71
    0x1007028018801d00f9941076543e000c2c050004580c09280c00040207940241a010412101c4101020b412050020f50b00074030400201c030704198000c0d01c40382614010000075044800840262500700c040c0c406403034020301682201c9202e903a18500d11780c032035084004880902c01501c03a1540d03030490326512411580400000a21840c400982a01c0071540c0c114030401c003030401c402e00991f0040660f546259040082e0400718041e1105440c036100350342028002d2446002002030442e581c4586c141c2c0c143d43c00c0c1c5051010203100050301c0080c03694070001040c0e21885006082e00d203141340c02004000c00000d0580d8a0500ca55000808036440300c101180540d442d41c0b4007912940c0c050010b40d5000010312048500c41c50510401074880c40795454000000e1381d0352100c2015a441001950780070f404080c8c0400050400310159101e68200868804880e818285005003007285405041d000d030b94040d0601c0c0c15501d410406880c9500301d901c1c00c2e070441c40103210560104011142c07810550310201c5000f003603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 287192859 1250 287191609 287191621
    0x904060b040b03010504050a0803060d0f0302060f07020c0f150d05251701030201140f030f090607090e011224050910050f041101121e0606090503060417070f030503 72
    0x80c0c95946410b80e1090745000c00300130208002081c0c80c01d1880d400802151b0300e5079200300240403c4090304024002014865402c010150001200b07805483c142c00b151b5410360b02e2010407130366003821603c016045078402000200ca400d111145180e0386454030b10050503d040c0d03103c96022913200f180c5041c480ca01c008080510920050722a58882d0f40b50304e0140710340110310f50103e420120600c4020304002e840c1c107031103000281135000e5810105070038242d541d490510007005035803a08180c60404882c0101c2c004581c0d803034002e0080380304907070303d21324540c00c1c6c0d0b841e2501e02e00d84e44160700c4040d40d0310303160080c5602d1000c2c4002b115170240107a225000500307040c8240c603240386c40030702403512280320b2a050030310803500035040300c03964000da0010401e03140002400048600c05e24500b01260f0a80c1044042c50070511054004044091505c0c0304020b015030b05d010484041c0c10601c01d0f107405801200104002c107035601010000036031000020752400d0708641d101001c000e245003083d0f00007034000c014440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 287194109 1250 287192859 287192861
    0x815180f1f02040f14030a020d050c0916210905010903050403060b0a03020a090b01030e06011401080f10151404150809070f0b0d0e0f0c0a150203070204020c0c0904060b04 75
    0x14005204507002c5082909000c524000d04080b402005078440301004042e080d0381d4200070071041c140d0702409c100c8400c070813440c0c041d41e100d920700c24140c031030120030000903400050b040f51028542140d590b541d0207200b0700000a28441c0000c00c11080142d05c444046010840900490540501c650303941ca9030380d0b1460a0100485109002c1544195003a0354200003685d20000600190340040341c000913010b44540040c0d0081c56500b210344802c1c02401d000140251102c00c07255900007081c0c032070004d2503686907050f84050170308458001980403c41d90a0143d05d800c041c802d52848198200f1191104c20110050041c2d08a548038050b40d8102d01c07050031046a11480320764004060b10010300145042c01814000a8014003a4907414130010030484a420f2954000e40c605104040603205900c000003041911041050007480c040c5409410004207443c1e00da0a0281c0244503501460400100e642044040d500444007001688a80c0a010009685120f100c41c00f0714071880340003072140d00c10340c2408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 287195359 1250 287194109 287194153
    0x21507030b0a09050a090c0b0a0201060806090d0c0305040b0309031c021c0b010933050c060c07030309050d020703060c020705090f09030f121f0815180f 67
    0x800d42041240d182035140d0208810903105145808a0250b503282e030044002d10041d4000361800c200c440300001c1d120700100003817640d89a80e034028480c1030b40b02c1f0307000b9903100015604d802007a8800c180c5040b5603481a501500114400d00e000b07450030780d45024402040d08242e0700e00495410004802d5030302c00f07052019464007507a00000b9401d090480c07481541c10702e002c01d49440d00316103841c58494542c1c4a200144041c2002c0c800c500203142040e1011a40394108a000041d01c06031128114119400759090b82c2c001d40030707040101025074881d07440104075042440100c042c0741c2c4580c01400068000d0080801c0c150040c0d000303102d62440c60030302070207446002c40c0010a43d00001c4060220b80c03034024420b5846008480216003503190a00c41b0b510314800c07030b00f84074500700000c5552002110344030300b05801840c959105401068008010302c40c88a00c0384200314075540310024154101c0035005069910901000e010072034681039400c0d06050420000c140301c07154100680000b0000d0040e0021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 287196609 1250 287195359 287195371
    0xe0601020f031201301b150801030203060c0c0703080903010906240611030a031806050405030318011802040506040e0f070f0f141201020408030a05040815071d030106050607030215 79
    0x10003000040922042c0c07200721004050a400d40309683c50650340503c440300d00040c40046180c0e48158021780340201031600a0002f207209001d048040b80380c0380780d80d00a41c1d5131090181c01030000319146070f030380c19219802640100e8055484418402c04a0014401d10103840d04010400e4402c030b1101100c54200c41f4141c000c4003d1048081210015440c00426901c00e250607045c0015030703585007201c002500e00e11400040145041004000c1040004409540035518070901d086201450454440c01c1e680c0d8100c400e0201d40c4180c1c0072901600c0e03d50043d80d0041c9024000180c044220b5054608242404c8000c00c0241d024840411164804210a80040c480004041c080b2402c0c411162504941215020b01c40c201002100701c441034203604a8008140100840396620074404004d01203070424803030322402d03004080c030620005074100d056610400390f03079403001c4408807030460803505051120926a00356503541c4010540d80c880703500410b640d6000f90020103160380d080d11044a800402050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 287197859 1250 287196609 287196659
    0x2060408180d05030a0504150e030a03080c0705150114061317070b030f040309060c0c06081807140f0a15030f0b1012060503070b040e0601020f031201 66
    0x204000300d81000c0990308607030264000c0080382561400000d4612014000203851808001041000681c108005000700c40c040a2403a010103503200d02510300d500d02038801074041d0046a0001d0000348109846070b84100c02c18145400c000c1c46840c3d00c1c1c64a10b002c0703c0ca024001c0180b00520501c02d1044503901200d40c2150001d2510b1402807503a4018001d511490f03103080b040109000c0f9a0106200600c098451905c149407a8508031116203c0464152402d41c0407404030074010400d0340c070034108401e03980c4d0003840c50100c25103000b4040b9100000207188203c00880011300007220a8103114420003840c01044039481da1410000304040a203000040368441c0340c084e541000b001e503002828000c1c000c81c50400295401d1080750603400b504c140310f032007980b00d45850348051002d0740013494a0780444007901c003001342e1a10381090682d903540ba0f024048414506000c00c110040020741d40d50f43c422818415070301c1200001d00d500e442d50300401e5480803403059810041c040c080700380b96040c81940182d11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 287199109 1250 287197859 287197861
    0x109060f05151605100b0118061e090f1202040b03030c120a0e090c0a02010c02031c09060b0303040b0d0c02030702090a020a02070503100c090b0403030e010c03020a0204021204120206 80
    0x10010306030a81000740160300c81c0d00400c400b1042c0b60780b002e01d050519013003030594404040300c800301002440d01d0440c090201e041070040c089039441207c4664150b5446496080c00c00d40d4865841c102c1114001d44001001000000420300308258100c10004000c101c001c2c12074462a031040006030b51200c101039000368014018240807010018950a44d40c0341020000c0e61100d0300602150f14407044440990040c29041c14044100f900800616034040c81d54004c0140e500c00b9082280c032031050965400c0c1200701215804000c030f0256200c122070f98801d20000512201201c04a070860300035520054041c0d02c00704091201d681c090140e407001c1001c510145152082940c001416004043e1000b4403141d404030b49a0f0b8440d008118074005002d00804a600300c410074128003015105180c1e0000014400b60800203003100d43c2d40660302600d074183c481c1c040c21642c0318011140c41c0d03224181981148102051000542c940e0710091000b945114402002d5240c01c6c1071100008156031442411588490 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 287200359 1250 287199109 287199119
    0x1203070803040b0a0207050d05030403030b0108071d010c06050112030f081306050411150307030b01090308070b07091a040e0619090e01020d0f0b03010b010507050a0b0622050109060f 80
    0x5040302d902c50b5210422a00c981c41340c100307036002030003030300b170020400e10902e200341015030f80120146110f2482981c0510609546a00448082c1025074605001c01c1c01011180c021003518004144211018034200e0005141030b00da0000f602d00c00e80c0840f81106200c8684014103511051f41c00e000141402c6c01c50381828042081c90380600c01c58000352081e940d84000ca010800d0790080c1c0c800240009100d080780d48075035241588030f80d00541f904e0000c2450034038a6416540034900e0401143d0b0406246400d0140c56210b032044130000403c81420000381800110300c407180c4224001000c100c0e9518551580e090101c540414500034101078810080682805034440c007490308102511503005003ca8aa0750134022580640582c0082130305c0181003280d00ca240c0304103039026480c0e20008400030b00410089200550340c40c49030300000780c55500905514808902044131503074000700c004e000074107c0d021000007040c3d00102840b000040039280c4004110100c500e02a0310043c0c488000d1400c102c510300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 287201609 1250 287200359 287200373
    0xc100912080f13031101020a090f1a03040605130b040503120a020306060316050c0316020418080d052203080709051903200a17070e070906030e1c0905120307 69
    0x43c916102640032440110030184240d00d107091849186000355210003600078080c00c0380d00345000b030a04082c075400c1c0004001c4080d45450340c003415100d281903c0d58440d901c0d14806010020110b6699040d82e210000004002406041c031460282028640b604c0c940c100849039990003421700000c95005000f80185aa105022250040d03003150036418211090714007a5054019014020640d0102081032042c5004245113150080c1c400c4600300a240c441e219550240c401d0780300054103101c420f00c0044005074195100e69007040281000c0e00010024480032842c9060b1060120000344544040c81605500480c2401c00381030101c52400c00302c8400800c49071200028400502840080301020328058051440c4c01100c00740030344034040c91078440310030742c0031280c0c00040030700d041c400e00d440080d0500c060724506000d841165600f20b03415103002011400b5200c00c5d54442028002e4813448103001100c000308068410561b10b404500518081c100900300800d5120a04103400c204030b008002043c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 287202859 1250 287201609 287201611
    0xb100e06060904060e0901022a0c060d090203100903020d0806091303050903010e070f120b010e09010b0d0b15060301031a091207060204050a060509030a020609060c100912080f 77
    0x50358142c0d15001c4a0000a002d4429940b192010084240c10b01062800640003090442200400d05049618007803049100d5400c503d00030880d9004102e985d51245411300003021985c0d4014170110307412185400103400c2104040035400c040e03aa81c1d40c00800c064041c8400c1d6a24011810410b99928040020841495004040c4210180d0f000244801c05001c0c1702901d9480710068000c014809012041d5503842109000303014044030512000100d030307048c20412941082d030000768800d44d0b0b481c2203401e00705190050f00c2c0c88002e5488011500040e00c6042c034250f062401140c04001030300380790b0500d4408030100301350343d40248000c000510105240742c00c81c42448900461002040d80c80b00215424111307135071001000a90005609024044e06d60082c10a48200301c540090702c0c2d50780d10040d01c8500c12000d201340c1641212070480090b244c803901500c2c031514080c1209242c240d13540060360030604501040d001c41540c03940f2520510080d031403072084069090404a110f810320202031020004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 287204109 1250 287202859 287202871
    0xc1e0306020a020f010501030f0201170c07020d0c03050d17160203070f050a05060c0a02010f090203190606051201020318010b030634050306090a06050a0909021504030f0b100e 77
    0x140000396255020303c01c01c1060702c104000002045076507102d16107119940c001e203901764002040d010481e140d9010382e81a00b4002d0303254003603c600d424141e50034818203148484d0282d0703002120b2440000842c500f44820000d006007039036840500300c0c01d44090302c000c41d000703800c4807620000b00c1000210316030000100c411558000f5402c148920342ca1400d0f502c0c005003090004c1c0940205018044104460307400f6242d90212900244010a11030440d81d00b21025090301039403640c0480354016004540303098038900e15000d60b4010618545072030114088005100000c41c0681d400010001581d905801800788192540000c1c4103404030080001d99800000d400d907564460746048000401200f9034804520694000340f40003010708105015001d50000c4450324054034402d40080c0540006103d100f0607280c4c014503030401c00c0d081144200083c2550301c41207800a58003003645240380b0480307000d00010b40c450307110000340b8100392400c1c01c19136030040e00c0541144900b0200380140580b5200c0300b64884 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 287205359 1250 287204109 287204111
    0xc0201050c01021e03090705030111090d05100e150f010b120903090904030c020103050603060108250f030b060a09020306180a02070f1214040311091902030903070c1e0306 75
    0x5540207015500a1180a840c03482410076698044c41c0760707140102451058120405a0705002d40e620107043c00e0300c000f140050081081041100d41610f029031107010b249000310111000144039020400c100c8010070700450850788000b8142005040040c0215802400c0981074062075240c0001c0b16480e00800c5500102007002c440080c0e030300c010410a8400540000345000c1c001e043c03600300030b401d40c1c0c41e00c103080c2e0010b410400010b0300341c01d001a0080c121012000103009040348103640003aa003030030683c030103010340c1c0440e0f000800c050f010b00341102440c041c849245c100c0c140141000b48840c42030380710003c100c0c010701c1003201c550b880d10710595400816070b9110420b6501c52045200900c02c0c10305c010b02c040e010001c0e481c2800250010455070701c1481d00c0791540c0510404c0f14800078002d610004003205c0360704501140c1802d10700001600480d00c1d0050020715101107402c030059070400c80795509036603c08103101b41070140780c0324020010041d80c07240f482d86440c203025411181c84903000c06004c103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 287206609 1250 287205359 287205367
    0x81006140306151c1413030206180a021f110a050d0807030f050414060601020307081e0405090117100204030506070c0c08030a091a030f152d1509010c020105 69
    0x41103000440380403081caa404c8002c000c000303202d9200100400f4030f0342081c00c2c14680006140031403c586140220360103800403c0ca5907608000c004a40b800c14400d0252401180d08040040e1100880a400310006d968490b10f507a09100c0010050340003a01291110b03403001035560f02180b8041095451241d407440c1c074801942d205541034018000010741601c0300d9182208000502401c1000c0c5000b4059040076204591503501c01243e99000e00c05c0d01070144001080700b2036074401c020101d01b54070010a52a00d080690f40c07800150900c000364081a04624a040705580007841400202e001025400007103040c070303066462303280c0d903102c00500074028441007c06a1b801d010341640d50100504003001126514031039502c00414840503072140c54100060343c420046281c42e0203040c0d910800aa900d0361071542d0f910184c119945900034841600541078220720800c216803440b07010007071500d5020030040000d01205208004481275200701d40100e00b80222130b166030707003e2403240d40150240b80468035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 287207859 1250 287206609 287206639
    0x8030403021903050c010b060301050a0e040609080307020f06100b0301090c02070b04080709110304050c0607031815020c030706050406050c190614090307020307180f0c081006140306 80
    0xa400c1d8980e00c0118205407807592001003640c040014860711201d1740080c401c95402c001846a180001c0c01001c0d07024000b02428004000c04129507540117000354008180000181ca03001e03a658001e80300344c0010b8008040c00e04d00040c04100840d00080501d00481c0040d03c0c2089244280c0418040c04054030344038220f00381014420007140004c1d00e645401c0507039440c2d580190360b903078900501c6003e9101d03050214400d02a0031843c292032060b50400060480402401d042051a510040c4105c09110400500351083c3d072002d0080c00180c848150405405441002c0103450400302c0080184281e00000c8280400350b40002524119400341c100651114280c0c0e00b9a400c10a900c05503001507080c1a041409100321500440c80038024203082c4101a19a0210075490f8440c0e840c0c0650558000c00c010403001000d0168603c140d075200000040340003107110140c065481220300c04000401010a000c02c4c54950345c0144028034260900088090449003100d02c5404020300062050700d6041c01c20309 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 287209109 1250 287207859 287207863
    0xe091003020d0201200f0105070f0c0210030e070e0a020a031b2a05010f06050906120703081b0307050c01080612060103110d08031303090e0618100503010f05090c0114070803040302 79
    0x42031111140c2580c85030381111b02c0c002d008107001c46143c03001401e840441c801741401a442c01c00310b0b94000d80003684078180402c007580909040581d0740040e00c1003840c00100b4001c4c07400b040f8000c580300d140269035204200d800406070751039140061501c985010300e11400341e800c10503020000c000d000c030001e0620190042400f8004c174111018209500309541c040b8124a01d82c40ba0043e582d040762003010680310203042c8940003440e0390900350998030000d018404522000042c0222000c21080300c1044c405440c4582e0464001d0381040790741e42d000e00c00440c02503800040403584000162601c15085e0848114550f807502e061001402074400b1101e2100f00fa29000815001150031000300343d0f403801e0480f10306528544100c0290f00081c0c80d94808620b40d00350802143c01a07200030319100c1c1d480701d28030b04030ac84440090f0110320a50f4881c030000900f51000c0c02070f03944450080390001161314244c1c080d10b0402c00d005a0050400003200701d40102d5058510603118a2600080100c0d142d81d924a0268 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 287210359 1250 287209109 287209157
    0x9091418100f0603020306090c010503011a04180506030709110f09060c010207031707020105010e061c021c06150815040f0c03110118060906030f1b0e091003020d0201 73
    0x111129042040c0520b4032007054001804a910035401c030744c2036a45454030039484002540c010382c0060030800041041c1191811160002103010814628180d0789000c403c41171b071a1300082411241c0c40d84108103407440c0c2480000d000b4481c06106000141503c40091a240704126071b044e050301c004180906962101d40644600c000c000008542c0c81c072542c1809810301a15140c810800c00300c02c40000c08142c1b0600445040320030750000101c154841108100d4a914145400302c905c044901c1c01d8000350740c50490142d003085208100c01d000d05118101001503422103400e6013441250740b24100001c51002641540d415249045081c054603145840d41112070307e000040c0100d00d100383d021040c0b10300740400d003990035026255012414011300313110301003114078420180441c0b0f0030317242000040d0094000d400500401d000014074404109840700c0c0c40405400351000007004500610301c42d0415801d00e540100d0b96080c0320310010720355400922140c4290344000d0402820242d0f02c403655040361100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 287211609 1250 287210359 287210383
    0x2030a03090602042c01090e07091a0d06060f0b120103030e0612040b060112290a030c091d0312060d0c05100c02090a140f101a0a09091418 61
    0x416481c10007034020443d1001c090165941c02c02445c40001084900d0703200d040308070358000024007030381441d0480a900800d060700a0b00c0781e90703450f02c40904041e51186500c03600c0a21a85000448034209120b05419007155002000c809408000890010b0500390381c6a0440e64546000485151100d0102e0a5402004860b0900d0b0901038140310812402c103412503c104004c0c1d0301d42c100c4815480b0410f09070703030205078400e450402445240c0510f4191500b20703090f400029005000c1b455803503568040741121079010024640d031750010391200301a4244074819603c900001036040c0240b01042c1e07071841d00c018051511660240682808103c541d01e1108020400203110144c402d50403040504401e0484500b244542e1094000481d0003400707103e100c0050070031005050440d5a25a42d05001010242485c081034403101d40000f034080e400070340300d070000321481042501d07001c201c01d024084015076080003e04c13030308241c1c003c0c0004c501c055000b40e00c880f8004100c2804d40c0e44d050e826051178891464 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 287212859 1250 287211609 287211629
    0xd0212010f1a0109050120280203010c0c0b06010e0303090628080103030f051e160308090f07170102161209060912020402070224090f100203270616030813020102030a0309060204 78
    0x40031400c5401401108c454001d400074859070881c0c043c1100c00c40060b8000401118441010860701d5200784000360543c2400740880307280913485000a6015040003010350441140c25506c203604188802c40c03225502e0703c1d410024140d50455501400014884204404000e0040340c072120341c50310411640c0d002c5407416034103581c464102c03540007205444440240c000c6145030000c2100501c00003004a80607010308003600c0d40c2820700d410742d1155840d5070300c0d6142564083c0803810010501c40d6200800910400629644c01d244490207807500019500550034424001c0c81081200380804c4104401507049a005071b85170141c1c80001c5988404889820f000300110080a410482c0200105460382c021940f88010702c0451b01041006a5071b03002600051308284101c0041071100c58981e2a44000f80c400b0641f007140c10000300340503811040800d41e4604144030005c0503d60800d10094100c0029144a881d070001500042e5891086001560416a84520007000c2c801d03d94196006043c2880c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 287214109 1250 287212859 287212903
    0xe0a020307060815040606050901110a150b0409080d050118060501090302011b0c08030c070509100e06031005090102030a0501060c0f080d0605030f030a0906090e060d0212010f1a0109050120 83
    0x440180180c001e270410a010602400b0064101440014107214441c0e200d4a111750544282d081071000c1d0521000c05034015889204980004040f440a01480e40c402400003415615024542d071f0b020301d6801c541d4605034500b19003842503983c051801e1040e08c1e02828502401e50701c01500c4446142d0502000c1c0a030302851501091522020000305805409081140c1ca40794881041001d0740e0ba0684541556801d50b1904020400300c0102a0b84d00500040a560768440e401459206544046680c049540d5001042101d070303800c0d5100d4140501894030b4605111121541d0b0301510b42000c20740a4800c620202d03a120002c4135a80015028140180540d00c01800d2520034a90720341142903154041084000b01250040c40f03402900d084401030b00324028241c50b4503040c0074070328031405400d0b80c112944500484202009020f492a0045283c100052003810078407076001d840da4100801d0f0411040420402450785d00883c0710442c500403411104612068040d202e1038500c10909640a02d09040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 287215359 1250 287214109 287214119
    0x30f02120d1d19050d06020c06011202040f02030c2b060612060e090d0302071505070e0307050931021c03020106060507170903150a0e010e0a0203070608150406 70
    0x4282c0c4250401e038a40d40000411110b82000041c194144800c502c9901e5040708000919112a0301007040d4000c0c0b20061405003a6040641844003d03001300041c825415203100c1141003510901c01c0181314550210300714280115001c0c03613441140014601c445a00c0c0c50902a04901c1180c004807543c10201041070650301c4070301601d0259007070440603145180100005200c44007010780c9114003003504c0540129401814150300942110406680702216804550071188581c07151030b0040c2c0c140e44030300300c2004403081050319160058000c640202c034a401840b0707000c02100d0511040200c042245000004080c1c044692a0540e172300280d400340001040000c034100001031018030b24000c1d8024480540c039401c060b01d4134410404014074910a0307104c401c5060800c04003412130054000c0583e40d03021403150340940d0b400801e031040390881e650343e01180c44000e824403503528240d00000142c880080589c002980740d004922a410500000f80c0005031901c074902403102680b04010400c00049840f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 287216609 1250 287215359 287215367
    0x1a09100f062714150c060f2703091e15210f0a0c0201020d0c030c170606030f18030a0306140f0d1e0602070819080f01030f02120d 57
    0x548071800601502030307030562482c030484006005071044081c582110b0902c0d002031280d85209141c1d0710000d05800d10003080350f050b007880014002d403681218850942000180314200e4480310710b85600c4c250300c031207900500200200584010100407105001c50889158840501c001034068040c0e004440c5000d0140ba08416409860103809031410000e2610301403180d100d03811001c2d07850b00584c0b0310352800184c044005811130103811089200243c10010307401c4801050350394002c0103034082078664000c400480d0f404410200360b5150300381181400c1c181080410400d200180c201840d07400240000344000030070050340312141d8043d500b1a5541c01409200900030241d601480d83d136001c0c0b15480324650310b051010b480030100010619007061178070f030f900c00d180b900201c80c0483d80804184911800b00e2014400b0f8a0414042c1140c03603580c000c000c8840d001c8568002500050154540520025010070300f034450649900c520a0703006201240002144c0400680e08401d551042100300840c40d41c0c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 287217859 1250 287216609 287216627
    0x10603140c1305041418120313060b04051006030c021506131404030305060a060e1804050111040608041208010b0403110307032a0603110a1d0402031e01091a09100f06 73
    0x14101e2461b184045802d2240c5a0a100c1c00c40c4602500600c0441c81d40540348142041c4140300b090001792013040c01e0040350030340e0021a42c1c10460001500200255909800740c2d66030903525101030882e1020074070383c080d4046005841c95026222140204241c01c200e03030b20061303113222000b58510803440d2a18004014010844505004054914000551501130f81c1c041e84202c40040c00300c203800c1c40c500d5a120342201c00810030f4034150340341d22a008040120800810190040b0307500c02080d4030745402d00c3c01c1040700d019130032020428104010041c11400c070703098405495104400d40c2100ca003150020b803410489800143c0841c040005510040d0545c84521034100768007290300c0055562140c0640c22584650344501402c2810803514400610403014294001032002c4000d8482000c040880c00304d030004c0f2940d0f1500c410a817041140200c100507842c0c01840102800c0c400d0010764420808090744690010b03024404c01c0d40803c41d400410011000901100e081801c441903840c64001d01e0100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 287219109 1250 287217859 287217871
    0x60c0c081c030c02030f032d0114090603280804050907120e011a042f04170a0f080d090213020901032f0702030a0f1a010603140c13050414 61
    0x101d00a1400621400401901c0b0300d040185c3c3e011f41581d90310307595501401403000e21511000c8a0900c240c041613980e498080c06019a80480c015044825090108820000c1c1c4017910a80c041120140d074000d04820b1403181c5100403010401844540c0340c58866401607401c89540105107804022020758001100495882d043c2010700000365442601e40c200d42601464421030191000414003c3c202504401c001c00060507203c8200e0080340c0100d0000442c0c503464100350240082d040203943d25500c440c80f06000b1360005040035a1490b5200e03400310505660007415000e0100351000780301c02c1544401314041d0040c00e016481c102582851000f9886400c50394080380c501211003052a4a0355000c2c100419070314030f02c9803910740315070030041c1680002000301d0345845110079510014507031089814025204198002c02c0344038248140c4042d9105030001e200700b40c54418041110700010f11140d400114030131009035103c40e4144050700c038840e150440340d0040d050105660146101e0994180704071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 287220359 1250 287219109 287219111
    0x19030c0303020a1a09070b0a0509060d0207060c09080d08130506070206070207140d0b060f060708040302100e0d060b01090f0807080106080c060d15120b0601030f06050a060c0c081c03 80
    0x1411060092a903210203170b82c03800c04c41e4003010050150307008620091040d03444074180310b801c01040c0000540e1992014089003403458010440c0000c01c030030390107200d62200090800c1c00000c1d003454400c81d03035212201c1e9484200034155000c90181030761060302261494208058519a20f002d101c06075076540103079a014018841e0901c00216800b80c180409030804008000404040e0141c0b02d040400c07070701a188030341c4000080000ca078650740d201d000f0900070b4800c01440e51a82d146d0700410440c080d0342080c11052190401c0000b1103641e500b8040c8620380d9100c0c90000300d14161000480d030034401c6400510070317024140804074490340005620011102c4c604000e103d81516481195190103583c0450b5400640c14010360307c0c0d400c403607001100c2240b03e03a600361420340da40e50410403064034400010360782c60200070184440c550340360180a80419058009000c03251a00307000c901040003510480f810440c0c0c100f2107904001e441d0390850014210b640c11240302d540f181d008000d91101301200c24001c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 287221609 1250 287220359 287220383
    0x9020d06021908011d0c1209070303080c0403020901090504050a02120304091d0d080910140402180405030a12020d05010806010503061602060609040213140118050c070219030c0303020a 81
    0x5501c540f01c0d15050310701c4018140a141c0300701c1c1500180c0407001d0881c1c2c000920910820341041400070352548280e1a0000400d48680f55050182003454007404d0740b0301d40741003040148090f840f03080030141101c45078400020300303aa80d420114285982000000e43c00100a60780c110b00c1100007000d0801e450f46e05104000c040780003c5081000f071519840c0b044150490f0311400d040d6406a20025404503075181070311b041551550b5860308840082c1c02c1000c40b45000000d200c29800c05080c120f0154404040d401058205a100c007552806071b02485810003a00c00191000c00c1c1440e0155049040c0114040c03209507141c800582d2a25030901840f4003070301c0f0710000a802603090804116424101c0d401a00c9070f03448900038000e03c40401082680c02000022107420300384038030f00c83c2c0f03030084915070800885035050400801e000c10325155884000d0341008240210a0405000c480001d0360490b41903c820042d104030020000c441d92010f880d076a14100300205040e000315500003030a1252412200f4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 287222859 1250 287221609 287221657
    0x50702040f0e120424090b0406021b030d020a0b0601090519030b0f130201030c092c0c0403080f071a04030e030d050a080402010e01050c0706030e0f0304031208060409020d0602 77
    0x1007401144179500160028007800311480c103840703156016034512480c2a0b5403403078890300a214180d100e030b0b000400584c41100201030030710b00502c1c81c44400800b240a0a4802003480c4000d5681014180107400c044d803d10200d10140e018040703040082c41c000d00400c1140306030f4868004121282e1000b610f82c031041e4000101d0050300d0450052090a043c039150362408003940046004142c001c1103901880311b124804079402c940c0d0313111201e50a0082d8501d8411000f0b001026103080005890f82c9030040c1e0038001400003032181815185000400130506841e00c5160500000d0b491001104240c241002c00c207100c2496480140c1d07002d100c000340c045500d00c00d40b001080700c03103100702c3c3c1c59040020700031004540150b01c123000500b04680140b505ca81868480d804003420800b041c2d114138080703551002100e9a2003010b00c422071900f0310b100c0285062600e95252482c0c0403581d103c008041202c520001002503070b5a611030941d950700a8000f48280d481460203000941c850103035003403000c1521100c42d40c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 287224109 1250 287222859 287222893
    0x9060602061b0a030609020c030901031505030307081812070801060e010b0a03200307020f070b031b0a0203040801091a090a111e10052703060412050702040f0e 70
    0x100400040000c58805030703081002e00910342020810300704050704d582d800100c040c03460000c0e00780c06041901031680c0e000004005000c607682240742e4024030707000d10001c11490340c01000f51020141c01948040d5203060308004680d1500316028280c0c0d01600305011a84562400201c1e002901c0d450402040442d07150082c918030000709104045010604000d800c1c10140302ea0030405654284113840200c0100c01c101114080c0c00072038042006902003040b01c80011000c200c0c40008007240c030300c1a859030810b5000c621680809051035403004000191b0a40c0e658400c0049500914924000301f1a05441d89442501c54500140c8400511313552008220105008580c1c420002d0f0700081840a501c026010302101005080748582800000c0800c01e80c3d0352254009003140c43c60690390540d840304101518100108080c0b12010304140c1c51000d15102d4070000b9400f60080d0704036500000700c000d0100704455505c00c90f14025000385c14510380591007011074001c5240000c0038010f0383c00c0c0b48000030300d540e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 287225359 1250 287224109 287224111
    0x6130f0801050c0717090a030506090106060528021e0304230f130212010305010b040c170c1b010e060103050c0f030c120c030604030e0316121203020d0c05040906060206 74
    0x11680081000703540c0005074814003050144400d17062a50901740c1000c00030301e0512007a4030a1b507958200b082000f2208d03400380b05240c0a401203042c50741c1040d00c1940310001c1c3c2c07154501d4031040011240307000100e090003080003511100c80000030442c0907010801c010b0702c9410a109115020309000c281c85140d00c11000401c001920103001d80d400e503a80e000030446504104480c2d00324003a400c08c460040048003000e020f01941c0280008606c101a030f8091004841042c901c400c1000020045104030b1100c40300c0040c6c00280e00d41a40340c5403900004180300869040710750300034642ca002800c0348484030101d23110b8122405201511401c1c9a400203200c001c6440f4072030b090340b607007201002c001035141c07850b0344140084441048624002160000c20710300442a1000d402089040305500310900e4104030207804102a0344010410916003032680c040c8000c0d9400051220741200b00b07000302036200f98181c805c4070007280018004a50b00c90405800e40e8001d010311203045050030000b244c0d45000103405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 287226609 1250 287225359 287225371
    0x19020f06010e04120e0f15030910020319020901140426070b0a03050a0e06040b0f090a0b04140f071706152d03070306020d05100e06130b06130f080105 66
    0x40c1d071300c9910b4082215100380b0125866440310345490400d50540f00c8140e044940c140d0f0b14500c566030705146481a2902200c401c1c81311300180100100444c6110401e101110b98072184405a11540741c080140e91041100440c540c0c0820046400a0429104c09079150107091508002200c0c4610107509a00d98125009152042c0c1040001800e40d0340b083d0b000d554054500c4070b00281040541005a041c100d05940c10b0b1482888642030040c07003201c0b62501030b00224024000d120703000300c0c0d40d10341b05440c20051003e071080c0c601d02001014010203101354400c640111003079401194a4616034880b1020b010134110362072040d040007440703030b20b0f00940340f04c1b0110b03000f05100c0301c040e50401210f80d40c9013028035020700526002c2d11381040e0740703040200c0400303144204400b5031290303004103001c404c0300c400403c0407000880680e0108074022903904515000b413415a4070321942e04a01c10301d00054100000e4054000400049404c0031141c0e15490700c059416041ca5401d80543d40c6106600b6188180c0d00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 287227859 1250 287226609 287226623
    0x12020714101e12090807060b100906180803181f02070501080618040323040e2206020f09100e09060402030c041d04060605010f0f0f110f010b0901050d0f060f0219020f06010e04 77
    0x100788441030107061050300d1161f640755055233441d103d9480d1429608240003c20105500b03482d418042d1070114400f000d50a01d4500c0e80c1c1030f054054100965850407489140e0500c04454089034403a100c1c2d1084c2408041400a4920681454940140480c50a07102d40100001d4000800170724000b480407682286c00200d503442071912142656074039110283e440b540078200380400f1030006813540c00a0a1443c0c10745090030740b83c00ca1a0140040c1c1c07041019481c00308a01402a41c03031236030324034a409400450030340c1e00503100d82c2d500e12900081d10864000200c0404803164110520044104662203940708102c05e0000c0750f5144015280b0a01241c284004500c1c1c200000c000c032485210b00c1305452442e40303424005000b03507580e0681441d18013a00b51010b80d444840e0840d20303040c601d40103401400151060000061140c82c0d03840400c0c0305150040885031a40c005c105001c24503019200782040b0a4825002a82294800780d591101007141440b02e002d40ca00010f10000c014490511603500111 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 287229109 1250 287227859 287227877
    0xd090b091503150909060601080f1e100b070501050a200301031e020405130209070f020705040b1801060909050c0a0e130912020714101e12090807060b10 67
    0x34490400e6040180030011101c100ca001c07440980c1c031340c025180143c02076030152520303041c66030004004c4100149495542c0d42090706206440d05041c030703401512801400d0640072901d03100c0c40300c0300610300c0340c0c002c4040c4c0b0000b040e6807007440019070100e4002c0d190002c041003950324511078012582c084075000d00002a0600040002c1450440b006403d40c80c180b10144018007a940000d04480040e02c20a6041201c1844141141051030015400031100d04085901c04203030000255a58100e006260203252038112000c074507200c06010710031006259500018541e104c20700200070240a10644c0da4442c102408a60403400303080031181180942d9441c40009103902d400c1c002c1040500c19403450382d0740d807030304104046174600070042940e94003a4007902911745070110032080f140314410228420110060240f00807a08801125200d000c0c0824081c0b24000415054408290080c078041c5150304000c20070040000020050004030701c1400304020036410385043c030069510881e038060129101f49 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 287230215 1106 287229109 287229139
    0x2041805090c01030b09070e0a03060e010b1801180915090818031212180604030e01120504111302070816031116181d0d090b09 56
    0x440c0c1400b40d000f44400051000c100581034078244034039a18235454988901d01da0500440e0000c10400c14203d00c926444c2c00b030269510f4482c82041c40b580030030060281c100989069549680f4001509040c1e410300d0402801c1301d044c26501d6502e1f43c05080400c030918054a00d119224041403901c65003034400c90141d404a0b010028402e8002000c120100050030040c2c03009203400800b00112915101c0c981c441014459000c280180620b000300018550898605421240281e81d900030303414403051850101d41060740d0091400303985c00100c00c0645080e5401981000d1912001845e0003416590031003940d0203c0b0f4220211640401c5040c02e140c3c10014018400a40a014086807030b050b4035901d078030901d2405010b00d12090010f031402d01106a90001d440440300010540008000410300350365000c603042120300141c00098007040b840700c40c4c0140c0d4401c4078003a0007240c2c005400 = true := by decide +kernel

theorem cover : BRFrame.Cov 287050359 287230215 := by
  have h0 := BRFrame.cov_init 287050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 287050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 287050359 ≤ n) (h2 : n < 287230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
