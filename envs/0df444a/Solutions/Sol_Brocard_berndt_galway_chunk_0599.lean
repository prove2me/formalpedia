-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0599
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:39:42.369138+00:00
-- url     : https://prove2.me/submissions/d14faade-fb38-45f8-92db-03148ab5725d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 107553956 ≤ n < 107733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 107555206 1250 107553956 107553959
    0x1101170c03040c1d0103060605010314180a05060103060b042702150903010603030309020414100909020f121b030c010504030611040b120106030c0302120703231303020610030c 77
    0x1448400950b40240c401e114030401c1507220742e00b80802c1c032a03000302444e00300810b00041052000d58465800a03140a01c0c0030b000800140046103000705018202c1c00c030008403010b92a80009082c46802500c95124090b40e0341c5503504e04240014040350607245200d02e1a02c0059200c403c1300c01140e4008441d40f40082d0100d020b142c082040c2c000c4940d104044000c400c200b040c1003030b6000c0c810070307001d1803080d100001c0c2480c060050000303c6110340304040e005031102c0244921001c07c9942c0d241141c2c07014801080b10b0b0014404074082600c00125103030000c0068114803001c07400816400c556818400543d1070000c0c07008101a07942e0343e01c400d054042001000148003140c2d55400241d040d03404180c075185030550714047c10b20f080d40900380c090301d050240c2c0c0042c80110b5040c014041811010310381503007800c02e680b80c0307120105000303400030003850383d200c03110038002104240000c0d50170443c00c08000d0510303040c00b4041c1b607011518411001801454000f0b010082c0000a6800b540c0d04101d200301d407075 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 107556456 1250 107555206 107555221
    0x1260c0114090109091b12021305060a030b030105010609051002011103070507050c0607060603120c020319060b1206070e01050304050c0907020703050a0302010b01080105010c0b40110117 82
    0x203601c80b0481c02d042000d0041d001c20400c410f40906802d542220444901118007800c2c01806074090910400748140108519071800d501e4044a200b512002c6854a54600410000f580200740c400034070354041d400d00c4000100150081c42a40448500f510030010942101070304900301c8001822200704803105001060f400c40c403a10240205604c01c1013201e140742242000a511500203034004c44003151a1039080c0200040000c4040401d2500d003403000740340030705600094642c41d00c5003440d000c0035125100541407200130f03002003210b40030107480c5852460004106a03106d4800321007a4001c2070f080360348440c8551007041180e20640d048000b80480e40403240c02c0003600d140240007541103100e10715000c80410310600051031414440e4000048450f840000500100016440700c1c1c184860b8001580109412081d0103511010500380e40020803504101480c03038800d14540d0000f900340d4100d86c40520481c40c420145007030f010b080350b82d0000341444011106680e0840008d43c0c40e901d11740205441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 107557706 1250 107556456 107556497
    0x60a0b071505100306091518121211180306010f051e01050f0d020c0601051f1808010606050904110708070803041109070216171b0f040501260c01 64
    0x8102d0f601c00040540f42d40740c54032070943e4001c240070f8880c1d840d81c4841703409080107407250603000303408460111000032098407600c404168445800c030500400b000480c880c22019804904014004003aa50301d40681003401c56000c400100228000d00c01c0704000308000264281e098101c400051030641126810990100117800b400e80d041c1c1444000d01040c4089005903026040c50480441d0041c2c44068008419140c81c00681c8840d0160514081e60341068490300b040d20781040d040d00b8110108150303464185540300c0e26074881000b40d4139180000ca60240d0080c028a00c100040301c0034040491191540d56551003140002024000104107280c00102c031000036592090043c0c007180e02116192000c5440003100300c030315a00507005503400302485004003c3c60300241600b0402c2c01030340720044001c4c0d591510044a29010350005005210044e0358100c00714020ba1806030051045513998818240251000c0c1d480f0505012a005114010b50b00003c1014035400162f40d54651241500a030054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 107558956 1250 107557706 107557711
    0x2030607110a020f2b0510020a0f0806030c10020703030e0f01050703080702010f05040b04030809060c2209020a03200c06040b18010e0f1002040320030f0106080303060a0b071505 78
    0x4200c0711040d8031000805145d0403090240b10082c040da44a45006e260217030500d00ca110105400c24410301032105620b512a4505e2400a0f450500000070380356440000d28040c044a90745502842c1da03000e0700300496000c280c5008aa2203510384c400fa082102c406c220700c000000641c1400920103104410110f845101070710340200c5036000000d5005120400706e81550300031102641d1801c240010b1108040d44040d0056110320004054280c40c288010400e8452249080c542e1b420100703990ba03102900c40c810903c800401141c0011035441c41012005409884103c58000402c1c0d04944030250b04030800b011180d102c9510005008190f5407036641c000b441101400c1210308140c40c035618000c0100c00d100715400341c0c000600801c10300000e660081e1804104181100742a4014801080050311aa06140c015100c142d660702d00002d0301d102003882c2261001d0704088a600f040000503e04101000a60040b41c0586801da03046449040300400d45c40b030340707200429841c0f0542c00b030304802d207240c0c0c892038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 107560206 1250 107558956 107558959
    0x70510210207060b0a0e061810050303030a0c0e0102030c07060f050c0102070b010504050a0b030a020d0503070b010e011505040b18040b0a091401090509030703030b0402121302030607110a020f 84
    0x6000e220855100c200d800a520844400303940398044081c0f8581002010002c0c1070300c42e60321103d4a00000422603c01c5010350a60110500030041500c00901c404088050b2401400301d0b41c0340c0c03501d07145000141082860b00804504c9442c0c2007005544040219010842d0907001424494038101c400c40300d82c0032446441e8200081407200c140c280c0000e0005046541c0120401625075040004100803a00d010701440e4106180502c0f40740d07143c50204241401907011030f02e0300240302e11424024258450440000c0c0040c6040340041500000800a14181c590b028290312902d00000301c02c0e641c520a9004808a0840c11700c0f14013011100c440c0740298901015001058028a20000c1600c100081d000304104075228540100d10400c8036010074010715204070300b880a4105035007610303141d2041d900b014080541790484200316072038540440c2e1201c01c0300c0c210325041d490102d802080031000360004074030a02034800032400f001d11811f400c4c0304c94140341001c0c0106003895406c006880b21501d1845 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 107561456 1250 107560206 107560247
    0x81305030316080c0c060a030203040302010b09090d0507020a260609011a0f131b020c06090105070305130308161b06020d0c1712100f0b090f0d0209010603020d0c02070510 75
    0x1417050780302c2070040e0074000c03200c0d00c0160b01ca042500c1d001c1d003501d25803040c2c58024040841045002d00002031884501e4081d8240740340da860560000c152524101d030020b51408084912820a0900c4849800b4580d840c0030180c13070403600c0300d010103400c3c0c58840180c4d00226400c2840c0701c20f903107044c940304038071741e20010300075441c4c02c07100140c01c4280d4002011600304040c200303191420280d014404a0b4a402044400783d18002000c40084d1103406042001340c200140440d002050058101c41c05000e542c2241c051038031203612500390350190b40401003c944c03100c201811820003220390b402510030b03240150003814000d407c00c04121904921100c0658842428098086151401d10010150203482007042c0481c1e1420340200c0002030321b240e00510796001a0403040219030343e01002d4030070405003101c0c0744114209140000c0c0c4140048030007c0c3d400150500005203841d0944d00600c40c1742043ca8091000000d0054160303203403101032040d540c000358504203c503903035446505035107030000703584411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 107562706 1250 107561456 107561473
    0xb1c022703011404121403040b01030627080403060b09160305220b010f05100e0618060307080703060f050a03080d06080d0203070309150e0d030e0607081305030316080c 74
    0x510890003040e0380541d000c4815050245e0803136400300002c15034019624030a451070415641e42c1a95400501c40a0710b903990722154915910503c0324411010b4580c00c18070000e40149080c00c1d81540c1c03061100321249403401d500d45009084c8a42420712407040500004601071981c0170907405000020141c100780c2122034110041560321044030300e461401142e03880780755030418a4994845425401044c4221080700141c042d003603100c100c21404c981c065441540701d030200200c1c50190751200307a550317900c01004020003c200f42e10028492003030080fa602848020750b80d400d07009415885010b0356411101c511401c0c03000c02d00400080521510a0700c000841c0c5981e00c2103030b424151010701080050b00300040000034980d20440283c0035041e500029038611140c203d000d007000d2910a0002d0162240400840606002d40046e0642c0d91000e0201980d5500b1894104000e9114070542c1403401600e02e00070600f400c0000030740c1c1c80941da05003141210a081d40341c001c3c498000060320342030380c40340996 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 107563956 1250 107562706 107562731
    0x203011509060e0903070807110f0d0305030a05060406060504031b15090303030e010501050a050d14030c0c01180e0c0706060f150e09070801062001060b1c02270301 72
    0x900c04014840000d0004081e42080680c803950b440144c00d12215500611000c400705103400110b80710342c0d6000a01c110b03149141c3c00410045020700640542c09010120503200749500000158400c0b00d680308104141c2e561801004201c81050050340700084d0280020f00016600411071400384151b05010fa00350f650307421611549006407602d400015110042c00c1040507014065990300a02490090185604040c086030002030b40c0d1184903c269400308048042c0701000c041c0700712070742c80c0300c00362a0783c0d0310041541c0b03948130041c04103140056162030b14640d00007201c080007825110783d40420318017501c54038500c1c034054018a8054079000d58034000014000820800e21004102c98800300390307859102580a00002072407401c0e513020300440303010000720341c1d400f0a0450640340503041107a80c0350117514580e4580c00320b083c5401469880d000002c100505040c02a01580e4028603003542210105030300b41c426400340c0c1d40500940380c640c0840c81002c1000d60200708220070040c0000803014a58613 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 107565206 1250 107563956 107563991
    0x14090406120218062d030a05010b1206040c0e070504080604050c01080a05070e060f1204050705040501150f0f050c0d031b0e0915010c020a06091d07020c0d020301 71
    0x1441a4801800d80907440118104054103200100c0d81c0115410189042004101d02c0f001501070528a0141e0200b03250000d82c010205040d101c070054100c2d4400345a91600d14020107240c1d45040c460384007a01c00400044001440f5481240e00580d01c46411380b81c0111540303040805050503003070104c1484049410001006014420b6025500030000940c00c400090800388001e0800c03800c032803d00c0200f0070701a400c414050582041560540d40c0d5202c105603074205c0d8001c200441500d40368030400d01c428003000140c0f00c000d4403001c80e4100700c144d90314680030318075079011280c41012641d10600000703014050f24424000d80b105062991420119030821810080d050520b500440da9405d1036603040d012032440007900d0141400e04451492070000001d81001000300040c034070b01d80250203070040383d10800c20511110b5019100a100544a88001d031400140d402032551801c00c0900010304034014480f140d000d88903540190414140b15400e2001d0130344000f03c20790300356481ea01517003072108465 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 107566456 1250 107565206 107565209
    0xc0d031e03050a0c0e010c170c0f06062112070f06050a0c020c010329030f0601060206071115040f0c0b0f09041802010e090414061303030507090305060714090406 71
    0x940d0700184034900491114111510301d81c0800030804a641e5212603660070009101409410040c1182e4502000c40484018420f48610800c80d0181c520b0454400c8000a2214010340044502e84140340e09400e04440b04807401d40d94441c2503224a0741c140b000603c040081012a0180c041d1241c020002e44803c419104142c441005481c1d4a050b155143ca50520540403440402d2a007403100103c1015401c540c1d0070b14004031123000d40c4030f50300a07060303540c00c006900750415044261251581c2d549c00103500e80380700308c81d5140410407000803403010400c04100c940c2e20b0159103406555688550311028440d02c4207010444140c10138941c080358900e58031018003a1006007030b1b00a60317030389265824001955480e00c1503041c000c0c84a6001c5005030303009035407201601401d0780e82c00c81176a2641403a4212158444800c3c46d140a2541440002d09400c45403400070781c0641c03801c1c80f05845004048404a10b50700c000f8159401290210710080c0c0306248030312550701c203207441c507041020100c00681140e1b6203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 107567706 1250 107566456 107566517
    0xf050a0c060e0907030905060601050c07030c0902031902070f0b07121407090812030a0c090b030f0115020607082a0c030c060601090303050d020a0306030f11120a03020c0d03 76
    0x203070034590103140760050880303031300c19194a014030084519548480d07460a020b4035250521a010414a1444208100c840d00540c0c0080c111039071296a102484000d600945805441c200310407525044101c0c14021101c82540c003543c0309a0201158540c0b003181180544958100600ca01d40c0902c0c2010f20300844c245038580c00780c030f002542801500500092003e0388141c0c0181c20003299400c0610f410740c10b5991100320504003040310100c0403400c685506554101350a4503801006000100700c0d06e6001d103040e01c06400c0ca03106040400c0d41c0690b0354410071500c10000800d8000010f0b045c40b540741d414214400d103a03664002c200c0c1401d0340554107400280d0465140d0744003007010700941c282006211b800860070b00700464103e0660303c0c01080c42c030480c892444641d4000651001451180d44020001c5401c210900d0080300d086c6003461000340002a140d00c524080c5500144102010800c081081e0b899001080c00302c59401c1840009000107105030240900c0360002c282e500425041c0e000103422 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 107568956 1250 107567706 107567717
    0xa03030c030b04142203020703080a1106010f051c11011206050607080c011b0503011e090912030f0b01091404020403020607031106011e0e190f0905060f090a0f050a0c06 74
    0x91060a8400c01c4480c51050134400c2c160010100100c7c0d00461194162900190030170703520686d000007950ba58940181c450703d43d03c0740e0000000c04915000030001511400c45544019008180300c01500451100d4003500040581b880c1015540c0100c04d8a690030511a8002c55503503520301c0050b0050b00b0540c1c0c1943c40100009401c0809070080c4141c55139001c0c1c98145207440801c03503500500c0d500050003400010b03039030080c43c811907502c81001800102007003030051043d25400c0c03900d48845a107a11514002c41e0520900c22042003413400bd444042e9010303500c00304e180b031400245550100d402600207800c59402c20000c00540c44540080003464026154005281d0543d2451450468160f020062401e06101042d00307203c50102c2280450b4004400011143c8954502449404d01500044813481c5050076201d00c011a0303070070210b20f01d4011400c2d80c034542c0d945082860b5400d411110801d2940081401c1c00014413500603407504070380950300715146001c040c3d803862594070168120001160 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 107570206 1250 107568956 107568961
    0x507121b1202040f03080d060515070317241828050903030f0601300b010302040f03080708070c090f0515030a0b22080903070f080a03030c030b0414 65
    0x2a0441508081e030980c804045190900d44500c80686031042d00000308502000560100c1203406904568041c0400030f00c580c035030050f120034042459001c420114086036a450109289040c900d00781e6104050111105110780c0281003051001c040a400c00c1c1c2d8000300100c005940c41411000a51088003103a401e10740d8084040200d04490040400348400c0743c0c2442c3c100b0080c40b10100541c0d401010114028109880d2a00140c03071100e1080105400b80030400d441014050a0398542a502c0c4800d100030003241d6a980e004500fa441680100001c002a01030100b0008070660014000c0f103020740001400d00707082d0b5440322014203040c0d000c03e000f15115001001a00110b00c0b425400140400105010141c880c01094541c82d00c0100580f0443d2007400107461550304046c3c0c005040924079181030858210315103002940c202d03249103802445181e60116400f0000ca880b0000e4460b048000c01c3c0520003568114007809940040c80c04040c0c4030b5003854004e4813a8041c0d86110340300800b0700384991 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 107571456 1250 107570206 107570261
    0x16170a050403020c0a0f090b0a03060203070201090c05040c02191a011d07082205070902070b15090105010504032d0b0a150b0904050405010213060c0507060c1203050712 74
    0xd1201c2200da00c00d10744180304001c0540d1046c1454100c1d50b25032070204001c1002c80001e050440c1940c0050300c0980000700b0403512aa0651003004440d109465000f41c00d6110000e000448a40840807001359100b04e416181071036505448020f2540f003070b20904603c0341247c80d240302d118408e0b44a0101d1446401e40130410500c03100e280c0741d01242d80c0c03421001e6490104464032550003402d00301e41ca5030340146440c0013804403c0c0404000f619503000c01f59940c0d6114a480008080216158100b650400c48030010340d00c0e00c410098101c0d503050303480b942082d045403200007991440c0d403440360300c17024520801d00b01d80c0d4083c40310003052030180c2c03800710f1645402c400c2b440a03a940601d910081c0000c52000f402620b15000644800b508150780008280e611464403d00a200c2c3c000323069401c13201c0040000300194024400c0307400303030310031015141c650f13544013000d0b07446071281d45005160908100ca07151155103c3d9102d05e40c044202d00c1c0c1041103049148200084032700094290744016600c00c50003c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 107572706 1250 107571456 107571463
    0x30308040b0a052503062c010b0405150c011b050a020606091009020c030912030705210a111009111c0b06150714100f020702030616170a05040302 64
    0x82440b0800d000e1440c051002c221100f50406440198003044182804828801d62180d40a0903803070980020140803040c941c0c1800300c0b03883e145170800031410000320b803661400090b9011541c011b490890381c945101110f840941180150341419966000b0151815a0080483c2e181c0c08058407001d07035480280c40000e04140c4001e0603d4003403140c0700103104403640401c459600b01d800c03010700140c03280c040f111014118403131003080e00c0d17000110706811400c41d04003000412005108004036003030f15000411385219040c031040a96500d135018404075101a000e840400804e021680a490320200d07245629411104004020385048149002d6410181080c130795024200c81141115518152280c0c0e0368400d0b10001004217000f007840b550400850000403090314038465008102e0000b903e01c03a1080d59030781d050342141051040c20907100524074140d91003110b020380d8019000d050b90356600581c02c1d1840c1441505d142c2000100403081c004076030340007600303806241c2c0b40c0c0003c81c450605041c001d19 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 107573956 1250 107572706 107572711
    0x120f040f1e03030c030e0a0303020c070803030c091212030412140a110f070e0a0c020a1208040507061403130201021006080a020a08060106050d0b04021b0c041a0f010309020d0507030308040b 83
    0xe15190010386c1c8410500001c2d41030381e05605160141c0d980c04110b10050614885603c03c81740f5100210034022070583c8000a80b0f01040180d4180003401da44030410750742d6010304c0c05800c202140070404140845c40c0080c0d46e0110402c541060b111016460030000d4944c3d00a11040c0d000074404512110044010f01c40241e45600f4078001700492801c0107810301140002510085500780e9030407072042c0e4203009010048000d40c0240ea44492240c5034030002d084030400311000c40b041d0003500c002184042c0144102c200480d0318621050442e582e420310140c03a100c807050142e0552084a9550362011507501464000d400014064062000244140100c0414a4004140a810440050141c0c84d40182a640407001c1c2a101003400d03000040810000c0c482c01e55010045812050f0041e003010740001c1101c0014810340f020000c06000028090104030003421542d80800c01c0b800c081001d61080d040880312500051000315034950550350f107031501703200358022004511000c04000510207410704599 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 107575206 1250 107573956 107573981
    0xc05010e01171b040f2d0b031003062d0c17100504020703080910060509150103110a030504050f03090904080f0d06060504170102120f040f1e0303 64
    0x303006061000080c2420707181540501c501d41c40000060354003180c0704600700c956801000c810b03696139160850004942034034000c0c0354440454548041e08444500201c08203a08115440802d00742082e24003801c035440030b4055840c0244d1a84c000c40400c80c1762040c03201c17481d41da494034a10301c410041c1c0c60841c12841c0e1013028a040c50081c42b9655107421042801e048104000c042615590740036407500d000e082a0000340d0010b10100b40c4000f01904400c110b070082c8407540441d03454080801d4a081621031078014950440d9080c0045545220744d80011850f00005050105414200001040041d0864005040043c3d11b907014482480360511083c4d03514078107800594500030314840402d00d140d2000d0001090380100145504501000f5819141903015090003844810f42da440c009046400c180500300c003020441c1002d1000490520884a200c403080507155103503580e007594041e101d00e00400a4844a1402c00c051000407068000140034402040a00c905005c19060003401c0305c0c8140c4800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 107576456 1250 107575206 107575217
    0x6050319020f090709031a0601030b030d0c080309010605061204020a0b03010e04110d050d031d0a0c0504090501020f0c060708010504020c060f1f08070302090a0b0d06021602090109090c0501 83
    0x1009601c0b01e4100030302148080c1e031502c0031a120290100c0e000c000341c3e8005800f860504401460400304107040e940101000d071f805200c4d00c07646000709a201e96a9030030342804910302080c404000342098000d903600039402400054000e5403480400d515604c00707601d0000d400c0c400790400c011480d01c4440f031030280c4407040e601c504540c10051074078103032000580007400a07000340072418445d5603481182400d1640c004165a00d115883d04040d01402d045014061a01100940d24100c1c1a0018610400316007141c842c0341494900300c01c0c072008241e8900b058905540811401d845c03002081c1c001c201000000c0b0040405141c200e000928080048e004144035500401481c5803d032000980c082e00401a21039007492603c400407044e009484e078252503519104440000038280b403010801e042100c5c02074607841665602c0740d131780c0c0c1c00b1258080c03229584140b1803265940800d20f2a030107080300242c000c001c502c04084580025454035001d0b44103041b581c0d12607100c0001c000440c0c0c4007038020082070a12 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 107577706 1250 107576456 107576503
    0x80403021002031f0e070f0503070215090a050312010906050604050d06021602040e0304091107020913150f050402030c220b040f02070813080f0a06110c0f01060503 72
    0x39110700c03444001118160b0080b0116a00083c442c0b282c1040707404000c2080c80d201c0e500c051280c4042c00440b05000802e0307a10018012090141007124030519481e0301500c215a600143d00d041920003a14009503032060340543c0000420800080100d81c00000a400c0158980304611b4107903038640d04501d000e640f0034042040180c0f2110045688070b07078000070160b102c0b0f885d031160601c0080e11700c1019501c5410a5030003001e592010004101362440030718140054805030010750360503c1940e20007500b00b0650400603013801701c0c00f005149050b11409112003403171031076800300040e21004403030814030325980d20a000443c80d0401101400881c20b0f0b401007001507034030341166220290881e0400010780c941c0f240c000c9980d519071205124000740340046480310310034285000650003a40341306081801c0b454011a03405000983d83c0300b00c8083c000100009515541d456002e402810000a020b28007032020b110704660501214410309003c0700000f1b5a9894602054038282c00d0800e081d40d20240d80b0103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 107578956 1250 107577706 107577713
    0x12090a05070b090f04090308010801150807060e0d080a1d0d050d03020904020904060f030b06150a0507020f030a120906110601030f02010e031002030f0f0105010e09060a08030c100c0804 81
    0x41a2040340ca40382c40351a114041000030440302d0200700102c5510600d00508441099002820305058800d2000204042ca503402e000d0101d0044500520304254003484003000706038414802d02c0781d40107000d08030b59280d90055452910365044124414040787c20520f010824140003404c021300070400f00c500c00c01000c00d07030300c0d150380307948400c1c4c118030415800203585050ad40301c940484001c1c80703003d0010820700390355002001c00d130781c02408101c4c1c012007a100455164545403801d403001407102c0100030700d001d84580007074440740c0c40000101c3e00848860300050060354148204d40c00c080c080d110540d0590014003000708800100e030000021311104207014050400c0016116040d42e610038040c0c0000382d000e00050b2100d0005000240d070600c40d802c0100c4101d0130a40185000c0caa03448040305980c1c442c006010000c0d002401080d0005010141c1d000052a0450210790090005001070100a07140d0b94002d080d03034403041d10515240d02280c54005201c0061051041e035404926001140341420354 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 107580206 1250 107578956 107578963
    0x30c010806060703030c0509100e0a0801140c03060a030206030a090516060207051201020d05010f060e0303070b0a02071b06030c080f010506090d05030c1c02011b050f0f070609030512090a05 83
    0x31006030030103580b018204e1b0950b00400440b10b203402c0080c141043ca08150b00001e0100000b64a218003850b10b8405c0010a844140100003000c0c00d40d1138104002d58541e50f000050f600010006648480e8800000001d41c0351400114003031302800001140c003811504002e443c101580030060b00040c10108200900c5030b01203003080c04e4030021500c1c2030102c2060b103c2d00b8007900541465802e028036002c000030703607a0070308941602103940c29100c1d0304000f180ba80406459000d9114080d240388902d82c0001d5074050b035a4000c200c4940708240b980c40312070a01c11882c0d01c00c1c0c4203401040c04281c0c1d40c0c80c00089160000d40d000e42c8400301c030103500791030342c1400003286042c0690030045000b408804070540401c03006000f90307181c03150046c0c1252041085072000c86900e814200018000d546044252001d8101c409003100d0950350300c1d100c60345007403410302524002da4040400e07144100400d0040034001501c60144199050181d6201501c450740108402d4030114080c00c244840e070b0010001c400020000b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 107581456 1250 107580206 107580217
    0x1e01030b011701180f140103050f01090302210706060f060311030c5a12010501050f04030b0f16050a080412030905030c060a0606020106031109060102011409010902030c01080606 78
    0x88110f42c00013211300009002030000c1c2503203d071246007840f01354046501105080c5040b01e015904a41000300e0401c44d1608031402400080c0c0140c109018241d020020b0b1030803118280240105207292403115180c41c8125110340d0404503c3c2d0907400002c00416605000d1042c81c07a100c40803603441c50410414040e400d200c2d03076480900c6a80880090130303200340019101e104040080c1011980b40015003142e841d00300c1c10007141102d49801210f41a068040ca43c10350f00f21010700034042c0d1159007040c00640e50b54208180c0f4003880c1c1401c20000c030010300c405214038054140c3c0380c0010501d0803c00070902e040101481e420f810060180281c6c401b241c6c0c000c0c0029000f0340c02c00038245111034a19811000780c20940340c05040d85c84001804031005000240041c4074900e2746c401004081d88500c800c901741c911511018103011080c0c40e0f8074556141222010b500071205000000e1495890303031804070104012100d0f68100d941d92111001542400d01c4902c0010000740703491961450705400160150052 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 107582706 1250 107581456 107581469
    0x150c1015060212120c0912060901050c030402030607080604061502010e010c0f0c03050913090308060f0901060903081305121b04020307120b01020109080c030d0e030a0c150b1e01030b011701 83
    0x2140b05d4158000845600040252145d0040d007180e4412a0b40d405080d078412079207618010000e410729000c03009481c0500d07401005041d59840d5524121040c06010305025401a66140d000a0385c41007440c000c0080c1120350004500030141c2ca0b21682125110b0684405102ea801450308075658400d02e20a1103d5260800ca03403100c0030100400c60f480c0b51103006490152400c19a101815000b040310361054801300c400590080c0643e0074400d4401b420701c00c402c00302d045074000740f00083d4004080d08004c0c42d5000c690303c1e00e9030f4170000a0f04006603040c2c01c80140d0020000d082034200300b10f44101d21001d00742c0b419461814200c0004201518407a0074501403a5241142c1607283c1c0300790403040c2119081b0b042c807522040b0b03019440b034803079101d48040312556103401900c00c0607510200560703469940e1785c1c541c0d05000015031922040d100d00000c0c0100401c0c2d941040041c0d5035a610004100c172100ea2100004003030700d141c00942160681d58119042c401421303000640264130b04d006a0550f01d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 107583956 1250 107582706 107582737
    0x40512070c0305010221180613060e15010303090e090307030f020a0203100b03010f05130201030c0212120f01080c130e01090605010e0708010b1206150c1015060212 72
    0x51401c05406003002a00300510f694000141c620b088130340b01c08201104041e41034921b2981d10341404101031181441d42c0b510403034100c440010403441040c0e01c4103d0850090402013065120080b03914203100d0f02a020160500c00740e0700510515078000541e5026040b40c4070400424282141042d43c1d81c02150700060800c400427a000100900c28004002c51aa01400b1216107113a401103040c054030703011000502030345c60080071000c44445170180ea8001c54699403801c10128440c2c00440c058403681050105610aa81c0040b012141c1040100071861000c43c02e2492820560001404d05006a0080c2c1c1198032044464441d0b43d0740030000c03c0007600104001032208081580030f40501500c0102401841c41d050001400d0707180050030314800c00ca2603685450581e243c084c841c0e1a0301070100d62a0020590b10001142c0f070034410500d07500403100b0784902d800c280c411481d241c43d004400eaa113440303071600c0d600c3c149008188100d980002d406580090000c1840031044181140030ba0302880d2407201c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 107585206 1250 107583956 107583967
    0x807030807141506040f090201090308090604210203070501030e101505060705150f04030507080304020a0b0d0b040e030c0d050d0f0e0d02070e06060910120f0608060f040512 76
    0x1407102c041d40380496044081e02e00c0d5050092012400d030800f1030310306001d07608080041300900c21500c030300f607092581616110560350458540d80c100360840c00f4081e40141e820031000c203450720075001d0b15000000e840007210965606105040c180005548014185810040a0006e6040108101c41c2c21400c20f280010325070102e40d17680d0400c000302c2e48001e0300480c2c005036000c28400042500703080b45100410451060311520b0b2000c807009000c0b14040d00103101800140d00064880c0021a0458002000004101d0f281c40c1d00b4001540103014010045588030305020160819000703505681207150040e40c00c20030025078007504c1c1c4848000c25020000d00055030404e000c2960311801110100724003c0180399144bc1c80c490b03561030003001840c0036124001e00001d05203140300d6014420040508038908044e080c4003030048010412a0030b00500144401d15896401113120346902d0b2080c048002c01d4061905802c68140305000d001149000380365410000440d000080549441d410103016554a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 107586456 1250 107585206 107585213
    0x60403140406050720120a0c0f0b040303050f13090501260c062505060f18031e160809010908011401050d0213020403060501051c0506010506090109030f14010509070807030807 77
    0x405c4403c1a82c0d02034803440980d001c0781000112462060302c5070188921090312030341d01c0704502c21184213003500c19070104400e1000a100d000604070030100000301c103052040c05070324a07140d148503801100400342e4420040117145110308421100c44210b0a4004804500040d501e03101c042803406203025020000369544080c5500c492030400f0012480018801c01007031412a8443e40f0903582065001e00c00800b068414030100440f0440011410040d890415204000b12041401c044031032250b032070500010213a44140307101a82100e12809050b6501c80180c00050302161940c0c01c841c50980c541821045d9045401234481d0554100b15000840103da910000b01c1101d000c80140d41d056002060010410500740c00041c181c98045540d803595400141e984218000c1e40b0300007612690210004206600700a80104071122041c0b4111503410340360f45600050707000c02d05080314990700ea100c007038114640c20300c2419000440d00b40500700140c070300b07902c1c155100b001307000c0a407428000003064402c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 107587706 1250 107586456 107586503
    0x10020c011b0f051b03071d1008060403090603061d041506030203100e010b0904050307030e030102090402280504030c181b020604020a0b2106060d020403050604031404060507 76
    0x2007550121581400320428038050351a041e11051040d0403480500101c2c91074500820380509561070040e00c000e502ca0746800078240240c018041040c4104483c0300428041d40c24810780d4801c9019465070b0503d5860310500500300c49056004900e881d000d10060f9030030403a1007808542282e002000c80b8415100003414000900701948000e5051060307a00400c01d5404507000f403440b00b00110b00811001c3c4d219420711661103411100280350b0341007008480006806601091003628000d000142030100d1200800d089a00600c005411900310300d5030800c10f03010080040500b028685855402d040c03865840d00910002405015400200a20050f6800d4166444818007200c0b112001d41d40c80020b070006919003205540581c014401d10341c000c1000310a0604498250510071042185049a404401c80100010b800c5580c400130400c0100c0c14000355002a00285000d04060002820103281c0078010103500301c000c030202c590501c8100181904401900c1d2f0158000c00d10441c10143c19840408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 107588956 1250 107587706 107587757
    0x609030201210213170a02011b0c050306010b1c0213030f060b0a0b0c1c200703120509030d0207030f06050c130902041502030c071412060702010903090510020c01 71
    0xc10740c1c408151940c044c3c1c1c1d5210920308a40948030091a442603885525440304030f030400103404608000a034501c00500602c0c51031446024030b11800c00ca5454600284c00c003207013a4040100550b020a0748014054480030f1281d444050b15001c502e4840da19007074089052880c031018001100d003500c14414080346030800c984540c0028103030600191521150301c22074100300803400b41481170580c0052070104e038141c0e01d0f134104542c1d01e484032081150a40180c03003a040450b0481c1038054110004002442c804401e02c0040c0c09844140e2607080103000c0c1880c12020229000c00c55025180030030109200c400b801403040c0c0c101c8404640d56681e2949039204c0c5c032510003d0030b407003124120005540030a40c0d028105540309505010300d888480030040340d890043c1c54140d00790760000304003088011400010306012000240210205000d01e04405090060848040300542d450b030010104059003c00e90f680601011651140306c03401c0b038080290348580340695241030000d001c00f0780d81c40a100346079040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 107590206 1250 107588956 107589017
    0x100b0714010e0307030e09100905060102100212010302040516050406031107050a05070801180804090506030a0210030618290102010e16030209090105010302010807141603020c03070b03010609030201 87
    0x10ba8815241c060b9641e004070b00542c0010301d10000990340d850084a824018050300c217004c0e90703070750600254070020300d00075114505520a005030300780c8200d00c50020340b074040071901809a1035851b40c01440103440f8010543e4141c01030f82c41c44401925000b00c240c07410395000b4500040c0d00c101c01c5c00241854440c814025180384905082035041040c001a004150b5041d180203000300140880803400000f882c0304010552401440144110f160960000b584104011f04481c90903900381c011400c04042601d0900000b51204004e101000c80c0400c523020703005103418200014080408081f20311106418a140c40d202101e2201406a03c00d4000344d07403091000054800140102840c2c50088115110481c017070300506002885c5000c040c81600c0c1220f40685582406a48102046078070240919810000c2041406030914480d590002c14041c18441d07002000c40c5d00c000010103162040b41e601640e09040c1c2040180078440d07000001c081141d90a08044440900c1c07050900b02001140c0181c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 107591456 1250 107590206 107590211
    0x13050405190f110d091208011401080405011d0d08070e060909070207050405010602010204050108160f0c030c080403030e0405090a050c010e032401051005040b040e0604020d09080d060e100b071401 86
    0xa900c181c0c4e00e0b600c209205440b0701c2c620903903065070007000d0340c4100c024480c1e543c20f00d52000701c581081d4081d20080d0b42c020b10540c00095801d0078480d83c000440e40042101c4480c1d0f22019910400d190028055034000400e81800d5a10040744c6c0005800c81c030420705000c2c0100704007008207800768020440c4e0006024010014000c035138642030002c2c000e4002e8810580007403140300101d81c1c006220000d503602c1c2c280d80d585460580070300d00c40980710031340c001804070100328146044201041a401c041d00c00b4512956078000120940c00030401500d5000e484130006d500001481d000103440000e00780c1c80210700307080001d030705036500000074103000c0d802c1d5070701c1c0304210003040c0084404606031440d4140d0300100d614800d141c0e42000122800d00445c010102041803c0000b0301003500d04107041d41c1d001c01c004102505d85091100302d0350039190700035007c41c0d020740042001148000c2d18000c010241c251803515260341d140100081090300c0980c0b00d13041d1003a070002400c60030301041510b06c07049420700c94000d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 107592706 1250 107591456 107591467
    0x20d080f0d1e0c050301030b072304030b0708010902090a05091806090609120a05040b0d0204090212040c080a020901171c020705130b010c140c041113050405190f11 72
    0x803031038203a2584080b0740820719100402c00c082c1c3c00b032001e0702d040ea074100010a910343c0d40c0110681d070800c64620302d004003a60f00c01810b21000603400045c0081d521441d540641420100005491303844180c004200090040c403005500740c0b03e044400048500c00c4070205655140c0e1242d0740d1a849100c00341302e01c140100400c128640000081d0540204082c9040729004800c3c03043c035180034014072120b4400902d080104000ea90081006400540341e9840014545551a0201070032a03114606c49884220b6840810083c09508140e090007400c5d4000a801010030304d5000540354001400741c0444000301c0c00000e04801c5040200c1c2e1304103a442c1160b000742400c482400795460001e482402c1c803410344001703440c14034201c50059140c4441d06031200c3c03580809503a0368460b0381c0347c04504186280f00d2402426103540d40c1d0b01905820082484150b0384d01c04e14003034101d41045180e00103501039070034441804030110700311265010401100b4030028040040c0e425030006040200d040101e488408120f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 107593956 1250 107592706 107592731
    0x60f150807140307030b040812150f03070609091e0e15060a030b040803061206010609050f0d030906080c0915180d080406030e030c010e010b10020604020d080f0d 71
    0x600400e8815000c11035140c942d6948614501c03802921406405422842041001842e461051134000f03110740b0b00182403040054145c80200402c0f1143c0c81c1f4202800301c41c103054188411086010881070b00980103c60410a0190001c401c81c441c10580c10741d5005a000100781b00e2418401c10040740070144101c6920200c09941d89182c0e60201544511080c04101503240020f581c0044030f03401850b0031320a030b45e00c0c4c0f118405a00001d03da560407104925102c006584140a01e03400381c011307500c51300303074540c1002e05010f401100c551903540241d420301d29250101c3e03005030000c41103842c0307450b20541541c0c40f0308600b8243e02400310859001400098030840b0380c0c11420107410741412845034018190504000c0044400c0e20000181a00504001c144141442504a9401c019410341201c0c6007110180465086070252030078048903075503603801440a440c10b030007140031210540c070003407255003455000242c815890f0031008243c00300018205942a0200007540c100300e603206010801a5407541d03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 107595206 1250 107593956 107593991
    0xb04060f0609120f0201121409010e07080105090318031203070201050a0e010209100e0105091e190b0414010314040c030c150e0f0103110313050d050c1009060f 70
    0x5074201241d0707900e10100d240030301071a007415040d4020140c55412505900192041d0401004076008103407038510718103031a080a0f480ca400380558100004400c50903819003810040190400101e5074102003d21000d04d00c0042502d0200d410100c12404080c00f120000717140c03010801c5040072210021040025454040d0b004c20710034a40600c4c280107034500d00a41508034032900b031003141e01c0043c41c518810070381e11980d2002c450403018145640703000507a07000110744025a0805940000302005800f070507003019200300c2070191000c400b00600750b040c4049181503005501540320700002c2c0c0381d140c1d07000e6880391304080da29441203820900c01e8105414200b1041895001c183c40701941d900d0300141c030f0300ba404e0503620003400342d030386024441d09000e04004241c5002d003805410036846030720141201091034000e50007501026484031080805141150038811f2a030742c0f110034024140250305078088041199060301c0c444900005020078103280c40c1c0010041d0244200c1e03690716280c050703900900d108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 107596456 1250 107595206 107595209
    0x60307030b0408190c0302030a0309061d0f010f180b09070f0602210901020309060c07150c06060504050103110907030e07090605011103040303050f0d020412030c11030c1f030b04060f 80
    0x1101d00390803268040009640300d0b003805c0710003030042e4010050000807905c41d03071101c90340c90b2150b032000c0759410500c40c51074400f220000b00c02c031180e0046e4a078001e420000348901840c0d030829130000d00155001440c40714081001e110041c012000324000103e00081c14001400905007180c0d0f644500c503100c00b0025516550266190030201c2040741e8132113021070181c190740c003126050380114502a45903040c00425048842603884a12444c24007180304100010200740c0442d0a5a9001114295060401c1030b208541d0005008030300c0c10b8014000300c0c1c001c028028a154066810717803040c0c0c4400004400510590f40901c2090103070010106413100c9a4101c28101c6d11b0990341c464a05a20350890b03600c030320a03440000c001c1681001814003801c0650054904102110307001814146d481c11500703500c0404000480024040c401034000308500c1c134105461400c4240c00412030481d007400400c031345107a20b4400807004d41c8590354052140380709822a2014807400b4005010007a5140d0819105d258076 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 107597706 1250 107596456 107596477
    0x5160b040c080606090103111002030c03070b0708100e070c02030a05060403051e090d06092a03020406210602090a080a050102030114220b0f180403020616080f060307030b0408 77
    0xf03040100e040c615294036043d050326040903050050000200070040c4502c4000a440f065000a115030150002c09201520f0058060b030503801d00c070315185c0300007012030744014501d1404003160340701800055440048150b1120090a1600442d441400003d281149000005202d4810381040000709688071028040150301c410480000800500002a1030b0107184111034210302003100c40c00c0031400c81c3d04903503da02d00420401d0f0116102c4012621180b03140c040790b04d10004440020011403d11f40300d000001c04200759190f41900065600e100d90100c1c04a029081c2600403809003a542d0b03e2010010040c000307401125400f20040c81c08078040c0d042485010b80d05100c400340a032040c00c003d10700020010303503915800d9541c5c4000d03010a00500988c910f450b0061004405101b654456585100240070a00d00301c035090319203881c000746000002072030f252048901e60b550004941d00586941c0d080924010304c15015a240c5000c2468803030954400b8004000c02c0090000b4040883d0045c00801417 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 107598956 1250 107597706 107597713
    0x20d050a051c1b021810030c0504020306010e01110c06211003021f0e040c0507050c0f0a0302040207140a030f0207080d050301030b0a0e0f240f040305160b040c08 71
    0x788a0052940040b802010000c140c0c50040c00841260702d070a00140d06100503c0800b074038085021580100c4012201d44499402400702882481180300d1440004c2000b01c90946ca50318144000030086038082400d0b0b4180f1411800350008031409100501c10145c01500b8151902201810014210301e4800401c940241c5000032a1400d0780400030202600d0300500511100da0252104100102412450104024510303007940215940c074024a02c070340c1c18a0761415210541c60030200d04005502c28030724072501a64000318102c7d11042808011207404540c0142c403600f043c00e080d407801c4200b5044030614003c03520f0b40020503402000c0005000303074681c216007405448412156941421580a074045141400100001140c5080700f0b0fa0242d1039140214048142070b04840c60503020b541d440c00e4a800c1078856003c00c08196212480c00794000040c200b403410b04001c480007002c400351014040001c0052140b1540c00e019900454a075802200d01c920362605003022501070181703005d800d03001c1c00f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 107600206 1250 107598956 107598973
    0x13120c060608030a080402060a03090b1602100506031b0420040806010605040302010203030406050901090b01260703020d02011b170306120f0601091d071401020c0d0803070305040f020d050a05 84
    0xc0b40041603500b071800c541c4a507813903500c2d10340810000d50414100c003810980c45078445400241c88001060040c040c44160b0f07903001d440e070100a410a50325181d40c480c0c0910300010044155800075181c00e5003509841c04481c00503602c800f00c3c0c0640403c40f40f080d1001d419030080f00c4840900300041003100c01040c1a10100e0341c907030404841034401c81c80702900613881440854007007401c5070302c01d0f41c0201e400400001c14100c0d035501c1c420881c400341e10040c551f0b250202401d40c15803540f0b1440f481c035811170010304510780c01c550002c1e4008001404c061304010100099010011aa2822180c036a03000300c074040512142841d07102407a4000c40d00e0f1406603280340c1650b8546540080c45003401c0f00c100c07000d810140c1c01c14021a0050038174008007100100d040701d04c6407060304144a02320150080080c2e8103248500320002a14040400b90382900504081a0100c00b003880d44c1c1c162500100f1a1401142c640c541c1d08150818580d01c8002962100030314610300101b00c000649110300d18850026a201c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 107601456 1250 107600206 107600219
    0x1f170106080303090a02010305060402040e040303050f01080c21030f04090b0415030f0f110d0303020301050a081606030f0603060e030a03050f0c0d1806060e0f09032113120c0606 78
    0x3d01003034500e141c865218800081c0150302982240394460070103403005007040d554444134600c3c14400d44082e00801d07942e03018800c01650394084140508141002010b250041201107107500c4035015460307081401c2035550030845a41401100c400e202ca200d21242c6031500c1e546040010400b074904140300c2d500c0d12100390f00038100f11011008581d0088245001300403a40c0701e10351403080300401103c4503501c0b141c2107071282c1d680d0134a00201c1c84c003e6800588079030401051044030585900002410b902140c1c801605440100401e02034a02c03c0c80c011601102e8400503502602c03081c1c2005000b070f400d00d100914080d5000015020141940d074090044c0e48542d00011400c000644180102140820182d00421041d4100105440c0c400c0c120108015841e2100b004440c840d03001150303e01a1007041c429001071000f00c280d0040c1000014602d04a00301258101c1c407466080740400f12140c0400050310010900070f541c030301e1078200c60420480141c01c44010021b07524241c00302d0b0709614104001c03400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 107602706 1250 107601456 107601463
    0x4050708101518090605130b0c03040807020d030e030304090207030806010915031a04050906010812090901060c02010c061508010f140109110403050313090e030903060f1f17010608 79
    0x486103100e5008400b181007214148107040c64240c1c4425951300c80c00c1800c0000e060303105a6200740c41040401560f40c100745401410300034060505050440c0501c14040070825040440e00803a5040702c0c0c00b44284524038041c0d03a0740001d0082140d050002080001741c400884e001050514030a688000a658406006545078001c0380210444008190b82c0500030354081c0e44001c0029409c0e480811040ba024400a026034108850420103074010500400c1b4400c010040955401162034020b801c00361030b0408a0344188052142400b04604004218150b9000d100c80d20b038100c0d00201c040c0040180ca809040c240c0c500c2d44100c1410358a0442c0c01c0c0c00042c1e041c41489070344a096188a03c42d6440c04c4088409048107500c0e03c000002c08200010008004000401c6c50b500c0812000701c015141c043c0c420111071414000507865001045600d000c1c0d900030500a5000e00864400d4626443e480c0c9501c03205021040001c8074101245004540d520701c41081c00c1400b03400398021b100ba1a02c6100040c2c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 107603956 1250 107602706 107602721
    0x54010309050a02060c0718090c050d081206040207060c020a020a051504030b09010e0a0c050f0909032b020c0c091e1317040303081509070203040b0708070b0405070810 73
    0x10707a0400740d00c180040c6469030050510988172022a880c580d00c40742a800e000601090591074140d845e0556820440b504000304000d01c412540140e164000e52180311042c400c80404440f885c0003080001e0320382c1d8495041d244900d420000411800e184608060750b070741607059050b40f04464801000503c1d06e07104640c0c0717542001d10802641070a245d95101c4013078000c06000308007075540340c0490f505000002c201543c0880c1c042c0106540181c505801d00c412020b60140440c041d10640781000345406000044400210b002692032001e01000760170024001e44200300e141501c5d000080780282d6540009101e1010380341100c448031980c480c84000803210a0700b50003004007402280c00541c2140a89041e5a0918001e102040516880c00c2801d4010f43c460b40089000c19410018405800d40e04550106000c030183d0b400c000c9400d20110280d42c9015900c0340319010200040c812040210305400d603030103680e01650348d0801d030070300e442c4c0703140c840c4142d0166080310701c0381c4485401000d4640c0207801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 107605206 1250 107603956 107603963
    0x1103040b0417100b01141e120121020d020d0c050603130309080a020109032d0308011e0f090c03020c060901021c061412030c070b0a022154010309 64
    0x40181d000c50070f00140790800c0102c401f484106902c1c1c0c6604030401001041c9035550100315651540c10f0205110f070711121300c441161030695440b4000016115080000c8040d40c045400480200303041c5841102c80c042500b1064009002009114002074100c0d0132a031158440e0701c0b019a0183c8038a9100c0c4c1d80c044a00029002074001034003040861081c00204e188600366940f81952a500c800403611240302c17070682180041c03c54401044021209000506600c9011503800da485107800e181e520f03d91850b00400c014540c0d50382c2c018610794000d6044900011a800a0303c0d1186810350f50507000350840902d103194201c841b400303892000300d030748200d609403401d02e031015034841403d03414005840d03080403403280984002c01980b01640401c105260050201200d1581d540710403240081c28003079080007401c285a1454072005600003450259071205208894822004412000e0503116580c1c0618401d8400382c003c2405404109083e40030007100030b404002140610102c00446c100c0b541c3c404003a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 107606456 1250 107605206 107605217
    0x10f02031c020702060d050702100b0907140c010603140607180e040605041103010e070612140109180c0e010f05120606040b04020910050405030f0c0901061103040b0417100b01 77
    0xc4400c051a0b02034803a00340003030119804e1280007170491080303407015118440941e201e41c40e8000700300346e40d0213503184011041d1003800309030070104030160040c581030004910050020444030034004007540034200460300700140c0b140d0200030249050300c0307050580c4d940d80000c2c0040c1000e614204618005022683e07102001c100b00e9076152921401071002074400c03220040300c1c402c41060365801340207440b00c4000341000350500d5480c2040180c41c6201800150740c0c5e40b820100c1090101804580660440c0c2e4484408500f2944800300384001c0c1c044004001c001c0c440324200481e03040700340d10070b0f14182d401c2004445070041d25034040195070459071003045220f50058002908908003508041c0f64444080c1000d4203000c41c440000d92901780e00048100001d00114040107540b034104418588000f4140240c82c1c401c05110208500703803014081c142c00c2c00302da8500006129807c004590040000e10007446c2c0b5903440308244c0400340d012520889c1c080c8101e44003500411540d02c41d0000703400050310b84 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 107607706 1250 107606456 107606497
    0x601080a030807051b03030601080a0e0703140a0b040b01060206070302071101122007150b10050c070b0a05031f0609050f030102091002010b0307060e0a2d03030e010f0203 75
    0xc0b60014002801c54003041014000480140f484074880c221194039000036544a1402000062485030000c2c03400c0304540c100201c1c24442d5001084100541c0d42020615240b280030f10482032402407181ca0060440050008103c03e0100c0203592505a507050f90075600981c441450480030b84c003846d02c010306140742e03021070030001d5800b0302c248450600e000140828003641a895400340000c0c451400d02d4500c10010782c0358100001013132072224281c079403081042a501030402052200c0c8958269030144040011500103181c400c01c0500001c05a81860961390b60203844010300c20b800c16526210514410b074405403102107283d000d40250340203542c0e48100d99103010100311040409500d000d80656080001c000701c0d4407000c0704c2615a4120740c001040001d8002c0030725142c00c905074054801c01c18455282c5404d0364916802030200ca981030b0443c1c00c046400756160010501e50034003141d084688540000801da000900880003440903240e003081d80204040982c0c591107410030342c41158145409 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 107608956 1250 107607706 107607713
    0x1030203100209042009130e0d0e060c07032103050403020d0e121204030b130302121b06151e0a030f050111070c0e100b032a0403080c010e0601080a 65
    0xb030900b1220003030000c20718070301c050f84030304803804035114100c051400069000005d09094240c80c2c003620b00c8510400c00b0302c1da0400b4590b09e50080034075030020400d070250984070a985503020368404641e210151203100f0743c0c902d003210138040080040c052640003850f10480c41806231203284c1c400c3c0d42580140c40c07912a800c0007100c841c014201825801000c0400d10b0700c01c0c020400044c070403100c860103030b2030b1b9903829400d0502d145c0c0c4000344880400c6050004000000343d000c0340e1504100900d1411a440e4095403d1440f43d00c680300a00e00c1c083c2c4104802c0080f10400080003043c8190700303855010849614650481c100c01c1e07000592070704510026030420000d80359004020505014200000c1d040c0d441c141e02e103034254004442505c001080c0740f020300c01024289481500841d0442809003e245070010481c102c0c00001c180300120040a0340780c0f03003641d80340a82034207400540240c13241d0b42c82c1c99140c03016464020203a28500c96190010f2503c2074400000e44038140d500800003000d1025150381c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 107610206 1250 107608956 107608961
    0x20a020d03090b04081b04150e0709030f0b0402150c2e15080d0503010608040209100810020d0e0a050c060706020903010203010f091401060503011412060c040e010803030103020310 79
    0x110407010000004000140000c5600241c00075103507402c003404414040c5501c01c025081000241072080d85001c12103424030740c0242e0a40110380400c416241c8595400d0f40070740704040f0f113078009003109040d40081001c1003881f58206210354402c4400ea01c810301420040a00c1d4000c801c2000313150351141000c2000140503c0402d8840c02500f1020b00941000c00004000d845104c010001030014000e01031000550038885444090740c83e00d0030314255890240d00802801001d44060700401707011000c210b084030315560400241017103108599608945400301c42c029030042c000800b00524004408014217004100400800d801c1401405110300c40ca040080703070b9010f151b084409a81c00c0110f110203440a001841c020304c1410a598106481c240e00c003802c3e41c0e841e4480c0000680200c2c014001150440705407815601c1c8103801000c0003e462000c5011842d80850140d26441050700304a142103200c40140203075a203440e41801e0690380d031500a07507240401e00000703605401010358400c50000c1503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 107611456 1250 107610206 107610229
    0xf060207021804121b2a06020105090c0f060903060709090e0601050303030406050c19020a0b09030a09061206031509021011030f2104030c060c05040b040b030615191b0201020a02 78
    0xc0c00c000401c20a03551b42000741c03000380300f000d451248a141d00c2594694000401001065640000c0c00703549890850300742c86404002d00385124a004542c0162152520015240303e100702030100c410324204150040c01e1940706100c0c071801f00d410480e1032004110f02080890480304040c00440c2541c4a40d81c071131015090040c070f460034011061101c0faa4400c540e00c1450307442e41846c0c001d00640001810300d01500b07400186014901c0c0d10400c80b8420302640a03004c3c601325040e52030300e140490841c1c0c8060000c1d00c0d0f56440601a11380e038220550001c0362560000f0021842121404403107100e40c07a007900d8101d100c05821407960020f0018071410010b08004020900807441c0700f02c5003808a80e0040c8181900f617400307400141100d1008030810485204040303400c44d0070300b005400d01c1d2030920759141622960092081d10704000c13002c91481d1700d6a0300c3c850110321020034665114060055501200c0354240c4e1030134005220001005000041d014032a81c030141c069010f400310f90301c19024440b030413402 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 107612706 1250 107611456 107611487
    0x5040311041103040c060807080105090403080403020304090213151707080a2d0e010b06091302090d200901050612060a0e16080603070503150c070f06020702180412 72
    0x1181c460140100b10440118462403203003920301d61241c00c1c000020500c8200400140a000803880144055580c0c030241c00c0c0c0c02a07042c034110590359281d203030481c00c5005650294141c02e00100710b1000007099500c04034143e50440e0a00c00c2c1d45031743c5079012102100e811600e000c06d40441c001003580706e84125a05540524800e102040024941c048c03ca201e1105c000000c120f11b40415852100554500a4111800d41c00c070090103208410710004001d4800d94070f2003441a804030b10000d225158a0301603404c503040080040d9030000060601c024a40b440d43c030300442181c0c0001912101d442c200c00124181ca0010346030030b0802d14041100c0400c0003000d4100390780203031040c070002a00380400c100715200c0c2038054180501e81c418244041c00078000503040368480d40112400303005a450000310004900c1c259200043c450715801a07115241c4550b82d00070740162080c0002c0701c00e02a1607001009501d200340c0c1d80c03241841035440754500a4005540c010140003008040160310f500c41c1c130485055242 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 107613956 1250 107612706 107612711
    0x260a051303020603191503050c0607030309120c051014060f0f030d1e020601031205030718030b0f010819030509010909021602040e1501050d030e040e06100602010b010504031104 78
    0xc90b900080c565400840b9000d914580a440c1003a0051250180e4a00c00c0c20800070540c01504681d01d00340c07a000710402480c0150004501300d021f05200345c20814503507411001c003c0100002c1c5400402501d85040c0c20703580351017280c008c01ea6a24481c8034a205417840102e200c0c17004d031103210401c035100904a000e16485101c0e152040340ba0742c0e05210407144025151100d10000d540c050400c0259410032090500350b4102030700420110f1010360078115821018944103641ea40d4008081d81d0f0340c2245500305d127081ca0b80a102104200c001c0e503001c1d00945901c040e00d01160390b44d010441d038603065904080e0070f09900000d20300000f03000c0c801401d49107505050800c2004c0d00c50041c0401c0742c000802285000d00200b1a10007541041d224028502003048090888104800940d0103464818420280038541702c4c0341c1d51050520400450740340850041062045d105c4c00d001031640c44000307403036920f880301580c4000500640144102d400811040c1c44d124145417131a00c5d82080c0c601c490f2a056001034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 107615206 1250 107613956 107613959
    0xf030206090414070201060603150b16080418050411090403051b070801150e06010201020703091802040b0313020f0a150806040204030807050703050d0903020a0504050603010f0f0603260a0513 84
    0x1d08400f00c3c140f140301554000a92180341c180010306483c03203448080c110030358030b00c414402d1035003039004c42c1e040c107034008618801c0c4001c905c3c0c40b21840c0b0960340f0100310a058000020200c481d00c4d003005000340c4c09a80c030b800381c00456004014081c81d094a000b00490b10400055914141654028240c0f054440c11381e101d0507601c034019400d64044180c24000303000c5421040c860301c070100c9005030f00003800384001c60405030700d69809272040c081030107060760717040c610240355920030050340482c0d020b081003481981d2241015038004204d8840582c049204150312203002d18241803180d200d0b400c44040207003140300802101000c0e500d03a074001d0020b0f500700703808010200100c0c004c0c0004100b081d1182000740740d0360340b450411301c0c1845024165a0104078030f0110800160b55140d2010b01695021600040d444c0c84017000030740140b003080003a010381410054261030075402d5034071420480f801a415403441d400300b0800080d02071440c0e030711141d4091080c890108014490005000700b031071007503051840d41c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 107616456 1250 107615206 107615231
    0xf010201090c170609150118020405100e032a040c110712050d02010b011403130b040606050f03120301090c020a061406100c0203070e0a140a1d06010f0302060904 71
    0x1281a0803002605074003008800210400304480c0d54420108009004a0340e50120030204405061180c40c00405e120340d010405107105a0465008020080640b10510400ce00240000f5032641c0700e14440e0003050302448559407207822000c010800180d0713060803003c68908001c01080d40481002c10869a415a01420041040440060041c141c0202c0ca81922454007074940032044030300c5011641880082000c07640c02c1681d007280c481005091980380c2d0307203c50306a502d08540540c0a0003502e82082801700344005070f4400e2040da1425610005048816000d040d03079000c03c00b40300c02c100c150130001000500f00592211456402502c10354650780f143d85c8980d8144d410940710088884211001e00089103040400c0c0c00c0c0d81d01245c100440341120640001c1e40303c2000c0e1041d034041c8030143e0b0004441710503942c40181211a001480f42c0e5130305110041c04000c002e50742c0030400c060300304145d40030003d100040450481c0c2c420b511100b0424216401c0c80401d400501056402c26142d25000111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 107617706 1250 107616456 107616473
    0x80718080a050307020306011e031716030e01020607030c0804110d0203030a030f180f23010f05091e03040b0d110c0a02010207050402031506071e0c18020a0c020f01020109 75
    0x1d090050380196250111070041504262045c0c2c030540c103405855800c80c2c12441d031052010112500581e4a508060f04011301d41068440d04000d004591320f4034454501705501706803841001c050130b900f1030701182e90b40d0b8405e07022500342262810128400000060000d008040400782091004c0c0182c0500000d55010070300d9a00030f1034100c1c0119813100e44d902c400030410302c1030803441905d00b0802c00324040d684d200c0054002d00c0f001b0280503540004a80c868a1894000300052980140c0081000000440300b910007040300b83c90701000b038000c4a800d0a03400000c84500788420840c1805149442d1406003052896440350400700c00140d102e0400345604030400780a880e08081c07440c050706417440e1501c0024242034054211a03c60307441401130140c0e040d210069211100e6013135650702c0d51000e0074248210300d92403910300d5403401c581c100d807400e04209007202414122551034400c1c08141410140c003409030300aa640c1900012111039000002d440c02203140001e40406000008480c1e030360345c44100301c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 107618956 1250 107617706 107617723
    0x100507080906103f0c090b100806010f0201090b0c041d010510081b0d050103050c040c02060a0902030709050108281106030a020d0c050a0f020304050a030b270105010609051008071808 80
    0x40702c1a00d000c04008810050003641f85003803007203032010140d661549000c3c00c3c0c00400b600c018104070641e0082d04100e8000d600040400350000000d010034980501d181c01940d2281c000d02c4c400e600402242408107a8500308981640c8004190b0404640d180200710740b1110001c0c2401001c803000c1c0c900301030104050008000d03030000804081030315811800c1562a0a61441415010314034041c00109103d6010540c550001c40314900802e240d44140002498100150000b420780fa00c1c00000080d0640c0c00580c29001c2d4900c007912190100d981074038104d01d602d25400152445078029021006442c050004503405004014018201841d0700103040c01c613032904203040d000c05c10000319a2400c0b504003494801900749480110324113030610000c10203120162000512520815010490100303050041e0392561045603006001d80500c01c140da40a04003c0c481c0c40049152114041507a04080f200c1c54801100e54494400d50b1701c61600858103440380340805403541d03080c00000701d80a40240000703807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 107620206 1250 107618956 107618963
    0x18070e010306090b06060306091503010608100207050d05030108030706050c0d090f03080c04030804050906150d09020108060604150c080c07090b15090d0f0203100507080906103f 78
    0x1070440002d04d05092140f402a0001e48501028401c01029907681c0780e203181c1c08180c24020440c103062150120b070141034948c0240d0054001d40001c040420065030144c010240500e0840c0c0d403010340c0142c15038640c4820302440e402604100814000716250780c00032038120b034101d0005032074080c010521034203d401a50084030500b031004c40c484207260703222421a41021400500c070340390514542d00c5880c00d1085124050184040e1000284990f542140390081781e80c0304c05016990340c2e004c0b05a14010000d1030700c100e0215003c07201042d85402c01c00305603000d89500c03c285110803100079400380c910890480c81261f40e207004210300d805120341400003600800700d403140862040f48000401c030703d0441c0e00c034141c2e03423004003800902060b507200118112120b8107d680f0142441060001ca0b0402071440c400100a40c10b2030240600740d03901c504401d01c038a03086820344841d902c80c0f28401a0145152040c00da400742c605114562000441070070030304607030015105049540c0340400050003003209900070b9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 107621456 1250 107620206 107620211
    0x25030c08010c0809010c0f1d09250e0d14070302040218041a01050a230f09040b030607140901030e07060206070f051e030901090c0b09010201061d18070e010306 70
    0x100020ba8005110b03e07040484a4000e2048469490005042d802900c0d00c00702045565041483d88003e0081c0d01440b01c100545888050b150842c01c80040448100751018542480e102441100d4400d06d403c0c40068030003041303403403080d505444810303030281a00180645400386040000c0140c2c1e076840207210300007040280e44441c0001c00c04110442c1c914803d801c1241040c6502010b03070ba80d0000880e0410041070030440b400603c426a200500000d00402440d000000100415066200c0c1e01501324034070100ca00388005044d107800c3c90349a04061f038030308004c1030740742c6006036001010f00d000d002035010614000540e600110304040c64950b96074802009a04070000303001005500111180043d00103040c1140740801c14404404a26400c400162000740c002c4003140403101c0a41100d8601900309054540c0702e071703c0d5050b00362580e12807241103001d0341c6030005c00a0743d000c054900c00600b1400f505411107c0c1c0d51102c0c1e102c441c1e08a48250700640c0a41e08000c1488858100801d010b5030045000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 107622706 1250 107621456 107621471
    0x915021303020d060b032d060907090507050c03040801050a11161101110304030c030c05090f01090203100312030f0f060f0509180604030519050306060d0902040f09031101110c25030c0801 82
    0x44900c7e0b00c482245a5540e0000001c01416000024094048450038000003601d562006400c032604d000302801c0300c0c864003000a0003d50070700c05401c07107030048180b080204210f82c019001ca104a102c0d250100310700d440f45100241c081010740b81018040703030307040c10400c0600900410050440c0c1c015041102c1c205c60111040c024045004024809404141c5945040d0b0805901d446441d000500c00c0003003164000001034001407904204100640d800120018040c0610030054058110400d10000c0d4610f8103103d1030080d04540100400c85440c10b0301000c140b420b11080c40740c43d0000030030f100a007402c0d08090080311101080051302c52802130b03903150b80b0342803091032000d80108450030941c10403209005004103540e81400301e84011003100070005031084a440807402410b500001d03200c40a16084c0c0c6003051503000b909180c840718504000300080410004a040d450052010318370159100c03490bc190111034041aa40904101098020b43e042d41d0f640c074500580705503008011701d03944035940d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 107623956 1250 107622706 107622763
    0x1503090601090c120908070b0a0b01082512020702060a090603050a060617090f030c031e070f02010c0602090319110906010203032e06030915021303020d060b03 70
    0x24098000344a007402541c2d1046001071190740d024400041c03c80d5611560010000c094040b1f40700c1c194000305c14802c902c0c1103800d003030007001d61010303113404102c50000141c046002c1d4000f01c404400034108a110b00c000c4444200c5061000c0c1040d5400d640e820841c07200175a440d5009403480e10440e0b170700c41042c9800e1240c0103082d038002400800d1400e0905c04144100c03a00440c4080d000d1443c001c40398495078030540801c2c0f030b10407446001c00e410702000651070340c104c0011004091a6007203d10140e40b0328200d2014039658420710001812a010800b42940158813841078400e6007809000e015003400060000242014050158404828a240b4280042007a20001d0210b0b0100071550a4880d18054002135101d200003070064416142d090a0010600c50b000ca00513080355a801c188115541c4a842c042d000384107078941610040003a604a503007004003802106d00b00320f14001c01c40703201403035035003802680c1003038039002c035451038941100c0d25094804200e5402d41c0941813002e101160318170781c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 107625206 1250 107623956 107623963
    0x4090f020301050a0f050607080306010c0614010f0503120d09021f02010b0a0506120105010f050d05041a0f100315060801180204060504020708090f010309020d0302030d1503030e01030911150309 85
    0x1e1000545c0b6402c00000c001c00d82e9110250b030004c64000c41080d90380c2c1e5443d00104c80104d81c0c901c0c000c0c4201c1c42c0403860084401800845c07416240032250586215031034034109569955003480d020031880d010005681d5001c00e83e00040c00c080e00c050f000000001728450079131502e075100d242140c01030b0f65440781d640703551401d045440000d000a035000380c902012216010309142050003203038180319025039100c981c40d2103801220300840222104202c58101868800e0661000812010400201c480402c09064088402174012000d0b00041d91815180d903440364040003050b501c4c1c6440707030b50f42c50f000102985c0c00e0081000110380c00e68002c0c09010140704100403074210703800c03040c000c51041c0b146000203a14032088801c40c00007200e080851401d8000101c010341b540d4074000f900040030b800b2400030982c000001d8400c03049403420501c17401508007100d5044403090700c0040c001810075400031080b940281e208509003400f980403441140e0300c0304080b13000100c410002c1e8001c0c0c00d0020030055a4401032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 107626456 1250 107625206 107625209
    0xe0601030b120a030f0e030106030c0314030a021b010201060b03010605070303060605190806040905030c03130e0c07141e0d17010b09061605100615080105031e010204090f020301050a 80
    0x21950104040c00c42c1c2909030741d580344208001e0034050700000c0030325a01e00541e035401700c00c400140203201d540d4903880d1500c0756001c107100c121004041c2010000c0300e040080140c46c01002a54000c05408020f81c1111410240703143d152410340d566a5004507080395541c0055029044945030259039a00b189001000c68042d50310010800c102400801603400c440c55416103030f02c0143c41c0540154550100140041024640081843c0300008058a03c2600403020380b500100d0654414191503807a00b014401900c22694105910810010f580c0069620514144e001d40700e0011204074040d20030f078003243c090824280f200070b0741c0401078449074130b40c4c0000f0704540c8050102e1080985d52401140318140e0044081c4184179800c0410300301050381c1e10131084000703a90007004484500d52010f280030300800c0c13070303014800c0340d200010f103010105805420010704840010f401000039103180b441030011001c90119480e85550204000070301d0b081c3c0c6000300c42e800307036001c10016039035403501301005542c0615 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 107627706 1250 107626456 107626459
    0xb030d0206012403110c0a0201110601030203100f020c061513020c0601031e0602030a140601020c010206071b0b040605070201050708090c01180e0414010c0e0a03110303130e0601030b 80
    0x8240140f01d0703d00d89690b00720301c0f000548107002c5007104446080c0d004c0c008140040c01ca050020a100740f0801001402d0fa814034005c1c1c840340c103038880b42c80c00765031140d009000c042e4142d4050220845a100160f02c0141c80340c0f0441801801c010400c51031509040081d120300d054191a40f02d001c03240e14010624001c2c810451808500d84206801d80da41c0710b00052001030481c4820b580000b00000516964100955010004542d01c0c900188100010b0191031501400340000c3e000007000d55000055003022803130141c00070003035940e603001c0840304d0180c0c07462990300603018180c03944000340c403030213032680218030031440420380c1e10f040c1c80c00900b112001001c2800300500c000c00d0050303026012842b102c10310000e1074000400400780c60b140e00050700c203920003e91420506c0c2003205209105010600015044000340845110b051f000c0b203181c562400c0c42d0760701891906081000410809100012a4003c1e0940341042c51606030058030820a60000d84800c0a007002c00680b9a898441d03000c161a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 107628956 1250 107627706 107627713
    0x20706020f16290316020d030b06030615040f0303030203040b070c0c090203040305090d060b0411040b0d05040f05010915050106080f041103120d090302120405090415110d0b030d02 79
    0xe0300c0c9408904680e5204000d28401e007900f12280d02203000458101c01c010400803250f80b42840350300764511010110101c1c005005405c0c0451600c3c2c030a00442c0241d05000b0006411500c960f01000b0701c8031024001d00010200800000403440f01200d020802580641c03401610391810303040400140800a0840c030800803203140e00d0340080c0e48a0803070002d0300c03245640161241ea52b86801d88a03403151071089640000ea42c0c500c8810800303550092110f8031410f69003445034844840040c0030901685c064040c421005010312490544260310041d4844d01607540311440540c0ba49400b400c5407a414002d03a40303201c9500380c00c821483e8601078140140061b00e408082860440b0700824030107000341c8000c0020001041c90744070399804103c540040fa051404941c0d4407120744000380001c155120b001c40250054600304000a10001c0c00d60707007240c8014001041980e901d075640c00010b28024450701603140d8038941c0305003003034010020b840c14090b41540041c0501170001010725100404144c0c41c00c41d403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 107630206 1250 107628956 107628973
    0x80706032415090f1503140606032a030c070b0c070503160201030e15011401050403050c0906030a080f0904060e0402010c0219050d0b0703060609080a0b0c0910020706020f 75
    0xa00444000085030818000394024241d146011141c000e071590100c2c45504c000c800106000a6260444600943c40d032401c0148040141c041c01010204442065010741c0500c0002c40080070100251600c0780169407205c0c4000c81403606080540080c0c440039003103080403814008001420403e50f8101402c40301c4641031110507901c07142e4038441c0e01060b03401003101c2c000410440e40284c2081818040e6002503980d0700a0040c42d2114001c824445d070030486104803203c40855006000b00d40580b50048058030380340445a081c00010840540305a0701449089405004207621001030426140f017000c0c166558a220020807054900a8011000050010081c040186c2c0c01c03400c1e8001095040d10541c0048070302c520032102c54021640034640080640d450207041200008105115403002e8078100700180e00c69101321118955070055001d030394001c2c448880801c00c0c0c100e680d944020164030084c908070a00000c0750f06500d040c4600d0300540d200d01ca05120498040c400d1300c10282c1400014400f40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 107631456 1250 107630206 107630261
    0xa020a060206151e060304030e01020c12030405040203040c0b0c15060103050717220803040b180703080c030f0a05030a0b0616020909010b04020a0c03020c0301020f030a1e0608070603 80
    0x4100708005500c04d4800e0b030840303902200d0b20448109000b4006101d0368076450541000b6083d00034127030b0130038018040c1c05c01b4802c0500e002d8151038004041c0000840c1014180401d000c025030002d04183e40a01150100140300700c15032008144e00d20341311001d0055403603079080c401210080641a54141420241001500380c0e0143d08556019038202411506469801564079500c010080307030f4860743c0b103a040c80000d1150190055005074800d2501a80035074940a030508130040d8458078200580021030104007050b41c840142c00c1d0b0813201003d907441d11500c0709600310140d01580f90f14002c1030303021040000d078100c50710a68110540548503186080c1300401c0380c106400e00020000c1c8148610004101549001d41c001c0c00c00c100003034401c42d503940040c10041c0c14054000c0341100148038100149040f400c040c003d840c0400d881e14062401c6880c2c0c5601c0308041c0015203030651103046074404007410695140180d000a0038002c1c00303030030000c1c1010070081c182ca101e42d44200c180c0190303280141c0c40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 107632706 1250 107631456 107631481
    0x90615030f02122d13170a080f0a14270106030309090c12060b190c02010806010c1a040c080c040603200d05010c02071502010b010c020120010203090a020a060206 71
    0x1104484c8000015401000c1180182e000e0249120304a1110345040161107800311038200341c028011a0609400201404050660711800049400060101003c180416400000c40d6081404000c02180e031080403c400e4032155412562079130a800c00d40d008418459070380381c021260f03140c00341c001c3c4111406d41d00c0c0a014a02ea40c4144007110780c0d1031110b9041544507030090325140104880900c4600da480021105a03080600303455040c1d0030956030ba070020790065020114156041c0c44100065403904015501c2043d02c000c25140c94141ca0240044121303288001e52045105281d0a818036013081c801a10301512000301a02aa15140051000c6102007804180d02d204590f580340c0d2380c8200c030002c580c2500c0c0c9808002d01e55800c01c101d4403216600450014103a54014070b80390401912404c0880c280c0e045d85240c80d001c03c40000c000030140d40306583e1850118014504480841d02081d416402c90f4403c03261507040e5045100403034110710f401b190300c40080006200600c680c0c10800c032200365 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 107633956 1250 107632706 107632711
    0x8060904030513050607060b01020c06030112060902300609150103080f0403050a0303020a0f03050402100804020f031504050609030c060f0405120301031529040e0106090615030f0212 80
    0x40c450049403e982e51022018444081c0a002d890252101142e00e450380180c05c880458602500a215540916003020020380b812035030500d60418591b0740d40d0725440e000740900c500998102881440b000400c2c049914000510800034626003400c000d105070582c180100a0144521600550714568041c0f10100b00c190649800c070180c1780e80c62041e405107800b544500d5100410310f02400726032006141c0c25030301900c181000e6880707031905400f8481c0100d08403a8200d0b0000c4d448841265189045449202060b5101c0e1000d04100c48404003400000d1a00c80c0c0c0c3c078003003404681d088040008020b801d00410785c1180d083c00007103051011102d100da403941c0f0b00a040400c0300080c0300000f024031204004154012809031016540d958481c20301c203007403201010b50300c10f20381d0600d403c1ca002e0400c881c03002c0303d038000c068108822108500d000c000240c22108000b00266403100e102183c402c0152090364010301884000740c2d20344e40010030240540f0754002aa50003207105120134214803400b07045059 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 107635206 1250 107633956 107633963
    0x80105061503060406030b010e070201180f1b05060f28020303131e15051503030a0315031b050907020114070c030507050d08010602010b0901180e070e0c130608060904 73
    0xe0b01ca90380d08010500a0416a10160040901c4400025202c000e04d1000d40a02c407960b00900501d6600b81d184040c68940103002400da0202c1c1039440b002ca8001041555407034840030403018400d943e200020340940005400f45258480003c0052003c0c13405054501d941c1184030782c034160f802008402944030300000380b0242d541048030070200200105008112404190651161380ca001d031410010701c41282c04a801d00001e1a260200d803a05024030280d00c1c5d041c600034010346c502444e03100104c000d80041041503c0e02e2180600c08400609810310b6012500c0c50000c00c1101103240c94100b000703811003c0c010a041d6407501c9107000100343e004585541c040c2c110709101c103610145241c02c84952041c42c0000d0060b0007407800c0e282127aa40010f0f2503040f110103500910411386050204404840b0078422070f42c000b40c0c016880f14003400f4541101605903480d00541c3c00703042d954a480011050115032104501c3c10020310080e039644501001d201030f15407454580468640000800d05410002d000603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 107636456 1250 107635206 107635249
    0x1e05040902030a050a061b051e09030309131407090308040b0304080d0c020a1b080304140d0b0103080909010e010308030703090203030d0e0a02040c05030603190501020f1c0608010506 80
    0x58056407001c001c00f4025a51100c200c4507036045c5414800014114140c520300b0510840ca41c0000c0c59100b0b00c2558428140d4a00a20b5416482e26030444981c1c030004010390103001c1031203200c100f80c1c1c900714903250700c0c3c032589404191110700c044c9460350088000c0c40c0c1070030302082e0030041c000300d091001901c05544152001c04e569840301d041a5403a4000c10b07030100b0015041040740110f071035001c99904c041c4cd204030107107124480c0d0ba081c845180d510034041c2c550310380e0080c002000700702c1b41280b0441e015000602090a4280070751a04185480b00744c00c1075824050001e41c42c68142002034240d030040241c0c44032000c4e5541903039900140c6110180c1010308040d250005001595400c0c0200c50120400070410496400032403401c64841aa00009a05c100c0c0ba1031740b081c1c80c05025604681c42034100034040c101c6203001c03000c00e081d40144400d0a5076150350900100c1c1400d0301c130000400c0c1c0040d4050380034a0b501c0703e2402c2502503e0b410b0704000c0315641008184000d0f6202c40701040c00808421410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 107637706 1250 107636456 107636471
    0x5040c0c1407091b11011a0d0c0504020406020319020d0c080702010306081c020c06210709080601060504031e150905030c152203080106080a1b181e0504 67
    0x1561800d00ca0f80c00a2262a241c098030303075001540304a0300c0701055125121101a20900fa01c0d803130813034101d501c00582c121148404c4030700d64a05208110000c80c0300310483c060040d141d44c0440c007241c02603003004015a000082841710745001e40d10585010707403244018020b45d450400010500910010020700484c808154141168045c1d08100d0140c0101012990048419a200b0503960000107100015028a00c440016030410004807205450621a40044030f40020312200b01c0c150b00424100c00c002e02c0b9400854003020900c0158000c19441c5c1c1c9858849082d424000c43c800c0140012031580c040c112030170000174800500b03500e200c1030046000102100355040582c15031041010112450143c02c1c0f010031071580e03014803140102c440010081c813010542800040f003504405003d00400c4403c80100451442040f13029170240c481c040106d040c0740100b004c07040e4504d10740319040100700000800a00b149203100e0a0004000c1c0d003580416a00d564050010150402e014407401345844588 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 107638956 1250 107637706 107637743
    0x61509010201091a07090902190e01020a0605130b0a09170901050702040509060403030e0601060212282304061407020103090b0c030103020406170c0d020a15030501080705040c0c 78
    0x202200c1500206071110583c0154411300340f41c1800c442d03076804251300750350200f0b280c8a03900c25a125a400c0c0f000000381c40801c00c6040e105005200d00075030462242040010019085010340d0380648100e07004040011001e18000301c1d110401001e00d1500c901d80f0309900c01281040b46080220030024205c00d80da5401100125014801e0780f01c047d402070b080c082406083c64002036098401d40c000d907000c102805a041c80b103911450b081c0725500069000d074508142c0c3c5883c0200900c2030403841d00a4640ca2000448035205000f911f5403054042400c110903130721104580040e142d011349081305c445160a00b89100071b0060007814845100d4413074085051021a40680d10041c80281c200200e003040303142c4400c05504960090004a00441c1030100005001c0350a90303040742c0e2a8020005080651098028030445080044091783e001c40e0b0310700300044200d060003100911400700d17074000c01c2541c1800310480c6003c032a58841e80c051498442c4514050780c0c0195007075003260344032400800000402c2c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 107640206 1250 107638956 107638961
    0x110a080a05040201110d0e0a0506040608010e06130e0a051015060c0807050708100b0a0e1306110d0b04061d1803040e011d06010306140d05100e06040218061509010201 73
    0x3040c0c031703442c0d2240000088442d0b40015840080e4801102c9081c240da40fa07005020351401217218130300c0801c180600600080340c3c0e05002076841800500300c4110340c0c0341c0d10483c4007961524200d0010b90f400100d510014000c05100d404190403903060240025580b006189002081e580704a40802803030640140c2000703406000c4030503031504481141c0d82192a001d032661148008200800400d1403c000401c2a00305204143e080f43d80d01c00c0504407958910442094014400e1403c54203243d0768405804406844006008029010500060041e42c9507060000b1a0460b4105c054404c04070404000004840c00d400c1ea400000d051202d0906403840c251305103580600d0b044900b0b501c44010020810420b11840a1140180d42041c526592240310056003102d800d03000303204000728410f8201000f801c0010588820900c10401c0341d14150120b5242c10481342449420032880d0094010300007036280000e102050450000003030711090500c5800500c240c8800100c444110742c001c0b46d2158168003e5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 107641456 1250 107640206 107640227
    0x2031c050c03130608010602010504030906110307020907030b01030b090408030a020a020307140a03120b01020604380a050c0a080402010315030b0f04030201050705070809090603070f030605010306110a080a05040201 94
    0x100100da4580080d0100c900f0389407003a0085000150580b000065245d205010340340c0100c0d01621049585030410600303c5000c8200c0d64100b01912003040348200584a015065201e12142c0d0381c0052500c07545000141901d4005c05020b210305914018800810304500413a900b0850300c020050b52400040c80582c11406007030000b4000b0321400803806d400c454040b8040c115284260380380442120ba0440c44400c8030a00c45078a4010782c810800540020b200c400b22488900360400c0a509900148041000544210410071003001c58081803000398045802507a400c11000140b10303040c1640c0c55401002c2150081c03000c0e04068030707002060944c0090602110142d0780080c051980b525104844284401d000d81d4110010744c40c00f070014100c0c40c030031004c1c1c504660344000c0c000e1615004904002080c0405408650715014000d00014081d0b26094020000c51284001181c4c540c0355090450480e039030008040c0040404000040c42d03a58040d00050744000001d80001d1540c96034001290004000b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 107642706 1250 107641456 107641477
    0x503040b0c0607032904021b010b040e01060b030408210903030f0f010b04030609060b0406121703010b04210501110c07050d050303040803090f01020708040312080402031c05 76
    0x90041241000a0010030000c512082100d420b40c907207480841c22a2851600c0401e0032070300c1980c14288405145141c43c0800c4001e001604000503540c2c4011081d000c109041c10b181c0d96020076404509080c0901c0d054076061200802c83c0900d0b00d082c4603203a04c0001c00081041c4000150f40840ea808459210441811202118018036000d021546ea80e4020385000350740c41050300029045160404485060300d280d40c0300c1d9030401c1d241d60b6a042c05803003084400c82c1c1c8103407a88080c3d00701703807114401c0d1002003048041030a524240d508103a40c3d503600c400103000d860442000103002208254049030700301c490800780103240801c5405400c1d191409068010850b509090303440010f8012200030b800c103140103d0a450b00150307244100408070340c3d4034a000b0f10750740082c400200030503880d8000c2c41c0d1283c040c00c02d86007408150040c9034226400280222040e000210381031051126081c50304003c1c50303860420000310304040d00003a90b140e001d42c01e0394821094032b10441e00800d10520581e060105c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 107643956 1250 107642706 107642713
    0x310150e180a06020405120606100e03030c010504080406110c1c03120c1d03060405060a090f1e030e04021e03060406030b0f150102150a15030b07020f0c0117010b1605 73
    0x11031600b42c01a40c01803080d50711487c032100781c40414210100d2854000c040003801820000e048000a50750504059482c6034540414440301010740801c0c000e01e131099114440c1c0710f03555030401501601e07800710500c2d215001e6000c2e1010341105e440c0c900c6107100c8148891106501086d00f898121421200c0751540d400c00c5040c00c0c0424140364008060342d5803440c2c4403641d505100603030010b1650b9010116030203400d0380c0c2326102041c5d4a00d12644402c1d04a4003071503407122510100d40340c155510604011341d100600020080c00103240d030010f030b4407044600480341940782000c824001031003c0c8c000748080d100340c0300c00030129a1941d0f03581c0c040300c02190b0100700200c0d43d2030400801105001c0884502c2c01800d29801c004001d0740c03000c281121040c0014a058851b91100d10305030b002000c0b104008001ea03a03542c0404404129649946481003010398010b1400030713007000728141010740e82254141440f0107035510801c1d0700443e0f100700781903031000d54650b610380e00510005001c5101441000d0700500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 107645206 1250 107643956 107643973
    0xa0204031509020f0d0b0c070809090c030915091e070909030507020301180b0a050a0612060213170a0305030a02040b0c0f19020f060304050c0901060c020310150e18 72
    0x1035030342d003080040d280210381d004416011201407048000c1920b00080000c81060000f40c0c44003e80301c09030501502801220342032002c804007085541105540c00038040e1400700400200c41d41c01c02499115154021200d03e4509040301c1055840950300d051442c0c0c0d41190854180b50340c070801066004101182d000d128035001800c000d003266011200682c0a9424801c81540c13400d26140380c0e80a090340404d603001e45654445d100c6000b8180641000c0c00541c54070300c00200044c4c603030003440c000f60141e00d0041e41c60b010400c0c100c1c81c2100c55407042550311842070402c4424103012564540044d0142002a076a5542c03400c2c00700244917640041c00c07a050b02260740b001d52100000c032010a48110000c44600258611340b11060043c0c2c2d00c00254461500010442c25007007200245420901c61411140042c0440c400100c181c1d409810142c006888032288a040d4075003002110501c1c149100c003000b2020300701c9862070451240740100101c440310034011540803500c0d94900c0d440d0020140030703200c403003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 107646456 1250 107645206 107645243
    0x403111807210608030417070306020307080a0b0a05100c0201030905070b0c15100605071505041b050d02030601030209040c0f03030e04060501030b030705130902060c0303070f05030f0c030a020403 86
    0x50300a00e800c80d449080c0d0030603005501ca00344104010b1380c04800c0150308145c034140c050f403100d18140340d1000650140c0b003000030008540340051070242d0522f8072071541d10303e800c019410480710607000d40780c45080034400030041600c0303401d40b0048014040c03402580750742d0580010703000b81001490041c00d902c07500d5000a1a2411000039000a0031030500b070301c51082c03041c146d01509102c10b46924002c034180d0380c0100081401100108021031050400e00d040b0040d8103151000c40300110381c260f0702130710b02c01c01440c80020b22081c110042c08080341c4d5850b899550740c0200e80d44110500009009607540c0c40070030300380302140350200020241c02c8035400700c6c01e8032860000c01c01207849104500941c100580480c00750701a00804d05010700240081007210700d0901004620502030826140e03c981c1e030030368a00980c55804c02480003000341c400544c0d8a0402000050460a0308407512042000034001e104050041200480d005414095255100d0300d498041c00c00902c5a42d0004041c2e00710340140c05081c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 107647706 1250 107646456 107646467
    0x10509030102371d01031d030d060905060a1a0a1407030e0405150d120306091503020a0f18050903091008061906140c01060306090b0109050109060302060403111807 72
    0x40c950004801041044075402514400040380840131141400906251203500c02e81c0890041401ca9000220100b11160399901310750200c450f9044d019203400060040b0022401080d821000540b440a03d032440d000c4400882c40c40361911525440002840e140103a03c42c203503005002602c039a03e290344410f1458098041a40c1c0b58409000b03504290004038101000c001003c00300502810004000040b640d44500c010262090301050550340c410114500721103100b62141d01d80407051058200703040d801045400c1c26264803a9440d0b88814006000110390742044074004006076801080f02c1e22501c85081c19809900c4016030446800c140f910440c9a124910ba0700034002514903a27034201407900b81e50b41c41c0550f801800c01080c008441128034080142c01000786070350301400020155100e071ba410b415218012401d940c511a4100140300f041c05c1c07446418010a0601c034108906465540421201e000701d2002a141645a109801c0140c5410340e1031000c0d82d0030034480308101d14203820302401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 107648956 1250 107647706 107647777
    0xa1b021e030d05010b07050f0d05090103090201110708031804090302071a070816030314090309010c0302030c010504060501060809070503060106051606060303020d020111120f0903040e070201230f0105010509030102 94
    0x340c03407041c1980301c103441e0008270b80044440300c184e441c2c514042d948401940940610b510480c108901c15584128201c400c3c042d240241050402451b666084810000f512440c031100a5106031b140102e600e000a40025565080744d100c842200311000305a01007030954055590041d1030304030001400a03540b1300d09035202008174800c0d1010400130002001c0c03a201c001c030850300004198001c1048928940c041e058910342c540c828412203141010101e401420f5580c280d4003114826220b100500020350441010703a070100c1000010003000b0b1901c40001e5590f02c3c103100c0c0605104000074400c0900fa50054450b86481c2c100c0b400303009840e42c1c2c2c60022356032090101e0a4005500c2c10029030701d10700c003410444003a124024030102950b240c07042650300384103010700744c0716043c4000c22000038040c1500071010b11420b2241c00001d88503200340013035000012400c03c2e110003241002c00f00a2b00380201c2a80c0c5040d90000c4c68102c0c1c686107424040f900910510402000e180e4851407040c009288010b103200c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 107650206 1250 107648956 107648963
    0xa02030403060c020c0a17011e06030c0510090603020310120c08060709030b06060307051207110d0f0512070905040f150519030f0c0e0705030a1b021e030d05010b07 72
    0xc410f200740101d884d4000d18024652101104404012004040d90607040289184000244240d6901344442070070104852090105803504000c005218151310380398000e044c00d84070312203101c8086c42d0090a01d4424010341c4181507001c000706602c0c05140c00001c014100b49840740107920400e003016000d00480d8802d6201a211b00400502030340c0c03040c840d40c0704607a0f000c01065190b480308001c10201e40c00003441e020800c00f080c080314005021104d00540103900c41e1b00e402400e9941e4005403410800000991000d1141031145024410303481400c4400143c0c1500058015031246801102e00d0711043d031103e54000d08203012a0004640341e8464180c40c1c1000c4c2101ea042076076802404600382c000c440c20042d803e404442080800c02e4000740385440c52181045080d01a10b070600725a14a60a440c3c641c00260040700704504920144601001d115007641c04031030344008050000e50b240e8025440d8041c0c085d8040e0510403843d410400c0d0782800400d1002400150385500890696070425401903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 107651456 1250 107650206 107650211
    0x12a140105180c0a0611011404080a020d0804020d020f0f03060703060602011b0e010f1803080405090a09170706020f040b03041205030106050906180a090e0f011b180b0a0203040306 79
    0x25070200c0e400080340300440d84041c0c00c0d44036240c038110317064400b440004850740c103954841c80792644d007030054030000d4403503441007152680b80d00c00180d00900c4c20344492081814060143c1c184400b40e540c04040c551859412a540e02d00100c4200224600e54101e8090903090311584080c0405681c26422a81c01d9814650080210003101d0b50800100ca80c1802004041428440380c110b4951148440034412000c0341051007080e03064a0f4200d089101030743c400d0b211640003103010301c00e0b450300482c01a048410307240242310024507512829440d480d000c10010024074001807620811000e901aa49c21340700611102d13407120303074440c5c003800709900c115021549022008410a441400381043d607050b1007955907000d0400103500309001c003541c4110b80c00c1743c440b01280f20314102c65031408140743c041c0c60a80c1c80802c001c0140e2001c1c5190403545d0344200702990400325030b80702c850400105000000e50030701d07080410322800c42c0c90f000c0d00d048503005011420310010308619025000802841203134840c1c00b04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 107652706 1250 107651456 107651491
    0x60608010e0303040b1f1a03040c060c0215031e01090501050a0609140609010504090f09031101020a120c090e070806030d0905100c06020927010501020c012a140105 72
    0xa440d140c1c402120f008241c5d440040c0820f40340103102001e4012903840380001c2a05503102c2c151011543c925070122503603003000000b000200304004000390024022420120302c001030950004120240c4403598505403a00800002c0c00c00c001a0034615a60299041b024044c1d6100c1c601c0e60090042400340c2805003840b05000242d00c2d110740c50410031290181203140c5016940010480d081c0e200055860403c00300744030218540015101d01003182c40d01c884c001400d5a601c1c035020704041c002005050781644180040c050a035045001c4480810303c1080c00192070380300b0031050328160040d801c05010104106e04004c4880c1d00000c0c041d014080407000c5541c9000c55000454464010b800703102c2c0c0009114801c1c03800c42e40245a9030510a100d600c0160512032100c020078050414816842d1000b41685441442c6200c0c805c0010b001d0300d82031000c1d00c01001c100c0006014810311551416030340f001060f11100802d60110303c1c2c52000da00040c00c607440d0f990290064082e007415921070100c580d94039030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 107653956 1250 107652706 107652731
    0x1909060e010b010e031009020a24021002090303070201030203220506152e03060b0a020c0411090306060918030f090405070c0201140c120a02031b070b030a020912060406060801 77
    0x8142130303400c0b0040051203980c0c500310030040a05201d0a040342c00074000030000c0380c0d540560084400d4003e07a207110002d142c422500086c98407055086013a0041d104004019440d1804800c4912003502802d0151752600c480d103042e80c0c0c9590ba070f83c0b021500e0801c0440001041408036502e4094105080d0110079030300103904100c0940000d0f01c1811420100803810300c1d086001c0f4907440c030170040d80e041c001055139650010401c0c551009002d0340050704140c02c14442c600d41071140f81503840070300c2070103802d20040c0d801107943d40d1405072400d440f44801400059814a01c004154883c058110030790740c0700c074803000c0301d90b13400c0d00602c104900c61410f28002480b550300c208a01e0142640507520818286012003034404240e0007261619143d00807100c8140582138860010408502c555005541d00d103101c01e400c1c04e5403901401d4446698204600802082144c0e500f9030b81c00248011005a07200078850024042c0c1c10000110301c100d00400d810801401920f52107001100c400c18000e100711205481c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 107655206 1250 107653956 107653967
    0xa03020c1009230f09070206090d080426071502030105010e030307050d080a0b0a030c0e01060f020c100c0f0b060405160507080a0c020d0b04030e06070503070b1909060e010b01 77
    0xd43c04100650000c0d0741d82002c00d03400c5151102c0400750080a0000244010400882003141c002000d0f0340324030180803110400b000010381d019024500b001c4141010350b120700d40064010540d42800808101910b45a40004210740364140d010301510041c0e100c0325003500c0650400d00c24140810f0880c4070285003414040229029107a03c94040e0020706412a0309075160f05025024910155031140c01822686906542e80040c500401214407003601d4041010400e80c0e05070400003c2002d210b0118601c0b0742c00040b43d1386440b0b002c40b541f5444c016940011900081c0d42c803000b4100301d0844c0294000e0145801c4d40c0b901071842030f5400c2c0304907a10342c080380005045d542e00c2003002441c208248400b0841c1c44001e040c05400314503003034140f503e003600010b0300140643c1064072003180c0101400201038006900104206c0e0568040381070401e5500d81e1500c034041c00c20081c18010700d030b000040400e0100d80102c6440000d0b4a4100809001420094000c00c0c003061489071a40c45d00c40040e8542d030040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 107656456 1250 107655206 107655209
    0x303020604020919060f051f1e0c0605070f09060e060901120b04020403120f020607050a110c090109020a030608010207020a180e03070b0f150901060f0c02030a03020c1009 75
    0x54004000c0c503100c075401e0001d000c5000300188045604200c080d0302e550014003441c00100b580c00494203c0505101c10000c1508501403c000642105042c08a4164108400403402c940449154508403400041a9807009540000500c9140b41000300410140c100c0d804010504641d82c92041541c1c80780416256001c0569450790b0140c0d05003c1e445031903101e6407000604042c0030101103004000c00004c01c0c16604190400c0301c4c0c03210070442030000c01d0790050030008c024410b41300400c0c050405280c003500c184100d004542c00c004502c03070881c2e2400da0401003036180c0040908203014a60355409490001d40200c3c0b2801f0000b0300300940017840706014025190000c1e00104810307561441c01700d054030b54036400d4542c50320040c1c0b108200c440910f0702b03102411a0310700500b1015100d107041c03c1d00c0c050008004011820040d64a4001c41c80c40e12109011815106e0b1030400300b0500c1c03400740c0159140c0c0e500e50802581842101c1a450801d503010400c03501c01001a160310492464650302074503001c059 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 107657706 1250 107656456 107656463
    0x70309120c1115160f050106060903170a08010b030603031303030906020f031218070e0408091017240d0804030506010b03010b0702040b06040509090609100b0105090f19030302010e01060f03 83
    0x1030200813410404d0761241484a40308201d10081c2140c5a61118291804c65014101007002441c082041c40b00c50f0b40c0700e1461420b003502040c07404800300805020080d040c043c2030441c44000c000181c06072000c1040b6810100202e4a21240a0340c9103401080074405010f10801402051107800080c80c001040c0c41e45101d20343c4401d003480e515407007821500307030000904003540d12a04100040401001c0c03c4030340a5401600515907682d044001d101d402040c45407074070304106001854440701c8081c400e410f03800040c445041d0003024003440000c10606184021203a1091807040c031402000002401441164882c6081c0e0301031303aa0b0741c0c581d440140424480c081c01c0318800c00101d80180750a41c400840044010b1000d41015220303008507417140000c4601208aa22030810301000c05c3c400c01000b510400182d8042c400e401948000034900c0c0512410342c0d004503040e6503000721a13651107146803d15042c85426107401d039540e06000340a010143c06010465181c08070214208105400c0b20068940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 107658956 1250 107657706 107657749
    0x40e1003060f0c020c01020c1807170a09030201060e092a030304061218080d1e050114190f0308031806040f0605090a020d0b1801110715050609040209070309120c11 72
    0x405420640380c80d0341c02040d003c20483e8801c0040706155042d601cbc0e6004042c02000000c40b1a96840c0203801c60b0000e4211a41c0804c0200800c0902400021500819280c0d5030850003010108480c0c9401785503001c2c2c01560500011030045521944994054800610b20030103120100c0800368100d00001661005000d500d0b042002900d0381c44d098000c49076404c40ea80c1d242e4041750303103d0540000c581081e00701d01c504461914100060340703482c170700c803458280c0003104050500d071070413800c620001200d00c8014100741c004030014080c000f8019210f8500114a400d032041840c1c80c0ca00100c18022009048491a16060206843c20000240c1d4a02154050094078514640d62030b250b40c002c2c001000e01c503040003200889158401c080c041c00c600302c42e0041511707803100003501d0041d8089015003401c2c00c00c45d1401041082c030707544280c20650420380683e83d086180d00d540600302c01405c40c2c40c60181c40c82c42d2111070b83c1d00d115031140038500018014102e902c40b1004030810400c036402c0c1030f0010041c118 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 107660206 1250 107658956 107658979
    0xb0903030a0c0c0f0e2505030a0b0109080a060207020a090b030d03050405190311010605041812050d11090f03010e070603240e01080c03030708040e1003060f0c020c01020c 75
    0xa004602c40480329000749442007030542e0b40c0450700c02524071a080079102c032584806001c3c481e126030b0002907510160000924000c01c0741d8a00501074007008000708000341d120340c80c400d000d900403004507029161120684040140c24100381c0c021b5030004004070b0180084000018a0f04002d10403c40002402000703041464071040044014041c01350040d0307454020704140c030000031041010760012501c2a2122681c01e81c100d8511801c64855a01450050b03003090402d40d43c1e03150041c0d80282180d0303c0440c400154051201c211910f009079140300c1201460301102c00219882c0401410740d034402241d540c2c0b100100b14003410709982842001c004154402c0b030342404114025004042400e8903004040c1400d21084076100d00000240d2040c07203030080800044c414460240000707036070900160015494418180e88242541c8624414402650180b802040503419140c050a00968000c1418446442c0c0c0030010701c0142151a0340001611070a8141e041e07650000c03031005011000107280c001c070103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 107661456 1250 107660206 107660227
    0x1c0807020609120d08090d09080703020907020f0d0e0301110a12050903090402161e150209060f070515180a0602090607050106060c15020304200103060905010902090a0b090303 77
    0x7500900c0c0c003954420300c0c80c80c484907552002c100c11442c401a5541e107540320304040c0c01050409024843d640304200a0320307020709c4150340004841d800c5907416a0110180d43d6a00d038101e00707001541c510309000380146c07030949280390b034040a10980048110002c01c514800a0b402000d10b100da0804000819100898181505451f5000d0f030303800080501603a2034603003810001406c81c2e01059540c070680d0250344034641404108070318080501d8000403040300940f402d442d100e408a034100c214807a640d03000a40c69443e40c40d490b043c0c42882032039150031516403501d8035040e911000e03204420300000b40b0a60000e100c00342d014503000d4000582c58064a00400c05454040c06175008110b01074001c10100f252100040b424841c0030010049950382e9440c0644c14640329440202e1903034004c420600610074030012174524403805260348010b00302c140c02100b1701401680034106580c4100c5643c1d2400000047c006001d40042c015249d08030350683c181901c0e0003803011540541880740f50554000d00581081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 107662706 1250 107661456 107661469
    0xf040b010b2704110d02070506060a03020d02100e09130b0a111603030603020a08160b03060a0e04050a0b0406150f0b04030f03120507021005060117060906010c0c0f051c080702 77
    0x92800140c404140300309803410b6505941d101e00440d9810b04c6d400218101403000070300071290007100454000100c2e500d076400140b00740b607170544068450300c0030891511815008056801d0034503000b030440740d010b1a04a0362111a0303142000e0556511014000183c4450840e220340c6001203085842d4074100b004140452000000072303c800c070185a9a0400800540c1c1c0e079464810003025544000d280e46c2070040e0102c00d018080b40d00c01509070380180709005042e40d4081024003074514861181c4400c4d80c490420074603180300c6c4c1ea00605003001280501080c000940c200c1ca00c62600e11902d25030044c0e0754010b440131140244218002480140028000520002486c50515000c0d150003207548224044080440300c094a181c0056484a90b81e8840360201340180c56100340242450202000451042c1d41c03101e400500b81485420b400001480b01da003d00f52990704140c1200d10051001e80314110307038070828802d000d0f061103a849040c002500c00520100c106101d07900c842e10a00304036075542031000c4c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 107663956 1250 107662706 107662777
    0x604051609030b070302040b0c010c1107030c03240e0c0102060106021204210804080705040f0203190f02210103050705030303160503071421061c020112090b0f040b010b 74
    0x4251b000c2000050038005113015241d145000d0b00001a03040d0200d40182409040c1c2c003d85582e13800410040021418100745901160381140841001c00c2c001c21103c1241168803914508191420300d4240d0030b58000154502c59400c00e800700d031000e0362940010b0781c0c0c0b49042d0340240080d5004000c00d10201200340d4100141d6601c0003c10040181c6035034480410b07400603001034903d03900480c0d00708000d103864000e01001e4421410114030711f00b0030301c1d518201403a0301c0c80429038283d00c0e890b07103200c0115594101c8010580d0304458545648000042010101c020b100c2942c076480754074408502d81c0b50100840780a20708038080221212400c29050b60140c10091441d02031003100c03280a111000400018180041e40c10300b40340c11440462094a0a200064003090180448610003a5162aa804035415198090030522282c94100304030710003074804500b00402c0c0803003040501c61220201a00306005601c42ca1800b510303a0b0f03c0c2c4000d12840e0203000291081d1203002c042411506030314880515 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 107665206 1250 107663956 107663971
    0x905031002070627030305220f02030705150901090803120412110703030504080f0a0c05041e06030503040303020f0d08010506030a090b0907061b1a13050703030203030604051609030b 80
    0x144440600d68030b03c00540c06208044021013058508004141d030510800e0750141c03180c155101102210120003002031a60b500003012500d00344007140035541c01300405030040c540100304030504041e0061010309608084001400b01d030300c2010204460a01000362030a500715000e24118550341e5031515807400c460310850300203100e074120414003544001d00943c1e018601a483d216511031030b081c8480d18010016503c2c030740d1034000101290000b140c0c07403048800c44004071404110040000500d992801010300c0c211140351602400104004c1c01101038800c89020313409a54000717150009045d00c40300540b03ca54009030f03480d0018002840d0100145030421300400e000200c0306a90b42d0b40300c15014003a0ba20340c2080c0c0c4511420080c070755002d10302c000c401074400803940e2040069034400040c041c02c1500c0d0012001c20f240000d00070354004d41403180700c581200844104540d81d040294582d0700c06e41b03600e0700840c00d00d000140a5401a50f8400100a0b130756070300c41c0030b0f0b8a95100d030108500c000d001c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 107666456 1250 107665206 107665211
    0x903170a050f0a02070e060607020907030b0f033c0a03030911060310050f2209060905061003030801090506060306010c0203030d0c0908010501060e03070b0f1c05090d09050310020706 80
    0x14030380b80030030340b01410746115190002d0401c00d0500d030310000c0b07040004003564071034982080ba1400584606840c1900200340f07080119240c4100b0b80040d41080b045072409030035118000407800c442d010000d800e00700c0110390514112284018581f04054181d1a0031007001d80d004080b0b0b03900291107541300c504407030300070403801c200e442c400360001e240c41d0300640b024580703481c3c216414400d901d000103408004c21400c880c4a003540c50680818028169030700700c003031005036689101a080c4805074208007805030340502500c50918007580304c49c18801043c00198001a4800004111019039220306405208020882411a035174030300115111042c0400890301400240081600301c0b100e4055100d809071a80c40300c2020f036052101907821944143e00c0724007000b40300260b0300566100410fa004c10342d400d05c29000d6480c6407449081e100c9100302c0760040c0c04030000100044601410380d109034003a5150310180c400005403420204e480444c4c0e405850382c190084201d9035240784880e8002c204080c0b00d00d402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 107667706 1250 107666456 107666467
    0x180302060c03090901090203130b04021201060602060109110a05030c18060414030c03190b0406060807060903140a03051b0a0b0403110d170612160b0405040c0903170a05 74
    0x416500d0300001d405001030340c03001c41e0140680c50140c0d0034601400c0e008400310b08500c4e08140c004089503481c0009171081118402150564036091010300521114000078001641d48010080d40c4860901c41c1005513403038200300f80351a004540840c0e10141c035540d1010b045440300081c02d1180d611005411040c0880700300d640b02107460f1a80a0002042658074001c6404c0310780c424107040142181010784a03410261450020000002c1607003102c43d08804403c02541e16864040d0041015400c0a2107a1080c400009402c03544158101d042e42d20074010f48640d41519418141c3c0c5000041000f00070032418050f821803200b0074000d200c1d0f40e05400040359070100c1107031030303080b42d42200751010340009241c0d0009020001c82040280b0f50f005082c5015454103a525a103071304000400360900d841825140d484400c41d03c020400452000f0140c80c06603c19a669200c0442680c020f21906000e107040c0607038003250a001c0d400e12000c503600010030110302c0300f06e0100d00d800c030783c060442c04c0d00f0b00205110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 107668956 1250 107667706 107667709
    0x9100518130e1b0904030e012a02010e041406090c1314270f060a030212060103050d050414120316150516050a030c020118050102070b0a0b010f180302 66
    0x3500c0d503034031080a5001900401042d1054240b8821400d0b151460300d9a000040c0d09840c1c140545501c20340524200b04001c2160780101c80c520f000c4465044040120303100c948000d524110b55080d014401d8890b1203006505e01e0500c03060f202c82c0d41110307013a103608600040060411000701035004603501e010728500441c103100e6200340b00307054020440038911542000541d0800c15107022405420b808003014400c1e0440c3c402c01111801807a29503880e11402c00300e0841d80f110403c80c800b03075600034036081e40781100101080d50385009200c143c40300e10400044180441c020402c071415215901c00c40c00c2e40a00650512240070341401b03030300b07000748010851542d041b02c1c00c1c061700405078482d134020050038031002c00441c2500c0000d84180714400c010382030201e00035007040403070350300c030003181404641007555100c2a0b00500040382000d03804c1070700e40e10700130070400107500500c41c00b07100c1c10307110780d1a4484c400380d80101d841c0e8500f9180841d96000d800b20482d1700481c0f0540040c0c150303a18904032240c5990 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 107670206 1250 107668956 107668969
    0xd080405030405121e160b07020103090210030507030f060f121401050f070e09060a120c0b160308091203180304180b03060f040c0b0708040b070305070b010b09100518 73
    0x42c142c03011600107800844a40017010031070134101c1c0c5441c0003030004108041d00c0f0003c041c0705110703004805c0000203c100459000f50003d285040d00100704100140030f145000d00036020454144001a01d081000c44030300243d44610800c7c4d506650f105041309007020b5605005c00000d08007a40d8031000165600e40318882400344c1c1d44280c00f4466a8069400c0102025010350a4a03003400d2203100760804020144c2c840c090084201c400d540301c0c40075180711500f0300701707144e0b545504812200d800001d0b040d400148070000040c1e5161203662203224681d2038914441d110b1070004500c10354a4000c00108041c0c034070030700907402402542011b580c5050398400e000c4c0341003405c840c2c0d94a1015141c0b810405a45401e0055680c00340311000d450307107540742941d10b20842415034080d84128180224804060250240941d0041d100b04813200d40d0303e495905010308940c010181c2207409001920000c541588104160b515403400a401c5400d210103054040d105c0750490507541401c03011550401c5010ba0712107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 107671456 1250 107670206 107670229
    0xe0109050304060903030908060702060a11090d050115051c02040b121501050109290c070509040f0c080a0308060d0317071d0a08030d020d060f0807051e030d080405030405 75
    0xe4444020f005d10f0b52402410080c010b41c0031500a420a800308200c0e143c01052580d80804820000100d10722030f080030b96242d02400c030540348c0200f0543e455a0412205601907014400c0314804d9104180e0303034104025101d0765000d00c4da00d44001c914002401818660000385101074002c1484e900c050510799110300c0c1200d21015029420f2001004001d2560044d0700140a480c1c1e0142d011040e03525044d181041d561045291081d002d0f000602142901c401d102c0701000d04002064a41507080504100a0b41e0002c135000380c950300c015901c001420000001c48203070480c0e040d15000255920f20040140b00d112114041d800c0c0003981d800c0c02c0c00c008842c048903120300f5081e124903102481e05811804c1c2020108507290003200d074024240070091001040da0248104114096904d960032442080503080307070b9024114181009802003a1000e01081c131500f82c600907030708040e82402807114407070003030942c1c409070307816400500c1485d040d540f2611025600501a500701c1b0b24099031100400d021243c00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 107672706 1250 107671456 107671469
    0x22701030e100f0b010c0f020d03030e01020d050a060807051503061309080c0115050f040e1903050a18030c030209063c060702061b100f0e0c0a0807090e0109050304 72
    0x40c0c00c9007881e01d0a440c441c0c0d0040c039030203103040c0c0119071440c2c0d00d011f9032402009010380700750104401c88003014403a40210080d07000c030720001d54940e601400d014002e00002d0f100700e80c00c0b0303003042004100074000240c50070484000401e00c550003200c080c0302c917080d0392020b444590442101d414100c41503081d4054034001e648141441383c0e4a2202c120a0790031500003108210070303007501d20010001c50780d50809850040c0030445002811007995407103603252150710046900d41c08640c1c4102c01c00c0c160060301400e618017058a904100f0000c10180c0345064207207010040c001c40402c001413000d07061000c0c0196010038098401c2c0300c040c60403050600782e42c180078a403800018511808106c000402200071815400030740d24a420130310258001400d5014904400001140100c0781c0240030100304441e450b0722541c14010010f009003001001c000e003400100c845528400c0c0308000469061450030002103a00d41806008090b0410031080702402c03454030300715a190340f61400d90300440e400b4070045c4014240c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 107673956 1250 107672706 107672711
    0x801090b04060f05060303030c0a090504180c140306040305090409170301080c010e0904020d050a0f03030f0e031305062d0903010c0807020d0c031704030f03050a022701030e10 77
    0x70301e407804009544010b100b0140725400e210500c20b494030000180c81c0c00181450a83c1c1e1506440d010807205201c603640000e900606102000382209141c3c00130b4a10b580c0035036600c82105840d2004247e10aa410742030582540c0040c0001d40881c0c465009405025002400407462070580d4640e103000074107851111088180000040090a100700b0000c9121030080c20300c0880d0120540001d078054800401c0603003e0103a0458480c1003050034811002056442407070f00346002c1d21800c008004240b08007100786018038101760a89800e0000054451042e00c000c407090040707003004140f00b0f070382d0084041050008000700000e41d9585e1614507041c07146ea4070300a05615920b01800f003500b0344405108250130300c000309040c02030b40c42e40800c42c20308200b09420900c03203050007890120750900d50040745e02c4c040c0b5000424041010340c8201d202d00d450815076014045d548807001d003c03040b84140b82c411503010303203d4001880301c00e0100145000f05030050400003824120920080d00b8a8a05450741c0c07120f95 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 107675206 1250 107673956 107673961
    0x903020d170c0f011a090a020903011d010203090606041b030c09090e03070b0601080f1b090d030509041512140a0c06080417040b04142107030507080307030503011208040801090b 78
    0xd110f56912170607204c01da6400c0e10305c1a030100e5000c1101402c02d030702680c0c00152603c580d403400d4101c00d80c00446600411081c2c008580094000e4009403250846400742c4000308103145800d01480d03109848510b0003040c484076000055000b002c0b12003c00c4184510042c0005001440d8807802c2c200e00c0703070714000c4c541d602c0c107c2c0341c07080340d0388401440c0310305201a882c14450000168000c195000c2c1c04560f483d02d1655032807100007000e000303040e20240d000140d0020750b001c0582c0100903101c8090103032800c1c00f0804001d29081d5081140340100b00c0c20240003200301c0d0100368030402508444e801501640d200c66401d4031100c00122213a0041c0001c90142001e001c10810501e86100049100000140c14207040c0324041405108603c034650b0b10642208032002d880e505c55006041c100c00c200032800500c000c0006664541000d44815102805020f800040c3c109010040b60b0600754107644191942e802c003100c03030450360390024060311020340511000c1002c800912072110036600504041c03c0030b2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 107676456 1250 107675206 107675233
    0x1312020414070906030e030f220902070c03060b040b030d030209120a030201020a0f0c0c050405060f0a03050d02070e16110a050a0516080a03020606010e18011202011e0903020d170c 79
    0x1c071b11218002d45164410000e400002d202581507400c1c82d05420560040341c01e0300d40804071040c1540e00001e001501c0040e00f001046a641c2d41002100c1c4a031005022002500041008440c2c2540b04c4a41540040d40201e4030284294000c1900320780007040460300c40c803d110060f20700b03000224200e0250f980080c0790664160841520740310380e4214074065030100503941d0713540d8031040248615030007261102d01086080c1e54421051100c05009849000c00c0307603803410803c0da5406520041005405014000305d000040c0864141c85080000990303100c03286420f000320303505c10462015680318003440035040e0001c0d20610030301101600079030007014483c1c14455683c0c05c6aa1607441500c80e40d0040100e100025004510341d40e1018090911041415000c3c0203d00d101c04c0001c2040841125040045041e44181e07040c4000517000b0782e6034100c0c4404403648021012000c03081e05000c00d5070410100014509213202100315440781c41c1c040c21145800b0142c1d0300d81c0c3c21a0513014015040049850480b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 107677706 1250 107676456 107676461
    0x2090109050a030816030504080102130e01080c010503060906040b1f0f0c020108070f0905060d0e1002090303070f0312020706050603060c03152419080c131202041407090603 76
    0xa00800c4800702481c2e03281d541e0b0040d0502c2102e170700100a90104401c0c0c2c1c203240c007800c10341c1c0c018050140203642e10301050b21170360440f02460080801c1d8901e20000030841030300c002240480c0303d4040e16864590340340c920411040c0301d0000d10880e402030320389611042c55161000e100c0705c107500300000614140002c81c000b0340100c40c52041c0301d04102640d030411001d030b82d1101400b504908507080a1020719500d85088a51507001d0304156044040003d00e2007403000c807640300f8030889000005480340340c0c56440640007039205505003194503500902055000c0307134202100360549482410031049044046080708181d030040f110946110750b0f80c3d001c20100e07090a20070280c6c09892000610b01d5440d04d2034000002001c0c003455640222406000152066000307012002c1c41480440c105071500d000302200409002e031600700c03000007207600300402c07180082c16007580c100e6040012016040740c2407132a829000a00e00740305a0b4400d845101d1045900d4610314803030302a0b0440d55030406643d05004000d801d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 107678956 1250 107677706 107677709
    0x30609050c03120414010c0b07110c100903050f0102040f0501050d0236030a05030406030e07050301050a2901050307030f090b04060507020f0f1203250c030905060c0a080319050a02090109 82
    0x501c207010203100000f80b1441c00d09a8032000906045072440500c42d0110700d01240ca40c0348a03003110b901c0c491003120582040d10310049030f06c40c100302d869602c24910c10500342d00603413048014607280c0c00c0d07040c0901c0d8014400b81070101c80c803940c011705140710503070414850311358000002c29021803000d00018031041c1c251200400300003a40100034030072407603803001da0300d10440c421101059038425a0f04004032080c007004005041c020001e00850510048010007890209080f8050300c1c0010190192101c00610600c1d064030140c507418259996107200742e01802041c2d0814000326503c2c040c42c0d0000f6140c0e900c1034000c1e405401c0004952906440103442c040c1d640209001c50360089034101c2013098000350440c401d42c4024a045e44a44401c2c11034003812030031156103481802031000c880c40056000b0444800580240c1c0e80003020b0790340c0c0c0280025841800800300311f54028010140205500c44011130300901c40c42c100b4004140c15083c0c2004480d410f0300d1014109400046550896a00440c0c140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 107680206 1250 107678956 107678959
    0x109020a08010b030903040810050906130c0b030c0903010c0314060f0604030807051f0b0f060c0c01030b06160602030a050108010606080a09062a180b04030609050c03120414 76
    0x6150112800340685102414030580311066000000100083c0741071042d10001d109020072100c8a44c11121001d0150004850301c0420340301e010001000d04246d441d80c002c0c902e03001814540c1183c10001c5140e0564401020107001c1c0004100c231224584091044820b010050764001418a0a012901c6075000c00900b205201d50b0300d0001c2079116903207400c1210704485c0d0003028955500100c0c81c01c10f0806120b04042240c5e070b43c840c980c844804440381c00603225860f086514003d03a80c41c603400c0010a016001d03410071194002c0f01d08402c554029840303034000080041c40301d810700e00070050385115522002421620b450f000310522003501c010307004050240484000a00c0b280d410203100400c8080020050786226803204114014042c1c5a4401031000c011100101900c2e01000740c55140c000c81e0035414400900010240b6014440c100c02d03400a455070340000d41d15161441d15910b014060112003910700d4001d5480340007031a50100410150101c0c3c1e00c403416100d92401014403c064803102245 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 107681456 1250 107680206 107680211
    0x304050112050402040908070503250b070f020c03060712050a0603030203070b0c09031501060806030a020102120903030d060608091c05070209040602070203010f151202100503090f0a0f03080109 85
    0x18409aa007000c040203006880700c000140c250355070300018014100325240600740250014134007042c0034012000384513201e032a0034100b0b0315451101407030101601d009070107416034085070302150701d5030301c1811403024004140c030480e0128540c020000341441c038191103040c0840d00d0041d01c05503226080c029145d010019400070001d06145841c007035102d11562000402c0c815034100002c88000c01c1070b003552640000581110414000c2031107141c4040c01c28090f220104104400080462400041070000b441c1d044c3e000d8018000c144c0300690039600024035113581800103010b00d9600d540c0354860710004000603595190a400c10002c9141000068030782c500d218041d070450087c0c400d030008101c80450f507040d10b41280e80e070341d9421700c00000c5c003903104001d50550030240c000d1100e01c1250041c1d112480b84408143c0456a41d464101440200490080d0003140c1c0454070310031640260f011796406510702d015940002d400fa850b603070401c20748100490b4004000300e845000e241c0d10603a080e01410501104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 107682706 1250 107681456 107681459
    0x1271a03011a090613060c110d150e010906020304060504030f0f0e19030503030916050a080a060207050102040302090403020708070902120a1a0310050603010c05030f0c070302120313060b01020304 86
    0x403502e0066295041c0b1200000180c6482e961200c00490710344002a0030680751681d00c9040041100c0381c90802607810908c9020065139501d401c0301a844e4503544002403065a098100700c2002401d44010460002c1d5a582071500200d105400114412482440002018038145ca8040c000c9614202882c0400c070186c8070603040250004c051190000045038000b2000710020700c816520989500f0040032804080300b4844050f00000300d205000e0380400c0281c07061074940b000d002110300701c0e1042e04c4082d4461440c510100c5c4580d4000c0504a008000151600b512900410030161742506c0c1140142c6c404802004800010311814020381070080d81549024010006881580f030007608941c400c60307a074482144041e040c0c05865015141c0902036621501210702d000c2c00405088501d2800385d402c020003848842c3c4500100c91103240b100c40181201d886240020070f540d0800c40d4101c065200702c1601d28164600c410107180f20340e41d51280e105e41000540780c40415240400f08035815903105210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 107683956 1250 107682706 107682719
    0x606040509010923070302060a02010e0d05210a06050607050a051005070c02010806011211071407120b09160902071406060a050402210703060608130f0204090201271a0301 75
    0x305100c548141e0800801280c4c644039681040210b9200940c480400540444081d8040d00011071285904096561b102e1400c6002d4520b07100b40803981d2002550b10308a403044449180c801134100c4140403000034440c2d20744020503069801a0401d60b5140d01440216003048010070002d0f070094108a424082030403c0b0790085c1035440ca00030b0080c10b0010700b900203005ca0344918014000c054003500107010003008081d1130402a03001d1103080d40c040350a203c80242c441c40008004003200e2951071500d400b900c40e40c403a4030200d440a0301070312403401001444409010050400310190600020060b44e41d607031490603001c0028074030b60503005600b0403c20805c1076903c1c982108102c8505a4003d6070b14030404032414130000002c500c01010024003030612142e26415802002500c09548441c461510b420071944803c491340c80c802131822610425041c014145900054907140c0306041201039a0760000f4039204000d41883c44209200c0390800c10401c034000341c01c0740d0300542000310090b0300c0c65040c903c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 107685206 1250 107683956 107683973
    0x115030204030b0105060702010c0c170f0604080409020702190e06010e0d050c1003060503120c0708121903020903011e060902040b031825030c090b0105091e0d0506060405090109 78
    0x41910301c41c550200707d00095900403146503005540c001c1501c61020b840b1003291101c680c81200051305441682d40d04402c540c40017038903600594004109034103103898194042c01a504c6402c2c201c0e0480e885400c9003000d02039a0351810080d00ca081607924039880c100d0001005440004001c51040046400c20310100b0b40100381485030080c162942900050001c0b419400340c182503000710382500c19001c61618007280900031b4407441d8900e2040e55585070341c0b91101540c611500791001e104507410405040300010395082041079000509001d410030451400003421a2040441e00c0450886900c5121640d03425108000c040d1401038000c500b418109008020365000c01482070b10214080c2140008003001044500da11502c1e504640a440c24040c114101036071051100b103a8840328040c1c0803440c0162800354010011060396002d0914200c2401c0004c054520706140040d40700b14100a0411b449196600c40058001c5005101a062100500c41110401010150641d00d048102c0700011040d6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 107686456 1250 107685206 107685209
    0xa090218060412060c0302090a080f12030403021507200a0302010c0206070c0305070c050a0b0d0c09050d060f11130509130f0210031103040312051f09020d06030501140115030204030b01 81
    0x4a00045c1e0811683c1042d0000d1161a8120b0b500a06003d00012015000500030710b00c0101034055a1191640000340d069501083d90000c0150b0481e501c0aa0500c581d4103019034090703454904440d8000205020f000410030542180140e41c101940c3d00c2d05040d0240200340c9800c03400c2c0700411080c0b5007040010000807203050001c0412a0020311581400f4100d40a04041d040003080356030b1195803810300a61650010094105080c200943e1060490007040c10808940015118107841180e95480034000d08000344022070265607140d4455140d010340c8060302c4803109900d200500340d8101010030150900081c140300c201003070851000b001800d66200c2442c0130760b040e103490007428000d01054029114003c4c42002060010042006151380a0051f014040c010300d410805a00c5003a01007440035030701180300c031080158090402610380194006c0841c103240b400c0015407140c89985083c251242d20003c07005002d0a140144401e42110706070108228460070218a45891641e41031040e0005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 107687706 1250 107686456 107686463
    0x705030612010209060307020c09090105061f0201090b090c041406030703121e03060f060314060915180121051002090a05060309070f06021603020f01020c0a090218060412 75
    0x940300c901e400000d4050f41c84c0814001d01c40340d1240382c00700d402940d842c001526144185c0031a0302164401a06100711401200040d00800314604083c041050072000d11403504110342d650840300010526080e541405000c120700075010258500e020041524500c3c1402d0841c1c1c021700051011030354000400f00c0440c0e90081d4607408406607408103a942c40d480c0c0c5640b04004000c40c80c1e01ca503803a45030f0f001e5403d031504e081d00e10b0380f440d0300c84100b14110f401050812103a86064408100300e89401c0030200d40c0b020081410300c08404d0b202001c5035003900e004880c004906c407070308014040411007802002c5050b40381c241c00c04030f145242c2c0f1410b42e540c0090782c1c080482075001840c2d100e5a20351604503005810060807030795503414600c1e001683c80e0801c0c411300a0b4080c420708080740e06031010528640c541444012061994195000c0140c1d861a1070100c6044d8800c800e10400310b0380755810340000510030150300685403500000036121400060158901c10b050801040c481e203030a100c0e0110420342c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 107688956 1250 107687706 107687719
    0x506150d0905060a0608071a0c10021e03090a030c060f02040311030d080c0403060203150901061e03050601140d0207021f030c0203040e0f1008010f091109060604150c02040c0f08070807050306 84
    0x40c1d0f401c10740b2540c440c00c81a50650302800040352b461201c150020050805580b001c4403034603029421b0820240001e0310340084582000c958000424821030030704c050716024900c0020418034201040c022640070380d10403201c0b031290f526810014a020b01c904000202581084216882c011002d04150b02c5980002030400780d001c0042454100d00040d1980d10660241035000e040d40c588801078001e8a00080300d1102040741d040341c1c403409120307005031340c02810b060719840d60304c03420030011401c0c40c0c000c81400f4904507400c4c00000d0140c1c0d80c9040890307001c0a007155502c0070078030301800242501c492407a200107642c4100f1040101590040d00540c0c840d022401e50851600c403246000b005465981c400b40d802e41c200202c0701400b214907840940da47d0b01c5841030132412a000018012082c4084450a5010505200c2002060304841c10924815040d2400d001503007a0b0b07078009030880f10382450070800100d0340940d0700e040540060307003260408840c3c10300c501685084500203107544801007400c4d0180d80c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 107690206 1250 107688956 107688989
    0x405030d110a06150e1005010818030f120105120601150f170c0a0f08010f050108060d060218090106020a050705040b010903050318032802040506150d0905060a060807 73
    0x52042c8260341c1400d82c03107281446803001080c0121a02802401010780c80c2d504d03000410b401c802c1d1a290401140c4068542d41c00e1a6902203540f0300c00d503d00009215a0b02003080032268403111a4010141110442d920f10281d504000501450382a000c1445110b070340000014040450801c9076042d54454a01d070030342070903184c85012980751036200c8000c0c00ca50500c1092094035000e070f0000e0240c1c4070565035140300058880744200d601e00002e2044050b5000543d0041c086544112800d6520000180c400300020b0000d50b1500c049a00c034040f0420040c2000d41c0141e0103207041407005005007654801409a411980c45141c0c441815200e07141c421a030b14205290b590340100100b000554024094a8451000130130900100704c48030b40b80c500c80c1c050f994100b02c0c00b161484038032103640d0107045501109e030060b80c01c0c40010000500140d900c10000710502004c036003c40300030300301c00c03000c0c00020a1002c0c00c8e103402e03450424081c01010010307081400c1400340c8880003511400315101d44c05003c10ba40e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 107691456 1250 107690206 107690237
    0x3020d020f040c020d030515010c060906021207020307060507080606091306180f05010e07080a020310050a150207090203240d0503070308220c05040b01030e1606140405030d 76
    0x122801c052503802a041c4880010041d80202c1c407081806410341b400d003c150342c0c2401112070309000246d000d000c10401a091800300351a50b11200001d84034140c01490401540071a9441c644200d4807500141c1c80001e1490400186d806040c0c2c0202c0036040401203420f14900158031400748c6038440380190068008010b0720822a006a0020400c400030300d941e642985c050140600140c81c400341342c0d1411702c0c00000e1038180c07000c003807481640d580e92204800d45445145502943c0302611880d6501100710010032955603442c490170040400b10113100e079a108640c8040d050401d41c1d030081035600c2c4103104000590054002210200c0c10260900e001c0b66000000280300d0890140050440d1001003450f40c10140c20004090041415074070700544031504940030103d045540030300402da044000410405401c19422081920505040201368031103d01160351070301d5000c030a0201b070513882c402c080081d07a400c10120000030458180991034541032001081d642c504040055041103c856010b03c2c50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 107692706 1250 107691456 107691469
    0xc030a09030e0604120b011406070b130812010612050103330e01051b0a021b010c02040c0503070908030f0f1b0703030503160509030c130f06090f0b0d03080103020d02 73
    0x102c20001c00c616299034031183d141042e41c114480403901074004100100300d08100041d110040400104100d140c8892035464102542001d0300400c070010100c40841c00080340100681200884400e80000700d615020004044e02e586100c01403041d0325000043c404500e1a54602390030741c0b40400009280b000d51078200d588100d0035204018540d01c0c281c0c0345901c811042d0000b600030b60b54000060006e1002c000d5850684c0f16003200303500583d02049809071840c5440f0714a1400d1101410000c41408158001c50180c0e00411902e8000034000010000903e4100721580c01505a81c8001c0d03003810002d1681c1200e40c41000c2d00001005408900801d44210b007030054800d2030408401c4e039140d01c1c1d5a18010f8a01d420603a03541000c1c0c00702e4080503003298032600030f5512003a8024000e0401d91548414046884100140c4120043d1135400c1c030b121072140ca0107a0302c001c0841c101d00240f52008071140701c0c100d030180c00c030720380c840d003400301c0c070200829801480141034a80413130780039008981a1000900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 107693956 1250 107692706 107692727
    0xf080d02030708162f01020309070302031507210906150305060c161401060803070b0105010806040203220227010806060105030103030207090b0307051807140a020307170706090b010810050c030a0903 87
    0x170300c3c0d070000080003218040801c03103a081782e1082e0f00b281c45a5500d200c4109240d04105c0c1d9140000d540030303440c2d00f8100c00c5460003a688090a010000e80c010140d1035010a0710031070309200848010f0210f040080003002c014050b07000030345001190030f040b140301c05068100040c1c0d40c00340012488503000d0035014029070002c4001c115030b00c220303980c86007c0d213450103040d00240309160210b8610b03800030750380c0d050074021a84540c07135191140826001480404800501d10f40c8260703040901c3c402e5004040d940e82d1880f035120324500040d03454071f614280283c1e280c88002400c050420109000420001c2d0f000030380e00050380e03540d03000440c3d0061201c012a15040d066441281d0003001040c5102410501c0d0900b81d01810059481c5600c1c100c02c4c1c0c1420380c15102e070011000044c1d008101504c0400c1c60301c415002c000785d2060786540782400544541090741c030368001c1a00c09956100040000306400c005c5c081548842c058184994502200b240d401800f00801541c551034942d0803a001b0944100400740 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 107695206 1250 107693956 107694047
    0x70509010804050c19060801090207080d09030c08030c040306051b070b0c07020409060e010506040608191a070314071826161703030c0702010c0f080d0203070816 71
    0x2e8a10103110820542600c03240700c0c600100b1121f8001040f0040c50303008984215400203a4a4030b419281d000360700041901c01c038103408200320141c40e040010603500055005940044e21991203a003103040200071900054080182c000709004151201b40c13005054459040d048411100c0c65560043c1031a000d02c185100298010b203804140c400701320182e441038601c4100100200074030f0f55040103100461300305004040141d030004000b88803c11020710840c02c1d240c451460202c10111020840110250030b03038900002c243c0755a04691080310340990158440707103034500b501c0c1445d0b1030032450070222054040c1d2186c1c03400410ba407030f0764404140001c04900d0b520100301c1c1d002031400b0100421070a41d50040843e8550102aa01e6502030000140c0303005518030b01c1818540f01280c1c1c010359103411180c0d41140c03041c50840e03c0c24003051000000c3c2804a0034442c0141c5d80c1e250144009040362801821040d01181d1040d008146551146c2e070400300c81d5460000c6a15080c1c04400407480038000d0b003441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 107696456 1250 107695206 107695219
    0x21309090302010213120309090507140d05090c011e0e01031d010b030d050711060d0b09040501140105040c05070f0206090409050a0203120a05030a09060212010329070509010804050c 80
    0x2004140c0d0541c010f15400c030f005d01e916031581d500e4140e400040d50030401c0240026800e4a404c1c41040143e902c155004a240d0401e2a120040320a0100098100078102c1030120b40d503108205203801c045c0440160310409190140f04c100404c1a40d860600f8114080c0741000780621048059074003aa10102c00909443c11408110701c5850115018010000515000c0d00800740002507082c01041030390030460b07001c4140089072802e03c0c2404055000301e140307103005540b40e80440070551030311840ea6008500940001ca4482941c108890001d20706a01c442c0c0a645025001c04546521400f074a0b4200e0303200d510417040301c1e030700e0000401c503004900219500628014045081003400240c220700710b4800d034140e90007415106a0100c1d20700400d41d400d008904100001000a0015800055050b114280c0142070101040c40028020342c01d070000c4404120301c811805503540503540440880c3c0c6c030b15074240d950b40781c8150020042d0240d1245141400400c102103410031405205942e5401c10203405c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 107697706 1250 107696456 107696471
    0xd0506010e0424240305090312240303040f03080a1107170f030310030210050c12090310050103080d0209060c0d0507150b01020331090213060302130504021309 70
    0x84610000d0000202004084403400005110019025280200008103c1c403615640c1003c001d40c05071100601d41f141e14002001030725003414209040300d014034801c80384150400100700034511007400361000c140c03080c2e0003070004009100394007030f48000b902d134000c81864942401c0e02054070444069600e841043c0544500850b580c0503200318601180030020440798506140b0601c2901c1c0d200555508010070801d281c00d00150800380038020300103505141ca00c0c5800030f40b070340c454244050007864000042c00061841030302d2504004c000880c040031a020072040d40355544034001841003080003185503402013184605a600c400a440302c00d42423100b03440101d040040003c1c500e5000440c101c400f000241007c00040d8441e00c03c5a1070340406070001e51a160003044a4074419428102e210509061200e8818441010460003c014040700c840540c407980c100050701c481207081c0d005141050b00c1440201100c081400d20501103402c2a100140d403000100d40031017111034030b900040d200c0340c24040f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 107698956 1250 107697706 107697731
    0xf060f270d08060109050f0906010e0303070b010e010609052e1218170a05090906130c0c200d0602070602041a040f0f060f0f0e030a0302060103050708030a02030d0506010e04 76
    0x514443e0b01d003641c94445036a1a1020403802640990a00e50001252000100554000c0050050004009040f00e0400c002c41c2e0354050504c000b41c00a5561010070f1004000d407a03002041d00c8041e00c1304541915154000b00d1054040a030007100044a68522405095106000388189900c20302402c8040c0503820301110704140c0490f031644d0482d03030300201e203408040c03003403284094550b405120703501e15141c00da43d8020014658005000158008000b2000031940c510b00d121b512040d54441c0c640310702030350807800d0224400c883d0701500d1010801145441c40e2a540700300d800e845490380301d140183c882400d801d04500030f0040d500403442910f8607a2861981c1d031860005841103ca800317601d90400c0e51101c3d400324500b0b46034030a041c041181441203160203405a411900804100d280541c800e500801c0084c1c07428060300d0003a405a08244014810f006d82403000002820803440214604a01d03110000d640307204888504001d15944c0c2c01242407031b03101d030700c9a40c0c003884010000c0c404041031a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 107700206 1250 107698956 107698967
    0x1020a0b0c1b150a0204050303030f10090c03290d0f06091209030c0902090a09020304050c04061401120c081611060a1b0201050601050405060a0e030f010b030f060f270d 74
    0x541c8900c02400760310014203181315500844040d40c0010340503604607183d009144031100b101400362450040240307004a4814850b200d641446441075030040b9a040140420030090b0802d225801c030390f8161150712143c5610741020b0341d02c480b41d2111302451f0300001401c111004000e0054001c01710900c804015140b81c0d071049448090740d001e09a088007695403000031400300c2c410341e08181e0708070a802000b049810466400380d03074401e01400580b080e50300c0700d000040071145250001503202d2210300a10715a03590150b2001040c007882c1e6030800511048a4002d0230f04500101102c0300c10103440580000248039010910015018004880b0a0705042c61418090162270035403006a00c10030b0781184007144140503180c040c64068540700e2500781440244800755100910640c00d0100110040d01d10b0307201002080048034a8100029a610196007018201485005001c034142e0258080c4400180e0071429203801111050402070118558071400404a2071100e46c810fa90003200c00b480c00c00f82d00311 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 107701456 1250 107700206 107700223
    0x4062303100303020601060c0c0e040f0c060503010915050307030204090201021504110907050306240708130e090303041e0c051908060603010e10020702010507020d060b040f0b01020a0b0c1b 83
    0x4d4003a5501c1380c0e02c0d00c2040741e4240646202a100b561b560004101c1d0061800700e50303410500841c0c4c003001005042e164120f17610066885070b000030b0703000030042140c280980720f400e2039211b5084508040d20b1800000079580c00361404003901c0b4030303503402600045a0003003001140390035824880e82c109191608000d0034810102001501a141c1c1400240c1e81c2e9200b0b0781124810780b00100361500c01425030b031a50302d035079039403868210517520100409030100d8481c0d405880b46140301d94642d00304a04210f40000241c00281a680060b4424808e00c0002590448440c425528122090105000c141821014030381554819034210184101d01501010420b089130140d441000c202d683e81c0d102c805c1414203c8255091104140e0040400182c0c41074298005141050052403c3d03424145150005010382c4d0340c0c0d040480340380c1c4d070300c20700b060a5080074094021310400307041c400c010369030380100080c0d2100d40c008001046800d06c0c01c0000c4a000e000c1041d182c041d442000c0c86542512000034a50352031906 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 107702706 1250 107701456 107701463
    0x9090a02041a0a02060708102303010b0a121b090f091101020607020703080d270c1a0403021908030a020d0201060527152e1103040623031003 62
    0x142c5240b114030072007400c1210750040307007603008003082d6544030703812140307041d010300743c401e280d82c0c05200003803210588081441d101040e0044652046204020182114104004e044c098400e06104019401d89081c906c0c20790f0741c000c800d00403221a04074201600e4941343c0c00294105240400c800c0341c030891a840303e2a200e10070b01d080c03a10b40300c990005980d506400c83e003000050b40300d0001400003440603400340003114805100850340000200c1e1825004510800d1200d07240029500c1e0020302c000d814001005003580e03e40101c00402c02d10404480e446640006070090450f0380210505c0c03504805c1d0403000703004440a90b034403020008402074407480e48103c440010342c00d10b54003184030324080e01150401041a41d01c120110490b90200054900040990150007009840018207455800c41c038440f400d0b00f8401440703072040c0c01c0386200700814010500344c108005005489040240001107800b5039140d130510765003400c818000f0148201112060422200300402449007140c20115070800341e921 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 107703956 1250 107702706 107702729
    0x4050f040b13020a060e060910020309090703060b1e0d0c261e0403180f0906121a0c0418020306030d1106010e0601090503010c0f0201050a06060c080a0509090a0204 72
    0xa481882d56640300b11000d000c0d43c0300c0c214a20801c01640242d00c2c4011544002c1c11803400c108201d4001000f18080c0e41075240542c1000403440e6840c500203904a60000c91400c08100390350511090609a00802c0030481c030303c0003404080014201c40005070b4a43c030800c10f0085c8104014000020706494403610440461004000b102d5204084202c14a100380034054850000c80001030200c800c5082c0540290280203100005940740b00c60719010703078041e01c41004100716151030046040c0840314941d00c040b8601c0d07078403c0e4260015042c0080c4120705092002c41c403c86849100440c03030144030b142d11501243c00c103501c041b05614210740180d4411031040303050780c010fa101c1500c00e48200900e2240c0da42d05400103001401140c0b01050340e19003085042c07414140340c41d1910040381c2112001c855041c003184419940001d1180d09000b0154070603040d020a105040c40c181014000c005032000040036a24003280f2030344460f204800791500100010018209404c0c044a00f178002d5126003e565203400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 107705206 1250 107703956 107703961
    0x81c12020c071a1c0203060604050907170105010f0215090f0709060e0a18060207050102040909060207050f0d02070303030b060c070e04031404050d0609060b130c09050d081207090504050f040b 84
    0x4030310402d89401300c8070b5006a030311112070550204021b6000500c1d056120300c0078040495143c4402846034801c0c80c1c2911010300401d00264083d0012005900003410484860030800c0303070075404100c070bc80030710381c6090003010b9844001925040401a010710b00951051800024031520250080400c88200c00c0800059840d1540b100303003902c4080e20ba85007811000b95800001507401c1c0d00034011540140001400c2645400c084011b80d1328411099900f0b0f5008190a014400309101400d10004090003c0c242d03144803001c080c0d15000705102c0a41456600e4618130b005448600c2214400300701c03602030744c41d92601c0e0f920425210205540a500080007900000f0700c0d1039403481240c0c15104020201c031001316465440e003006e00700b02d81c1c085680d5500d0309440e4009403902e150100d2a60100440425030754280302d40180400342c9540b0180c4103c01006200001c200c0d8502210b00200800c407480030300b9a260707101607031031200503807005400c9464001089031000c58120600d020f10f204003013807083c58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 107706456 1250 107705206 107705249
    0xb150d060905010501020c150c06040f050c0306070f1209050703030801031205031504020c010216060f0b030313170a082106010512070e0d1703011707081c12020c07 72
    0xd0b0000d016403400360b44420b121514074517101903040510300011544620340300c3c100c050310341044410f90f41100d284685c03190b0181000303020712681d03640c1d80e020f40081c0440c0c03420420050a12003404090401d10a20f440810003104a9400100300706401c4000c403442c41d55039140c001c19a02c424401510500801c20390700e41d4040c031820032a406102e6418034240c031002200c00b000000e40c004140382d10107650801288040c0301040488990060283c01c001801e0803140c42c6440644100421981c0700e82c00c05c001580c8003260300d501d05420348030010203480d2510028013074079140003c0100041c0c0707040300200d1000c4c5080684000b007039610b05001c0f9916100d894000c0103440a014110000307800310410780000e21110b104801143c0c0b017420041100404000541315104040d00c2026200820720000005010400c0c40281ca60121034544001300901480c1004d000d88a03031202e01c0075108900c40701c0860740c04a1195a0300701c0c0d80c42c2800800c5540d40c88901d115960340d80076200b100c418062558100010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 107707706 1250 107706456 107706461
    0x806040b100b03040303020318100b03010b0607080301030b060d0206070c060f0f05030a0f02130b0301050a0e09030d0209030a0209090a0515070e09060a0902040b040609090507050403080c010b150d0609 88
    0x1100c580e520300b5802e60f210740e50141d0107500300411065982d41c0800070281e0300c02e410040c213a2011000308000a0080c2e0080515082d070381d00d030060754002c6804100490001c0c03102000c072070440340c001d01000b1007500d88a000541d010103400e0082e50010011400105000314142040201c5100b0b84805041180d10481a14801c400050703501c089007061000400141654004012180705018018a4040e4203841001e1000c1560410170050340c01000611141c00d118480d50060a21031550030011b2521500042d40d03032140da155016980d03000714070000f42c0e490403c01d070b90205034010402061031600c40945070b0b60b1b2038002d50030307942c9215105d06030715414070b80b0f40105d000c0c03100341c1c0d9100e022800384018040840c00203865150800311490001a03910007a00c09400580301c020045991245030080040c66242d05421480010385030406100322142c205080304c044950042e462611001d0b800d10305c031b00410303092034070641000500b03202c580713080c1c144c074010184040040820840207486200c40c004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 107708956 1250 107707706 107707709
    0xf04090e07030825140f06010b09030d110c0603131e2609130e10020414010c02012001020a03230708041b06020c0f03010504030f050c01020c070806040b10 68
    0x41500c0804c0f0f004440b20300314000c070340021655041c1d60f4031a2030750790364205000c4840e0b404450356040302d01801c4a07220f060019030f006024210b10130f800c122007900043e88500694210000b0301145102100c03030b005052010311542000100004d4907403404254120f050840383e101105c84082c10245480c05a800c0d284442195421210151018403104c5208100aa2065032142d406c10700307001040b80c5a4a40040d10f0725044050310106100c0e0300d00c0f59451501c0c001100c4482c5030f85c0140024400b40074910310312480c0603400d00e406a600311203400180c80c0034050901085d0503004600d41186e03c0b000540090902803905c7c0da041103c40050100b2081d904a0f511140040284040209401c0c5100b626803c1d0054014640d0402c4c05074484429920141c5a90250001da0803c540142151500c0c1400015a072000d40c0240111701d455a4000c100014070b85100f028841d01080403464003000b541507540c40c0000c441114031258039001840c0e1fa9070802c0341c003243d503640302d08009030410714070012000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 107710206 1250 107708956 107708963
    0x114090105070903020603090a0501050412020c01020f06150a0503030a0c020a06140d021803030a0c030206010911120702010e03070c17070e0103060c3501080102090a0501031806020f04090e0703 85
    0xb02c00f64150380c00c00559a00150007403e00d4031492a021020403828480e0f28051482114070058520140c14043d080102820b04541550415032419200103000b1031407a502100c08000c3e11f010380c45160008081450540180303806100200e01070031500c2d0014040e1021a000711820348045541d428119a180c80500206440031014010214094003070380142001c0f8840341140c3e042c82201ea00468a0350304000c0b0b43d9000640c1e845e0074401414dc0611000740508401402030081080341c82ca1040944180441ca1441c0c0c03400d200091411403003903001c0c440d03614000d01642d41d40d450908066500940c5806405144400d0310032000c000c54000070303501e04442504600203000c0e0710b1074032040010a0003a261401b40000c1001c03501a01c0d00c07980d464089c1c00020b1070489e07e114003c1041506545050b00101c01986c41040025041c1c0c1d510030b9440b040310b00918000c5044003503a1581188007041002c0140507a001003104500140d030310340a40709030b440c1c50030100701c05c04072044015510030340307840040c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 107711456 1250 107710206 107710217
    0x20705040204050a060318060e03040306050106032313170d0b060711010c0c0302100507051b09180102040f09020304050d03180803060f0306071e0c02030d051e0c011409010507 77
    0x30000a1b019420005541418003c02d4a45032502d4443c14240c1c0c904080861141d00001018410004e0a10400d4050222807404016942d000034a0b0341070210614015120342e01c11a00003807806c0c038100c059500f487d900034400480c0109120614035250882d07041200780300c0c01d002c03640d01076042510035a00f80c40d41010f100e410b05804600191000446100181e424201d00400400980c5030200c2003078100507169500c2c0c0d07070b41d540c60500c1030034070142225a111015040380344010355519400d201d9009a10030031580c2e010011744120311b009106681c040c0c07120200741c243c0015900740300d41c045c40c80f0390b015009032f07a0031060300c0e0320880455003030584d424904804103503060701281442001e103920280280690210900c03400000e49400d104507004000203805070b0f2045198000041e07154580c0340641000355001d40c55500107600c40c81c03039030b840c1c502308800031482c20b003800d13000340301a803681d410045010368810098501c0345c06480291050014242600c004c12408441482814840c1d40b09a489 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 107712706 1250 107711456 107711459
    0x5070e0d0c1e1208070b13020f0405060402070605010305011416081611100b1302070804050409030509100c210e0d0606050406060809190b0a020903160603020a020705040204050a 78
    0x294a099585071402c1c094840401034085404806400010442c0740141030103612500c06240c50190510b0040c02040600b262800d0b00700140c0b940404402d050000300c8012a1540e600340118009000c1d204000d0f050505190001050090640c0038130604110364192407216502c2420281003e01c0e5030a0300e1001607001c0340010081800134580b2942e00ba000e1400f5041c1321b0050108501e060b481303203a030701a21903558140640034985104442c07180c40c2203003010743c01d140c403e40781d00417513005504c0380302d000d66190440385041600c148200c4d6007650b40144115034504d401c0d10300070b01c178800e0008100c8014000580182d078044501e580a5607a407082e41d01c03281c56071103d0042c0004070130302d10012642548c5404000c191981d5a0040c0c030f01402c40b07555107100724508050104d10f08900c8640014242031a00d410300007284900c0306041e80b080003810003580d00c0507030303a010078a03019480344412506049450003107125589134008115a280c0d41c4c1c211030f803003a291030030001240318501c981da0307100d58035260 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 107713956 1250 107712706 107712719
    0x50601120803010e07050f030c09041523040b1203030708070503060a0b0a11010204061110050108060f0c0f0417010e010c080a0c03060b0711090906060112110c0d020105070e0d0c 78
    0x35903800416890400d04281c401c6800400640003510a041c001400ac1504e01850400d440380c406010708000e04a1690761514000340600341040799411754091f129240118103442c1ca0700b0446003081c01801240545014004c41e540340e8100f138a500f000900070348041218a4442e0782560b018006c0205124a858034144040005902042c442e00030311040c1d405801410340c080c07018000402503034070b07010710882032038180740d003010324440d101c2c0070381d900e000014004000c0001b040ca500c0010030024501945235010400e0042c042c01c400400e80240029020030300703400c851564011420408020301007004500200340c280c0b080100741100051810000588180e00c41e0030260b80482681070000300a6180c0307004103d2a4803000040c0d403d80c90400494003a4140311401ca903003e1208809003041d4180100000c01180f440203100c500310b600c4040e1310341c0c1390788420101c5082d2180601110021013080501a01902e0200c600c0c00100f069041c6c43c0840d811300f02004282030754805c2070403408034100300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 107715206 1250 107713956 107713979
    0x81e0301081023070801050f0604031a09030c030a05040603060509040b04021903202103041202060409090f0506070e010507081e0d060810060b1902030d11040305060112080301 77
    0x354000c04080350f80b14220f15411000015802046150744150141d03060605102e4801009000c0d14040c600401041010400010946404601c5030004020755119140f80d0340c5540117105800310301c0d00000504040640c0c0020041c01156410346050003403550365010000e002c030040340c0292010340c2c0030b00000c0040c941040c2d0b01c10080400034500242a80300e460b04107a00b1035003c06000380c0e034056010440140f0307082a900d0880e410306070080c041c034102800060740341e025030300c65030704494942603104045644034030681b0050a4440780800004156080c804440b048056003683c26005100204514511404c5002205001a15050300e88a80c60f69044180d62042c122607401e2010005920303181c2c901e4400401190851980c081041802c1c640d0040c10404d04540712032205140441c204100c018500c01da40400b4529610310300540340103507059007144100080501101d14011400707100b60a13000161003624017903021030f081d50b82c82d24a085180d1030f04510103030902d082400100310288111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 107716456 1250 107715206 107715221
    0x307060c03060b0a081b0403120c02150d1a19060c0203010204030f031722080a031d010c120225060905010f0b030d1419020c030a081e03010810 63
    0x10300d00021019070f503001038126500400080d500141400c000e004840b1002c41c64009180d00c0307684854517103855580e501c211030310521394080910040e034050b9001d665550361141c03400140303048059074441800780404018802c084180100c100aa910b044180c200032507030805100280c0e81a9000302c0c207101c4181d4001c500340c20101e0b40f540d02080040006032404041070903203403080c1c6448148500c5041c0350720030300c01c0041080a8101d059034070750319902e8400303944181c00e0350090303501c603554215520114007a144002a902d0400041c80388110041c07c158402803c0c00059540e468188400f5480700d0705910690142c0341c031340001c2c405021555841c40c0e07500c5048138815000014540c005075900c50a480c41c0c40300c000c0c4425501d803070070301450409000294946100c0d240c2020b01c1821038000403a907000d640300d455900d10900302480000c50080050f2440355070f000341180e81100f46072405002c990b1010100326400c003000341c500181c01c40110190303816526001c3c050300c056010114498002c144a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 107717706 1250 107716456 107716481
    0x90f060509030c03010f060f0b0901020714060c07030302060105010f020102030c03041e060903030f05010e06030604060c0309020616050c0603100b0f07062408030702090604090c08030c030a1e02030706 88
    0x4503d651103040d60244589443c818440b08003045031441e100045061402170782c800f101092040000c2c4450f6a404a211010380f030014013600040d982c0072000c00d040d03005100c003401f5075105080c004400e06400080c541d0403604266101d914580703e840049090b40000e0760011300301603003480401c000401c41c1c42105420f80c60f01320120041c5034192204003d844140c0700540100360358900001005010f40901405062018000e000604045002c26600d0328010b102428540c0d4910b07505440c0381c4250031070640d440d0000c203040c1d254103001c0c400c0070352220f010320216250b02c200740780c01d01d260400005580c81805031100980b61289001c401da009070b8010315a0000b085410080d040004000f482500c07000402c61680d40e0320818180c0709044003102c0e680114002da0710134070810006a88600515610110948001c80c2c01c03401c91621b032440713165a80002450380004600f40a84500000280a580032156242d08028040d18610601245c5814500300186c10405c0f03503c003c00c07451740104028460 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 107718956 1250 107717706 107717713
    0x2702060c0d1107050a261f02030604051605040308030903090607060b0a0608101e0509090a03030506180a020c0703020a08030406020c120d080702100603031e090f06050903 75
    0x24440a501d060150412030a0040b401010500280a00c1002031001404082c0d038100009810000c94190f884100030007180c071000c070604e05108044003170001c00101d05951543d00550405d03441c041d006500225040e1b401545000001006400f4691440d901e61a41c3c1e20b2b9a032405095440d4012254801041710040b4801048696550388482c0300515a0078052400040c049044108005040b01c42d0317444101000350101c10b021035a111107001c10109d44003941c40c0051a03048481c0d01c50305090070351020781d1200030b00040000d500c402007004010240b0030380e820005583c907481040325403190803003082040c2100318002500e603082503008100302603001d81150205035403a80059182079641d00a481c0035040890100300f056010070841a42400071103c0080e04406254020307907451045803640d00b00420031001c140d0850080c0056001d5804809041c04001d840342006808000308400030380b00c102482e088843c0f036602c503050960944040c0740c00b58a0403440e000f001c4855400c98042c0347d03070600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 107720206 1250 107718956 107718967
    0x4270212070f03081c110405010302070201030f050c070506070c03200a1205190207120807020a030606090207030906050310090e0f07090c0801080f0c010507030306031506090f270206 80
    0x2404a010b000218802c00c01c6030b5441203000111800306009002030004507040542c1c46803010760303c8040c5c07010340d6020720b001030700e9052034001240580303115603010b82540d00e00004d2004040300280104035807130091044070000d450b1441d04442c003209428024000071104586035130703800e503d5441d150350494200304540030b0342129110710084511410000c00880d1001403801c1c0500b003041800c01ea00c0e17100b40043e004c042c0c50700300c0b00408072949204c018103014000410700210f54640380d2010195030880f004200707560302d0380c103082e0003580301600c00d801059241c1000038440380308078106d92164140c0c11200c1b050a00d0700d90380380080e00d44040c0b90359070b40c0502d88040702c4e0560304001c40801000c6042020810036040c18010b0005901030300b0030041900314034080d090044000800c158082d40030b280655a030502418114014540340d0401071510401201c0384483c3c44070341e0011b4041d640007581c10050007182000d44003c803440340c240200e0303401c182060f9028039000400016480390015181900d0803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 107721456 1250 107720206 107720219
    0x5041805101d1005010903020109031b080f010b18070c060504060e01020a030209120a020102060705030613090f050c0604140609060c06010608041e1e03090306050c07020427021207 79
    0x204108050340c600c0b0350400c09101d002d03001e0030005080c00e08101c1e98407030440d00024031501550101a100a12404090081900c4a40110b00414812041d02d14403d114541140038000243c4a00e210b10b09490a1600d0003400c4940c880c045c414503154003443e2a003555035400503000080c810b1304d1103130343c07411b08049001084c0002c06102c41169001030340c3d4002c0b0b0080000d0260300d48100c0103540e001414500c0181d8001558035000340030360400948a07610303407001402c400c40b140d800704511400d0001c610104141074010703887e9a8440c000b5503003000004002d2101501661140c40100034203d00d14291508054005001c0108064003017071420021a41191401100703034455800904202e0400c410301c11150030040c80c5000000c040300c041c800a84450711654009143c0701760100c241018001018042d00c0d610700215846682480b5034541000010781c0380d044090709900032400c0200c4000705056403a8107032000400001000521045078081c059551003035034102d80644241d843c0440e0b03c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 107722706 1250 107721456 107721479
    0x307050402040b070c08030f09130b0604030b0919030f030b0d062c0c0105030402040c0e04060b03010f1d07051c050a0c03240e0603120d0606020c010504180510 70
    0x24143c056605591502c403403a20b26802401540300c00090741041c4034111954251100700d40190704200c5054500c00c40100e2020001c00c0707110400380d40028009400010400b0080c070451044c0c0f4007500b0b072085015001d9410b4405007500724010001020300c07190008450099100f92108040a000b40d10003444a45e110401c40e8404c1c1000303286543c035409055804d036461483d00084c1d10403200500085501000042d10a010140c8001c2c4916150220300520a1085c00c01807940b01d00100180f101c070740d4824450800381d00a02a00006440e82e0801040c01038585072448015411305404421513507842100b241c0c550880c040507040400303101c41c49664004680205d50203004200000503e0740d40e415405011940454084c0c1d00055400c5d1030349541600c0100420b040769400c940c1e40710305543d01c800090030040c1070740003846418400b04103900c40b43e245034085019140e0325000c580c1042d41c0a030041d9000d000c1c0344940d07222140d04000007103c0c001190840c0307070440c0c0e01d18000446c068403400d900c140d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 107723956 1250 107722706 107722709
    0x709090504080d0b06210705070819090b040303020703080903010b120f060f060d0f05010e030a0206040c0504050f0117070f120201081f060302072d03110d0c060b030705040204 77
    0xb0007031000f190700303001c00d0700074880c42462078402c03100c003884c245c003540b450088280c220240c15107081c1d00b40001090140500101da11103940030350342c2a075820050b07440380d04440100c00d5190000b0314554000c150b100c1d0304001c51742901d80503002032901070300d141e032071a0791903202d003001c039030555200c0141400c0386d10703061070411181e447c1c080681401d44d40c840042d460494010444c50108240d202480401e8842c8109040b50541000f0944c1c0a007106d81401c6006d0003240c0010b02c198840042d01c40426940860810b019502c580390904850f941d44c41000242c84040e2000307948510a080100442424140010709281c00740b416550115900c501c10b1030400da00c0d6200410b0245501000c008642c1d101c5035244d4000451004071074039040580036007071100c03001c1c001e9405040c0e001426105001c903408103600002040c9903003c00c0c070b0941e8060b103030246c0d940a03012000308100300185070082e03101059180765600c035a03440c40074144a44d02c812000c3c1400e4090700350540200400429a40c869000910 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 107725206 1250 107723956 107723963
    0x61305130804030c091b140a090e101805040b13031103070605250819060e0103030906021b031c0c060f02031603090c03020f0a1211120a03170709090504 67
    0xb0b03052841c110329030302034501c401e080c00d600b00001041030303401b580c004420465098415000c030340c441265110545059403503411034100c400100007008070600f0300b407a0010586541c1600741102c10b13001030030841030726000d880080c0110700320000546070600c3e2041c160740d480e000b450b01c00d520614000682d070070740d40110803d0707d81c03a441e0400c00903a110140c0d81c11102d05010107920b0848110888000c00007980a46a040e0404071208510701504d00340d00244058030303200000f5581540d6a14000d414100184112400350048507a464074140300c40c4190745040d10040c01074013500c02d000c600b20b644100405503143c1031084160204001c54524864031121802331000140d50b4107060001c400d280b4000248201050700b8103e890000610301c03502c403401c496041c0c031401031702e030301c0300c000640d01c030003207030001c0507042c0d40c0004d00800e200020f0f4001804500035a039000c041c8805e018420b0312000604000b90200e980b804500002006002200e588407540e4900400d41c6078885500600ba17070303800e03181517 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 107726456 1250 107725206 107725223
    0x3150b162301090c06051612030b03070f050102060c03190902130c17060a081504050316060501090b06040e0f060a0504090c08100507090b0a05040e01180c0806130513080403 76
    0x6004c001114801002800039420b0090500c040488440750121001c80d00510038201d84070044d0000d030082d00f00d035501900c020207039804181c4510907000d07507901c44d1041900503c10309006c00c03211104401144d00540d040002260030030007800c0b400014101142049030040f0b001c0400030418009032185002b08249542c134080e10100d81c1ca48280a01d00140c0b03500c0c450200450100420207002511040084c42010124520764070303410014258081c03c00040100320b0b000807903004000d020350215041e40c0c0900340c10401c083c084001d003d184d000d41c0c041d05110303550307201c0032560301da811400540c0c1c020b500038448030865458402140547c0d240e031000716421b48260406010b102014021500c092039541d504214914110800500e08040b034070822006540010324000c0607072084044030050003e070090741700107584d680c0d43c42c01200c1d0034281d20495540703814903c4110902c80d000050048070006d000307030130112403490114000c10024100210782c140120000740007034100c2014100460062480c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 107727706 1250 107726456 107726471
    0xb2109010b0a0801111615060b0a0906020c010804030c0f051006030209090c010c1509320105040203060106030b120f030316090e13030509130c03150b162301 69
    0x50001d58803068001c80c0340f9074100107500c0b00b484400b8003a20704002d080c005071811492030b41400040f85104030072403c3c019007000d401050340c1c1582402444001810780e0307501d0480355184c0c001c82c4c40e03c508400050010307208001140100740300f40700040d030032409005050348080c0c1c1c540e1000e03d000090751040481d40e031100f07001c00a514100c40915884034050b07015002905071000003c081d2182d0b00c1c40100b441c0780b42003411034001c14035400115100e9001107121b03940d1a20180c004080f80c1051413840e4400c402d0a42a40504818015240900c0d400f41c0200b4480c0d0074110700303030040c209000140340c0003100b5401404030103500700500300d0841c0744a009140c5d03030b0610054004511031000c060030300748a190704041044860341c151450348405a000b080460591900c2d081394a807080a001070b0b8860656001c1138001070070f0760f01102c18402107840804c00114062200710152600e407151a000550502039401115515400303003081c10302c50000c8820717403201c03981910382080c00d180480105a655204 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 107728956 1250 107727706 107727709
    0xc0f01060e190203060607031116060c020a080a05060601200102040308090a1a0403030c0c05040515030105011d010b0f040b0706020306090a11090118080d080a0b010311040b2109010b 80
    0x8284080b010300006620f107140c03810104e0b030300e031140d201c004042200071500f00307910800501c4210b80d1902d000500c002d08a5403000c000b86003c013076120aa01c201c401300800111920009141c03514564814040d010380d960f04001034903400408484d06d0320144580d19550450300003071000700090744c0f0403800c00761036000100512506641d9904401f944038800c00d40d00c462408034500341d0f804c495042c1383c140c40c581c03014940207000d03c0156002a410900b80402d004420241c42c070100d0001001354000c0012f6070b41c400f50350044071221010700190101c154018043d440c8190000c0c41070312010204640340c03660362400030304c081e4441350301034800540c040305022a91424140007904401c0a460600019010986203a214861010500c0c10312010000701c5c50481403580c4810000c14201d02038502094100401500c05c1400301d40c00c02c0141d00d40614801d840d07010b032145180300d41000c024281024140582e0340c0e000d92213414803900c6900c4400c002c2d440f1503100d07440e175481024002c00200c1c51115000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 107730206 1250 107728956 107728981
    0x90d03110609150a02030c0f1603030b090717062403070f03110405041d06090102070b01120b041410050103030c05010e010b060915070f030302030702070806070f050c0f01060e 77
    0x5201c222180c1140c0700350003d00d00508040d030340048000400603665102e40c030002005216030300408040c0400461010400c1031400700300b03601030703000c1e031001d000c04050b20301003080c3d030034045521401040d01c040054091000c03512000b40d1104015140c603100b00201d42c1d07443c0c0280c0c8550020000321a0000400c00081c5c2e00082c0d01e541070030a801d0520108a401030b811501c3d0049026880c06103698a071580d070b003044031190700d0b101201c0360b0341966132609180b07441c10b020394030440d000c0d201c00520317200024215480859190030150010048503d544070756841000c140c00c40c1c104000e15118800b1902c0e084102c92044900841c420f40300d811301c0c0201c85c0b8060342901c1440e40302d0f0328940d16124000b0600c3d15000100ea0000c4000c0700c0210111040000c641c2a500842c0b4015113400e190b90f04d49810190181d000b18010400c54003103035015940d504805689001c1210040c0020700302c40310442d1100d00032405000c080c86038109650343c841c04505841d0031240e15900c86040d4600300b40502a40d01d0444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 107731456 1250 107730206 107730211
    0xf0519031101060f09090204020d0609050a1505030d030203040503070515040b0f24150f03011d0c0702010c0c05191e0303020c09060103061205010203100e060d1106090d031106 77
    0x50003c2c80018a00202c1405a0303241c0c1c41440a071644a9800300304540d5254120342c074616010f42c04000c65521094100000c21045920a002c80c0c40c0044026204100c281c4840403604c0003001045414080c0304101d02039000500100c1d014070003440204d002500a002070004424a000e4030b1819107072500b0402c002d00d102800d001c3d422070315401880700c8140c451000b04410407240180240c0d0803142c0000c200070784400640c001d6800401303d054a1040000401541211811303100b484040041002d180c407040000d42d1003925008040118800650145690340041d9008090002c4860b0b5030304040750b0b4107110b04002c2c80d400203844005000302540302d0f45821805100c403214200781421076030003035034460840c4902c5104e40c01c4600010356503031180c1c000b40d0141096459a111000144c50a80c4c040d42080c2d4140c82c0540007580080358018000c03000501c144001040c0503040d003003c3d180c50420711413640c116a000359080150040907241d45c201111b1881c41f81d50313005800c1442216003414007401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 107732706 1250 107731456 107731487
    0x12030e0414040302061303091802030105040b0f101803080d0c020105180c12070b07080c0609010b01080c090102070317091f05040e0c160c06021509190f051903 70
    0xa1400b4032020030b0340003d80c0e83d400701103900c81c460008810708041c0e5080c405a80f00309034034a500224842c030300301140c010318100c0d002034400340030341801d49040115000d911090a90803940294800c4803a911804208450392860035071064815129105d4142903800042098100c4d501d4030b581240161b824411694007000410f525807801002c0231041c0d449408284000d0310694000f02010494041800080d0060821450241c0e590316585454105504043d03407100340c50085d000000d40c044818003c92a02602c142e540c0c2200342c0d44d2070202030700368000302203143c118890200c0c084000b41c034105e60815016540c038446034980c4980420080002038a0061210b024100740d6144d800c603030805c4c152000c0d0f8074000424102c0e0754482c10007003454002e007203d410307110100700d0340b800922040d80c08000507180a070342560309085162030b00540c42d0201f0b5030400c403181e21203031410591542625068142c0340c82900003008050700e9443d81c0d860640d407004950b2031a0b002d000340c0d904058210f08050075a106 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 107733812 1106 107732706 107732741
    0x11030703030906020708011107060f180c0503010f020c0d050313170301060318031e030204051512060306040c030f02060906070605100b070f110a12030e04 68
    0x78802e80f005809180e001050301c0b50103008100c02201150744c0350303140000d2640c40703400800300c07090406c10b0350f80c0c0c07134000c01582264880c3c4407610714011032660301c40c2402c0c48101402c603200000540d064601c100302d0103004180100e143c607200c5080c1d003885d540301c0e13940001458402900c5003000303052100000d080c407001d42440c0e000d07605035111547d0401c00061072000c000c4030714a442e1400750205100c15040401d8000c1d890b09010001580c0c030300035043c543d1350ba020800945803520601d1001d00007140b005c3d2240b000ca001303640d029030b04070002e000d14101500c807119200518000a4244002800d03100d042d51207400c1100c0e07948101070411940c80029080c01c1c0010034080c1c40c185901846224005610315a410640cfc3c500c5810800c440035100311640c81e940900c0d0100f107141c0d00400c02010004030203441e0000407020b18020307143c50201400700010002114608080c00c00001c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 107553956 107733812 := by
  have h0 := BRFrame.cov_init 107553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 107553956 ≤ n) (h2 : n < 107733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
