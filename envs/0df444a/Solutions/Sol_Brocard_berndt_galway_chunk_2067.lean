-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2067
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:10.543075+00:00
-- url     : https://prove2.me/submissions/c9391d58-93af-4ce5-9138-70dd6fb911cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 371582733 ≤ n < 371762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 371583983 1250 371582733 371582747
    0x10b0a030b042a15020d0c0b072606030705010801060801091d0d02010519020c0a0f1403181005120f0703151d0901060302031009021c08070c0801020415 67
    0x3401160800090803031540c0199007214035030710030f00c0414006a000d102c2e8805a24050b040595944000c1a940301c00c007070003802d503c1071803030003614142c002000164403c2c450400c4014101c020280145039841003c0380030035507003094950724072078054000c010556520412210381201d40c0e59862544592918021800801161410004850fa04845001031500422044892440c00d600004240c41d04904510300c07007c0d140360141d680c3e801001521071501000030130f41c914582101030518891503910300301c00c1d40480a891081e03280001700d00190710402d20b0115403816039040c2c0b0300b020585481c000071900e902c142e1944003100c7c104000812906c0e84080031040c3c0c0301d50b0600780015000d80c07070f0b4480c0442203501d0b44640c20321098070040c02c3d0703600f01d00b10001c0d03005081c040007804418190340c0020b40301c0303403115080c100259450850409645d207103e8811248030031000030461040d180d040100c032a500a54043e500c5a60107400020740000500c00c0b10704480001601c0840c81c087d40904032808 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 371585233 1250 371583983 371583991
    0x110303070e0a051018050907020a06020306190e01060806010c1a040c0803030901062d0e070c0b101706220f05010e03042105031e0c0a030e12010b0a030b 67
    0x2000b042840442c1940b50302140a61034441611101031640c50882c2c6001c0c54282908124019014001131140300d540004801c652564422009038480d80c41d00c0108080b8030310701c481c2103103440c14800e0005404800b642964180c440d255550009581ca1600645800725807000061013510b8a2008007403811010400c0f6420501c5240b45030301c45a51822001c0c0345400c25902451340e65514401000b0385204034058a4600e03810017440c1d081c807034001400307039154803042c032410027008641c900080c5503511824a40c5080e9522445044050030407000212001000380640b11010b51034144081c17400c6c200244461149440740841142d0440c191889220b00800c0c0740c04443c40b01080100b8070000348203000d88499000ea80c00215115403034060b5003240510f003031100041c1c2510340160040800d01c04401c488941d42501c441c1d420081e01084001114032540702c443c002c42c09a812180c007059032020150182c560f040b221010304005c1481103130708a030720050306280c1c000f03103810081000484a9a040751301c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 371586483 1250 371585233 371585239
    0x1407020d02030607053001062313031101080609041707050102030103050114060a060504050103020a090b030a05010e0a1e090201020a02120d2d0c0203160b0903010c110303070e 77
    0xa100c890740428900035050f00c119011074004a9550755903100408280e008501004c0381d40c0340113510b045a80b40b0707210b060050703108000218110040f011a0480070058031b82141850b50b9580e01e5001d030304035001c205400100c0b0109017200c2112010f40c0314503002ca0041000130000865501d40d5561907825421511540b001e001701030000c4e5003c21020300c05107000718003c100219100307540d1505001c0c5940d0003003c4034402c1550400074807945a07c0825034050701c10a080040c0d50f8180001d05540c1e46910380c4c0180d40343d041c000b04200800741590403c50490304404c42e07010380d40d01e0320200c00c020f540300c1d502a000340844910b49009005856040985420b0043c01170341c80030400c03500404c1180b03583c80311180301988240c0840c5641603004200200e8103421209448040038403010150424101c181c40000300401c000041095503000e1140b4601c032414640c00c0d802d40b0b56110303201c034180d4100d410031354480d51a002c0d00a810074086c081c450130f6062140003551455480302c13003e85d005000c00c00c1d5290 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 371587733 1250 371586483 371586499
    0x70c1d15280e090d05120103061802090c0919060c081b06040b010e0f100b0a110d180902040f290d02092701060c03111c021c140702 58
    0x2901100259264025042d0300b1109091071412155603860b01c442c4151400400c0b00411401003415605840305055a501202c0454405000409101d0f092151403020754400f61080a2002451081000703103440d08050301c3c0308814240c1e0032040070008141d8031070000030410040441e000a800b50008201885000c0780c40240d002c2d0441c41545010021101160724440310b03001404900b000c0e2602c1a40645040c030035a4031071820240c040d1258845200c2d44000700c4010541020f42c0d80a2a0203840c0e900c02c11341103039183c01c8800d00040100410404004916a10302d00100d804003050089800747c40304402100116803921040c10030000b840312406000c00800e000310101680b800c0028100c54520070b4015860308011010062000f400e4400c0c0510840040b8400308500d60490b203681c111006c505005980c0e007050304080c1d58920a8903c0045503004004800721140084802d02d540d082e410341c02c584071030a0b000c480c6101d04020200c1c00c00802c0100a41c9440c0b00542c0c1c0c002c1c081c2038409810301c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 371588983 1250 371587733 371587789
    0x30209010516060603031d0a1203030b100f14070b0f070908030304060b0a050405150f010201200307020d11061504110a08010302040b040204030209060907090b070c1d15 74
    0x140002c0c0d10200c00c40e280d80e140c0404006240e4050500f428000e14003007a42e078602c40760800109012050b11500203000c03c062150000c1c50301a0f130155100c850040c04500311448001d000a011541d0003400502188489000ec003070301c0801402c1d144a1544080800007988a8109103003540c50300400350000c009283c980070810180038409180210710409021031005014410030400c81c3c0c05801290046203010100b001c008104800034691040a9035405075280307001c0c0040f400341400211a1100c042a59054400340141200440c0b14008981c280c904155681000f2140350600b41c5d400380e0b40781d00000100715510126136844141d400002c00c0020a090301c00417003000d580010f0f0710007020a042a00400c25814140560301c0003403401c0744c04624050840d80000e9110801802003406031684400041e0418000c0c08480c0c0641a120106922094140b50070685c1d94554054521145030131100099202032401d919401002c280c040900700241d0002404403801100c80f02c000c0c20750440b8084 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 371590233 1250 371588983 371589007
    0x8010c080f06240a030b040b010203030402091b040303020a15020915161403070501150b180a0b040b0d0e01090305030613060902030a0207060b0a030305070b07020f0619050702070b04060302090105 86
    0x10000f07440941c003200d880c1c0c0c416001c0030f000c03034460207411802242000440a000e0f070780401245c0d0700070f604560109960f20340e802a80500c9804007201465040d0029012060580007d120881c05109005500c07601c0d1402c0d006c4410ba02422401540000324000070218500c00c4002601c950504031191040750320964403042103000a82c42d1003c25604006424000d004007070090903a0328101c101e640308180c2c90400390200700e1141c40030212000110740b000107142c0d81c420080c0c1d0300500c101c2c400c076911030b512100d80da56268080894040c6491070302849408000040c028640c096030144ca4040c110740d00c410a108980a40700d8400b240310b956110f012422000600c042d5000b4002e1041c016110074143c60510f007147c0721160030301d202d8081041c1c10400254408116011a43e0064039000b143d1241c01099152000c01d40202486005041c20441c0b280358200c000c5c448107041203410f22250302c40d08020b82c0c8a040c24000d82c0c4840d1000c100600101c0e010703400030205003206152848c908081c46100d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 371591483 1250 371590233 371590279
    0x240f0a0e13060b0a0e06120c0a1b030206040308130c06080603161a1c0f02091c020f01031d15040b10060f120906050906010e0108010c080f06 62
    0x520106901200c14002401c0c4503030841c0c1d1544116104200c11403d051040d8210300540c0c541108003c0181503a81103502e4017415100c60305841e0854500e03074103110006298582200140c100050b986000110401854100001d61140c058025150940340c41d00e040352980c200030000800300760b043c0c225000051044907800001c010b40c1da80c62496007000ea04245c102800c401840d90203498000e4244120507001c0803c5414a88039541d541c1d840d0700c41e244580112000304d844e18030044c60a0403065841c4600e0b0014003240c10b040fa044d80c8489200184d00e62041095000a90480640c40341c1c05c205500a43c090360750130186a505001c0e10b0180903441e4075020400300d80c0c0784408202e505000810880034643c0e904244002c00003214541451001409401c80a0141d01085950003000d01000c22a43c4203e01c116000f0b2010303c201d103000d5000c55a200310a200380c5540310184400040d0704081032040100004583d564035506403905140481c5003003000c0c0c181070780020650501e01c405068048 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 371592733 1250 371591483 371591497
    0x40c0302060a0f03111e0c1606020c01030f060e0703050a0b030a032f03031f0b0a0513060305190b030f0f06180d0c150902310b240f 58
    0x181c2d0b2011403508050040c151850468420200c00040c41b41440642007206100d64180042000c00e8075680c0344540782e031610f00801582030311a55428000306029601003285d448540c1d080e01d0501c82c0006c454030740b0084401d20310881c1e05500051012a21240c0700303400c4250000041302d0040740c042c1070342c40000d003007103100c140441c0401c2400c0ca8407603081d405c1c94030802551505c041402002030301415401d8030780c0300090441d10080d00b100a8503044281c1c5a04910240c001d11029544600d00f405c00500103912600080d6034900ca40c480028405110b0b001c2c1078842c04400c2c1c1d940c844040c4405405e00940180303030800386e140c0135420200b610702030100304e441081400e0000074032103802c15000b140c02c4410040d0694960382c210113410220643c20810010455502c0111707624600c040b0b580407002020904802135021102007000241c0c00c0c08030307000c054070319075001101c0c0404104541ca1005c0b181601d5006410044001700d02300c034211100b451410100a49200300e1510221030103803c00da0340910 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 371593983 1250 371592733 371592737
    0x1e05150a0b0111070503151008070b0703200309042f13120506160e0a0803040f050d1e030512040f140102070c031b080f33040b040c0302060a 62
    0x14101d4141da800302d0350105040c5400b01514000317003040c020a8903a4540303c0050754241c4458040384445480e821507800901072001503542c46a16505900419440710a0590005584007202d01e403c010f02103035080d0f000b40c1c070001140b60991380014000580843c0c401c2c500b002c40c00326541d8090300e4502080880030102e030460071799204d030204041e00c1c0c180d06941124004401d489000d0001410010b4803540001482d1600c0040340c2400100310f078034000003007140350800c20640000807402000006041691048800351080310740342c8d03040c850010340c40400903046906401c0c0105101c101008540c0a0724003030710f0f0203460142c800003035054035041601c086550802d006044400d201032402030380c140e41749500007580f0b84007143e10b800040d0259800003505a181c2d40801d56108029030304206c0003490072109444104d204165080c0d118400c00c3e500c2d00e00b003c0e1001a100113140d0070007603040903003544120003017140c803940c0740c800d445503005004446c010008036010000d40d541d00b0252410141036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 371595233 1250 371593983 371593991
    0x1502010e030c01060603180c0b1305031906050106020d0203040b03070e1f0305131505090c040c030e0609210904060b070501050603070e0108030d0513060e1c0503041e05150a 76
    0x1244001b0304650982054161020240c241c4000040b088409441211020924243c40340c840d06071201e6101c0007580107613410712500381980d05084400c1d0401610b980540c0003080b60307aa80700000d0f6120440d5015103030068200308414044c0c07421a4000d15041501c62511122809600c8042090030780a0708050400340b800c0d81401c922a58107000700d5a00c0f5011881e950f80741d032001c0c0d0b04c1a02080000084010b203548800006502540810101850302801041884403040210001c0c004128091201285004110008000070000250210024007001d1203140c0030509c000d140c042d0b82c100210b410360140e00c0e13903070000340841d01a010b403802d14099800000c8074202502058541101c0c0d038484450400307418010082d0900202c1502c240c4800c52201150781d41d111440040f40881184008180d10f103020f001e14003041000507440c0100343d05286a43d5058001d080c244c0c0e19010494005101140f8004080c040200d210b14103103409100303c08468400309000c0d10000c4a440460380e071208075030380b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 371596483 1250 371595233 371595239
    0x315031a10060201021614010b03190c050603130201180338071d01020c0d050d08090307021309050309030a140c150a050714011401050114030708011502010e030c0106 73
    0x64092000010b20b2180000c40c13804040035a40c001116065a0280c016859070035440c0070500b00f90440444414000c7c1502c0a8000d040340704a45001407000075a582d071000340000c1914103201e01104e001d8030f1011441620728601d6401154101c01c034680c05c200b0b900d1080c90010000e18100308503c02004d8500500d400004404c00507101400c0c81d04901c030396030301e500342800300c00c54206641210048102da8200c20360040303c00140e15000003850a0340d00a251500ca0718140030010404250145159807200c40945035094160b40d24005c0f218040d500115a241707454004c480c42e8404a0715500c42c00036641003100000c0003c1c240880711030161441450100b200282e10000d05c031022041004907002e10b0440d600765526005400f0f400080014418000340315401d00101e82c0010880d08408802808800488480340c82c4180083c400c56001c07460030080c40b00c000400800b03482c801c0c11a60303030b10f11081c1e01e42000c5c6441c05040029240943d5600d80d100000908280000c02c60615058000f01c0d02c907103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 371597733 1250 371596483 371596501
    0x1203040e090c1c02090408030a020423041521020d02040e100c1106041b0b070501020408010f020414090a022101050909030307051c020904091a010b030105010f0315031a 74
    0x1090b0300f1442000a8410a6000140e50f06a00140c0103904111026207a64031040800d0091140d6040721040140500900014030000d50b002e41080a041e10140302d18502041040d003800405e00810500100702001174061505644080503424001054003141600030b4022400b2503054540000b8160482c0d400340c0417000c540e004440b04030b0068608802c1d081504d0150540b01d142c007502c002c20740008040300003908880006100058045603107080c3c2e4914440c0340040c000c0d8002c3c45426840d5003440400f2065295a01c207540440d2010a07000d42c1803440c600820448580040174110105d60a1220040041c40001c100071311600d501101416541800c081000904ec01052040c0c02c1d0310410411030116403000955550140d03c90b03542c41401e0f69000b10001a00801d005d0903041031801e5034840c00e00148032829214148a1081042143d0300c1e011101d54a110034001d090104806d9500044103521a030712a4001c3d21080d503800c4c143c2d03900c035541c4558070000061110702c0d03c20b0380424840c280d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 371598983 1250 371597733 371597749
    0x15060e03070e010602120c0f060910050c071a0603012a121a1207051f0e010c2006070f030302121e060f03011d03130509151203040e090c 60
    0xc02e451180d002580340c007400a584a10b0711030070607001d03100441c0b0030205950420181d00d400c05800306840091400030006a42d030640c0403001c081c46400e1401141810780c440f011200c560b40c04c000e4101c6840c110a00400003881d0107001e00d5003640d601c9542da0001e03020116081015440c076100300748800f455400c020a0010010202c0903030a25090105d00312841c0b91100b00c108450907152000741882c0715170020f0400c9074592200b5082013107941100103e5680801c100c104900a841d14142c210303010b001103440c1191408020980403200000881c50840d172107400c0c2007590b000f4100c80c501460b5944180280081403000c40c0071a0b00440d5140003261503401a641c09010807075040c088181c400719881100e04050700e00e500583e500b034820b00d81502d080d042a01030342d02c0c100c01101c0c5102d13a020855904d902041345e803501c18100020200702c038a484010a8003986d0142c5000c420200c01c0410000560301102c142da24500c810440003802c0310002103100e2290750004091305c0358500b06002c0c000c0341 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 371600233 1250 371598983 371598989
    0xe040c1b1b05090f13030215070206160509090a050a090204020c0309011b05060c03040f02030a030c0312140a0e0a0b0103030309030801090b010203160c050d0803010305100509100c0315060e0307 85
    0x251250008000e521030603072134800e50010070904040054641341c28147e040240c80b01c0e60010540d400804c110400340c0014186000302030302c255001260464841c101c409009042480360701c0034090340403c442440700e40185410003d00c62001940400950014040740d010200d50b10054001203036419441d82c2060070a40101c000c007484440381d10996842a032603500044c103102c092500840400c1c1405180d040d0090b58030ba004e000c4174803003426400d01401c030791a000e900b280000d070042211036501001e070003084910003824501d00142c2d11102c0811016000310b4175014480e100309961000890142c2402c0c44c020350007030b10005100700ea64240102403180580128001d035042590342c21482e40e0003c1124082c40c600d0020000381d0400d817030001394103441c0c0c1e4445035000010f541c541081c05080001107040301d215108840c82208000ca40b40c060300c208032541003680c0c02826150140e0040da030010b50100b4524600040c11030041030f25034004241a401160025005041c1104d040c2010032800002d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 371601483 1250 371600233 371600239
    0x61b3a14010503060103170304031803050c04050117150c09150c1207030c030e011e02010c020c121c050c011103010602010e070e011208040801050c0304021009060e040c1b1b05 77
    0x403d40c15171f1a002c0352840207050704c50003144000005010705102d690009003207014a64101071841c1d51341001070f903460403983c0103881580341400008503000e981420306c408000500140c591002c08203506002c00034000c1000030600300401035101c4550f111000440300c10005082076031280342c071a02851070308015940c084004003080102c400400e422003a01026541d251034150000d01e1071100403a10814440300e00d003858101d149001400507019040501d0b04469a4225008001c5540801091000364015031000c0d0f004500d01c0902c04000585818036101d107070801e107141030140035a1508480c40e101410b440100080018003506034203003d84804c1080c0d840040c11130a0400c140940c40410611038201052060b004000c2004001015200103100d154020000f918281000d160740e5803040342c0880c41200c4041481c0c20f0540110a0801540e140d513440c021010340d258248001000501030080600c400d00d0525002440b14bca2980340703461145001c031104030480d054085a0600319000b070340c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 371602733 1250 371601483 371601493
    0x30506070c080f030604021c0c17040218060102160603060303091203080601080a1e060501080c0403050a0f0f200909120706020d02130b0c061b3a14010503 68
    0xb00740c05100b0360f03450015420b07100f60340b601e072280042c000b8480d0708203014001c0b40d500f02010f1550a07a500000b03440c000d13501d5181490620402e44c003000001120300a5000c0c8921003a140240341d0051090f50000041c01100d841c1c3c0c03112034040d40d00100c00d501130000240c841c0000e204141d40681020000c03e80044d01e0f0716000070139a0083c00740711004214904110f07040d40001c07620409600460b8062030b03a02d50001c010000c15246402401d0b90780100383c0810348102c040f48032900d03140d08640032030390090b001c1c082d00b20082d661a0040c240c190001e54100451903007141c0842c1c2180780c5240301d540020b0114001d0311000e0b050201d915001417607114030b40c1280c2c0207004004001d4046845c0c2641c4136500503a11409156584020701402d07254074030752000c01300041443c1280e14020300000741510221440d60356414945802c0d100442c5480c21001c109021091a843c145034040c0c00800c0e0042161030307405031118113120640900c10030f106120342c071501004003140201011350702600040e00901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 371603983 1250 371602733 371602757
    0x108090604021002030915040f05060c070b0a030906050106050a1202190e0a1505030414010501050a03301d100f0c08120703090519020a120206210103050607 69
    0x2a849000080010b8040d54482c961006402e100f8070494071903920003090b80921903644840d0000d550000e001d42e060784003c041c4007280d640303450303030648500031162002070400c00d040402c8440a60069080f40043c59110790100c8000741071806018060600d680e661600c1c2d4181c01c4006256540c03051f480f00500c2d1040080c004128150302c0f00d8103d11030b00c2c0c200040410b02c40008107401c0ba10991280b200e0003550100c01c000190302c500194029809071461010740b030541c081142c2207070000e100329940205071050400008000503040c1d046007450b003011441030201000911807881e14096181d0000303006101e0126585441a50240da2910030b80300000055070302040508058200700c1e1003030600c07401039051000c0001c49412106280d48285581c0b406042403440a4060851103000312124041c50f02c07a9064000310301c00c1c0300e80c040d800401208049180c03045080b959001400c081ea0451401c00540c0035440792403240542c00010080341504030b42c55420040c0c10407502608200030000000c01e19 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 371605233 1250 371603983 371604001
    0x903061806061c0803010f081c021506030a0b0106020726030f0f07060c052107090302011214041110050f03060402090406081606091202150c12040b0403020109050108 73
    0x1d90750150341510301e05824082c2041c010312540c545200209440d01c004004a0105c203560b643d4402c940a1100301c8240c0c404000380e03600300034031808510005900000c680c1124003200801c0701e4100c0c0c0c0107415500c460a841e200e5101000090f0018070142c3c0c0144c0d810405110501c0c45640402e60101000150940458101d601c1f4800c0303840c0419560b9021a0011810624408481e0070f25441901000074000501e8013030203e80040c10548005ca09104041542c1407041da0b10034450061903803020344460840c0c2c0196442102400940d54203030391030101008000364011100c5c01381c3d004201d070019200c685c0303041040b56100000c94800300042445242c041075400015290044811100540c82d00f16010100b00102210341c008a941d200d14644018265102151103068581c150b954112560700c4d4541070418001c6440000d4200c2a01007501d0f11000254029013515908002a6000d8038050041880c480e0000e403c038141e98080010100110342c0c04c003024800820007030130310480c245001800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 371606483 1250 371605233 371605243
    0x703120207080c03030a0605150406020a1401060b0c03040306180c060318060203240901050f09180f0d03200708090321071a0c0f1303020d030509030618 67
    0x100296140d00454110200a40c100580301e0040105044036141d00e00200104090303e45c1c3d101e40c074091010014044070901003882201e06541e80c6800400c039075012980d80d60024690300f600c403080355603113440104050004000030700c145103003400116166400d500300344040754210380c000c40c500400c1601c2c80c2c000070342410842e81118050b06000a141d0506100da00e2224030540300144410301c00000c0200702154012811010300c00c68807025000b66140003405a01c02083c000e0075031021001149001e185003501d082507005856100260007010465511803400340e40c0e080c3c0d40b800d504060744180b401c603407603c6041101e044114401c1c81495400380d8100143c810000301400c0e01d400042c01c0685501d080080e0040c28070708800c1000c1d03801c40075410008a400290088815004000341208a10000000170780552802071036285031419881014a190b07020310041480b4070f903146800005661254458040103010b41c440ca66900707554020036007082d00062018004084c1500c00d007006484c0015 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 371607733 1250 371606483 371606507
    0x60f0506190f020f010c080a1b1e0228020114040506160203030c162102060a0c020d0b04080a0306290d0f0e0705040501080d02190f02090a0c090602030703 68
    0x202040440454003040b404c00b105045031803003c1d824004c80307043c02584a501c452049580d00d00800021740d0690405a001c61080c44807400030b9540303003180310700340c0d0448140c024040841c0100c4560003d01c14242600c60117200a440c3c02d0300e121362a0a056503040025811442a8526110710f40b60804001608078000c0c4955079032426120703060907013152400c108031161000d120303044078000281c01203104030310442030003050403540d030070348030042c030b148081000a08442d0f0081559003418081c0c0000ca078428602d0750140e034411044000c80300818071014895014033b018410f09035440610751320180c1614000c2d072280e040c00307162000f1480b40207240780204040710800c3c0c0c0259501d9079981c1d441d1300580012040d15101c20720f0400101d201c0c00b4000703040c43c00c0302c0c030a072824066a80d0b62319019446a102c4aa510f015070045800c01c41c20704040710400000901c00c1c8209240702d200d03038002c80c1e501141141d021854070340d542e408403440e50f00300700c4c1500140303d40e1005520344840c1d994000c0400507444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 371608983 1250 371607733 371607737
    0x81905040f1e031a04030e010903080d02030a060b030405010504120807080a0c090b0c0a05120901080c0304020a0315020c070b0307052d16030e06160b06041e060f050619 74
    0xb1482a0058008102002c000c1da001007210800c110511864001144240d60071000f2031b4411600c07003160750259100d00101e0790451400741c01e07c50000b45903400b0b54001800c107100303103079242070100758001620f000e07600882c043c1c0300004072443c1c21301d400602181d044c0106400d10502e0020000384a5000040d0f550107100d4000c04500e502e060f08003070398a40e4854000a80800f000300e00c2414800c400110900e82900a44c200d9446091035811260030703109202940e40001e060130f000640c003070421801160054805004010310316070380d459000139181e40318004a40d450700024502400d10041103000050405a6600c500d1400c2c50328000e88544149506e43ca142d215100e0743d40048050700d541074100416458003c1e6451204200c0b003101e070484264120301280c622021041c66091087c15120300c6c40d4081e10035007000721a0f483c0d041a10030024a1241d010b42ca03190440305940301a034101001030301c100b0010600509044000b6160350f0240c0280340148814070030058101000a20601300c40064 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 371610233 1250 371608983 371609009
    0x5010e030c1e2e0b0a060e01020111030606030402012607030515090610030f14040b04030207122003100f0e0106050904080912190c06121a190e04081905040f 69
    0x140400d4044d0000160b0350744d10150003080014942d4201042d14501c0a09030f008020050076900030400134003040d42c417903400210038000280194020003540c94104851007420700000000a010301011100b12213140001c2d0315001448003903503000360300c0030420b0401c403060f0f8040d24000010074010344038079412504254494185602160660348a60810040d1920036401c604d8a414050b0304d900058904030b0041c1300340200040c61141c508043c0751040d60103070031070300d01c54a22402800c240d5100341d05142d26009451480400c2c40880c031031807142c852440004a50290100c45060071681c0c00d070300c498020480c034800c120000d0130744000c840e034051084031008280707011140300c14030b0440c442200c0c00301d0001c0041c4107401c2c410300c401c4680c210350441c3c1d02c40101126944030f0205462111018000482c3c0030703148204103103017031041c46440b00d803242034003402256188001d500781c540c00d4a007684c0b070075000a3b04a5203072402c84410701c070ba8049410003510302031411184030700501d001c4c4200035502e00d00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 371611483 1250 371610233 371610313
    0x2003060a02180616021c08090d140f0f0d0e011704060608030708040306051003080a32030a0506010311031305011d30090d05010e030c1e 60
    0x2d500651058a20180c030711911030f54180340800f8210081c00c4181e120741c84010103000000d0306201c0b00002c080d44003146900345001401807009819011208982c441184090090300120030028258464400402000450480b0a1040c1020901c8082d030080000e5000f41c0030322a42c00281071140301c48541400e11032580e0f24280040149003d07001318403035000c0041d800090117071003809802524090403080103284c41e441c0c0003001c10302041c807000703084800601009028034025003920075100c2c00d14215404102059000940c0700700400051643c1c9407000c003e00c44100746038400c1a500142c2801c04100e0761030400c28008007400000c0c110402620400c0c201700030071500790042c0c1c2120a009503115205104250842c0d2142c0742c4541a00700160348064010032142401486842c803001440041d140c06011020b00000c003007440c009568070f40d00c0d040a00d00c1140200010032034050074102400d40784984030481134406545101d0061070381e001f556255010740040014a8005a000c10704000b0408 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 371612733 1250 371611483 371611507
    0x403030528110f0303060d0803040203070f080706030b040e03040b03070c1a06010e01170726103602030a0f0603060b120102070c0605070c09050a02072003060a02 71
    0x3000981640d09144194030031107803240c10080e85015200c0003401d80b240c880320081400c2e0b40f40021545030303501980b644080f4000c500d0300e03001107030040d002a00352000c1c00d48482850f4404e681d541e01055550b8805041000f40d183c1c140300d0102ca61004490500140c0c8003120f043c1c2c0c0d00e005034011070a80c04400004101d4050083d8442b83ca17099220407851040140315030b60b2081003c0c11200180890011031507000c00c0c0d0312400c801c4207030480c0504501c010b61142c16045134000c0c115100d41826803880045806842078404145101e8a403200340191282d0800303080008030740000d02442075030866404200c074001d10641995907480c11a240042e260782d9400303001c8002d08040c0c18105c0c051441d00f2008403d01640b6004031070646400e42e0a03642d260204480c0508030b04c18141d0162100c0c9840d13805218803441040104601c0e03000e40344c990f100c00e03124490f44c022101c5c00d80b0140305407a80080d10b4000c00025621819070702440101d00744041401c3c81c0030a844100c010300000100f50300061138a0b0b490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 371613983 1250 371612733 371612767
    0xc01060f0b092b0f0b090303100915210309080a0f031b1203060608180309060a03021b0a0b060d051915060305032203020105040603020a02030910021f05090304030305 73
    0x9241c0020303440481403e03003040b4085460101040d0f441d081c0c0300c800624112000002c580c0a200b6408150314040d240c800e10707500401e81c0e0151464000c010351400a00312003482c0e03282407070b5139020200c0c94866800d8a00034210003000d511502e8190401c60152011580030041281d40b0358140c105050700e200642c3d02002c4e0b5802d0780000402d05004a11117500050741a4045c0c4162141622000340607156085d4131000c100d0b880c080c0d0700c0d0640c810800c80c03090341131040181c60308641130300b0054103102c01881c000c100d06601c0300c041401d40c1e00920f408020301252011080c0c01c0b140658600c0424031030f1740c8515445000c60404400d4900103100780c00d080050103004900d000f118002c00300301603500c80c44c1070343c2c4aa0047c0c0032000750b00460020084160003407003c10045a0b4161102c81c81e2900d001d00a07001303500f04118841c158042444250010340301c111908000c5e048640c00f43c00000c558461615074040c3c02d031400070000e46480d04201c1d00000001c01c550a5980606003641c840307202110f285494 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 371615233 1250 371613983 371614039
    0x60b060301030506070f030e03070f0807020a150f0509010f1d041508010501080d050a0f0306231002010c230705030c1c030c120b0d0f080c01060f0b09 66
    0x205900000002c20301001080160140113640d0b2103010310020030304110151036002c00700000760707081040700d03a000031007d0310a42c901600c181840c0d8202917568000407800c400541c8105040c074a50b002906c0c0060380010442000314040c2021401e00c0c1d40040004c2030703043d042106405128001e1006c90040300f000031044a13400f002803051046c000541050b001100e818440c604096013094000f1036620341c04280000d1a000340d42c0e030300d42816601344045401000e0604460181a52004040f0348803403e90102501f0059040b5101c6c0c460b1548401e21032140c004803420300440e49049545c0780e109500c15104040f031140050801c000c040206481881845049001041440006441e0a01003004502c151045080030010411098840c0382501500d0403444d011000412040c0b19851a04d4a40d00c000d540300030240a5080c00f140540e01c00c080c3c4c408404d02907070000700105e4104000c52090040101a040b0358454105452800700102c14502806184911501c0341d6040812a003039204648512 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 371616483 1250 371615233 371615239
    0xf0b09240402040207060e1c02120a032a02070302010818060403030b04141e01150e1c081201050a17060406020c0c030706081009020901021e07091e05010801050f070c060b 75
    0x208811580820303074a231488004070034179081418420302c0c49400400c0c00d04a805400d603506250100d1003074200c0050000601010300381603c2407040814843c4a02c16108030441d41c0c004140483c210300001d00b10300401440c0c440d296042d6907041880160101e200c81e0403075858180840c02c0d81c690710014002e4202545031505c0b98200400304607506a02619010a11101c3c218001070350f600c0b0040b158540100c2031040c0d001c40c0c820741c032a1141d8180031400d000711b25580311a41401c02180da4481c3e4040d44040381001c1a03490000052108d49013407036480008000007103540c10540d44295926485060040010745241d40c081072201442509000c045068a0002e0941e2051912002c3c080c20700348003903c901c20011964003021030061b440344220b82c9a042e0580007808001a2540f68000d08010001c00d209540142c0100090005550080d004042c00b01152006032a0694204c103084810581c01001541e06040500c500c84220594a82c0c201d245860060422a81800d0140c083d21180d551250 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 371617733 1250 371616483 371616491
    0xe150a050d020d06111305130b030304030308150618030610080a110427030807050a080103020d03090810020919030f0b1008060106110609060f072007030f0b0924040204020706 77
    0x3c00c00745200306c0700a40b48203c0350400707198a0b550b186800c5404225105405a00030071060011a02820006601c01d86500304041c02d5100c91001c43c040703401c1080c0c0c0500148801c1010342c2245414000c0c1a440080705034100d0400b481e007880c00355541c65010740507101e03036400e642000f180d03142d9030802c85462740903000c10510a03203122901c4140301401801600040d8100021550300740c4100125160347c509130340d500003c0c2e4255020000180f0002034201c003840210500003804000030301c12040c58101c60840181c540c8015400d101000040c0d8080074481c090b0241c092002858a154040d0f22a40010000c0419641e6403028009144550000c072818400d4200004130780381d001e0315003440d0340c00c002c007a640720b0785514940c90b41d211800c2da01050294800e0000841c80c910a070214851800c01c0c915030b084404007040f40a042030702c03c1e002034a18000304203918080c040e521024541208808004080c1c10a800000350f4230003605172012000c410544c0086401e554a80e0141c0b4072031604610100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 371618983 1250 371617733 371617747
    0x120b01050738010b0403020f040b2d1203030f0c0706141504150b0c0109170c070b0c030d0207060207061802091501081515040e150a050d020d0611 64
    0x4461101c48540e60611424240d80300c141024003007039010f0403240403500c00703070410b0305560801c04000764001d260380d0819a40d48040746255614003001c2401810000540d40c40081088416a4086810201400307691914408030090800000b22a40702911040c0030f54140c44505552820b48542e42c00903109a0170903040c0a241c9024404050060038030807061038000c900181404181c03030480e0091044054045001c0194800070780c010030005407c03000000e45040b032503443e0880b94401c40d544402d82000407440032420b031400c0003010049e00e032124406041c104a20599a502e02c03520244105070f50b004102c500800850b130701a656041c0d8042d00a000740650707200c04445d0500d00c03240c20391045d1040e81c049407511400140401b4070140680d212240c9558007921500c480714042d502c203070803070030031040d011019040d4000340000d4090390007000c15508140c502061441c40e8400d503e4450760050004109690300c4031540c02d02190b054409021211003030070414000c2400540d102d01d4503200088407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 371620233 1250 371618983 371619023
    0x100c0212010204082b030f061203050304060b0108010305210d0606030b011d0a050f130204120c0f051008090f010c20070b0304150e010c030608010516120b010507 71
    0x40c1082e100b45204458005051500741700b40c40004044400c0410003103000c81540c4c62081e001424644440c00010561540d503020460860b1018034003500010030100600040005da8000c41c0c0708400c013440e1910302941582c0320151240440c2c00c80c49405000c684544421a4030700064540d0340c10140c200704049076440ca8094080c0885091181c00141c200810384020010841206c0e02c96102518543c0410305000070b10500000040286a1203884c8400e0907500341c2d01030000780003030078600d030003400400164685482140419003003208400d01082041c0207545510910501110b601e00c0e150304142c8070310040600300b40a801050000d542040728607040d198100c0301d141d103c0900300700013018900e80c01d0b1950b074480b8041c0c0143d40709103008101040c04100801d5020100008455000400d03851081e45039007120403003120540401d490384420040ba031420321a0590004a82c00c00ca52007448074200140144200110301c1081551660820f00b203074455429510916030020503800b80050483c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 371621483 1250 371620233 371620237
    0x307090603110103140601030b281701020f1603110609160b03010b0f0a090806040f1421030a06121407050111070302010e060f0706060602010e0c0f100c02120102 71
    0x1059944182c01601480954030030b01c15007103e6220400c0701200c81c0c42c1e64004401400e10704500c42c0d80612130364650500d2a42c00520001c4980c3c545a010b031030646005041044a040c541c0200101d134410f1086514a0304a40c00312205001200e50849074484180350594440c1c22880d4100c0852040d0300401000d07110010703002505820b1100c00002e01a41c9000c1c1100522090140881d01c0005024803c3c6801344000a84260251800c10311842916180014903024048400381d49a66140154005210350340058000307660200014001a05e15106484034070f060003641d0400111000001406d84c400c40e0740618054070041a900c140d0b00b00d203040403118038200500c0c00103d80140140042c496004450900c100c1a03000003070071a062a640065a480300080001e94010108101043d45e4442c410000c00f01d01e486054000348141c20600e000307084500340c410905003903020103511141981c1d4079680c0041000e04860818043c07840000842ea0700140c404d0080d0084600c00c5000d400c0356042d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 371622733 1250 371621483 371621489
    0x20906010323060405181b03030705150a0c030501140919020703020303040506060102010905072304020403030c03030c030614040906021b0d0e0d020d080a020a020a08010f0506040e1c020c03070906 86
    0x240900864440c1c0d0701b2512050301c84200340030300380d008054a00c0c42a4007000b0340140c2c0e80004080e00d04003540798840d68180484981d12040b1518050300b0068640e41521070388004213410700d800c00084d818031a0a03d0000c54014169200d00484070000d003902404080000c2c0310481c0301000d546400003480c02030343d03a403c150303401c80e0300d8050703840000c1c5070b54814800e00c2201d40c0c00c24002d20039145081201d021545102d03da1400001440c0c421703c3c05620b0b140021b000851290703540411400f41418000d003103801218150082508001042111911035200e440311000e00300e8000031803043d0352812400078841c6d00310100e50440351f8035100801c0000480c50000030ba21603251281d818070010204421444442c0c4020b512458482501c008150650007600440d030903030040b942c129040d40c001510030101c0e070740b02040301d80d100e400d504503202c0940507058001c007040c3d0f005c0c06050340c4010307042e03181c400310034420030b00c15014040d40e41b0301482000060300292000d01510b50040e22090854040c18a80c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 371623983 1250 371622733 371622739
    0x10e0c040e030a0206012105071409100e070e010504120b0f01060813121701090606120b0607030302070c0b0f04090b010c030f0e0d0b010806090d1b02090601032306 72
    0x40705049081d1808400c6800d00142035001e01a981c1c00e0032546162181e14414006000318402c540c1c5000030020828000a0034801c14110401450b00d0100156284018585112040c0b64101040001c0030a0340c1660005640d05049030700d00b08400048070300340a10b620551003403110b08104010301000400740c6005d0076410410703c40343e80e22908103030754811003a00c00c000c904040b641c011000c20356181003464080ca0a185c52184c2003420742d144221043d0a8103c9031401ea5207140c2000000e400a2040301c410401100c1840525200d00c0080c032640500780c005801e258002402c1e008201c0c422000c4405000c40c0041d2680340e00481100c0c1110390014024800c8440c50f09155060355030040034400042503041d80d914011034240308049030b903129404940c6410200030b0f0f208500050040c100b143c041c02d4180000c04041c500000140c0c900800c0320800d2050005203850380f101d1300b060301d5006842a8050f95095600d031079901c0120014900900243c0d040d03040d50301c0209809035220021070040000f1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 371625233 1250 371623983 371623991
    0x11090a05030303070804150209030105091515030c090c090603070c0510020423031024062309031e06090c040213090f0b090f0103151505040203090708010e0c04 70
    0x40c905240d507074402560344201003a405000200001c0d45506030400c003010110025007852540c0c2d000c00e09580c41079614404a0300140040140050440100d50b03101e001d981103068802c1f03509020a4507030013400c2072140900710020001d0402c5170070700111002a80301614a03a030340d1a00200080c14400034020484050003810780110300701d41c840c002d03201034900001c002200d903429204c58001c80002106001c2e010b0007041e5140f889200c4a02c00d0300d0407111256090514a410303964070501182c450b812280031302900c3c1810002c0e482200e040d5054216411010741d03558041d903c00a440d044810f08950301d00500c000e009265420702050941c0100c2c0d1403130858444840f00c001b0002a406106050010300032885000c001010305338110240403c0342e9200040d6654099001c6028200122500c1110007441d1004004004510040100580c0540d070204240d0590f0300062030b0210443c071800e4491a004008616a008140300340c03801080d0000080283c3c8004c1801c3e50385952442c20030603c0340e858 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 371626483 1250 371625233 371625239
    0x1b1504060818120703180f0b0a020f01180c050a120206031510051c05161b060203010905041406070801030b041e060c1803021513030507061706030a020f0105030c0d11090a 75
    0x11101b003030742c1078070711346054045400c1c00c11752603428580080c01c01404600c500400c50001c07001c00c2c0b082c221440c89040302ca180308c03809810001300c2c2c220075500c000e000c0d1005d0142008011248a003a144103541152016601d840302503a505140845034049603001500110060983d41c21030700401c0400c00034008840f882e001c0c203401c3d008130f1740121010000740740000c2420789100d00c07884003c0140030310302c0d58141485810703848070400c03a00240c00007800c80e0750b604284803d00c604070304141860f40c000d00080240b40360001c4000c02e448010700c00103160190300000300d410441c507540e02c3e8440d11520311302034100f08414180746018120240c149000f003054030083c52000b44600121906903500030304441a00726070351103a9841980a031030b0b110014566101d000c00016024080c18005000543e1400a10380d04c9402c0c50f0380c00100640514440e600607038201c0010b0322040c4000520b40d109082c01d41d143c2d0707613906c10004648104080c001c0801d02d800307a840c15000c8000040c10031000c0a81d0f03000c540e00d803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 371627733 1250 371626483 371626517
    0x90907081203160e0a03020103050705040902030a0614030a150507140d0614030703020a1503021c05090c01170402011d0414090f0609060a020c01060b07051b1504060818120703 77
    0x8541002c407a040108145c1c00d001550081c0c02081d0000801e191072451b103540d5001000481c0c0065400841c52034030b070b40d070030010301100a0800c81441000c401400224050381d0320300c1641980d205103041c4494031400020321482c061840402088103d4003d42e50326640c59240d900240038074001c00506480342d0305800d4460a00040c003000780c80d0b0151010342003604220101000700c1d840312a09080580800c0600b84d882480400d006103001e0601003c00d25060030b0400a040c0303a00d40014504205d00070921500c44401410644c7c1c1003502820404541c48a98000c600051844100340e070304581803070009813031020380c14580380c071400191040e100c01100c00c00c3c1003516400241d581004030341c85000030501d446c070103a00820402c141a000060900c0c0c0d14103c0c40340c01d81040c002521182c04c0003080001003014a5020801e8010880700e100c11220400c8400c18280201d0040030100001500099000344242c40b016800281070000c036908010302640c0340c5025848408224006a5180c44080070300c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 371628983 1250 371627733 371627747
    0x30c021e040c030507022802031f1404030c081303020a080f0f0a0201020303161205240301142809060905100203010501080f0726090d05031509090708120316 69
    0x4503a542c050a0311258a10303980f089412403410a1050380e00151f200c5d401a642007007441d184450811000044904003012681151104501ca00d0b1800c00c1200b0000000c2d44941749602d2190f21030b4180351182c11824241b49500101d07000250025030107880801c480c07900050003080080780c0003c4a05045840400686402403034078024096401031005c141214101010b21040368468a0800c200c3c0c10404159400d45a0a9403c01c1064000c100c81c2c000711003c01104800c41c05050b4001d005140c1000030341d040c052001070400c4462110b40306040d4a68072240e112048000e600a400e11041e0b141d828207100801112000301d80a114812141c4504980d0b0300a417030403183c05845140c1241e583c4065100940320060400c010860340001d50340780702d5843c0000013070702c03254807042c0307225031410901461518060000c1030f001d12005000b00001c84140050480340740c00f040c0c400c0b010700c1c0c444035900c610307041103034010107940d024004030b031844008440b02075881607603044040c1d1580c184000c002da600c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 371630233 1250 371628983 371628991
    0x3050c210f0f0f0d0b120a0c090b031e070e1b0304020d0807020607030e030f010608250305060106051201150c060b0105090409080903010c110712030c021e040c0305 72
    0x60368284407511040244070041c0c0140b052049041d450b0111102c5003001e0366101c0e0000001c05952800045620304010031102c040c0c040800c018040050301d0340751007110910610032a00e4243d00c40c035240c25141c4042c03001c9240503000340e06040c501c1d610581c049407a00318078024030b444608140c00190007045104080c2c2452008000b0403403a68450b6000d100c40e03a08505000c0d11400340804c501c4005889506c0100380c0540241c1d12103a910240720201400c05600c014100300c207a0515a09100060010039940c92121403194422068450324030702ca090201c0c1c03940080c00e68003c1d440000360b400d4110004001c0341c020340401d04056a00d41001104050380e40b01003500040001400c00c000942075804100131840504243c1d08121075400080c090b5032078140201d80481c00410341803e107040900440784650204d00f01b01e0a880c98018910740d40d018544113a58168162400610038540155070a074100c64004d010080030b1001600c1d92000400c1c54104507002d03a161071070044145200e0720501e401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 371631483 1250 371630233 371630293
    0xb0102010c17041a1906052d0f06040806070e060a090302040207030c14010603060e0a031e050706021201050f0111060c09061308060910060f0306240303050c 69
    0x91090901c07290045400c001d20846880301c03202c3c40b820034140038542a5101d0b605c0a12415096040101070030243e420651102d801030050360107100030700102c004004802d5001c0004c000f00c000111001400e40c2d0300703090b580c50700b2a200040105543c240891040d00c01d600644540b422001104240a40c0c3d204e00f540e02d10024100f9181800103140ca60014001c4600901d0201040c66082d00c458114100e2030a450600360b6498004100b041068050600c0303100405c00680504142c43c6c40251110320480020244203003109400b06e0818080c0f006c0e1002d00303400020454640011182c00f0090b40313028081d00d0700c038031030f100d4aa1041e036105000b2001888805d0025042a4544980e1100c5a400c0481c0c0e803a4042d10502c00003070903184802889006040d180014007082c2000f1070402d00b08407026101d0032506003015400e001004000040da4200d0741d20070f04c0015005401501e8a045011f985002c084182d000100001411741c48409810200540001d40e20f84804145c004c5403035070341c0031800c421 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 371632733 1250 371631483 371631497
    0x81212070f020f0708030309010b0a03050c01110a0503041509322101140f010e012c0f04151503020f0118090e010f02040509310c090b0102010c 63
    0x9036441c8074039003504454030140126100781000050b000c1c00d01400b500305014560010040020f840401d0160200e003000c1603582d9035040381583c4405e034940c00000c0b60241401980c45001c601884200142924150028150303234459480d940348000100d400180d80c000a0801000031070325072145070607204010141c11200c0c964425010801040400b03c0240315404a00314009407041031070b000300d40c015608110300026030134101115000c80d040014110306100080203006010b0111441e46042c19074849031900c40319001c000c0c2c0d1120700014640011640341d60904d003445001c0c0741c40c81c08140507500c9105212003004240515400b1280c0b10381080c2c915a42000c3d042000d41000c101c8e44802d500180360081d03100e02c840200c8612090164400c000013661012140c001007002c2c464112501da603400190301d032918240000701400c4001e080729541c400c0d00389002070314403071301c1400301040040c000d1010742992150800901ca45c545200f910140d50801007020265881803040708607520309912052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 371633983 1250 371632733 371632741
    0xb01080f06060f0703051201080109050a0b13080c030316030b0d0b04020a08010204170c0109060f08060406030b09010e060901060f12140316061424010917010501081212 74
    0x2400d280006030196030826400c104410b2040c2c6682e0080c010a0b0107910303055a10346442c4405141464141d12117007071039152040850000c0c0d0301165080c0401e80256056180e9100c2103010003000d032038460010100440002c05c8079180b1804070181d8403c031081c40042c15142c42c400320580560350440c0e1420707031102e451034540e400110030b9406690418006808100700300e4941500300d00f240e020381c1140312042014541c80940c0e440070080010b0109083c40c0c0104d01a18005000c2c0110b40e010606105000e07640300084e01c86d88807588500b00454000048100c1c80c01d01c005664000c00000c14800c616000700f80002e1401c0b44140100380841c0e5070784800340b0748103240c04c08900403800300e1141100d191031005180b07002000c00b0000781c02c084103000c0c61084100e00d41e1411404403041c256512000da05030200b005103003000d0121303417050042e0081c0000c2c80d2080242c0120f440d101c0903000803210500c003000900301c031201503102a041e10001401ca0700c100d040e00c01e2190150141c260781300d080d040710800003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 371635233 1250 371633983 371634001
    0x30603030206150a0b0d11070501090203071d010b07060b0a090c11030315010e030f010603051e0c150a0302090d0609111c0f02040608240610020a0b040c05090103150b01030b0108 78
    0x1030030540e181c06e0300001d100001c0c10115105610049040c3d0300ca80d1148030f480158941403207103030020306100812020201d510340305411802d0051281502c000804500300b01402100d40250040d00d20040020031800c3e243c1c040c0c000185803154405d40014926844000d04000010440c0d028042d8105012800b401e40001100e002a0345040b158043c080c82c20000302c0031500740265409544a00b02501204810703903407020754580340e00c1400000303074801d544644803501c51001c03890030100010441c950300d490214059000e0310820449a421918403904841440441e60120603406d100340000303602e48408500701b064840480411510031083c0450f100c00140c14041c0000c5000d102410100d100c65845403071a007401c02d0101070854803d400d864142e0300880d9044c186901103801c4508281c004504000255a210054001046240c0e480007060030f20406401d41c40c01030034010140300301c41d1b86920380849035001f840b517440080c50415504445030347c040d00a00c3d600c24010303513809013148c1d180210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 371636483 1250 371635233 371635237
    0xe060402031008070b070302011109010e211905010f0204030206030f060d0b190e300903011506020d0807080610090b030c0403020a0506040803040b03180d030603030206150a0b 77
    0x40005403040750400042c080f03005000c0030780244000d14040740c81d00403600b0041d082d1442401e84041d1454200070f807071416a0450401781c4007000a4440b0f801c0c140100190312441d0349100904125842142c0391541d07400e00d4465001d110921030b10003072001e044201c07001020380c0501d01000390700032003d0002824044000030486da02200042070310480342c4003030301c07a0344410744151110481d0030300702c20080030207410034021100700600500007000142c0207046200016848030040c0104840c6100d9100821148407090710061480207000b0004040707003204c171003203103080740c8140c41c09030140c2c00340e8250060080744c00f14451082602c58403c2aa01c0c20f040010010001010b5030a100e01c102001c904441d240300514425540400c400e0b94560441c0100490702d00c00303500203485244200b0060107008000f0054804644180300c1140e00c80d210008800c146121009c0040294400e60746841d100c01e505800075021203010350241d82460f150841c00310350300b00c040b0031040c0e00725442c90f00c100003200d041d01c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 371637733 1250 371636483 371636491
    0x3060d0c0f0b030105010806030a12050706140702030403140f030f0c03070b071110050c0a050c150406050a0b04020712080a020405061801021e062d07080a05100e06040203 75
    0x10424103041d84800c449440e58a2a810000180c0400300040c420b41d40c1100b80c240e0014401c07001007000080710b07968281c03482c1403501c4107010000086018030821005400210b41c107912400b0020081ca8141e000a5507900148820f5a00f5818003050b00034520001c1402c0042c21080e0380a186058100003040196a001c02c00004580c07104100c0070010402d40700d1030038041c401c266544003c5030301d0a46180c0c44c0000c040c246166103880d00c4180b241503140d4200721104030302c09041c481e032225018031003203041804000048404595050030042006180d510527071007050752802c20420100f241c401d0000b00e006415009100887d03801005500d87d004280703c0d5400800c0d81809032a040c2c82c0d00100c3c43e030341c00400841003102107070f400ca440c40d03680521030641d0214041e20718001500c40321201d42e903142400f5012540d0010300115603031100c00b41840e500107419084003244001d05000400401d400070440704044590b24200210b010201c4001101d022a81250300002d880c2c0c43e07480c1000020360000d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 371638983 1250 371637733 371637743
    0x20105040e0a0b0a0803090109090b0301020403020a09050f011d060108151507140a0804030f0501060e07020a1202060112060b030f0d020a0b060a05130c0e03011a0f0307080303060d 79
    0x80400961091102066842000050302c0030030050308540030310a030042c040d04012803d03082408054000e1341d002d911034040b00c24120340410301469407000300c5e00911594001a4104064000c0070940f5816900100d02403582030001c01c540d03030303618203200f84244003a0311b8040c100407401c0b002c240903601c222a00e940103507000314110840e0107140b0014040c08130300000c0820700c6c0001300350402032203c150030b040c16140c2d08001800c4003134cc0541d90f143c551701c01e034000181014070345103500c028803a09521540140c50840100103032400e240e00f01a541c0c1510f1031045a11061510900002600c04150903040f00c03401c0a100185512030354a0b10041c1458a42207074040c46608801910101c04000b140c0b91040590045d1040e1101410810070266009040314021402d841040005031100c10301c42c01e05d14003a0800244125820b40c0c101c0fa98910001580d5066080480d03c0c05607000c1c034460b20f610301d8411180c59011810304001e15450741003e00c64603507207400501c00280c0c40d0030400f541511a5100f2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 371640233 1250 371638983 371638987
    0xe130201030605100f031505030604080a0903170c0c03010c360b0a140403050c04110d1104060306120203250305010609052202130b0105040b03090a0302061e13020105 73
    0x80d008900190b0420384c007080050001c10b42441025010312441d89590210348030560310320b0074003010903550080584000c1030003d000902410aa101c0d00703030711015540c411400241d8038142c04036800650410109200c0d54043c042000403517143c14440c0c031040803c80d80352026003079480324a1340791441c03600040031224400603100308440282e42500001400343c07891442d84030340c040c100c020300354240825401e01d042d00030842800440c5001480c0c815a402c00c443c0861030f1140c80203806200d00666400d0300c085404e08600c2c415080c1030344041c0c015a030b11580d0400c40c080e0388080c02407940d000642d002c0d4154000c08802c058001c10780e0300c500c20045828449020442d600e80d51386d800c43d1a0303640610083c9660341c05204c41c8000100e0410102e124200890301080c90680001c4d01c07090030b03094903111082e070b18030389092240d00440941740240852030040d500c1e4901141e0b0161142e00140e0110014025400065102c16070010a1094010074071111026030b5103100c41c90003600c2200b0000e82c14000c003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 371641483 1250 371640233 371640239
    0x510030813090e0a03032d0c05040504090c03060b03070b0435010501030605060d050d0e22050603061e01060c0807020a1d16050919120305031806010e1302010306 71
    0x180d018801d84981000b005000d13400fa00d050040889100031b8080c10660020381c0c224251460740c250141c2942101c03140045c000e04110000d42c0d5610239035000395000b5061040c0c10303052211009102c4100e074040c00c814000320980340100745d1075a0329406080042d440a10090140070280d610022901c0d01d11180e42078205c1d801145000100302e101a914a5a910b4074014400c01c20a07002d00c3c0d4001c0400d480901c45000d080c0c5d901034441a41600e2481040844038220fa101e9464042198403054000c54480608443d110b800c0e0240c50111120ba0081c450800030078a45a03141007252150180703000300f40038903428000210340d280042d10082d240000240104005650742941d50401000311004200c100401554007400d4020000c10341c2e0f010030040d5003140e801c55004011a56285000c6400d00c1c0003200c00c8030a505440c0d01a004074544030700d10b001c4807040540142c0150301a600e90301c4407c4904502080050341d0307010074003a180340c4800903800b080485d40d048003140134191050601289150f2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 371642733 1250 371641483 371641499
    0xa030c0f0f0c0315061802030915130b01050a060f1b0b0114100c050c0111070306050403090612060f03060b060d0c080105100207290c0706021e010510030813 69
    0x4a4241500e0082e6400e40400803c1007151824041c0440d2510502c0071524000e03086284400b00c400c2e44520b00c0e00000010003000c000e10044012080c2450403008605144840c003030411401c078011100803003030400202d9640350003803218045038070b40da4400c04030401c20001180c500e42c0603040c40c1c0042e0285034810000611000d0803e01070120100001102148a401c000380600d40607030203405c2c0054052140c02186000c5a000451403080c02d000303110800c408000e6190181a40c009400d00e85801d06200c105a4440703841c504446542d81e55406030700e0340d520f030708040f01c115100e43c002c0084903400400014005400c450301c1d81c400204080c0c280300e501003840382540c02505006000500c03400041c800c0789400c92505158040b144010170340d036800d02804a07890f540c451482c0c0b246800510140d85180d0145085680300c40c1d84c081a07a90082d40d60401a54030138091242ca545959642c2a507000c0c044144605403240b10294158085ea07403450300d0b815419072110b8102e0358010954040412458 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 371643983 1250 371642733 371642753
    0x30620031f0902031015210506030114011224141f0e180307020a0303020705030c10020d0c03020c0402070b041106130605390601080f0a030c0f 63
    0xd6030000c040c541d100010007107040c4040c00d6400246500e4418014004c03e980c060314402d003030380d0100c0400010040700c0001070718030100070340019407082d04640c0c540c0ea900d03801e500880d0050f4000d800a0011011188140794001000d020701c9484140f4003200f43c01107840240c01b46254a01031030b9400104d903403c151502981d9050030f591107080003840074170244101c8048000007551091420358605401c2140741b84451a02030841d0340404001152203032a20307010b00844070764a600510f4035108580e00d01c0c000c0e4848886108041c0b080c02041199103840c00e1440b01d116010806038003410001e24044415030340440c00200c29400c5108800c0c8603c0c4607250b42c4010210310b401642c40340030038a02860300c90b60041c01d08138558007031042401485405071802c040307081501c4103400e185480d18281c0385c0050392000c443c4148107000d92140c40d1600500103507a100e0407507404480039034401e681c0745c0d0441a1340d004041814101a030003240d40d9404a441100c00785003141c89154100448006031311400c01e50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 371645233 1250 371643983 371643991
    0xb0603010902070b1b040e04020a05040e06040c060c150c0e030d02010b031b18131209030b090d08010b0c011103092b0203040e0411040e1605040b030703062003 70
    0x22580c0011500b00f403060341040039a0100382e1a68224100c1c401a411145d14095803280000005080340460215503e4004202c050034001d032080020b9a0305441855840c4c10503101940c0421000901007543c600c0341c9c1441d40c41710f80010140f411803c404a460008000f0340342040704024289a981003507507001d01c01c2d1019484e041c0d0020400c50750000c100b608000d0800450038280510054641e050740742c1010000d1041265685c020065a450014080c1440300d024024038a44039403802c50101508001c111003500d002c1c52021502e07550b420901c60b503030354940c8690350100c0c1c00c1000410031509104000c21248480c100041002d40c1d09c46c004a103550019154500c5903040240508814043c0407010020684000500318100701c4028001e0744074480c90240307200842000b0000740c00c0c0907044501004015018204210350b004642e4580d4903004103199400c002050403400140c2440c060180c00103410004000d0804645181d0300c000090031010000f00c400c41036024501c2d40b40182c40061403007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 371646483 1250 371645233 371645249
    0x80118090218100e060915010504120302071505030907030206030a09020303131703040f1404020702030d0905010e03120d0e010e071202030723010c03020f0106060306031a040b190b060301 82
    0x10b141020003401c0590f01150b045200125007800c00c20020350b0b181a501c03900601014011880a0010001290a0320494001d2460030101040c25420160300141100c01c45107000c007000c400303d0f18070300d003241d4920003514400c1142c0e02a00c401d00140c40c14030011034010001ca080000da207602c0f54003190030b640002200d040c628005110030442e904441102c420400d503d140550310b002e0400c1c4183c0210382003030080c18421002403120b80044e49959041382c01e0b0503001030417500703040b203050802040003045010322800210340788801c8501c1d060001e450b04404440958950801c42d180c2c11040040601c20311402480d1f40b1443d03181101d0b08180a1940035010604405860300e12500503d440c0000307641c452450080325a074403420325100c40e40c00140b900c0e0246044a000002030508907d40340705e040008042d07510f8901c0000380250140e201e0300407680300d0805131b112036010043c0c0c2480700c0411903000d4203403540200001c801c81001c0081500c11110a00002403402d4000c0101c4c0140c4c20036007040300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 371647733 1250 371646483 371646529
    0xa180b0f070503060a06180b040e0612070b0a0c0f0f051005060d020d150e1006060e09040201020706082d0a050a0605010e0d23070e01060f0801180902 66
    0x1400c000c090580541c00304081c10918a0360416102013914001a4898041040041028030740030b04d0243e445070b03005101c4080103e40f55070b102c1c0752504995500392101d9108828110002e0322110001c036002c0e04032a0341c100094101901007030240ca01466407202150505200c080c0c030f00c00125883c24600c41940200c008101c415540d0058004540d40541110b00c0751500306d0f100070069031081c000140f02980700c1403201e5541d944020400280012041c9410140202c10b448840c424071a4002000c5890301e64415414020b25002d03c103501038150703400380c010f8100410602c07031240148045a049000d43c40a0b04140c4641a58107943e000d042021804c00e01001c01405108400e80c02600d4101d520980c040003110f1174100060040c084101c00503008540e4101f028043c420301d80f685000c940e4003008400652010307545420f4490700a409070b010f04d42d40e01d000100360313a40701c0c4085001d05c003c40d40360340c482c0340d007442c0d581481e4a00e808080b169480d01c8100000041c0c880321a468441e0003080750b808 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 371648983 1250 371647733 371647741
    0x50a12020705071d15010f050702120d14120f090f0f0a0c0e101401111c11120a031a04020a0306080d0309210219030906081005030c04050a180b 63
    0x10024000d204580104081242030003c0ba044039182c1c171404002c2420525404011458140e81d103009000010351302c4070104501c5c8000107404240701c031110a0a50380d00d20380301b80c5501800200d002da00700c0d070104a040c00e00000c036a080001c02031600213081000f151111b94400c95800d02d04461004544901c2e049015420700b044108001100a400da0b942c42403803030724100204d141c0c04002031007181000300300c040c1022480c1e40111100d0110003440d1082d07c2c0100407800d42d41610480340d840310030010700d00c000c00794081c1402082d04060807080912161510700500003c8019081c0c1c07414030400e003444030315240007540d00c510040c2050b09540e100800d8040c540742c030701400c0500000c56a000c0c0750901820b4000100d10b140c500c000306040d001401094000e010b0102e1900b080034865023070a006104d0000c007410f8020701c07514210b40c0d5964601200f642d4a40c4076035850066480b880c0e805034420b10003080146000d8208560000b100000040c01d121103182c4c0442d06240590240c0301542c0300c100f84 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 371650233 1250 371648983 371648999
    0xc02130605100c020303030601120b0a0902071a0f0708040204290a050603060325030b180c0a0b070f14060a0c030509060f040f08040306020f0301210c06050a1202070507 74
    0x1110b08100c090800b080c03001e8854000c25203a2000501850400c40320101c081d2050742070354020704d60880c014101c00310290304d52a20780b00961040400351030001d41440c001050300c10b000b1640d07201e25074560488411741c032880019102c003100540201c0e405900c0369241c11082450040341040440c0141030303038190340d0f107800903c001d01000780c1026000750700070400c014103620b000900009152000d0441007265082c0f600b8451a040c40ea04000d000101c5501400181c03868115000400600001603a14400312441003004202051042d4403084205110b1030010441b15401c100d40c05010303403160101082036a00e9181400380031a401a440c99841400d040c0040e413510442e940500c0d0f12005143e9410708440d0581c0344031006100070024000110003004020b003280c00c5d103005542c880b1003991140603201c41050150024002e1010308400d400480f0842c0c0301440850710403503048080e400005013840c82c07c4031258814000102889080700040c000061548000d00401340900080c1203d24104050307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 371651483 1250 371650233 371650249
    0x303080705120f060909151303020705130b1507020d0809030f07030c26030f0a110304060302030f0a0b010c020603060103090807080c0c010203040807052b0f06060927030c02130605 79
    0x100c0c0c0b1980c0c0012800d02c156a28107030001d800004a000300078001c8c40b04d140803445e080a5400043d001507000b8402c81c1072400503000000c101000310b54030b02b90005084050107050188070b101940c420010347e0200007040306500240000c07140903096030100f0000b1840e052400c00644d10444200780203000130410060151300720145080c0090303100301c01080341c2d242c10b55a805480001c15041000041d00e11a450203542003d1304c0c0040d4109583d207980d030380c16002d40207403c220360b06040d0484540029103000d089206201c1440016181c0804d100d00f142c00780400d0303800c0100540d0501d41e86403004404501c442c0702800c0700324411309031180d03142c5d2910300c07060801484080071419540180000c0c40030303040100c0c01e0030aa80080d83c808024032410421850100c4912411022000d0383d141380b00c007404044141c00100c0c034011003090200700da4468612080746c405540442500b0040900424600d06101c00050264040d10b002980e204254000034910103140d014100306554031007042003207041c4070709 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 371652733 1250 371651483 371651491
    0xc08030403080906060301020c1e150718060806090703050a150806060307050906010c060504060609110a020607081e0606070b16020d0e01121e11090312090a0303080705120f0609 78
    0x1b00960504400c03244060b0340f1904000e01240c1500f904030707000e102040422802000101c2851140c04074180b0000140c552040460804030b21013942901007203490250700d07003a0203150003901c01a000c2d40c0e1b503a0218000e0201074001c0410b1078a455801d101e82c26049204d07030141103201302405250401d03108052801106500450041345000200304003a80c2050242070b640c2e8200c02d001c101e83c0c0d40d42c07038400c000304810b03040102d0b032500d0a001d40a528580402400d289040c1d502294900e403640801039071a4a03007180c19202c411b503985e01e9060748070000643c1a03040300c8003800c02810150540d03201c0d181c404c02250445c0600580d0203240250079030410840000704241d00305180b0708108800024000000048004041a00c030100c0e41d9041070621000800070524507420403111100c90f50880f1158080b080082c403900c2405501110004c500c4112000000010702d400d04552039a603040d1400040180200f0500c242801541c640c9282080218418515840450041c0c40c051080005100c0c01070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 371653983 1250 371652733 371652739
    0x5030706121a03062809150e15060613180203090607090308070201031a1002010f0605030619051f03060213080d09030b090a0212100507050a090e070c0803040308090606 74
    0x60001100d40c40106950b90841220b05c000d170700a00f071500104091000303010a80601c1894500c11b10280516200d40500baa0b00700d481c2409a000341c1e0341201c1d59407480d82d00042403080854040f504a01c1d0038002860366040f46900644600c0d600d500c000d6104000d1a041c0000303c0e000410481003000a0180a03400341c15070802020490464441074681d00035448001d041c1560f5440022012840c1c80280340000e80c02410910360725000320780240a003400701001d42440e03081c040082207600d8003040c814441c00d10f007013401143d012013020000c05018094450300c031850290002401e8240b941c101d040207107020b9900540e4410054500003211180da0384601e070590411009c0442095000010386c0849810040c00b031300e1f40e158a40c0303803414201d0044000b5808500f580c0100001c03240858504217030300801208015039a10540c00342c50030b1241146000c0020010709050000d140346820454002d122494107400d5060156202881c035802500c0680109100600704203000e041042082d074444019 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 371655233 1250 371653983 371654021
    0x30301050f06070b0411041d0f060105030a050c10030b09010b090a060309020f040e030c011508010e07080303180109020a030f0b0106030b0a031e0b010e07120c050f0705070503070612 80
    0x2941303a800e00c9000140c4001c021540000c2440e180e6600d9400042500c00d5101c8040d01e844c01c540c2c01603946441c082040d00c078a00400000003801c0c0350100d54007c0094001c1c01a00c441c0303070301d0020407183c42d1b0344040d10014550b0310764a100300b5440d6411864047c0ca1001d11099540900402304101660745501020816040c0030f01d41c070058032a0101c540c5030441c2030301e003c03a058021184407400d41c011155001088e610f04110320074080c0854007428100c1b14940020001d40e1000300f4500d448500c14062008160700400200d0134040c042c40000c0c4039080c07c0f20000420506c0da500054520f02e5540c01907034560500714600040c42007400c841ba005200a04040203160101c07008603160501a10000d006040e01808030a514038a0300c3da0b064a196010300081d42d44c0d82c45c0c0c01e00381401c080c1a42d10500080407010620f1142d0014491500e80184986645080c81140a00302009510028085500e0300807004000b90340c3e03e08100f00406403a40762103c1100c03c0740c00d07002000319416950074100c500c0007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 371656483 1250 371655233 371655247
    0x1502060109380a090507030207020411030601020a26030a0218220c02010f0603050f070902071509030c05011d280f03050408070603021b0f12090d0b09030301050f06 72
    0x1035048241081c0100ca4002e00c02141607400034584032116405443d03513134186001c01c80045c0d8594001c29030203108442c1040071003515154405103020840d1002d025030302a841d035a01044541d03403074520902441c09403100d41d240412080701c1c00d41050b41e40c0c2c0380d1542c01107054105014000352141e08c0306401e4800c0c0310700c803000d4408054500c9008400345401d039902d00c050318169200f9040840d4540d222a4248540c1d6540c0c0380c460f41d9405c8040c48141c19000300c50000c6194041030080b51a0715400201e1100001160000040104a549006c078103101e10180c082e00017420030300034444c055460b00a542da0540c0c0c02d071489806d0100301c90752000460024881140450301c00d090800e071142d040190159a0b480b0b42c507041d142881542c122950f83d11410400049440c2d00d60001c062100c410a414000b0340d0b18140c03104c0e90303501ca01c00c0034103d507048a003402c80559000350180140103001400d100c441100c5840d6030341c0b821400c0c2d4040030a40c00000050040c0d0419a80b400488402603411618240c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 371657733 1250 371656483 371656541
    0xe0a0503090d022202090a091a101103031302090f1306050606070b0a060609081906022217280b0702010b04020705060114033d02030a0c081005030307080d02041502060109 75
    0x46070100f648150210300300e20ac0d049121707048480c4a6a00352040380d81e203060081131140c8013100d9400481c801c410090010380d8044201100901070200c1d0001c1c64042440ba81d0380760050078000b44955000842070103071002103500a01868081d00a5120002d5480d04141e0010b040391a650480340060317000581003812006981240c42c0000c4d080400180c94101d01e43d0504040125000300350910b1960300d2020030300710740c690f021418103100d0a0407111480d081d08040c2d4072140c080c036617001d04c14043d5140c400100700d55590082c0c2c44506440001350500c0c00f60000b9081ba045a807065a45612407001441075180c04100c81c003040d00110010403030403480840d9041011801c034600c6030079100c1540380510410491902100419420905541324075213410048014a011030902c3c00003119200810300c10035150245800350340004d00038620b0701803587c4541026511800c070715040d00d0f0b800c02000901d00d845603500815440240e0150007103501d0300112a094503081e4518681d2485120b4411003000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 371658983 1250 371657733 371657771
    0x203090c010f020c1905090108061006020a0201090b0d060b030a0c0207090e2e11180d0b010b0f0906030f07020d0816111c0e040e0a0503090d022202090a09 68
    0x1000c503114014011700201414080b540b6601140c1c20188940010802e00030104030107104a800102c107116155031410126511060458041d0200320300c01000d022240c0180e00a00c82c0407408800420741d0341c0d81d500228000c0e8801c49100481581e038404001005505000c135000038601364405012400170f1010340e0b03803a5035020303140e07244041038024400e03014296108540c02043c440c100c204550710442c0b104285940c00001400175038100c40803503480390700e00750311072000c07040e0401e187c1c1000d07a0038864200e0441e0305c070100c4030261f90014011008140e40b03c500562081070318103104002401c24110103485d040c400c241400030302c02c10004202d07000b59080c06c0c0c0c014070780b0149010385c00c292000201c02c0c20031981c0e90b42e1001c0000560041d09405400000d03141015405807010800c0354a105051a290700d25000010312640040107a807000303203000d02c50100c4d0f0070300040c21210810003140c80c0f054010101718080b8400f80e00841c0505451425400e81c0c1c0c000c1081c030005010380300c0584100441d107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 371660233 1250 371658983 371659003
    0x40305090a0b1e253003060512100203060103060f1202090c0301380a031b051c0c0203220906050f090a0c110706080109110f030a020711090103060203090c010f02 71
    0xa2101030220400c0c03040c0c02d41001680d04401481d01e2400e5050190080c41c2c2c6820002c0301c006c241480d40018550a01070030300010803180601424155211910f000041e50000d014941050303210140482e1110a60040d8002054012402010040a881480111840100000030301101400104200c040b41503d940c040d4010840410b02641048424480d44418a549054181d0082070030f00795542c040c0d00030b46091410710940440f07107400701c0301101c0500c01c0c42003a141d81c0005440040ca00380007500300e415145000d0045d031303040c60910249440078440e09400890303200c0b1540c504002800c0d0511800d0003400b0152140b10308420f500b000302d000007502a00000100b42d4503584611024820341e4441100c9105000761402c0a41c0c41400a1240200b03000d2212000c1c94500f08810f454501811640e4080565900c10708580da4420980d00940049500b034500a49502040c4800c0d40d0300c1e55450302175403080b2801a1a030515444080c544074a906900c1d05000143c0c416940b40c5400007079060b16 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 371661483 1250 371660233 371660287
    0x310080a0c030b0c0d0e01050601021b031e0705040203070207090c0f0806060a0e2d0a03021f260103140703030912050123040b100b070803040305090a0b1e 68
    0x480d49500500084c58413401210350101468001280c0807010190000390041600b40c1c2143c0940014035100380c1400015854154594001441a1440340c40b0500161840c0c040c1410b80b000310b50f598011400303991003100c9800c0160041642400700c640c00307100b0788002c15010703d803015611030b5400b400f40142c80003a110034450040032a01e41c0c52644501c0e1020020180585140001c0c0b1560301c2112620440450450412078100c00c170f0a000c1c2400740b011011241c00422942007940c0ea5200c13082c2c0320300420407a1080010b010382c5840c80c80220b1030480710303115905402c2d400300c0d8514182640221156003c030800d82d0851403040021a921907690300542c0c2c2c0c1e0182c4a00e42d00750518180f0700600c0c03091100399500d1003100c00d900b8a04400d06a091085000d154680b1496a4020700b400c285130b2540548030807000f00b071150b880414059000741d50b1080c800d0a2041c078003007801000070040c0c0103036400720307000c26000107070107456582da50350881c6404005c1d400765041021031489140214000c401c01c3d20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 371662733 1250 371661483 371661503
    0x5031b03270a0f2d0b0112150c0e09060102011a0907020a05011109120a0506150406031e150b061e07080301030c09110901080f0a0b030f030310080a0c03 67
    0x201c12405000e080d2015500000b4103044200c0c2e85800d01064014210584050500d100306000280040c404000c240380e0008040c9241d03801d00e0703c120711a00300c103401500e1051200c04c0100c000860341c4503210500c0501e456001070f110600040042200700201030604590415a0481203118074400c4040c0b155401c0b140401c66a0300c05804030f1070f203080181c1c0034000b507080c9981403a142500d0700040c42030440940302403480e48804105250340d031000880042440d80300100181e480a0711401480c0c1c0c15038001c00100b44950380c0e403a2804110001c0d407000443c80c2c516403060b020000c121079003054540341030509200500500300040c9081c001c8409074452280ca40b1020344034413103003d0442c0c03a420b40c80484213407030f542c403400c1c4003a840100d80a41e030b00342c61820072074510603445036059400001050751351200d140e80e1062900c1402501030140d400d003580307600c0800e68039901400080004401c440045131649490b10b46108440070951100c2d480c0e0704103801c150302051480b020901030f80c0d004480c4c10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 371663983 1250 371662733 371662801
    0xf010c02012304140f0108010909030903080c0c0108070f09031113110c160506070f05120a0302090910050d080c16090b09090d1b0f060c05031b03 64
    0x80d90703000b00c62544101001c100c80d00c40703164001100252080e5828400a1039000c0b02e01d40070700c04003400114906003c100c0950040081c0b041603009800d0f04d074030034901010f05d65507a1796100790b103420a4144500e6500070400d003000b80e5a02c040c04550000340c600d003c008034000124050404500c0b0300010b80104405944a80c1030307100c1c0c0041c0502c52410307100030082c81c12401403c00d107680244040d4501c9001b520807580200408200c01070989200030860752a040c030a90f00c403131601030030010881d901d00810120a42020700c0d20054038540344036482c0580e0300c1d02034070100a940e01d4001c1c04502891200b13003042c0300d5078540010101841d42e002d806e840d074071502d90055524151480031100c00314590900040384241c0681c0151200c048141c40041c600d1701e401060a44541c0c43c401c000001800f038100007001345c11140e10500955010b00018901032006440342030a884000348a440424000400e200c078070340c1e04491034140d815a012606040d41000c030362495030086d1801071504100b401c20701e25 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 371665233 1250 371663983 371663987
    0x50709031106160c03030c02090703060b03011214070e06040f15091503140c0909010c0e010302090a050307030f12140913240f08010e0309090a090b0c03040b150f010c0201 75
    0x3032a043c58000c103401d15a40c0e568a002000140c401104074080d0348010042200303140a0702481c000e42d0803001c4254150717030034070041c0901c4031031012050712a0144041a41c00c4500c0034410700c070240581c00e121240a140c0030081c0015510f1390701c00544c05030300c1c0004586202d4926107061059964006000c00e020350b90700f070b030110704075560b42000e41503481c0d07002c411107800ca0001e070144064000b0303190600e03d6520008490700b22502c580001022a42d810400e642540c460341c01426511401040e460782c56403600c0101c1c1c5401000d800866804151002080901900540341d145503c0c562400780c040301c03512100c0c40f4580c0140c9a400713008038400011490100301c0d43e00034699040400041040e4242c5d69103007460300303c48510a40c8030543c030041000c1210141801000641e021900007146013100a50500c800b400c0020445081117540b00e04c880009210b462203140590720111195480b41080d01741400c0c90f09014081001420000c811445592a01c2c901440d0464003420b200c29180074074001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 371666483 1250 371665233 371665267
    0xf0a0b0a020304020604051c051203071b0222021e1c0510030f050109030806010e01090512010e0105040c17010b1507060605030d030204030501051e0115050903120d050709031106 78
    0x111f65070080d08400d03401500c1345400d81c01810940a801100c428402944054020b8881a80c0c1400007071038101003085040074200c0c80c0c2c000c0d00c3c0b010709408204a103841c52103c030030700d5140d07a4a10168001039200e06001200300907456a41402140610700b00c420040f4018502a444066410a4403200002c4802c00c9040c40000119042119070126884620b031981c005d26042d1000c401003000c010101e01c8070b5200b445150302c1940c0684500c00c80c1414081004490003440d52004019901c0b1034103d0203104080c052180200d203c1e510005c1510700b0312100d4444e40b404980c9600c1c0c280e15000302d4807099a41c0d20782001c022040c01c0703841551002d643c18001c005c2c1c5103903041a80c03d4481c01819190707242d8198002c104880c0038400070003054942c0c034981e09411482c28598448509c4da03000601c4150919900c1020048813030400c2031074244000003103424842030240e1141c0d940301c0818511010300b12070144079409070892418003196411641d42024118800c20348500a0001203510401030380c84c410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 371667733 1250 371666483 371666489
    0x4080601150306091a040e06010f120c05031b1809030a0302090f0901060905030f0f0c0111160608010306050a0b0a033201020307020f060915040f0f0501050601020f0a0b0a020304020604 81
    0x1c248034085e2170060707520181c010b000d00e542c0100d15244207900b024a0100d42c00d8180c0710852166030650b85080440e406074054a50152649905a41c3c00507040c0d80411542c1c0090301e444030a207540082c4841001800c01010502e40030b600c0d003002c10004018404000c580c032200c00f50030b00584030b10550000c2180f0307003581201c06801200c0c5400102e01603400006290458004034100d40382c2203241c007019030700d030000e464102e5040c0d03108000122041d8040d00a4401300b200741da0481c0d00c00001c100020000078420342c040310210320247d0051050041da80242d5600181c001c400303001c60011480400c0e06281a031001610321f9043c21203c24030f504283c070a005501c1d10781f8003200c02e5103d880403d503000b90301c2915204050710072581d05101c44480440d41500c141310550107402419036400072000c0b0004000c1c0211000310460032500e0018200400440015000d100001020f2400800182c5054400d440e04092544041c1030072000502c0901e240e030384007004480c00350f201e480317034404a101d40c02160 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 371668983 1250 371667733 371667749
    0xa0807031110080723031504060b0c03090609120d0c050d03111c0f0e100c090317030c07020607030c060b0f030a03031802120303042f01031805062a04080601150306 72
    0x1087c803a0009003820301001c07420048404111483e50f07020a40094130814020703035180e800a004001d00e52400c0d40c042c1601070400340c640004000c0d4203159500b4400c203202410f01003242000100240003042000e90340d44500c80c241003000b585a1400e5100502a2001d660200c6000c2c4001d041020300e01d41140da01c0340a2020300f44811002d00002640b80d44214000c00015881c0400c11341203144202e03588022660850401c507042850500c0c03510159000511503104000200305050040e04d03000000c110090003a51050b6034420645001e03415078000f507044c940b080540c042d0300b980c650b030042544400340340c2c5070800207110300c0c0684450441c800c002d10042e41c009100e510340e41c0c1c00c0324080f0086114500c1440c03007554209104c0d402c08015a100000045480382420104042d03501a9101d40a400d00d403002c0ea203410341b0256649031808008803044014010100005a60007201194095200b0324480440d41442c0c140a02d00380d0f80e820510038403a183c811000d50858440c0130b50300c21405455a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 371670233 1250 371668983 371668987
    0x51806040635070f020f0c060a110c0a0f180c020309011d090702010c0f030603121202120103060204170318041d011109130e060c090604050a0807031110080723 70
    0x118006406441d0307200b2120054061151a62407070744c0042104031003808000e108d10b0500c200d2900403201c0701c1c902d0300007600910405031381000f030341e07101c50142c4001c0060456041040c2d051800700d030922413036810500d41e0282032172159502c5a0b000300650300051400c0c40c2054050202c0d6180528440c10054510307004007401083c030042540c103402c402681c003110388400120b689a0302e012402c0341e40c03600c0045d10090044410015a81c070405044d103201c00401d001504120035a20704492050080c0c3c02201c0d001d0b4005406c01142c000d405694000d000480c01a6003850000c080705803419050050b01c40c440c2c1da03035940002c00d1009440800f103010402c8402000524088002c903d0135500801400f4450301d40008160000c00303503402021448060f400151250303440d42032000c00c20b074000c7c84c1c019500c0714090002040da52100558000200b151500030044c040c51810640611058150300038044d890030806100c182c0d0704100c0654110995240c000d114a015a48030030803800b0104046814501c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 371671483 1250 371670233 371670241
    0x10206041e08121f0e130c05030115140402040e0a0209121204051f1d010e100309150b1005030604091a0603060a020c1f060503010c051806040635 64
    0x10a84544900c40344480a289041204c0c141045002248a4010081e50750b0780042c001c0744090601d003540921070510014841e444a000909480c0c04402600140306e039813204001c2e01c1c07030202c21004122000e50301185050304004100d041e44d98000c0c0f982500343d40000e69141151150585660b4043c8000d06460440100403c481d02c3c5038400c1c800c1600c144600160f06100400d007214a459400d860b4452942d4822000e945c151618484400c090507c002c48141c3c0b506621040c0140b0840341155a0008580115140004105071100214401c0900e46107001500d0780341d440103589040100c2c06c0082d140d580d250005805059441c20040017940003000007030b1804c114120783c50085104030709445d078a545a050007400c074012011031001d00d41c020014441c1040840071075170348140f003107540820019200d8005c6400d40724040070840005000162034001192901c24180c01d00c0400c0b10854641450900002c218500c032080304a407002902041d98a85c0203491018410802d51000188840c94 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 371672733 1250 371671483 371671507
    0x506250f050d050a1d03070f09060f0b0c0706081b0f0a0210110405040b180403111e030901030c0507140304061106090a0f0510020f031006030b010206041e08 69
    0x1080310111420711a5900505020340240c0c282c51203841c40b030b5030343ea071180c20010203541c00c186040d001e980c0500560310003189801c2c0390118903000d0900e541000c20340d06d00c0d0031980a00060b281d03010700318021042c0540d08103540f0208224040b10340d5458464495107030442694001407041d0842002c0006c0000c14080c04104207002d007512a805400f55401050f403003000c1c8040e5510803214500c1000100800d1040d440c00d580320710f66007c4042c6ca95280e0304002540c5411050050b14240c010800c0d280d103d806182e405c0111740103c1e103444801b1888078a03034074034007030350790140041c024140360b110010345c18920b01c503100b9280b20980003902c07a282c84103040d10306603c9911a004040010f10401443d0b459928002440c5001e03071110b0340100404000c644404121007a28a82103500380284074101c0e010b038501e40080d010421441c108141e80e41000c0c0401c81c008900b070740c0148207040c142078101c15a0303a004103015600c150070400264604052620070320840c0ca0907040104040c8002c100d800e40345c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 371673983 1250 371672733 371672753
    0x3100f0612050105030316060f02090402121b0a09150e0315150105070b0a020a0e030d0905100903121101021303110f0607390605090a0f0609050625 65
    0x1032a10500b003200d41d0f04e8405158981c810480e041d1107901960001600040f0540d004140000c00d0304001030801512000007816a801f503140d40c00c10343d2100c1c080c0701503820102d10000c41c08800104c20342c0392088501e405000b05080e0f2244545283d5940040080702d80252a6501c051400500b901d00e11004040c2c101640c0d81c040d14080e0fa07096001640800c19401441108c030b40d1500680f4003006607880025110182d03200302008020040c0200c0700c2440e9890401c00320452a1361a2030b448200c0d4240710901410310000155a000c220000d00c1c00c10115503a00380000050f404c0349010144c4400503048140640300f40f400f941018440c0030740020a2010640070854844002c039040d4075902c1c500c3e42000039a00807001c2c0a440540301c5001007038400e8003483d01400f00780385216610859400c050503240d1840c5541d0001000c9140040c90003884d10740500d000020306000d14500107802c2c00c11000820444842c0213070750003114002002d0410090103800120b241520401c44c14103182146000c21200d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 371675233 1250 371673983 371674007
    0x41203200c250501020705040b04110c060109050f06090103060506010903081c18050c01080a090209100311190b0f19200a020d0618151b032003100f06 66
    0x581541d0b2052601c42d08460000c65005071300500c0a9820242004001c182c0300700d0565126558032514603d46403010040c210000307400c006000302e90302d4405d00c0000d40b44014005d1040401c50803c0000719500d5804650550390070400000385c07a03889000598a54849070400785c042180480c18003000b01801d41242c001c900038203001d01c440540103001d41404090038100800715046501805000d51054045661098200301c0104111116802154214100742c5101920040100d01841403103000f02e000340000509541c5919142008490469200e1a03402200034140b000118481d90803010070654410b01c50a050118504000381c0d03020706003074005203003e003903441001c1c10039040b0b40303010034180704444d00503000e16100911503503481d000305988829462800c41941007800403d0078580550b036400c100810006658664810903c5500080010902018240181d140c41b408580d42e0b003079000e517003800205889888009120003940c1e281c1d00080c5e000042c54000041c05640b010841e211 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 371676483 1250 371675233 371675263
    0x7170f070e0306010e0414030717030138030601140c1615021504020d0b040515010b0a0512060109032a06030509060615040b040b07050601080303041203200c 69
    0x51140c01e94181501ca0000344105c00c5030000403000500030800150a200e0441d5049064a00d003280036036828103802860003c500034100080700600c860840d464100c0c1c20000c0384112108000c0702905004050b40c12000300480151f804008124141d008915009000c2040794105841c2e1008450b52a51010410b41d8001d00e44c5070b000002440301d162210315880c103072584d4083d0008200c0ca200d9008589401b9100700d8000e000c4038001d0b00490161a0340c1c60141d8030071400790441c0041c22800e16400841a0044440900204210303070031290807000325200d0710b0117107c11100c2592001c00607100d0000710780c400b034041e000704e90350b4001d000b00340d0010025141440c100b031000710b9100d0f1003c41c2242c40071110380a0766440240850f4032403810060480e40c103000032010901d0b16864251051458200e03900c103690b08400803481c0b000304031003030100038050803040004509500c1c064880c15813400521844800307260b80d030308500c00154240c02a50f42022450b42001c2d5464441d4602103507200c1410340742e155 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 371677733 1250 371676483 371676497
    0x1403160b0f061f080c040b0d0b010807020f0a0204090215030112050f1b0d0203071a0a09170a02120a0606060c0204050a05070e013603260403080307170f07 68
    0x840361a20308001440070b14250010783c291460148140c4000700d02900030741c00d401c424440094407134201d4000704030101108001080b14040840003401c0c0040203041da00c159000b82100c60401c40001402e01c1b007641e011600881c0f02c1503503001081d0341c03210f070410790080060008008510322010400c1315010310b00c103031b04649050010b0074110740c0300d46058a000e52107040d50440340b18a8074081c409408160300040c00c0c0e5070b0b0560303070f00407854a0b4041c001401004d1140895210000d40d0003200c0c0c84024148200082072580210f00c0140c1c888148280080c45814001110220b1207010008800d1079a40218208161a256400074100f12080c0c001240301d10f00b000c000a80415190044034082c00080e121403895400000055440c0000c40004848194402c1d5030b4106119103c0c6050441c07029041403090381ca130840c02c100081d03014500e008029101c142162240204920040710100d070b8010500c0713a12901d40050480781050003c1040201010140c2400303102603400d02c4050107030080f501c4102c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 371678983 1250 371677733 371677741
    0x60801051e030c01034206050408070501031e0f02030411100905040c0203210402041514040908040b07111207060c1103011104090e150c071403160b0f 66
    0x852041c0d555281d140d0581c02550a0341400e50084c1c120700300b852032955256032a030044c140c1d9104600d00d0302c681300d0040c3c00e040342151070000c10051500c0162266180c10740ca040d041c144c0d0305541d000288212410140e03184814403029080303404000302240b000e00d040c0300141d040902e940103500191016a00540310150010765403501c90341c42440c50403152542e03c0014079040401c0000c102c603c01d607806601081045082103203001d003000c035100f131555044900c28202801440102d42d1100f10114601000000600c8181c2190491240c100402c480105035650149808841402154805501c608001c110a002c10199181081610400369100000402030500c01d90b52084188122000716141d0700c14000415000003c00443c2c00010b4004103c8244200e0201810303845070b80143c414075620354510190403014484144404109842030304a42000000510700781b14500d0001c0c1103036521890810300302401d100f5614940101c0403509602100c0c0d0401c0711a03200b04550039005041140001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 371680233 1250 371678983 371679019
    0xe0f090d0e010806040506120a14061e04080306030a080f09030c040501060c06020d180503030a06090b0f0105180a090b0306011d0f0c04050607030504140a08060c2206080105 76
    0x20141e0140169910b0860b0744407403017400014440070b0078160300300e40300e80307c400701d000c1c01003055141c6a8451640700c0c566203054540c01d03007440d0000d001d040c640448059003d40046010030030581094000b11030696944801000a2601394400c000034445003000c1101802d1410b41406803031441003c1c0d09a4040c903045604001c00c407802405998007240c90700360540d000c50700c650302600103194144130008650407100000004036a10520484042e0701c0081040b540b099030303014480041c05101c40034400700c0c201c04009502182d403d40031b541008004643c1a202200d800424501c4c07007806810ba0200310744403003c0002078854089001e00a229100002507000c40130400c0d2685000004507040715501c41041c2a60420302c007030700000d24410300b4407000c51076a42d0400180380740740c131940701e46648928207055a18501c07010441c0510a071040b030010883e0400c04141d9035400043d5903003817079403a4400d102072112032200c047e15034514000b512020460780d41000d9040d0584900f1640e40000400001301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 371681483 1250 371680233 371680247
    0x3140103240e0d0e0d050102040f0609090905030d0e160f050111030c0d110a12081e070e060c0a210206091204090504150e0706031b0801030215040e0f090d 68
    0x2805001d60f001203c003841d020b00c9040d420542c40d000800030401010941c6030f050980c0c10a80003501040c80d070f0f0008100c0c481d0400301180041510210a103d281802d494070750301c07802000705030b02e50385445418410840e401840140c00402c40c003003003a0001522602900b0341282e0364001c04e4040b4501c2e81c804100e403180017068829210508006001c0c00000410440c1c809020300e954054034440e0028020000c7c2105640311022031140c5d075035810b203240960b03140001075000141d80000500790028028940e50240c0d809011401c2515401c0e9100a030140f00d502e00821810b001d01865059410070602d040054a400383d060b405500b01c1e002c64844491990301d400d25450648002541040100200c6070300c0d8000c00e40c001d01a9441c120001c1e01e6091507410307906810310010490f00105e200303101c2c4a81520440325058400c51982d82c0740b121459015011800601000e840342c2d030713410b50b40035a819042d400c59000d400705010100e51030501060100440b402551348480900600c40c2901086100b891 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 371682733 1250 371681483 371681501
    0xf0b0a0510110304080a0c09020406050306121603051b100519020c040608030a0801081b0f0406120f0507050303190f03150b070b0c04050a0608070314010324 69
    0x4041181803402003002480030700910340605119059000c050650800d0018200812265014001c041481d103080f004d880d485030040c5602d00c1c070502044c0002d640c003130280c951000342601d440c81d00c000766103c0d803841c22001c1d0022111040c00501c0210402c000401c01d0100c490001609103019000707201003100341c0c0e0040b010800000d40603c5002e48400d05180801043c1c805801600d1030319501e500800e041d10202c0d0400c003282d5200040111401d41c1c407804041c01046000041c080c844d00b0455440d1a00c81c00e40d012510074120f080403840036075501d41c4540e0043c00d01d42080c100384029032902409950448800b52034901035000c0000e220b040c007204a5002d011410f020b482540c4110784143c6154221b50701509c10035641c2c1000a0307a1000058081c1c015150350645592118440d14052030a0200200540e02c0796105000130051602e0b8044c442e425218581440c1003142d41e080c40440061000c0c1e00c0c3c00d400e0548200000061040c10520740b0305100e0320191160300c4245d0205228103540d4130742 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 371683983 1250 371682733 371682739
    0x203041a10140a05010e131413140f030d0e070b040303090e01060305072109020312180409050706081b0315090a02030708061e03060a050f0112030e0d0f02040905060a0f0b 75
    0x81c034400c40c40e15000038250f0315000d00787c200184490400600000610f01181c0d244070400c00301600c8410711500202c0c41400b0008680140000405001591b84034054299201362207a110861404103490901140010b012096541610f07140d4a05004050611902c1101c1600b4802e00002c50360520074000c02e4031484862312801085580709180d01030440e4444c2e80352504913512100400107079000c1c4550305182c41c491102c140c0f25030007007900c071072044030701c8100c00d210b03c0ca480e85440c0010004030709070b0200e44c940c0c241500300b03039515212254021115000609102000420441c80b04d44440a80118440aa6141700035a560150384812407005403401c902186250001036034914020100c2c50111903501044484036100341d011074038018058405c2c110203500c4408002c100801e141406005000901800500c0042781d100076001c0700076030392102e009655041122041c441e10002141f145540903004200762101821301681f615000e4030110022801d061907981014058050090703070309401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 371685233 1250 371683983 371683997
    0x24090f08151003081803250510030b0306040f0b0a09150c030e010c020604020405071803110d0c17122505120c0a05070614030a0203041a10140a0501 65
    0x116039901c50100901c10340401d490302a001c07000441e8040580440c08400460b051004074050030507042c20740180b000f17221440b2024040c2550a004407510048800540b06030106005503d400c801810b02c0382c0c400c50b0584104001d00c403c01200d03080056880f405030890420035100e131003000040d182000c2d4003410741401c8003c120741102d5903a1050f96442c646003800a584164458a5425035028421040c00b50308124100000e60510340a421391180e40c1c1d00d0305000e0f407804241ca5401d20141404050100c90030300d440030034161142d8206200f0203401041849850f0383d90301020000010010034003c6da400b501c031300001c21841310342c252a445e09005c6040303510640c0078650807400180040003a51648074650b408071103901000014070710101088080d01305040d003428920700c0c0a400d940301c41c08001e0840ca101144848080a0381d8200406510140c0c2e26225420b0500312581140c642017050b10040041c41281c3c44c0c0141594111032200c50910170003100c2c5404c0011400341840b586000c07540b2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 371686483 1250 371685233 371685253
    0x60d080d1823151603060306052a070b0f1815071205041502071a090c0a080a02010e010c030509120d0306050a0807031205120403020109020f030c100f030624090f08 72
    0x4411207040d00c00202d1310f00020415503c0e12340c071050b64026203d42030500204a440a051000e4000e000d07806045120100e103009510b641d5000810001400c00c00c00384c4c0044003050b6040c503d00c0d540c0510501050481c1d000d0038042c8542910040199914004955103e4960038800c4240c0107840c421604206d0f1484002c6005005d80080d502c11034040f25000707544030404640b808410201802a16441c0c0104441e01c2e1200c00c2c0809882d2541100c402303a485514900b0050b81c0c0007618003100c14080c038043d50b945100389410303109400f56441c2c955000e040080c110102807c00684417400c04a80d0750188002c1d030762a020700a1101c2c90b40100c04c180e8000301024400319140d116a400100c0d030b18a0128034000b200d50080c0d4039440c0544040b00140d4686002c1015450191541c80e900013080303004c3c140b904084000614400b003c81c0c04481032049912642498902943c00352005298600e201501070743d10075145d0715000700e6400038001240c5494404140071901c1040e41d400d40304200700130445590 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 371687733 1250 371686483 371686501
    0x9270a1b080f0604201306050f0108040c050411160308071808060a02090109030c09050f180316060e0f060103020a1203120209042901090806060d080d182315 69
    0x650b569039601c041d105c19404d121305848200006582c0502040006421824403080141d06030390b00302031604021241e0244070119444e084c5501c202e403400c40300000d0142102e00c81c040c50340155143c0b035180303480c2400700e641030541000c2030f14803880039943c529404454404a2900c07804541c010844103501c0302000580808a5170300a0800c0401418050a240e55990340c1b140c0f075422039001801000d0311402800013070741d48800c019401c40010a8502a4015a544d04503a40d00440105001c441100c554003001d200c1d081c1e1100c811201c20303c00340c40c9000102d02000396241d00031301c401c83c001d0440b410300040300211001005440e0303605640d01d1010140502c00d02010f50001d050360769000341c2c1c50580000c0c040c0154084206030340c9009410590002004c0050040c1c01c00b98040348094004404000c02a0303141480c107001c0603484480c2548515040e007210004000800c042d13038046800b1300a031028418071800c4070905041c1108a007004084200c8100d4480d030042d0503d13524001c2400104403c44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 371688983 1250 371687733 371687753
    0x4150503040501090803040510060b09011706010314131707080702010f02070e0103060c031a030c060d0b06070506010312050a0f0c020301090b0a0e070504060509270a1b080f0604 78
    0x24020b40001c80c490b40680c0303d150096200f0780781103903e07600c1401010400e15041c02120020545a00800d08040707a07040041e104010144400c1c80c8030401030b00140550b03000c0c1d0b00c4411020420014080d051828610220300c5150b00841503814100c0d455420800c0d001001c211201d2175803003081c441c1000283d60054500708007000c0441c05600504102180c4510b5601d202402035020712000305080c051040090100c405201e0545201c00a4040d441290380b8000381e1500140020f407040c030703500d100501551004010340e14400d0381c42440002c0207814840b00180041c1a82d00403031081744008003201c416156442441c201c48007003400c00540124141c02101200072090014001040c200e031142d60b02c07244c1000440d0f0619080380d894200617034030201045124041c0c90b043d20300b00945410b0800040700380b40014800018070b0998001604030942a45550048a107800200c17108440d851401e00031101021802d41d900c1e80b00500b000410000006417868a00480d2003d0410360300c40c0d031a0401c1071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 371690233 1250 371688983 371688991
    0x21b0f0f030a0b0c07021e03070b0d090501020d06091d06060d06180c0303080105010f0215090c0913021305061e120d0519020619090c2705010b04150503 67
    0x5400359200c00b0303012031003150a980c8502404842607030b6402da9481001103401006010600d10750f818000d02e12251400180d810503101c00e00c134056160085480c440024140050004000794000300d941900020780b42c108800b030f10701304c2c10b05005505810340c43c07010030006100c1e4480301f0343c04031020030480d0a044031801740f591b00030180420440380d01a4840701d14042038034112542d1043c410108141548501078070301401c6c00b4a081751010348626002580c5940c4004584030300800d00010940c12401000200c48102d4007420008880c603108243d240c800000c02410303401a815142420110751040c86014451440104480303030591031082000c41074120840c20603004030440e180324410030010031120722250078540d00c4130b50343d5070244821440e407040c04c0498800e551100d024408807985800d02031800b0010080001889111800e107012050b40070f51208000e083e42020803032000382908480041344070303041c105201c0c4d641d03508000d4440d440b075489000450003d504840103000e100301d0040d504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 371691483 1250 371690233 371690239
    0x80316080c0a210806060c03040608191b02010e01060501120f0b06040b18060a020706050a030906060b0306010f0c020a05040207051f0b030601090921030f061401021b0f0f 75
    0xe0b000e503640e0400142070f40c19a05907040d075941c00781c40003154040140b560003142a20464241824200d4540c0c0e28055801802d040c094400300080e480894020308a10b41803419006100c41c900c1807280c00426121800c0b09401942050081c100300c8405000700e00071035070182c0d070f034480060160312404001c10a10f0440181d80703440d0218240c2079034480b0090070150090415144c6d5030019a0114415803a41c040703128043c0380180300b503400c25500810f0705400c481940c10055541c50303041d80e0031402800c032010002c044510300940411038944c0880590b1142d04203072544d07061541981c2058a148042c601e0080d40035003210f00c180902d0415801401c4424031880448040340e1900741c0d040200c80d00324144e40c0c0c403a81d64040943d21460700308489401018154400c000d82841521150007076202c8504000010369040c0312842e01030b01c40da00c48800002444002c1148980b181101d0501000e0618802e006104100e0384950032240701108c4001c1d2040202980c0a4100c4503092211300070040510b81d40c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 371692733 1250 371691483 371691493
    0x3060e0a0203010e0706031415010309051603030c29010923040f060605060a0f0c0c0504090c0816050f0409050f120d1401080c040506040e03041806080316080c 70
    0x1005842c24024151441030490103000010304103c0b0007001c9600756880da00341907030000300b406035070000d0b0800f440c0b090200f0319000c1400c0c1481d06091340781580100c043c038a03074205008000249640908d200454520460494247c85d040c00c1d0340d140d1400811480303100880d142d0004002905103031340102d011454500360030840190808038008240c1084506550041c0c4203404503081220510a04010300012036a403401c1c407020100044c8006c10704400e080c1400b240340001820300107100e24203801498020014003403c9580c0c40d08210148039032140b0030113880744001d20b015034079107071803005c065801c060300510700070b2012803c00c8040d20a00b40152a10700400c00000000c1300c05014445101641079021561101222441342c02c80c1d400c8100796901c52041e40050004074408150100c901078111008100f640716200024020091343d2000c036003600c00000c0001346080300c10144160710802400405c0356a0350f03000c000da101c3c480d51052023445440c140400000528400c007500007100454100d0b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 371693983 1250 371692733 371692753
    0x509010804140313090e0109080331030c0b2a0f0417070314060f07030213080316020406080613030f120204091d010917090609030115150c05030403060e 67
    0x50441d4811034400c2c4e05400d5011003404420410b02541c0d03080035000d0002c000340440303a04d80d002d8600000d48400b5070000e404841c5905c02c0004106c03600302802c0a141044c1d107070300c140b8000e42034440101044a1a00d007000010b0b015088103541c4c03840d208400150b802041c0c2d4041d80c84400390b030000301c802103002e400703000208a140c0a66021008206102e000301070417415401d2140321000c010454001d076620880800240030840c20100707420000d80e050158070f03019880111492742c003d0382c2205045200c04160300d14100590742200405a00035074040040316195040715458941c21981e042508102020036000207100e80440785626845203018800b5000404a500c10380e03129600118450341c440310461161b03c203071000c8404d40c808100080090701019507441c0030800c0350f00400d55074068013149030601c2d915071504450240301d0040081110108403450782c90f04000c607014100c824081c0d6842e414065000d82001c1440c0740e0848010360925141d03540e0031000d018038144101c1207000d05003004c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 371695233 1250 371693983 371694023
    0x519050a05010f0b0307090213062f210c03030403081e0103050d0f02060906061311070606091b140a09031a0708070903031e03110f12060d02010509010804 68
    0xaa50038442c030f10204070304040b1410103150440c182c2140304803d204011602c101001c1003c184215421821b20015601004d084618084c0c0c0c0b001500489101c000101e0032a04000708074614100001e450762040076070400403203034483c0210603000c00164000c001040200b4021907429500000d00d2030210140d070344411142e02c480c0020384c011115544401c0901548903005003081d14121358038030080c0950300e82560341d00e64900002d010180602d510003e14040f099158108155215070070310b51607985e6449207800d200130102da2050000091410084125510510b8035000d80a141d80e610140120b04a200c0d040b05a0f000320360100c01c2c46030004001001030f940440d0102e0b01400c0d4010840e80f8a40040084c2c0807aa00810610130441428030500001c0d801444a600d000800340c55101c0c8075441d144d00740c0052140c2c41507031059110200c2c03920740c0180c5010090a40c4094444080803680303800f02032012038910300754000e0124034240720003043c43d440b42c041164858012400346116600c04602 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 371696483 1250 371695233 371695241
    0x309060f0f040b04030623060108040503040b1305031b0a03061e0c020f06010f0b0d020c030421030e040504031b06060902220b0a02120d0213090902040b09040519050a0501 75
    0x1c0f4100c046410014080f480c81007034010a040c402c0c08001540504407000310840042c2024144484400418280b00080003642c0c0582400314601e5540e403c0c481000e0312100413407040038821301c280003071001c07171208003a41058551000381000320020704650b80c080207003500f0300d40120b960110101603c10321220b0f024011130410a500501082c07075400f4411410504160072206038249070b03600070401c40e006001220300d202d0600301b00586410704440681e040d407285e035100341c8524481d41404480c007199400006071092294983c40c061003d144148003d607002124040c000c9120302d040ea06c0030f1054201780b801c80a21a02d000107040c0e440b51010700c22038108098650302c80c504d51207003102080e0041e1941703016040c0c00424600b0100c1d4100000c2d43c0b0305081400002446011580301d611180c2d0b0740544080060280b4000c3e1800e8490074490000c19089000768855410514030f080da5040288586004075003180241000260984151900d21028481140c40e0301c82c41c401c400c041071003841 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 371697733 1250 371696483 371696489
    0x3041217120a140108070510090e0c09090708100303050c01090b07120c08060f100903080301060503041509050c01110a02060403150b100e0906010c06050f070f03060501020309060f0f04 81
    0x2500640700d0601d815581e00720b42e10362011540d40700414005000140000503860708441c0b0480d0782010303101c04000c0440702d42000d584426105055001405051740d852030240480b42d005030340441040c0e031000e00403070f4251010754280d40300340207048080c0b021034402c0004040081c0440004540d8500d19551410b4003003040b6039150002d0381100f1051105200c41c010565040820300d483c1078030f410320200103698501940070442c41440d885500b918a580201001c000450f00701c403c55840391703911034002e082540106e130304507003101c03825100d881c05502910500f08110303006030041c03005d05801340065800e161418804540c0d449040c083c100103a4a18001b04003a501c50a000b041d00241150b910080d40d26031f801552240c065800800b603603e81c00648205498400c40751000681c035203600503035519481c40000381c400b9052004000c035483c1d1700003242d80199840d545030703001410041021012074000e0b00070f540c0160000c0010342a5850a0800f401c00d100c880a2464a4003070340300d12100c11603000c3d074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 371698983 1250 371697733 371697757
    0x3030e1504020307060e03151308031609231012060306240b12040807170304110913060b04111b07061707030f1b02010618060803041217 60
    0x401c1004606044c0024401000d03141400410301d15503074002511280042003007a120124803000946280c080000d07806002d4000540c82da5900f00428815070f00c0051400d020007064180c0e0000442d4002d0040140d809000d04500001030300b40c190030003940003000ca070200c00300560801c050003a00600c0c4101030055100d2070380091286c01400b452100658222058030205005241c2002034210300313400c4070044000146226080d43e128503200c07100340954100508130300c071120050003d00c1c00d24001140135030f0080d800c002d165100d0340200820003c0c100e4016180d5441c2441500c0000c07420342045105c0c0e10006c00126010301011940403035038210082d800c07080c0700c540c0e40a0f107100d001803120030302904691038000004810035404400004000d0920030070076589007594104918140d101c100b20b40c620804200c2003907400c500080c080c08581c01000382e004683e180b0481d400a00d84140406c0700c0d4281d01271410300349028594140480040000e4402c070031414185620190f444000341110302200d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 371700233 1250 371698983 371699023
    0x1050108030702120d090302100201060801050c03011e03030516050f030307200a1e0302030d06030503090f0909070e0601090b0a080703050c0a080417090411030906161b03030e 77
    0x94010024071511082c8140c020785c00c00060901003591103161002500e40644490303400c401c1c0244100d00418040d40950802d510303000900490350441d90046040740c404175410031031032203c10b60119114600b4032004000c5401000626103a0300d4064000d6071715409a0700751561101130980c10782c2554070844110740003615401d040340011865050840a140c0d12400820b40c00d0300998030501f10783c8241c0000c0105003040b803146c8007014420001c9034071503c806130050100a81d00d18060785e50303400c04e100d01841000306485981136400d2410010384521200c1000308220b078a800b1401c06101405804c090420035001404100c52040c02c009013035014140e601c0030510329180c54001c0855a0140110042d801d082000031441981f0005243d046504807020030051008001d400b4000e11030390b0349040d0064180300068407440d04c0310002c0c42c03007108500141d82e055501e40458018212886042d0b00c04621408042c9445050b480d00103842c540c804d0134005182525201c4003490061107500035505c02c1c4803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 371701483 1250 371700233 371700247
    0x21c0e0316060e1905060a0218120109050c01230705210301081203070503070e130905060a0b0103020f0d1e0207050105041202060108030d09060209040e1e030a0507020906030f0105010803 82
    0x1004031081e0700c0410000180b00f048136646045c1c0312100904030802d040c5d000b1a40036401045a6102001c10800501049282c1101c00390395000e4128850b05841c14000c500c0c1c01c690a5001703c1d204410107083c1d2403010341ca0710001c102094540c20190065401d840350058420f2248288403203110045c1c041404151250301d1b04500d40c1c604114000c4908440c40107009101e0441e412900380e81e0000c0c514103000b46180b402c44042440d000ca0074005001441c20030b401801400f0b00030800900403003446805020000e0424019404c5c0d03c0380d178655594203002009071000c8405079911184402c9003406001c0b101c03a50700c04c0c00b070040c1d821240040d102c59568409000801c98484c450420320040b80c0058505507251010ba03035101d000700703142103600a4984410100f0015039604461317011200070820040c00d0003420041d59110440c02100082c1c041a000c45201d0020010a45080094a45d40ca03894110f5680c20700900e0b820180109400d0301c03e42101150780305c020302456010f4085000210380b2104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 371702733 1250 371701483 371701511
    0x6160215040f060c02061b120d02070605010f0501021903032901022a040902150403060c11070b03010303030209060712030b012a11030a200112021c0e031606 69
    0xa0742d030b80f150b418480c0100700d100041c0c94000c180d403258000791107804014101c1440b454101800314010448400000500c1012440309034003034088540101010041c0c0d81e214841018999494000c141c09a4004800300302001441d0400c1141d0a01c60320f80840c050348030800c0c5410001d84244e072090205203000f519a01568104a08241d035101a003078002400810510048405072442409008580b43c1c214141552aa0a440407850a20380d01c05950b881e5241000e00041800742d21100010f107a03203104113104000017808209491311250b03200d07c0d5910f1131350b05400940c001d45842e904544140980c0700030920400768400d0941490b100801c05540b0400010002030b5048100790700d0302210007a07403900c02c0c02c46501c01840da0707004102100d889285e60000745041c40202d0014940701a01c504401506404008404003035804e0700e0f4900184180304c007400690003103070803550004882001519a01c003141e0000025105141c0940c5d25010b100021182d132202821000d68415446403a0007200700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 371703983 1250 371702733 371702759
    0x3040c0e070c02040b1017060301020705150604050f0103170a3510080703060c17160207050d120c020a1802070c090b03061302010912050d121107020616021504 70
    0x114200c400c0c0c00c502500220147c1684a620100303510924550001441500e09604131840309400030110748140c9410100168051070448403280541e0a24010401c03200000b08282d040e65889250440e40008200300c0181d5a08503540c19020001c2c0c100584581601e9406102032603c1708030061452149524402100d10310007a114864240c072161082040304400700b0800c09032079000742c0101d0762030b100c403c048420310140c124000b40102c07031805018807000c00c245035a0b03510010717400b44d4014039034844c104255840424000342c00200c1d80f00e0030101c041c2c410039420150394802012021000e8980002e604140d040d41d014140c0961700084d0a001c4c0071000c0302210051071041c40030700080e0080c0c2d02207522010085d114910800c5004100811680164a850040c0032000c01c548002130341400c10b107a0f102a0070700103a01150706200c0360490340e0b959000b0210548541d01c41c2d1440c1004690034031070075900070540346900d080d040140400513070b10708452742e4007842001c020301d855504080d0124030036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 371705233 1250 371703983 371704001
    0x1021050c01020f0d1101020d020c0312070311030105100c15020c010614030a080a0c0203011b030c020a020108130f12030917030915130506160207141503040c0e070c0204 74
    0x1650140443c0d0480030000140142c9070b6580c0e160444004860480d0075000e80115803840342e2035400410114003c110010241075100b055041c1400b440e03d640c1015412140442c46015802c541040113001604245440014421035442c0989404c0490b80f55030807100307000703030b02d00e243c00d9000074450070240d009000c2c01024005682c0782007040003400000964606076a4001440e4260119412400340c0c018003020000540150080c402280d404981000c038606200d03000001c2841c003240c0d890038510008a5007007207541a10340c5110790f00c500b5903409480b00000b004903400003180c0c80101c0011041c0d01201c008003903648010850007141c0c40e10000b4034050200c207240052080c42041104407000648864079522224007012646035400c8c9004400108803010340b07584240001e001440c10015507000540350168241e03200a034540d54450000c144d0f0442050f4810030a2050003035040e00c0c0d2000b550410b100380c012001659a5014500300084201c4120003c1560341001c2c0d425070503c0d0041c4010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 371706483 1250 371705233 371705237
    0x5090c07300f14190921030912020a0e0603030903010e0a1415062707020c090603010204060e10050c07120308010902040b03040f111806040c02070503151021050c01 72
    0x30f030aa1401d100b0700c060140c054a040c070381c180036000050036402814200090043d22115810340010560600d510b0890160101c0008240c401c00041141c00b8003d076010060b801090002d6091628041c030056460203884150b0502081142a0541d41c0034400c151000008401411002400b400e1000b141c0c00c0245e01210160880320050035a42c41a85039507520000850303070342007900e000c00303801182c4240b07241d0034240d81c02c007440c24008026000106100c60600844882c2c0300c0741e0b03540b0107140c240c1c000e500c0740c000414043e03c0c00143d2480e207418918000e551a150840c104180e15020070b140a0f603e60040c20141c103000000020b05512a03482c030f0141006000c1907181c1403502000808a10004101905540a40007180d0801007483c540100003c8020440c9082080c60050880f04c0d80080c0da14610640ca03100380c901c003090000c44e140c011210014090304d64a20700c8400d0080c074000091031100d01608640b00032a18064803058034285600d110040144c02030b8a01d00070b480c080da410b6403141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 371707733 1250 371706483 371706497
    0x9030e1306090228050307021903180b09040c0e10030218030102030c031608060a060f020708120d14010f12060209041b03050603150105040c0e04050a020a1805090c07300f 75
    0x407c2c0b41e00041c0e80541c8001d092004003658200d400c003121060080a00f1881522008800084d041d05c00c00107080000380489040081d46000603084e114400a0b0103c072350449180b031060100140a540a008d80446172034000c0e03000d01031030000a0032640300b2038681c6048403020060007058503030700c140c00c00c8203030450400c1e84850405400007000101c0c3d0340b103010204101d00005022241c405d101c99002002d00004403401031036a03108800c0d031a0442a03907040d54070319000c01c211040c0042ca4409049920030845c40102ca41402c022441980301c402d01079030419000c000401d040c1c3c0342c03441203800b0403040c41e103804002da03120030006040d00e2018050512036800340017000000010001c9403411920211750025a000c40c1031720554a141c0903200440d0301516040402200010302d40080075002d41d196116400c2c41c2118244808400c66800380940042503e00011000b43c8501d004200380c030302840600030750184022884544245400c1d030001c1044000e1001c2c070342c05410900c20705602c107060034494 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 371708983 1250 371707733 371707741
    0x12030b28080d170112080d09200402041a0c03040f08010b130507080a05090a1a041703010f050607110907030b1e010203071209050607050307110409030e13060902280503 74
    0x3c00010418000d6a02c04495002e4640c2080b10b46404c940301900355800a1100c50b041c0e041480c2512816408840142c00441e0b0807502c91602c0d108860565040d02d140300e00500d8180c1c05503c140c1c000c109404501d00c000c100c0855546007407242c0c41c2c001d000c400c0001c00c680030804184540300e504540303d0300c50a4284003c1c06501d0f50410f42c03255005445003000145c5542d030070360091418203a8100034120104807c442646c1208942146200d0b5000d28034480a034003244840c228a403209201d861442c185e8000b0a120a2038008000c0849a0040820040081419000070680c40302614650007095980d001804981000e40340c400004200c003031568941d0741110300203501d0340b060030380050134080340000303c0c4101400b40801d038010b4800179015580724410b92500706d559500500c801c0d00e1003000100040040d2800f0701a050794151315a4462a074040d40c11b061040e01000c5001c0c082d87e20b03494503000314400210f88047d0030007441200c60501100400c0a100010302c1003280c1100070070804100700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 371710233 1250 371708983 371709017
    0x12020c0105090913030e0d03020705030c010c050712020d08041e0506160323040303050d0e0c13020d1b0f080c0301030c05150f0a0305061c12030b28080d 67
    0x80f643c03000c0f401007000031224961804480111a0201c0550700c002480000414103070700184840c1510410390444514105c03070001503036015941000102113921514040c490052860b804c00810340c0701805000d108102d56039106442e801c260400000c40d1120303400f1041c00300c187d003541002000c003a00c3c56460140030483e8021041030700000a410711001000c030b58880c844e00309290050011a44803e92250b4581c03800800d1a4800305024042c10704001a10389410f2010400030540e0000800c54506400c58800c003c02a412a0351451000c0d540d40d405400d102c40e2200d00f013142603600b607640c1d4420110190000c0d04550001d009240719802c02c0c00140001680c503010781d070603584201c03240c104c0d10f1a0111020003030b01c46d803010542c1040000c02c8504040d90160000c50003084200e030000741c51410481e010325031480a040c00b40c02e44042c4040000c5e4180668071610350010050f21003100d01c01721040b03907209807c191804d21000c0001010400c000441809101005c0079546002071003084c0010b03030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 371711483 1250 371710233 371710249
    0x1e0d11010e010f093f0c0b03010f0905071206060e0a0b120a0e03220302040605010804050a020105181f17040305041401200a0303051509270a12020c010509 68
    0x8251810141034608000184141180c1300700540800340160b00d05c07411855890035124903581290140c1c0001e50100301c1801c010b042d241a10081101c1512041c0750141c42c0000e4000548603200344551010f40d80000600b900842e0080c0c103054854090f801591814030031002c0e281d9004041a41050142c43e000c40048582150041110580824015000340100d4110b02c1110f40c81c07261440e0700020746107041b010b51034800c2202c0c02200c003003058035665001513481389c500b00e40c0100a0340080300103c00660290020704065103000100070420f0307240601250304400c084c02011280f0345c60440c10a10981d0284908220042801100241e41010b5078040d00d24080c0780101228036004032440b0700242d11075240784429001060766402030399143d1321516100d550780b400c1680041c0c10a800074401c1c040380c5105100129001d0036852007035032640c1010b800751a41031400c001130900c07a10b80d8080000c003085010105402040919440d540242020389414461752841c4c0c1803240a2000814641d580780e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 371712733 1250 371711483 371711489
    0xd060b18130207052d07081c0e01020307020409060b0d0501021306090302011e031e020901091e0e100b070507080c010806010807030213080d020706091202030c1e0d11010e010f09 78
    0x1c1402207403135001942003000310310840200c0305115041000070340400028400c0201040c0b0800d000808c6016a4126404042187c1d0103000d80c0c01081803c00604040d40000d001a0140d01c002034a41e6400c40003c0c031107803a080c0309803180d03900030036039002011a01103210020b104604001041b00d14640c0060210031910031110080c07481d48903111041400b84c6c004010100f6090004505d1440c45d42c4030800079000a051240043c00c851000710751009020014081000c50b80b24002c00a441c0c045540d1a4034070091001d41841000000081d011100d013002d04041ca01c10303006004443c1c217200c50b9614055040d80c403a070400401d4000e0211590300400ba40e5004005071402603a6500c0d005502c01100c00350380e0001100b4450484005a00c9601081a8040d50340c15900c19480c0d9030744124038240035160000c040c1d8550000840f00000e4902081c44000311811002400f07950280d070300c0000d5071074900c1d807070554a550003800c00f8440f0b50b90041005160031403d09119040138080b140c02041108540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 371713983 1250 371712733 371712763
    0x120e0114162f131b09170127020d080d0912030b0609060a031509020c0d020616080702071d1e0f06040c0212040306020a0311070f03050d060b1813020705 67
    0x403070140310b6182c20b43c01043c0c4003004e08030404c01003806184000c0400c1040c1c403800026401480c01c2c64031008060080d09116403d003034813140c20110704805041e15146100d800c036448544c50008100054621001c0c050078440304800281401c011b00301400110398540380a420581380101440183e5942c03803d0b981c030b0382030640d0001d4039203085910a60041440e20640303030200749451400246102140c0042424400120940c0d2700d00c2c01044059a554009a074074203c0441a480c6680840e4460401c00f58442c016104640c3c117103550750700003080502e4008214141151090400041180001d44400308105041050146141541d6a40070b8554041e014500c1152101c4850384450b00c01c1042500e605100d100c4c0341e42c0c9680d02c0c94050001d51040300210042814410240800f0180c44203441899411650846000303405036401c6405500030044640d80380d6072001c011460300c0d124005007451102d0040c2418100020104016080b109000720800e1207004000880000f88049113503a0b0006c010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 371715233 1250 371713983 371713999
    0x1a0d050c220b04061d031e07050307060203090402131e030501180305120705220305060c040503030a0810090e012f0a03021c0c0819050103120e0114162f 67
    0x1805170983c1e4072400b5410281d05101c2c01c0003d0f68840004035070160403c8010302118103540da01c074140b41d1030303034424401c0740091f030400c2c00b40c45803074106500203101903841c140380080e170140c88202402007102c0042c4451200c000010301401001030034442c04901c8ac0c9652912280301d607040da001003140c45203150106055200001084c1000e003e07005651908040042d42107000542c0b100740c00b108000e070b20081d580343c8600d2000c02c4401d08044201c9003501c401501851405110300d03c15100e941c0041d00d1540dc4120915001807900464460900170324488400851010310300032111102c41548608520f076a0000348008902d00740300c2c011180710000604000d40c0303034030b90002490340c940c0c2c00c110802c514501340603140000c9940404032030f00c64083c1002000040141c900306904803202400300611400300380184100403400342d000c80f015454145816030140d05055440c800e00c1d000b81c816503400d441c01160b14003c105110011000d2402d160419038405000c0c10000b80744580111101c9021741c1c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 371716483 1250 371715233 371715257
    0x60712060e150f04060b210f041e0f030f121104140d15050f0a09050a020f03030d0903020f0c03010e03030c16050a0305030a0b0d020108011a0d050c220b0406 69
    0x442c0e5010303c2d1288000c1c0200b110395a0b688461b030b425849078401100c04c401c00b845156031522008800c0340104025908e00751141d490350b56040c2880e48451a400701c17034001040c41d100044d844031100c10a07611903030b6901100a0b0244025055803220413904060380d040c860090700e611807070803d6408441c100c1c026400492090000300d21404020328028011500d00b40040528030000e400c95401960901030f8000c640e50b44421400c2101e1901d40014078540103004200094900701c0c00c6415064001001e683c540309081850b0401c40f102841c0840168000485c2c0d4076408500344070075015203400781c00900242c015100e9035a01c13403100806161600d007000c583c4584440018503003203041e5038000121101c00900303044c040c1c030340d0700100c8084406509040c0040e6180c104040c0120840382d060311441d08903424902000c003032601d4840b941141040c141304460701c040c1c0c5405080e0044004840180e1385000e00d0f0101ca0702c814070061000c10324000071104004125000c41101c08450b1035207000981000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 371717733 1250 371716483 371716489
    0x201c0e0108250e0607110a050303030c030402040203070306050907090e060a080604140102040807090e061509070804110415030b060402040305120306010215150f090112030806060904050702060712060e15 89
    0x10507466820b400c4013010480c05d0412440d80701129004008464540c1002d23619006c0560341d110445a15005090910118005092079000786810000c1c90401090315a02c2c3c201107659220212800303000a03682c110b003000010045940c030b58010000703a8982640c80c2c10204115690310019000418100e4011402c40c01c0910a6055901034800e02c1c094501d0782d65100600006841c50006e80e5045028100100760080601d84120480b084003404c0c202c07070b80d03840b60000c0d50031034001801034504121052802641d60f95600c20021208105c2442130725403810741c03c010110220080940307003d54410007050010800c005042400900420704240c1e896941200403810b12021209051540380303010103101d0018a8801c1c040805442a10704c220740c02910b401300b0510880c2031242c00000c40c0c0900e41c03000440e1048100c01e03404a8064621131400c0c45810110b0201c80080704c00a0058009509000b20340f03030b1100e454408824490f0007030103460b00b0200d00340c8801c5009091b503080b11480c0000c03901c05071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 371718983 1250 371717733 371717747
    0xd1a161413080d080708010b0306011b03030b06210901090f0f0807020303030c0c0c0d0c06050d021215031002091c230601181b201c0e010825 62
    0x100c020190f818401c80b99078040e1880d0000d880c51401702d81c0400c00403811603102004d0702e00c15030050390340c000801c1031300800034480d082c0c207001a42019201c01c0c94004c1a02d030b443c001e1403460862074809070084a50504d40003850b2000d041d10712240d0614000384081481180141c0307481e90041284000c01034186841240d0b0b10451000130b4045c0004410040b0f42030200d0068031803045a4410f480d03011200d00b0400040d1070101e40010102c030004501406600d10940141c2030852021000601d48507001c0b0b240720310b018044071844402c0308050350401c802c1c00c040c0030035400d18104640030360904095100080044130000c1484240410704e91030384003404840540d82e408154180f408030078000314504031a40318a802d000d0507680000000d51341001d0b0186215004000070100101c013803e20310044d040341c030b00015440d52001c3c00d96040c21005141ca062084522854044d60720b000301c82013082c13000d0810907a5541480c1072200b24005c1000c1003044851070808400104014440c40f100b54809507906 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 371720233 1250 371718983 371718989
    0x608150f0c0c1b1f2c041503050c06030108070510051b0a0215070308190603021206010515070b060f1207030c2409061107050d1a161413 60
    0x7a128152102004149040e00e9020b0907000f9510b80c1e1244138031080040e2407550483d0141c00140c996105c1c401851004100500002e0031460790115810f566030018091300c0030002c0aa603000c1d40e20400300300704081049000c20024007940d1207400d56140010362a00c3c0c00643c03180d1405100f808800242c014402d604032595103c040c040b0044002c03001012075941c0340c81c1d0104900651040a180080c2060740c0e05071141542e25a9883c0e00554075a004442c00c071504400f07107170481da100c6902000590711480309070b000603001001001c0382e41c940001c1200c0440c07a51140510f56504000c11808515200b606a0b4401c10a4687c8c80e1280289004a4841c040c1100025200d0203842d10200c1041400304d0142d08807080401d540580449610f15281502800907400f4045120605c08001c0f00340038101e50b581580c540b03001d5903c66a5075601080f0a8007448800b1100e80c0c1c04010483c40c403052000c130041d0032400251a19004d0700c1c9203880601070b40717400c1d1140d58036140d02003248610384101203030500c06 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 371721483 1250 371720233 371720257
    0x3050706150e010801050a0b040213061d21071d070e2803030e101718060106080402130509030d0e03070606270504020607080a030b031f0608150f0c 65
    0x603c0d0303590b6041e41e00038081540e08001c0642002c10404c241e2905009445080c2d107102e6842c2d400c40d191807415583e885d040a580030602101d00e5042e8100d035107450640900420012100000b814403100b010300700b10321908403071020071404d8100480060a103001c17aa21540720304218508170800c0c2d000980b64a400c90324441040303a044034a04415030819007501c110307031198481074150303154442002005610282c80c040040c8140c5103619041e03520b030320707240c0c3c00c000c40707601280b4200003030b500135420300501741c1101011503450340a210442c00c0c45100c102c0300020080d002c1180b030a21050160b100e01c01c0842c003c806640f02d250190031080140200d58145900180c10458166201c0f1031425907000d8a001411a401c45c0c2001440001d007409224401d99000300103c0c6070030b8156032140c0254004a02e08001c1603547d2101000320f0f2805c00020844030800c07034510707040c0c591680d16001540c2da103405c1070741160803000740c0410064028580980196220f1040c800c242e4a0b6034034070291f07001d40d100c01c80d6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 371722733 1250 371721483 371721509
    0x40f0816050106060e03070b09061e0705010203150a08010e0c0108071205132112050a0b030a050604020a0605090609061608070305070506010603060321020c1206010e0109090305070615 81
    0x1d4143d8005540c4124005e0a030252440d541e0f40d15036030300144c007074103202d2a040714003004003689101410000406031a401040d00d4100802d9450386802c80c0c004452443c004403c001d00221645440100a4001c1124600030b1046000303202d1200e0b00c4042101c00780c0e0500180308080790038180194541c0749101d03c0c00c2d004019a19055112604840202c1302c20356001e800d002c1c01000740c103468130800100114985400340842103180e02040100001000100c903583d0342c41a104480d9400e1015950242c060802040310b8201801041580041a4080d0007888010418490182c507940107440d01d4907002c550150b2944407a221281441208220081c01c08400003000410140c100003c0c1840720700450498a031680c84101c00c1d000c81e851400054006a640c1c0d0a11100c614031a030000c030402004c0c4140d60b95007840e040840c1c41c03101d00b03001108040d0001e03001449500004d04000c0c0c010a800100bc1c00380d035500340c401a0030b81c4216140070348880c0e11107815880000910200384028421602800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 371723983 1250 371722733 371722739
    0x10327060905101104050406050d0f0b04150516020609030a1713050d1d0a030309030b1009060603230f012c07050702010813030914030f010f060303090608040f0816050106 75
    0x210280e1041c007a00b07201f01d01d0100085440d050402200c5030142d80030031a1504000c0e65142c135112514014400c9440405941e1280480c90780c034005c0900501440c1001ca40080081e64060b041c850002c00000455105010310644954050f1100c0c0c185a40780c07146c410300e80c0308c03040403a03000005814003400314441e105008812542c400c040c081103841c0b11490300e42c0300b98030004000c5203c0c424031000c0c001a96140c0c051010603408081190800000c104140c2501e640e20300340005d0310312aa0006003c40c4c0d031407a1641c404103a61900c3c040c80014040190b0701d0b80750560108075101b00601500407500d16a00a80341000b514090001e1a0500c40c1907403c042c0c5080d03180144507900200381240000c5450000c184000800340880600c140e1503103450843c1404c010114030f40c1da88242016516119640116149030400c0c42681b04040d602200170074000c0c10b50a0282405490340d001804000c5030804100118840f1400000182c0d400001c4031f42c0d640e40c030f4084403038041d503a8a0240c4030f546460400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 371725233 1250 371723983 371724011
    0x120f0906040e0708071e0318150c1704050613020604092a0201020c0705010f1206030609050c0a0b16020d05030c07060306120c050609060f0706050601032706090510 72
    0x1003482907040d80c0e14a5410b175181071040b80c40708034903007503458000f0401c200c500c50103000b0f8000512071002c010006201d51100c0c2c80d01c00084c03007284811000b4a9503203c044001c240d0020340851070780d00c10810300c3c00a00702951200e58442005200142c07a10100910808566035481107500410640f1000d001d0807203030032260242c0c0503e803084400c504010034203603c1881e0060080d94010603400020b0200380c0e24050054951300140c0001c442017010b140c1c0e200711345000c14171074940654080c46002131a180c29180a500c1c0c02c000002c45482001c041d1b10070403690340b182045481e020741d80115042e86820510202d07007150010340c1c0c014001d010100d04031040740000101101202d04075581400750b16914003031940c000c0c0302401d019141c1c1868140901503410480010801c0c00c40113000b5524224401b0040e09003600200001c9408603120800d010682da854010808082044c1d02c124210500c18121287e59903070003c1c1c003d044580741d082c00c6003400740c20f10000461100c5040b062080c6401c1c01c0d00303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 371726483 1250 371725233 371725259
    0x5062a0f0705030607030c0f080a0618050406060e060d140a0204050a020a0f14040e09151f08120301050409030e03010c05042420010e1507021e120f090604 68
    0x30b100e010744502c000203101d40d403003070140c6c80b103140141d00c038429000502d0741c0440b01c40034003d000040c4a07803031380000030b0b00f11107009a100099070040000281402d01c1d240032015190950712040c07081c03c00005000d49a603982a02c1c0140b5071b800842e81140c44040c400c0e00341000e406220107507000e0f10344070801c01200101d40040c02c038400f043e51001200d00000c6400c1e07841008100022884120501c402c0c00843c25204106070001256401c954040315208c0b8140384100c2c04440c87c0038403000211900300801688130030100644041c401a1000b0306106910074003500052040501c581c0d01e46080d070382814001c0000b1000141c01900a1001010010014046a019104141c1c0200459610036030381038441014510007103070baa446a04c00b0101e200314201041d440707032107007240f950307150040c1c00412400c21042d0010105203190814a10700180040c0c01c01c48240c84c07846a44496114030610102d0110740d9003004182c4070002900ca031005800c8620034000c40805035005100001e001c0356000341c0c03500c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 371727733 1250 371726483 371726489
    0x3080a0905040e06040503090d03020c10170115020d0309020d020a03030315050a0b030a20041d06060309070506210103080306210a0f110607030e0103050c0405062a0f07 74
    0x2405115560f8202d140c030b070307a914084802410b45c0d041400004000e02d000317081c601c5600d01910441c2c002c5900c000c0000c1c0c001c142a0104000b0802d4019515881106880b0141c014489007142c040c41c80c8807040d02035181c0100d450702804143d03882e07240a0841d42c44541150b10a90050001ca10741504c03860050000d0007007110420400306040400030746803403c0783d13101e0141c81d400c0c40301d03505503140c5d800c00b900500380d080440c484002e491800d42064801840180000b07143c1e07000f251810031080c1c9282540d811010308898000c1b042042000504000040c00740c0c100d846c141d4001c0e81c0c2c3c00e650601e100d00001001e00c8044401c400000010a0040d0000a9401f400c0100d9411300c15540581070b0f50742c5400c00c020340c091250031102c0240086698012040700050089080e080300c4041c40b80001e4156100c054114003040140d0582d0095590510420303922000d0f40401c1c51a0038140f5000599501410240c44012050301300200d40e003c2c1407540d510043d1020000319245d54210b2040940c43e43d210340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 371728983 1250 371727733 371727739
    0x20d150303020f0f0316060605270114031c0905042a0203120a09061e0c02010e060c07080d020c0a12030f110a1b02060a170105090405070b1303080a0905 67
    0x9800f2540b000c1e808500801d585004100862601c45c4000369009140c0d004c2c01c050720400e03540c0c1c60008240e00c40c2a5400c4906400b0250790448249503500c0c68103240d01a000010314038014407103006103450008401102d07020300042038110f840c0525049405800917000140c11905006c22110941104200201910011300700401e060901b010100ea890041c561a00c060b50450004580410850f9216014050080c1e03008128600840c03808800070788400c5003101103e540d980c14448065086c401c164202c2c81c20700c042c000f03a0038500841c0c0080d024100c4040c0c0b142e0400548980c450446070b0450b541d0604c08000e4502002150406107a42c0c1c41958260010904001a031407820301c00d4130600c14400900d0b95001d00307000710500111501a41a050600c90302d0100c4140b80240c0c1c0c034840541a0044a55a803042d9a45060b40e4011680010303400140100b40c05000c0c80300148001c1080b00650702c488809a44490507001c40f824910f07455400030342001030026030b58814940c440301a10595000fa = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 371730233 1250 371728983 371728993
    0xa0504060b0901030509120a110703061401080c030609060a0b040e07030f05160303050a0e06120c09040c080c04060c21020309120307051b01050c0102180f0a080c13020d15030302 78
    0x4c160940d07c0341440ba00b03400b1589420001010024041c0d00341ea4440e44500c41103c4409440790b48035811903190081807060958000c1c0100140181006070b940e200e9816000b500d400e042012815941c3c0102030014000581c403a03d03140e065846a5108080d400382d0102101c81c0c2659078149846210104442654240290b0541180082009400f44112545a82d400e13107412807181084903000c16481c00076030f00100811171314402c40b0004030458000c20713080341131342e503215800002c0000300d0302901d40305410b0040301710400070003401950a40e41103400340e062021110a03d841c0203001c4100742d41f040c1803050010042c3d10714095000020700540d036010303640c00c0d0319480c007031280559078014094010255803255820100440d22403041040d80d80d0181031141c14400210000c1e0b003642c21104000c00001c2111200051070716010503525942201501d001c1c00583c14155000e864150000859009400102500c0365001c181d41c1203c0d041303504ca10741084090900d1410010001c01880705400500c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 371731483 1250 371730233 371730241
    0x20031516080f01151e030c0906020c06120606220501030b0d02031b030c0a08100f0203160804022d010f0f231b030d0f0b010f0305060a0504060b09010305 67
    0x2881045008041d040342c014110b03071030301141d02046011068414100525aa10034240c090036041c1400c401801c0c1c0c4004c214840e1003403004100b0402507001c20110b40c0600c1c070328801070322000304945c42d1b0710740f40b800501c0b6581c9540100c0c000c1e200d190038140a41c2c03400100c10b0344107441e0003132190540e08240e9050103440940030030400360003404c00001e581500014000e034880c4c00c0c450000703101c0346000340548091892607000030366050000e9100f2051a0000500240404218410062183e02058003182141441d01e1310408a40310008614140f011203408101955260707080301d00c01019104e107900000d075a8111480030041100c822a0104d0700c3c030500e00002c0790103030b103c0c091150041e40e00e0019003081d2895001c008845440300300100c807002c009000212103032450110600365484010340d07455059400600880b1072007082071206a1411800843d541c0e44a003801c1900100c0c0c2c0b030041020344881c000198480d0030380e400580d1091800c8000a01a99001c000d00130500c402d8a00300419a1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 371732733 1250 371731483 371731487
    0x61d0f03150a11031b0313020603190e01050705090d0f0c0f090c0824130c0306081606020309010e01030b040504030306052b0f0f240606030b090420031516 68
    0x291071300d640500c00405d04244506040c0003941d40543e00c4c1c444285240059000f040c81d66000b592445c0c0011060003c81d045a502c60207070507104580040204403515081c80c00500a000300b010062207004400c462030207202d080a551541540c02000900c1d8060f900e0408410301c3c9a28415540030310704110020300b14900400f0280c2c460312004024444400d08140c01c556004282c50130740f5884a0408481c1001c0e15451140510405c40340d02c00040720b0b82090b11592600e07032680c00030655403580e400244541a1f01105580c0d0282080c01e0050010b4030082c01a006004002007454129140500300414564580c1120049070070a4039070109505c0301071400e0b1504882844940e440b10300d001503000000300090165090781c1d0154a00f8440d04d521650703486122000802d80d40d542142182c02d041c0400303801d119035401840b003810704000640244010650303c400003030001e4010006051800705e20b581c1c4508829680c48010b0070b441618120381981d98540e5000d4030349076040a14014403e5141e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 371733983 1250 371732733 371732737
    0x2205010f0c0b06120102120411010305060303070f03030c030207050a030e1c0503030103020607030e0a030c140105041415040914180a03021f0f05040b040209070207061d0f03150a11 79
    0xb6000b07580307240786a0300c840034000e0951101541207a00d650800c0014014110034111074099846010304a4418003840e0005003070b81e60180440d48260002c01c6460b00280e02034008200da02c1e0b05060101c0c404032500c43c290002d000ba20303009810750140c030084104040e4443c9008600c0207040340d1a03001400c01f01110a0000d07004a001000c41c1e1003080140050314061f000340010324072038981b06480d4001200441c00c4200954000c5480c0d07520100103101c141030480781038000c0c050a203055810540b400c14901052132070014070500440301150022240c4001c08101c030007074081602c084c01035000544214000e00000c40b03201015885803a4a0004a840404c203024a6501070b4002d02d500001010728103a60b060400c5002001a40c47c1101c50489941e0b00840d44543c0c052520800289098014803205c030400419403001c5405c112428044d1300d401c802e500d41e0b102d00001c03030109035680000220300c2110340c1ca070503d030349072040c07200d5140150580b600b014030841040400348503d507034008001c0224 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 371735233 1250 371733983 371734007
    0xc021005010518150d0b01030b0618010329100602060115020d052107050301150809061803121317040b030606030402032b020d020601030c0e0702032205010f 69
    0x10b940140b10158283c140346402ca50f600c03c500714898a80400103d8034101c0c1c1008850408171640104144015404616400740040c1c800080d44010700c0300241e202d900c140002440c600e0030310281b440b400e0601410b40769800b00426210340070b0030045003600d5024224816400140b103280d0012806500a40441103d4503250f001040c2d04040614140e03282e400104a185881c0c00e552180701100c46940c240901805454642c01e0384e0b54100845500089003011211083c4480042071120400c40005c034580d001d0540c901550513031880c100040d0640c8540c148a40e0065450011302500c4012182e4526035203115000c418100e0000c83d0f10515240a02d12a94004107014000528142010700080d40c2c02761004040d1214150712480d0860624001ca448066245118946580b211b8040089a0f9505541e0000f001d841d0701d50342e40c006584610f40940202e1800c0b00e00400c1c00203000304152402d0b42d205808a900165024100d0090000b16206003400100b010841380841d0740901c07108040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 371736483 1250 371735233 371735239
    0xa0506040c0203040b04090c050d06030308010911281b050f072403021b0f0607090f08120d02040f1d0c120604090201020c06130f241d060d0c0210050105 67
    0x1041e03d403100420041181c80412300c14800c04001c5c85094804e24810b90000d54407035100d0101a505100260317040700d0303440d4600c00303a00008000100c84034035a03402c14030003083c65281c90807071810144402c442203030f41105440500b200303135507500d000c124010460900100e1014111014503645220100e1440ea203485007880d000481c819419500d0302c42d800500e0b001c6c0e60300e50030b5180d0609082d00b80c0e24060f1a0726241220340c03c80b00034003a486500000304002401015405407206003421500c6840c0c0c0b8155004000c0300b04c00103421803c08000350191f4000b41407860500070704a0b81da1100304510b039000300505034080c4c1e0f2003000501078141e00040d00d80045801c01070180c90381c0d0741e00074030008052050090f4194818410204c180350345100081009125500c210787c0e00d14500b00084411008039000210b00c8902c512858183e4002e40764034201c00c508900c3d00002c000c0703001e158610f01a4030141c445412020024240d030144a054100030b106d2410395080700d004020b01f00c0e113442100c40a01030294 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 371737733 1250 371736483 371736487
    0x6010f08041e17180f01122304150b03150402060c0a1203020405030705090103030c0b040c0f06210903020705100207050a03050c1003020f09060c0c090a0506040c0203040b 75
    0x4a9405560392000c00344110301da110508082c0c0f142c9400107000112144002400103070b0036044009078088505500041d94204040045140081e100c14103a810409801e590348125207402c0c01090034014440f60308641e80001030a050621824203016000c09141036810b080f1040d0643c01c2c0042c500c86580c410201001045c0c17160f07420030085600c031a080030200d215a01041002c19032501c0010101c0341240c84c01a5606c4c43d05003414240499503001034421782400004101094000b000340c64450b40c0419004050740c0c0d00d141840041c01a40c00410342621760384d90210756190005030100e40e0040700440c88400f4a918440401940d00e08a8020016001024100300303d003040d1404002c15125401911240da450710301207110104240c5c03003a280c40c0d209030130b51040c2d030074690314040b00c0082c7c2e464194a0442c020919003540d2007203d400034001c20002510b028a268140503820841c500141720140c42d040900c0000e024046c280d9205200310710b00881c030b200242c000802c64040b42d505044480c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 371738983 1250 371737733 371737741
    0xa02070e100e0c0a0509040501080c030d02160603050606040b07050c120a020d06052a1b030c0c01141c0506040c2a03030b06070b070212091c05070b0f0403060506010f08 74
    0x413a0403050801c1c0c01c1c07000c1402455560b40d9a0b002e15030181c5079100040010b815190101460f20010261000075134000c40c2a580310031054a40724400e803202420003003555154500490854441d07a4070271803101a010507240d08100c00402d504500d64000c85450341c505115180a948410070904029030048054a0000018103140c001c140c2c081c0b01c00a0340503036400b0700003044014401c00c5a40c0c180c807500000300e500040c000304208107281e6180310010f40c200b0401143e160358030159942d50034140300403211000c140302000c0b000c0b501b1541001c3e00145621280e0400130010307102c10b0b900a8811414415540400b40c0728000c801c03100420310004500c800342810780042d0031000c0d00c2081d0b0070140c8580692800b0b4442c1b40c020070340c0d144200c0da01c80c0741d0f2420800090621206106030044c8d41c004006d0038481e59180d04050780401109960103581c0e00c150b286c5145020b4440d4040c403210000400c07140a03504020740a082200e001e00c400b84000e64130140111031440300e4040d04070201300f01034003117 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 371740233 1250 371738983 371739001
    0xf0f080403080406060b04170f010204120f061b050315010f052a07060507060b0a0b07060f1e0f060e0f04081804050a050a0e06270307080a02070e100e 66
    0x1090f04030380a06400a0055110104807500741c1c0a9005040e25048890608107600d8041050500c00c030551402141080d09041d100c1800b90b9209a000d031008031801e0000081c0b024540c8144d0030070030404160303180000d0070000501190002c942607007a6408080c41c07001594045c09021140d111640c1d02c181c5443c08080613604880011000b4001e000101e403502000100c04210320350141005480769078858400b840e001080d1140b406015000d0151083d08002c0d8001007000e8030790309680190081164029002c121008280f181c80c20f0b25403140d8800d12001800c250f6010011024503c01c06001890300ea01e40e0912004c41610010022034000c1d0000b00466446800380c403002e4032070364040c09015040d20001c0e0a80344256000120507a640e0140940390400b0302c204040420b10074060040c0d850442058026240c8001c1110712918407a40400d0052505004484c5190303031000c8440d8558541c000020358400035030080c0d0f40400c2140c400300e030188800c03641a10865082c001b018502d41ea80c1826 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 371741483 1250 371740233 371740247
    0xe0321070f0503070c05090109021305060307020f0105070e03010f05010e0402010e06070609030504050f040917090415030524040c0302041a060c0f011a01080f0601090b03070f0f0f080403 82
    0xe4540100000c4010000741c0c040c8001d1403d40d005d003090080e480d0a00c800c001d43c0703020681c02004d4081c0b041205c0340071610883c106104607081120000e4582e80c030b507101a42410713045002c90040d54a01001c0144550304070800f4600b045040c1d000f0045107500405800440e0420b0041d041c0707804458002500542c445c24181b1903800c0007800d46414612240d440300c0507110245021404618045010b0209007040300814000031030854040c0100c214070b031a04800d03a008085422000100012482850384503a003220405002660550034010b0785c905104d91210b2002141112600048000000000c82640b4050040d50880101005140b40d0341c2040014007202031800d40c07849031000e90300c0c3c1036500c11000c2d00545040ca8041c0200c482d11540d59403c4034440413480100e2403000903c031002e40d0340443c82c9030740b00c0c12021307540103070b910f480380141c4030b03404280d020007601d85000081205265221001e00900e080c80d80f1110000c6040301d0003504c600c0d43c2207002d880025205e00c00607000ca481000723 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 371742733 1250 371741483 371741497
    0x105070f021c1401062903180f0a06020c010c03060602060c070501061203020c040608030f09040e0a1209030b06031f050604061e030203070e01080606010f1107090605010e0321 77
    0x407008a06001c0e030f0728000d6000c120303002800e059568280801c80f4180200c0c2c054a2041105c120700303000001d005040c4c12501002e40443c2c0c07003d15118520382011030070083c0d02c503c0c80a68003200d48a002c6483c00c070010394882c0800b00e52035420250384d1000e2a00a000700420b2b01c0b101e801904460380c42101e61701c165000749030151203545d219130700012010300119802d030189009501510340c180c051800e2009451301948118801e038010000e014030550150190f4020324000c98010901d441c2c1c03901c9440c40c0031a0058054000204140d0354881960007200c0d0000f124412041d240081d0703102c20401d6190700d440480c440c10513080414104241550750301c02a80190b00600001e8860384030f041035118030041c1c098044001ca0350b50300c01e00940c901001034a0041208010320301c82d560401c251907880d440013420640c1403140c5070303402c80359050042009916410400048600c1c00ba520b081940151019100e0745010600c1e2040c111070500f00850354401c181c01010154107001000020720342c00d039000704 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 371743983 1250 371742733 371742769
    0x10507050a0b10061d0f06070c0801060e0417030c030f1312030204060306051f030c050409091109010503030a0c1202031b0706080606070c0303030c1101020a0c110105070f02 76
    0x800c030740e8002a00900d0b4180201c0d46840359140d0340303040c50009400542503800c036000d880700d007030301c11512680c8080d116880d0b00002d40c0c0f510f03180c1505161040c1e51569541080300b0039402c0c0a00440d194207050105440342c0d004291042c501025010303449c44600c01a501524034030820000540d820107440c1e445074114101c00c281c04144512500d5103039001003d1a50500060f0b00090100025036050080c8400b80004039022140071034232640c0d00c56016408881c0605240d102d882c0903d0060040041c0c034010b1180c804244240c08251030282000c050794a0080d02c1008882c00100d00b5050001c2a142c1186254560b0038402c451138440c0d4020203407180000045200410503015400c03400b101e00440340c00d4040007428842c0c100300f005040c02d1001441d06010388014080040418003001c0410226601070600040320310001c9000c803076404510483c04465800004c8565647d030340402c0000a0718090941c2e03c03121204503004480b02e101e075140141c04111a01c0101015240188044444070048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 371745233 1250 371743983 371743993
    0x30910050c0c030a0f0e032404031b031101050a090305122701090b070f020d05030903070c06120b12072105010510060e0126041106030c090a09020a0e01050705 70
    0x2901e910703490f6900c802c0c02c03400020903034000d90740c4058010348600000310046011740030000600940318224003085c1c55112030000716001103028035001310741c02c40c41100c000320860085801420f0240091821a114a00795032074400002d002c0101d6104c2e00304256455070f501032074010401005110614050211400844044460002140080d9034403403a020984004600c446490401c0c0300e10540051524050061f03c440f4004126030100c2c80c00028600c41c200035071240c4641d400310340385015043c0020511800c4007400305040d50002c0c1c0c442030403500404140300405021040c040000a21040208140d00210061112202c0e0f42801c096440c00010021099016038a0b01425280d06848030b03c40e800011070140485079001512140c0e074102030071700c8900c10114034081e200c04100076481c000d5041c10240498100512503a90100700e00c002400c407901c07824100e200c5111a4400c42d00180319107814200001c14002c45e001b61207c43d0001c4d111080400d40d100d00548036075000c05400c841c00e000e6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 371746483 1250 371745233 371745247
    0x5010804060213050a260c010e090406091203020c060a09021309060207020a0f060807020115031e0c06020c0a06030908090f0d1e06050711120a050f1b12030910050c 72
    0x2c4c16941700010b1002d9520444c16052940009207000045030b460703105038200102081e40b070390b0041c0c805031000609449084c0c160f500c41c20034000034445400010103800d180c800741c800750f5034150042e04241c44000d060b81c100381c4554180d10207c0700c85901c02034005240364542980c204441d486070142c01d00981c40949040013540c00511600307041d4000b0702494060440502c00da03a03000309015400120f0380002c102800004962100b00c1c0c40500c4018007405d114012107045a44145c0045c4915134008052908561904000f940720080031016030301030440001c00043e818401d010f00e440550704504c00780d180081890074031130140c2e9010215038011075035010171400100200d072991200d0b050000f805030341058600e840400c0c0c500c064581c0041015070304a4558042c0b000c5903c0c1c8101007082402036860070360040946203401100c1042e0f0484001003030707510302021065030281c40300081c0e4003500c0441410503030310b94031030000b600c6000d41c55000100308403c0d200250301140d0401102c2a400b410022 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 371747733 1250 371746483 371746489
    0x1106070305190608030d0b06070305030a18080a030b191d0a06050d0b04050106050f061602011107121a04080301180605040504050c012c040f23041a010501080406021305 74
    0x2980c0f1613081a44005918a10180c41d4401d0b142c56500c103d404a10b0141d49440003480c80c04060300315002e040d510786e0840501440190300052542c0d010900585035089500058020440129014083c0d03000c00c84c0101d0220a842c008010390ba1800030080c0d0003450414002d20003000280b0f00c1c04450b540b03490119841da140042d05400e00c0c40f81c1c000641c01e2510380340007800d4403410352000b4001d021000340ca42c119071b903910664502141c070020b11b030083c010500040390b41407000e500210080c055a000410603612030342410793700314090f07044107841c40c543d04000052010100e4014058040601c01406241d072106580d1040c1c03c040e181c0881d10540710700001d4110703003040e50304035910340c807e50782c050907541c105c0ba00c4d000a02da008bd0515461a541e04140085003220300307071501c16940c4000384400303600c080e4003140700100d00381441c032203500300c81d09403000c4800b050701c064501a440364000c803004044a20a00d050b40c00680d03584526480b150340d0031000e500800e009101e5103451440108440d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 371748983 1250 371747733 371747741
    0x1b0203070b040807060905030604030e10121802150f0901140d0204090605090603010c020d0e1f020105310206090d062406020c0603061c08070609020f01110607030519 73
    0x40f10320000381c0040d40c90028098041c2403150b20141c020380004c4100804282c11800b0a600c181065580404100502c0001c60701c00350304652450140b413034054334254401c0401c0c280100d0724400c1c2d61032194444801e2080314180903103141d610340258200101740c00780d4884c0071034920200c4041d64141c105541481603200340e80180d0090071a10744e941e85e04004502e40384880c0c40d003001c2c00380c00801801411031002915000900011410b10020501c0c0c41c00783c7d15050702c400d8000d41200310040003e624100000c2c0600b005440da051501e0849003e402030401c10f01c915466018205550180c4900c0c550902c4284c3d006038108523071040c61180e5081c0400c0240c02040a00c0f100d01c2020700519003852035507149c03c0707035513040002154040d4020300da0544581c800c50b500013604072420242204641000070420f440c050000b07060580103e8200208111f0350041000d851080320000401c119010044905204a10340d42e801d940c0b02602148500c1d010b54019504000e940c0c01c04404440d00e40340181c255 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 371750233 1250 371748983 371748989
    0x2301090e0c0d05010b0a080103030e01090801060b030f01060908070302010c0204020705340315090809061c050a0b0102100c0201060503070f170c060304030f02030405091509010608071b0203070b04 86
    0x641d4005800d81e090426842114058818504541d0400d03489110041524070140801400c0c000d401c45610943d83c09120014000c202d0b52009000482c3c6481010304641c1095440c07050000c1190008950603014050a0054440315401488107a2640d001111074100d103c02c1683c1040d420013032240410700034803603011039101c0720480b0740c1c2c2d4881c1144518010165892032000300300300a0030034030005a040984801e120030080300850001841c0c02c008806109400701554040c0700042d59030211030540c261803911254036a81048a1b64904a5080c01c1d10000180c503401600301c0185180410210f501282c040350b1035200005400342c403500030914242082d00714400f115402c0380c082007648103004004a07200810800b0b820600c0a400200b40640009407004040c41002000514203510030001c0d07400401000b408994207042c0441d048049840c2800040c1c041c040d00b000200d40f03036001e07403001402010641d60b09290494045191040c9407007624089034140120000005c414103c2005040a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 371751483 1250 371750233 371750251
    0x12606010c0804240e030c090405030c010603150c030b0a1e05060301091413020109121403041202030c0f0604180605090c0306130b0603010506070510052406042301090e 74
    0x10352001c14011307001001001082801c05c040368280c0c4c10551004900c0320081c08050701c00c802c194070343d841c205056008220800ca010343c8dc14a001090048903a512080d082c2c603000200900c24406000718160340302403d0f0b184e082001524100300d000c0401d0095000490400207111800d921040010300c0c6a00a0b442416010340301c0000c5809102d516002c1900314402418001d02c4010b03503400600303d0611482180301e0503d841200c8400e2041d624120100d241c2040d05036603569498520f030340a0100600e900340c0c000e1284a0804040d41003116401d41000001007409007000d113007600500180c06050a0041141c1e02c40c0000145610350a81c1e950254620340309a5071645004400d000042c1d20148040b08600c1c03e10b22400c44d02e845402c1280d040d644103031109982ca07006810200d150400c25481a040340d403405d001c0001d504044408c01070300c0d0303c007144c2800d424102c1c80c0400480d4041c5005a49000c00c0745098a0100001c00190022000040c1400842d050780c400042b011f544003101d0f150b107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 371752733 1250 371751483 371751509
    0x222050406060318060b130905010501030314071131020301090e03120402090a0b10120e030406050409020703020c030d0c02040f020f090f030115080a11012606010c0804 74
    0x4186801d02448000e004145030030802081209035020003401440c070060003103640e4811800c2c5070303144d031034922280120201c003e1100d80c03541d1030001c1c007e103003d12050b0005801848002d0002e410070342150000b0350010b00701182d2035040410001c4c59003d03c0c4409548404100c05014044004030360071602c14584200180c40c1d625241e07c41c0290303a65140791940305c2c0c01c20032214040d030304103008440e04079030140d624500750381e81c2c48408801003d81803d45544441000f02412005034441d142c104c00b034007485002c0c0910040c44c0030442d07482c043c9018101c0414400d000a001860b500d5000e030984a00a104a03206079006e1404a4103240768000881e0019000058910641c00c15015400d284c0b5040340e821480d00c0c502480c40070040c081d00c1d44c424821094a00506102d65017504440d1581c04440141d10306035648404481c5c0d907100941c0c040368540840f14030030482d580208111904d84a40110214207889028405030102d640244014144410b5404801c040354184015101905424407024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 371753983 1250 371752733 371752739
    0x80318160b03100909050a0308040204060302120a0303111306121d100c050306010801030b09010608060c0904050901060b03060d08040b1602030c090714090a0509040302061008030a1e030222 83
    0xf07484405103401c11030b070352400d080c038080000b04006204070300136805280c1030609407201e10004002d008651f20295104003040c014070040c030400310300850040d22030340303003002515485a1107030254040e0210080b011945000100001800761070003040c181203448000030030100545480700300d00d142c0040150194070031105c080c1c000c030f040d00c40d0740c100d0040c6041580c214540480024003484050000410305070a8002181030b01c5003d41207038000d0440d107070503070390246800144002c1ca500304030703012441355080c03070003080860303c041c0704080175500f0300d403141842c6668400600a0180000380200d030701da00d04110000720103070944054179040d4154001c5c0e454180c2e07240101407a0948110440d031044100b0424807012980151180c0c0250b0300e0307412220f403180368070b00000f02404020390041c4e0300030408408000803d40e011070420300c24416030b080c85404030303150b10780b281d500d00030012031a000c40d44c038400b80d00e0f258904540c6400490040c2c038015181078002c1403440078034400074400e46600000410b040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 371755233 1250 371753983 371754001
    0xf0f0501060f0302190f180608060f09010302060706020906041a040f140f0f120604060e070602060f04082a010c0306050121050709050a03080304120804080318160b03 73
    0x2c0240400c0c40c50250308000a040c2601e034018100c844040c18040f40c144001589400351142d034981c03904008100346440e41d1040040c0040008032030340b510521681100307a00b54036000d80840c1c180c9401809e0305042c9115a500e031002903215014059000806010000b551191742c100041c1d440c3c45401c240746c5442c50840600780003050340c1c00140004258001400c601e40316803040c2070030124111131040030345003105d01046140c066464440014006d4104100601c030f241e4202124540b40c40e421186086da43d0102241c035004141d0701b15030080d80c140b0100c1c0210f02030380060900c100306c80360032401c110711910340e14030b81d0300c081c07412204265110380c140c0242d41d801d8440c06000381002c0c24000c50000004c41800d0050b03212400791140c00e0f9540c808503000e544990441c50140001a140c014410741740c0c284009540c000311001c48008010003502d20fa807912554501e401154409009425600c40850381f101800c9202901d112903c01c8503101c0c03511480d0110700900604031091401e0b60380c00c0c0b02c007030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 371756483 1250 371755233 371755247
    0xc090310060815040201231c020714060402030d03020702040f06230a150c140a150f02040b030117121303030216080a0b070507150e010b01110c130f0f050106 69
    0x1c90050007580310400000d40d0708020f8000203404894501000350100604031f48581c0a6403074017441c810305420080000040a43c02001894002c11480828800c0982140da564000302c4000b9055040080d0f024002402900030b4a4102c0c0300420200c0c00100300c2e0150b1080300d000303070300426100019012001c1c1805102d1031026044405070750311140c03981492003c0e004207000300c81a00401075034088480c2400b0507008882c0405404006851200ea10f9040000000b1548003034584042c0c41d241460300a02d60506c212012180810742107030560303103000c5404506c00c1404010380328602824020220a0341140c004161402040040c4c0b0401411800e00a03d00780c03100d0f070441c880c50310b450800c0c4880c01002804d054803582c08461103016030343e03c241c120f40d18010b50000510845d201c0b0000400c00c801604010811440400200000c1403104011980b8081c05041c05049801c00e00c0031880d203083c114450040d4400003200440c441c1003400480f011214100c40003486580c0e92801071250642c0503c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 371757733 1250 371756483 371756503
    0xf0524030c180906010806011b050a030c020108070809060a090303090f08040906091a060702010212030c0304060507020d0f0305090a02090a02070605060d1208060a15030f0509030a021002030c0903100608 89
    0xa5403c02442e02a00103032203c600a0702050510554070300000c0d0b5400d003400d00841240c2c0c40380943d8211800780c50054080051600200d02041a040014094038031400f405803141510200800054440d044000000d00e034445007581099103650403040070864082d0031190791885803004541d2586090f03040c40869500340c001c0d00d492800c080800340341041800054800050454120ba41d9807480c0c40141e14044440035444444030010040062003104c00002e14455030281c4410f00a6503140c68040343c81e03015000d4460007150100c1003514045100b64800c43e440400481141e181007400d030000b45011404503040340706241c00003140e40c100103490180c40d0f0003550551301c2442110b101c0c1e45190541113000380207004c120640001819581e90054034900800d64542c51107400e0114150040c00341400507a601803060401d4003244d0050400411621100e415038058040314440149040182d400644401c54600003809107140684e01031005030b407603ca100c1d4000810b01d00d8100c2c3c0c0c078100b4440d45 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 371758983 1250 371757733 371757739
    0x1e080a0e0a080f0c011805010b0a060309030507170c030408010b130b01050304080a0c0209040501090209011a040e1906171923120301091508070f0524030c18 69
    0x410a0300000e0196416112000d5507050700c25103130b1345202c1071240100244400404c80c0c41c520850481030020652041030700c5c1200f9102008100d07203a120036001c1e10401c141c0100024010082140455500c41000c407418005403146403804080800071441d6170403170b8201340080d0350348202074801031602070941d60400c8141501488696406c00018216000c020000b40200b50001050003100b44500040156039600030f1152803a800c2c00c3c14098000c00b200c00049000300041c0c0000b080b84148034401c0382080c140c04902900c9d040c14003034628803840001e00071050745038419517107100da0825400f62402810350481d030400c81e403403070403540d51070151701c01e0358503202c04652000d00d80840c0740640e0300d00e1a44d4500e0719034034102c03c40ca04070500c0c2031840e40840d001650040300108869805410503081210210044000a80c0318900303180c45a82c6071040300801d60440404204a041c001088034149174180b180894440740042559245d038011601350000d0000010400380b00703176007028016042c2d0320517 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 371760233 1250 371758983 371758993
    0x606062d020303070f05090d03210e030a030c02010603170c06010b030403050405040902010216140f010e0a05040b010c1218090b09071803020d060603050f0307050d0f1e080a0e 77
    0x2032003000e03480e480040e048108100c8a007049040541c068011100c02490103458480d031501d881c01c004019113403012025180350f44140c0c110710309040c24040d2000f070700307140e40155151807103514041d0028a4040a0207085d5500c1c0c0308000003280c6090309d442011a00384801c6582c8100801c001030400805811040034428117005000100b80d00a013501c0a170f54081d83c00203006074080c00180c1ca17000500806070a049d085070380105940d2400003100041e140700b070b43d0600c0c0c812a00c400545440c100702c130304c0395007002c0080020400c0346000d4000081d00c850604010404180a4540c2198441d0b4546444040741035440b04035194420b100300032004003241c00c2c04000680184000400e0602c0141c03100d01041002c10300500441e010200c600021540149003101e411081d00c0c2035030140c84244000c0d600350040e001080c07240c07034000c41140ca00e40e0f0f001c4d010341000b00b182501501c005600380611410041c2d000032070079804156100c86020406035484402d11407501c818514140c5540304001d03a12a041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 371761483 1250 371760233 371760317
    0x3040c080609060f100b0a0f0906021b04181202030405010f080f04060b010905040212040213090f030c210314060102030415030e0109080a090e0604060b041202030109060606 76
    0x4003040c8950007410380d070031343c119603198042c166013148070f141c1240100321400600c0052450304100e5043c0d100a00d51914500c81d507030398105a0302c1c0d001c0511312100b10050f0040d070603140d181650040e100c140c68849a130000075020349820300303624a08402e03003015a02c009828001980c202c8210035552129161200307251400083c80310116001620040099488444030240b50717001300e201201406002c0e004544401081d048021541c505490903030003502507002c410f110305001e0040c0c101d041d401803002c230424442954101c4000600c1e140903a00b9020103400740c3c2448a50f52088082d480b826540400c0540c6542000e90016102621031419580300708001c11842000c020315890f40080e40c20300292143d180018a4003400415a00910407000010030300d03e441d0300070614005a03130313040c482c40c50203903a03a40902c01100d11502414004030010b11040250720114004040315520107800030841240d02d99548099403036035004080400c5142c103481100c500758054030200d9043c101a88255000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 371762589 1106 371761483 371761501
    0xd021b0f150c03040309060c0503090616020301051303091403070801051807080d0903020f180702070510030614060c0a05030a021c0302130621050a0203040c0806 71
    0x224807804604402808800d40740b0440d41515a070305200d041c880c0582e080888a20105c80c00d01c03040144018603124040680f10130030002c60490701404a900c10103096540c014040e61501c1215007070f1402013036110020201b2100c0ca00480604003506d03901107814001c054009040d190b00300000c0c0801c220008440c00d01c2009160103907088a51100811500c1d40481c4108a001500ca54024000b42c60b1500040c0e80e244001031200341c822103500b00044101108441000140e00041420800360404481c1d10030109881c0c03800700100d07820a29114150404454140e01441010070307400840d507003c0010641c1690001c0440e40c5424542c0c1000b5650f0303404000e407400d44003418611090171030180c004d4686040d00c100801c0e01c90390520400329140e00c0f141520b10b201c589850600140f8021601c180c600a000302d25015030b480c45e05007451085045d841e0310258040d4045010007511074 = true := by decide +kernel

theorem cover : BRFrame.Cov 371582733 371762589 := by
  have h0 := BRFrame.cov_init 371582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 371582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 371582733 ≤ n) (h2 : n < 371762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
