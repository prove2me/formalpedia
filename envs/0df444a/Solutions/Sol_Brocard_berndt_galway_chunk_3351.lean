-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3351
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:24:54.874456+00:00
-- url     : https://prove2.me/submissions/e3de8599-4dcc-4931-9c69-5bb1d94cbf75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 602517985 ≤ n < 602697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 602519235 1250 602517985 602517991
    0x348021302070503070309120c09020f090909060103170301272702090109140c090d0219060e010c051e03041d0a0501051f031802100e1009080307030c06090803 70
    0x89a2001645c4402d00d5086080c0500501c454080b104005002d55140c20f0740b8010762282c5080c00b6004698401415403e0082e2000120094250601d501d000c4074115540c0c8802c1c803051300c540b12600201c100307016001c03040b070b03058070845110a02310800100828000c0d0031003072a030b1031f94903030783d280c1c44007450107000c031448500c0b01003110300f80c1c1500f500c4c0108640044113900c0301042e18a40b5000443c0001e00d41c81850b0320050800c2d0058440400501040c80301030151402580056010140d08008044181071000c2d1180e55580000402c904401074520198002d000740c19640001d9594600030440700300381980070000001e481c20f0079036034040075180b080c44100d0910012041c02c01c00a040322148942c40c0100000c45000740914500e01050603242c0035880700c4c00070545c884115100114103c10440125940a8a014550303092007900a09052a4004c090310812422502c604040d1150401900740c90003003029619241440c0ea050f00d00200d000b0301101c4003a10f0380c1403480403469072070103144 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 602520485 1250 602519235 602519243
    0xf0603020c0d03200304080d0e030d1a010905041e0e01020d1107210203070f08210601091707170106050910080d030207060b030703034802130207 64
    0x40c450729580041c600744040c02e100c2c041058a084844a425504c0840c0d16520400c5400d056070f4075217650a2600841c03190b04546003070641007514080c0c00c00c02c000020404010498401c00c0901200d0309414a070f0a0003000301800103070024400d01031442c2c030340d00008680c1241040403147c840300d0100442914002620080e8903507000c5000c0c0ca44000d68000d03050154003184c1001d14096041d038030f00035580070703150010070001081c6008031043c90081040f260b48642021301d4481040c030038500401a0390143c40041a00c91110310075071130b1444440100e50203001e0507112aaa0b0f1410700061314054802d0b40d0302500b0328440e2080009c2c00c10b040c0c0c4c0400040782103840c004034006041005000d034891016114a80e007044505007001103190200b1105000c8446140140e40d4080a08102c005451404c0510798503018803100041095007040c1140c94050100d00c1101845034400c0180e89610b5a90b20f064030200c1034000b80503010b02da22400d49036020710040a03000c8440c44884402c080ba00b00c800222 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 602521735 1250 602520485 602520487
    0xc030711131a041401080a030c1505150a3309121a06060c03090409060603021305010501020705011809090201110a0b0106031b0f2f07050f0303041208070602040f060302 74
    0xb140340c2401e0007003400703050346203540340ba1079490701500903650141090050704100c00c903927410080040c0c2c4008000c0f00a001c14003802941400007400550188406c82d540c80f40040200010b50f4005c0100c0441224802124070f003142d01e0f81d0a0f000044020740c840d1031040114000010540788169946800000c3c05a007905a10800d0800300c0500a6030280980d44511018003c203691008000f04480d2011015a4080f800c2c074007520709140a0900c5400095110f030158450540310540390780014105c1d40c0c01d030b00b210601c035500c000640300f8042c0d295007034208000f000c5040c050340c00e861b0000c0203854410702d045400191402d42c103e04084528104584201220380104101035243c001d88a840d8149005d00c21407210b006806007400803ca0701c008140301045581e17141c0b042842c012821646c00d8080c4021681410740d030305a03200d09841c0280362044044013400d60780ca045c00400d171810345050762144640c804042d214244ca03500100320407a26a80c080001040403040c50281700000d000c80d45001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 602522985 1250 602521735 602521781
    0x1412310605090c0a09020d0c0e150a02012009010807030c0516020d020405071206061e110a060e0709050f0114120a020a2303012007060207050303130c0b0c03071113 72
    0x200080e04c8c803c1c419042007114035401110300d9552418907103100d0b8070311003500755954402e00d811380c003402c50800b9102596107212072a0b2003008821004150710203090340c0305070b01030340d0715038055048a01c0511048009481800504000103d112034410703100d000502c206099640f07036000800f528000c40d0040e0014000d05107000b03c0b000c003405500040e00719424071460003804003000d80041c0300458005002c00c000645d03003000c1c00310305200b00841c0507008001030201440488800340c2e2840b02d4420021024034100c001007503416055200d40c16038804600700a100001074080220311854194603e905010707101071940182d07a0300702e4203401071041c100414200688000c2003110800d50110717860107039040103200034001c80700c00210700c140d21281d1355035500c03028a81880d10081c0030711703070f4014164072000007444454201422b002d60380b148179482500310580c6602403100c150140e1108070b1140e500500c0020009801170f8002416800c0c05071170f080c0c40c0880750440109548840d0080c00c1410605840b03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 602524235 1250 602522985 602523007
    0x60f0f01181107240605060304110d0516140105071a1024080a33030f0606050f01020f030d05060d060f0e1b0f0906011412310605090c0a0902 62
    0x413110384a2845842002020302e003102141c074510004000a02049860354003c101c0d6032820440001190020110741486030071543c403a026540b036000b04441240c11043e29030103507104200320740e691a80901d07410000d110b1100d0341250a003002d0720428240c194418003080500c0101900003580f0031040c0c0c1c040c3d614121030b4000c0e00e003003800f4041003001c1c1c2c144041100c00800d040c8400420000011000e0481405050021069000f9400061440307404a1044080c0300030b6401c02d5007544c00440788a88410046e00c01a07958142407200c0b00025081804030180742951030748a2688040041c000181d0350050b0307038a641c1124401c0400d1109242ea83e9507122840c1d20030007400c100000801c5042904100c1c2c80300103404c121800042520503074480e000182c183e4400c0025071030300340d814540c03a9110484040c51105544003107440ba06101c91164803803c1d01d00d284440c001e5a0319041031038156130703c0c00da294200988001000c8525070701c18a5030108003034841d9003070b000050540030780041e158212820 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 602525485 1250 602524235 602524283
    0x200c060307020d12020a051219020a02030c150f0103060218130c030510050a0311040902180414011b030203060a03081801080c030628050316050102060f0f01181107 72
    0x84c40c0c0031602d10500080b0740c0e0700e4024088458000040350f4041681c0c0c1d500e00f480c0104e104404c170440b042e60000c101100f5040d000805000d135120f0580668107840282050b0b5072003180704454801030a04180700400220392158000c01201c415006001c824841c003602248030040a185000c20142c0d5906208002992610601d5000311501c030100d0866480c1000064800c64103000141400712128080e10342ca40d42c0b0b0380035200e0254083c04429170501d442900346c024043c1201d0aa40f40b50501100301c181217410700c180c0c4c2c1c2021116200350711003c0c3c07080c001c90003900014003040c2c22001c9a407022010a03052005044482d401c00081c005c030030648030004140f11009895011404c4060040c407842d6a6180b2007001c0b204014800c0680244400b0000c0c04e80005d41d5109507014003031300707600a0b80441200007a07016503c003a000c4442d00d4480d07204412291030200e5001160041150060200d0400a00d640f90180f074400c0d008202040c1400c1044565808640e0440d2084143c1480c180e000070560 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 602526735 1250 602525485 602525507
    0x41e05070e010b0d0f05010b0a1202041a042d032d050303102117070c08060105040c020a0c1e090516030c02120306091008030d0c030605030d200c060307020d 69
    0x180040c4415450a05230401e039007c1c00312248240440004c0b0b8040f202070741d43c15180281601c40541c601c02d00c501d98040d903158000c0c0204c0c075030341c0210305d000c10061041c803541081903002c4070684400503181d40c548030050754502e961000c01260703100c176081100b003c10300309a40c8c460050005c1c603070300d080112030310511348400d91000c5504694801603007244d144154604d261140c20080810101030300c007101d12928410030b000202040f038014400300c0d0324a4002036007410b955095508212180b44003a0981e62a80c03d81002400d0514071081801200002c03600e035407407540d444a180400075107a40c44030003034807000c99985c804140c0301d80c0c0740c2e1b150316072501400384030004a00142441c02000304940c1e000e44030081103e4000e00d1041c1c046800c0c190107040741c80041041031b042e40c0d219402c81440c50007411036100c3c80d4000034104078004c1028900800c000822070b03015100c2c1d004c1d040700c9403025488d008211542001030302810184c0c0c0340307940320301004601c1400c2c198094281c0680302c0300c01518000c1c0340d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 602527985 1250 602526735 602526761
    0x4030f03031d07170d02071a09180906010e010b090f0111030a081009090b1f150509010e030f0a030c060b09101e06050a230a030b1305041e05070e010b0d 67
    0x17a8000c1ca8903d0340203e11442515114040710080040c40c08403004548120701d61a500f290000302240a41c003590752095001d03102d044140c03103082e42c4e500f0905946180c203009590201c44100414012031500d800c0312b01e5807000c10b04090941100f504080f0782507400001c49034000c18080c0d8108503d031440c1a0001c000340500100800c0802820b40301c081104100408110f0000f4010040d9a404180070600c48010130440a8265507050030603002006a00111403141c04102d01840e03180491502080c0b211700003030004010000c141907510125041210b440c0283e6505598640c03408240d2641d49407140f2034030002c646200e540345040480940320040f04a95801500200030901c10141d002088031860320f07481c60108401c040100180410382200c011050f1004000103605980c0d0f50160081c00c04c0d400c2c11500c401d4060605d80c0c45500b5900101c800510510501c9840ca0314059800c45030410307240502d049038411912000c940814100a80041d18403000201d401c0181c203040740908165002c903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 602529235 1250 602527985 602527993
    0x91309030c170408070b0a020f0c010f0e0105040510030b030d020606100c02011206150207272304150608011803031a190807150504030f03031d0717 65
    0xc0d14010310031020300c03034028100c00da20001149407801c1141510081d01c0e180064602d01a13031403400190341da2285216201601960031021011000814503d402a07410307100d10b98912903140d41211128a00c151407030501206010105440c0c80b4094129146d090a480c0002c031403020300b017014542441c0392401e10031503001c0e03010482c2c15241e500c10b801c184640c9040ca500070501c00d00c0140c91120032007a02c55005850948000750f6803c142031090031001a60f001e4410341c0fa21400141203000360702c0307107410f0700d411050495407802c2401c0d44501c075203040411601160341854205600701b010151010707604024003a12411000d00c46109090040050f00001c103c0049145807040c4064044480a000d050343d4459103031f00d24948445502c80c200340200007030405041c54800d080101a40d0040758444e2003035040101e5805148101c640d552002501d46605041c69a0b464004041c011f0703004404150b00d902444600d007519604c0300e00b088009402038000541031800079101003010b40c0d00c41d489540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 602530485 1250 602529235 602529251
    0x82101080703030c03030212090705101d0907090503060702010c1403010303021515270702070506030c0a0306030209180d0503061003050915040506100501080103020609010c23030913 80
    0xc0005041085a40c941011086480282410785c000e0280800701c0042c08645400c1282850b00881d10900340c0b4022503211040c50a4100111203520b51401007500d4032206a178942403601d00b4400d80c03503210415140c8042d40d141c489011074142a41541e5040c017503911109204041a00115000440c000d802e00c0b0900b1585540c5000755100303814403400c24000c0d40307100071031a0007a41c0c410842411801400040383d04820703400d40009081c81e80c100302041e50307010001c12041d51000c00e603c0300b11000281824110380b581c02c0f4181c0260b004250341001e1543d03940c000401600c540d544507101300f00c41d82d0341d00c40c658880481181083c2240c040f507410803508004001c81d650b100d600141000100c1e02d00041c817650342012052806903001050941041220300708001c000001510030f10511581041d14640c5645000660b4001400e000c020343c003031070034002c1650651241d488070070712074000d00555405107000b07003004075030344460124001c0e2a04000b03403441103400c125001204a02c02600b040007000e0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 602531735 1250 602530485 602530499
    0xf14160b0403090801050702150c0403030207170109120c050c0d0201051b010209030a080a1112032d010303020120130e0c0d18030f0c051002090616082101 68
    0x210401401000040c220000c5014944110004405059000000c02c243d00340510040c0d610030518816030810b020060010341003010b040300b5101120743c55001083c0107414642008010320382040030f49081d658800540c80407560b42c60940180f40001d80311103104d14501e0901c0c0d03080c88130079065a0300500c02100c0d0032006036405421502d9200d205018111400469290180603114081240c2e605d88100d01d064001d000054005100f08940e54882200c006c807144091900d4842100d401040b0032000d0001803915071070f180f0700c40e0903241000384180140c5800d65050084000c2070b00280d006039922203121500c011345040407003440d100307480b4181c104841d42d104103050f120721b030140f14041c020300350106030040c1c405000e4999010840708180106000d0001c80714483d2410142540007640c0543c2000300c0500a905244405030403502030280c040d69814000b000c0d42c0034190044e00305030308000c22201800b1000310b46034032500c11041640d44600c007124210486802d40081034a840c00b08004000407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 602532985 1250 602531735 602531767
    0x1091101050a030f0f0b09060904050322080105070c1b180906020f03040b0f0105040b030c0118180608100605060a0c0f080d0b120102390d0f14 63
    0x50082403030255568094414124050b109003500b040509040000c00b80369422503810503286800141c884038201c1c0d81d19400c000c031b000fa050300c0c003904980081001d203104144c542c4112548621041c42e4111241d0740303500442c03c49200308c80060025190301c40e44010003a07000644542c1301c00140007513481e036003031040c214007135581c10014500075607507140c80340204840c41c1c06861110744800c03055500c9151a00b4420700f403450840c1c051034806c000d07000100d0350740741c5442103031082072000c0e005102c4a00745000669030744d0502c0d1240758042e002d030800003420007604c0180b0b0030681340c1d503003001c01c1e45407502e0941c0303240040c2d4502c28448207041103800c0c00540c650800791164103505250008113800e0b241410094403040410181501d00c0001d4617484404044d0040d010116040c0c0f000411509589104c0c0d0803030003040c1c03030741504d800c80d51700086179000c5240704d4400781000b50810600040581400b540340513000d880810100b4816104004544d401580c020001c0082080c00f61a00400c0d81c448051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 602534235 1250 602532985 602533013
    0x203090a050f1201020313050c090c07140703140a0b0f0103020904080703181715073504030e010f0903030207031205190809100b030c0607080f04032001020109 70
    0x2524081c1e078030401940c500c40c03107003c0310306940000c42d43c0341010519001d10500281083e10b96105242c1080c46905045151f54415441c40d0300b00d5041c10125900c03000303440441c03002e03c4054806c0e2500407011a549811901404841000501c444c0d500d07883c0c022003aa034000c2c050b20701e0b5000180104090303201c0281007a40f240e8050107003070391580345103004c2e41d505080840e404201c4d07a400e5000b140f5040300502d142c808c01500021140c02c42d5041100343d0301c0c0b041c2202c4603000510580782c17214903900280b10f1541100a003107040e070b5442c03111001c80c6001c04004c0301d05800090800c0401d40a81d41c100d1089000008641740000a036810341e20007070340c0c891a601c0f0040c00350610340d5000070310501c14011ba65914480070308003200a1a9120010b00d1607105450108503801010b04070200120b0b0303481055070702071000c0c000c1c2008070070000c1002016000601c040c6d940300000c102348119510000010409548100c0a00f83c05590344074403400e04810b0300343d40398196031505200d8400301d2400402155 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 602535485 1250 602534235 602534239
    0xb0f0402130605030402060c01090f031205060d03030b121f05130506060105031302060a120e031606051506040902030702010b180a09150c03020414030d05070b1e0a020c0606010203090a05 82
    0xa030329105ca00c08150301e4410440d2141c215441c12109a0810451032206c14105001e40c3c0c1340e55030480035072410000c0314030a40b40030340c0c022499840540000e00030b401c1640e403c04000c040c02400034560a20900b07251010489011624426013a40000d040070b00c200d540100d030900440e0700346102550347c00e40d292005007c20f4140803011000410320300300701c41c40c2502941e01a00d8107403551114400030740880c684204000e0b10034205810500c0940f4004180c2c0c3c440d40d04d401c89006000d4140e11400000c0001500541c0d286918001d80074454035003900a00080c988032400594a18100c0d030004d0854040b000904d02c16106200d25000c051b090315009a0041d1598000084640a41c68a40c4c1545001c1400500c0b25042c80d00000d003450701503020704209ea078045021140c0c500100d00f01a00d442040f2500004550180714160100d40d07159807203030780140e00341c5204201240380501000c0d42d0f00101c03001d190441d0006685a011101480081e421480030700045040c9620a00004c0596440f80a800c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 602536735 1250 602535485 602535487
    0xb04230112020f19050304020a080c100c05070b041211220b010c02030d05040801061e1503060503011103010620061602011e0902010206010e1e07020a150b0f0402130605 74
    0x58940710f01c003252040109040b8001c944203594101400d075800031501a8412a40c126002070a1600425135003441000185045259a40440103640c819a0250251104d202d07808011555014030301c01403001c0c10365900d9040403903810745808080f410019142038043c5c0c443c80d889540407071005034400501000784402181c04142440105c0d43d101013510041e50512804c07009124080d040b000400548940310003c1c401103443c0c83d00d2032030380d40b20b076035001d40c8904110704204040f007100408000c040e002c500d408511035580304002802d640c41e00d00042003ca03c008010030090340c0198101e40c14500c00340013010040342c600c54071511118010629105540020381522185100f9802030f01e0156842074000750755035464103010000d181c0040100d0240c07283c0784c000b09034200707200e0b8006c0c0f040711103030180c003d5401642d80e90181c0d8000234103008203510600e80c0310800515203d40c2555080e0002600254000210040025034150f00d400940194030400c80e40a010026180410958025003005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 602537985 1250 602536735 602536747
    0x150c09050d0203011418010b03120f2203031d030609070e070311030a020306030601120510111b100c1103030c2a01050601020616021506190b0423011202 67
    0x70a0142c40c408202042c0a0400b8003000520308807086c107003101410540081040c600d4103024140c0d5100d00003a210030101040c4a03c0400d020100c005044800c040040c2030f1285007a400721030f01500140e00300714003040c80010b042109042c1103290040c4c80d9002c80003051582010023282da100c5003240111a80d0740c0680c000a0101e5003e42c014005103401c03001e0460b6685031080090000750429280c003407282c001c3c8400000c03c0003080c0c200004454100b0090f260702200500614005c04102401d02105c80041c0f0004424240389150864403551050140c04550580c00d070920441e002d00c0c0301c00085c070052001c0d0855400c40081a2a4440140c0742d16950704c401809840044c03c107002030544403d1190f42c02904040030640045010781c2081e02100c205445070480e283e480010b401092005030b0010140c5050200c03d0b4206036080354016152801092942c440152a2890781c7c0100d00d02941c0000d04100001c1c1d01044a60320995074038840721481d8155000030800e1101c4040035611039004500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 602539235 1250 602537985 602537989
    0x30509030c070f05090a0504020117151c0209010602070807091a031c020c090105100806040f0221010801061410090b1303060e060903040b0a2604150c09050d02 70
    0x121400468010122078510f41e8412020030f0a042c140200c5000b084403c0204c0c000c50128002c2a01071035058482c103101000d95901d0000418004250031401c1015035801c050310f45456240e20030000452140481e030f107809006100c1086c8040e8480c0e811984800010018141e001c02d102c2e0552f0b0340642c0101d0038141b1603605030701032848000c900b0b6260050070140c1e45104203200d80e5801c0d84500745c017038402da043c1741c40030026000320920421b5003020803100440515441000b429a02c00001840011500361425030f000490f0000026016048a07060610302d842a02c1c00040c5d004200c19002405101d05103005404041d4440d060503010340c150900c01800b01e80140c0f8580003800000441341c1e20303401d400d090401404218801912030615007801180c40003408650711703200702002e100441c60240340c202c2c2c2d4041d82e8828250441009850510460781c00880d01304a1902c5503800340340c41d01c904150400408070708101d0071070404a807402d81c0303090341d20341c0002c1c0c5030040f9041250000c00070f03a05800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 602540485 1250 602539235 602539237
    0x40207061e05100b1e03040828140f0a0e031905010525020c01050a0c350403030c030c0303020c030d0e070501020f060a0504050f1219030606050a03050903 68
    0x41001daa5a005007100440e4a0954091885224000000442e155a40012180d02e11039010741000c84e4050700ba101c8441d801100081d5006403086540b80d241c2140d9210284a00c600d401095a00c8014820b05074401907100a50f11070510700d140c0b0f80c0d403600004090f030b0283c0f03104040c00741c010310014680309906c0780d8080c841440d04411034040d0344801c250500c0c02038002c03c070071100103c5600c850000524040300200303440c460551190024245e80701500d0041d40c16410000c1c000041100364402180040c07014440c0480c10350707000200d03c018041960f1000d01d1400c21007000b4240300401d2000308086a409260950070300d402d42044508841c446c241140071784111000207a0a1000044039060880c4a82c001316601405030203071030b41243c0340c07001261268140d401d20aa0ba80c020400301d03001c5071146d0b1055410510400459031580c580e5010903080c10000540141078100205078480d900c83e4a40001004021030f10701000f5039810820b0240242c050b590400040590300d60003d00c02402c200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 602541735 1250 602540485 602540501
    0x100509042c0607020d0801051003151e03060c170c030a0f020301080d200309060306030102040306090c140603042a1a0a1106310606090f0e0a080904020706 68
    0x2001c0740c0e64125001449650b500c402d6a031800181306200f0140c10701c07031141d41030b41d069820040114401d2030480034100c2c094008881120302115000500068201c80c110f003003a0381c81100d5015042241c035504208040780d03540920300081c0412500b01074914000000e03840d60061042c1d1810351641c481d0b0070010001c00e142c0704801310080c0300100104122a000595690700742890707030ba41104603600f48810784000d90300c2c609521541c3c01405206090324040000d564003007400340c001411b0076903a855546c10780b4400c500c140d030200c031a60018030400800d40510521320506032049803840c10603503941041a40c85001c0071002141c6481850522f0009450003030003090310103042c19004085040324003450307000108200210300500c0803498000c00c007040c5284034001c140201254102041851801c1c050085d0011a203ca0b40200d00030020b4018802d45001d040c01c80345c00169000d000c00b80d0012954500400c80f165070100384010005600c4208686c5144810755000d80c46000034946400542541 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 602542985 1250 602541735 602541791
    0xb060406110115230f0319050a08031e0106020a030206060402070206070605040c1d0112080705030c0d080a0606050304020d081608031603270f11060c070305010b10050904 75
    0x7440c00040071109150a60810001c0c4c034420a508075104041100d1000f01e8418650150410204021a103030019035031780c100c5000f03809490700e0f2001c03071380d58900c01c2e0700c02c81d62000450085d0300c504810007400d0b0491030242c078080c00100000e29054801a5942c10001c1c4901e1003141c000418008548860080d01c911a6105ca0188181c1c2058580104910018007940101840310f002c031004a0352004003007030484510341c00c441490703900ba4507100500c0d40325001c1900c240c07004010700d141d80c403410000d075800340146950300d00f400e0a0207a007145c1942c030342d0750000040020510034040541e55000c0c914a540303510a61b1296980880f40e00308040f003034409409480c50001204210700040019808101d0001c560f030b040110442e4030043d15000090a1013640c0403281071400e220000342c0c0141940022402081002010b252907400180c1e50781c41120807060719000017004008000e401d02401006030011a10305000c01c0c8021401001400388000580c0714544807003802030a1100140c0402c4c0c602d00c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 602544235 1250 602542985 602543021
    0xc05061614120703240504052e06180b090103090303320c07080a05030c09090c07030f09051c020d080f1803030f0a0e0f1903060501090b0604061101 65
    0x442c101c600c2c2107a10864100000c2402d1800b40488641400c5405c1c2620b40c0c3d50102c0343c0d19070701300030a0000508004115002c00f04101021003104520861042d42198041e400e44018034240180108074005040c1a0300031003000c682c0034070070301d0005070564848080070720340016042c0030f600b8210050003c0807610080b04994100d0300c140d24184480d0700b41c0c503200050030700c40b00d5190030031506d14a2080c000d01420460051040701502c0784a08001c6411100032120f003800c100c011400518030a13800c0c0d07444007404000003201020103401100b8040d00002c141090484645004d0105090802110316001850351404140d0119a1083e00481100c0d400060701c54072280d40303804c006000d034000d0742d0410580710b0344045d0640610b0004116000090b20303840c440e003018a10b900c140d8001c2010460564400741030702045e801d0340c0320b04c0c82c1416003440044100400c1860b504249080b540c040e00001d15260421602c4200c540b2048203c030221001c0349050407940d41e20a1050f0f004004144442d0103c07a0303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 602545485 1250 602544235 602544247
    0x927020c030c01150e01061b1a07020f010507022e0617191101050c01020d05070e0a08070e01030b0711011a0a120c151403040b01150c05061614 63
    0x100c0000075100c0c074001e0100030040300c0305110180440040f207100e038031080726090006108092080b412103050013281c081540d2081129074400308040110349503840011219020489915410011400d0310000007000b002581000b000094a0350300514042150050705600036801540b2006404151402d000c0c2c1000325a450310008010070380c050801220364030407180d4050002d0740c1a41140c4920350b0002d10f0400c08108000151082d030003c8403401c94079542441801d072007040a02038140303c2e81c5580c2d41c440c0007481d220100b0000503080c0e04503900703581c00311a007404100400b88550341034941083c02011250f640540454468025014820303585d401c0011001c4251909046038440c00f4080f960030f0f4125840780901d082e800e01c00c94010b0300345541698100010a04004040243d07011840c1140e03040da514001c501840e4000e840403140c44440b200100024000701c80d4655080d807541c270b49580d1040480d1116541d41201070502284a2001117000d10301a00030324a940b0034001d01e03812251100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 602546735 1250 602545485 602545507
    0xc0221031c06030203070e0f060d080906130911040e040f060b0a1e06110d030b01050d09030c0506060402070312020a03140106020f0f2a0d0c08061503060601092702 72
    0x407580e0f1104038002c0c031608001054200450305d100b44142e8000ea8035103100c0d542c400411214544502058400c0e0408000c14101d607202c44004003a20205011804402e40c40e02003840304851500c185e07004000003d2109010704210141c909410642181580720103c28a0402c40010240d03255156441400000d0020360342d074206e034200c0307050f03800a544054400e55650b829903490844150031780c800e80042080d441e03080c4c0640d0103002200300614203a400c00e55841c0f2075804484036540305070041a000d4420004010b420081a80d110009842c1542440e4142c2d901500321400e400b01c0d100b0298011410b0807840d486688120884a9403c1c4d0542141d43d403280080e40301c00441c5820710060240030700401c6841e20020b40c40f10307a04607024405200c00219080d4560900740c4a1a03946d001000c00e0382c0394041130000084002070100d10020300010305140c1c581039617031808110710318000c1c1c0054081003045e03a001841ca40450704500000803040400c1c4040e10b4040c24400c091990b030324400328400c2088 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 602547985 1250 602546735 602546741
    0x20a05120d0233180105010801020c0c1e060d090b0a270510090614090325020616030e13050106030606020f0a03030c140c011b0c0221031c 61
    0xa5400380d0740a1903008080100d490111180ca034015090482d0041c0c4415081090f00c0d80310300ca0303414154a002800b0a85405d407902a404500c0c90fa4000c501c00c000000c040c004c007000c5500480c2c0284014014805494141d2220741c0c03190300c2040d0105003180850340c0e5030060504a94010340c20700301450840203032401031004404c00002c040c2c0031903500d50b4016110108006054100000b8407004600708140806420000000c88a803620b6810041074059920b94960050003020091622040e2440c4081c0380e551441440b4207180d81c3c4604c1c4140075843c3e0500721a592240581802d15010450505541e1828403100e095041044102d2012075447c0950045041c0c62035a41d041c084241c0e100307008c0342e881102c140c250340d16401055030040040c0c001c3c0e004200302038080c03d041345040000e42c2c41200c41e4000001850b1a6515802c99003024003040036421401105070401200700b0782d00750041646000d202030200c3d00018040140250380504005444081c0000d4001c10747e0641102c8810300a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 602549235 1250 602547985 602548003
    0x510110f19030e0307021806010e030f0304240e010507140607170703090515040f14031233060d0f020c0606030a0206070b07050d0e0f06100b090904020a0512 69
    0x3d240c0300600000c0c01d004412615125001001e6009485810320035511084c40640002e040c003860741c0305210707162402c0c03040500003400351021315169803078080c12001c40d92109c069414100422200d803c07445804c00c0703029030111020b1800545074500392408500c0c6800540310019548100010010300b29440011482c07500b0503d104840b45440b905015001d4500d03401e0014240c0d00104952464501d035012442d03405405402801e0a07040c064072040b0111820b04407500c5140c00018021540003500c0c0d40700390b0450160810501c03405044030a440e1102100c1c41c0d81d42445c070760340d903078050345943e45000d80e100d103c000542000107028112159000b5440b002da0030469000e400c0c0020a64034008c200700d00450f8000d0165841c0c800300d0b0381d441c94035007001480c6405101c0709004190400143c0c2c4254084418414018488880008000c600d081c0c0d0050060301280344281d414400031000b50300769020510166102ca200b9111440061040070f00e80d0016500480050084d410b4507200007542c1c0c00e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 602550485 1250 602549235 602549237
    0x8070804032a050103061202011107091d010c08190c0315140103050603070f0b0304050708150106020c030c060a050a0c080d02190e060406050c0f0a0c0f120510110f19 73
    0x1d9200c0e030343d00041d025580140300344203019540340c0c500300c05540036100c107501d42481d41d010b440089480e20010800c503010007155000314a024450300080c11004d210b50280920181000090740c6440c00d02d200b120010414041501512031042400940c0650803010ba07101c401d0801c14078403a11441510030302619840c640c0c1c0001c1c10400071504e00c1c00d001c0740c10801d8030321138401c04810505040c1d5011182c5c1c806401100c140c0300314007000a034404180402d01000b40100b070751013159450710100034039003000e006084d8400e400c00220840300b40d80740760450305407500c942003203a201c840d80389098809a07080c010160038080001412000480c290b070090103800c036440407840950840c40c1c001c80d10303801c94a034000d801003410001402160b02450143c654102114101c4160207203403900380d800c2c0106440e081325411015001400b10318180070004000d414900b10304056242c007a2516903640c0403035031644024607170700c040f6800a031904104680705075030b400c80010341d21400d03010607942d00e41f040302000b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 602551735 1250 602550485 602550563
    0x702031309110901050901020a050604060213080318120703050304080a0b01060c0c14060f070b070f0507020603060d080f1b0c06190315090e010911010c02030a0807080403 75
    0x1003510025849038a44121044420a0a00f1009001503d195105c0c03e80c0380d05600ca1843c0390340004d9003c100041c400c603c91180580c8451001c222410b14120a0308107486542003484103140404102800340052501166003001400320706d0859410410660009804c5000000d004540240c00040d90003060740b20b40d010f801a030780c2c0d41c80300300c1c3e0a04180400800c04040041704000001c0e013000030b00b150b040024003e40c83c4c000d6503000c0c42c0c040e500c0303400700f01c0e076820150301004591340e0495503610406455080c803514003501940064400d02c401804140f00b22000c161010a000d10081a6000f035a0f020511554551403c092003a1641c001c2e241c501d454031420800c0f01f40b60804400b030710800668060b094041008511068020381450080d00c0d414854451002130b4501480c0941d44558075160000601d03070303400d8108102c01c0c1c860908051306100c00c041900d40107840000342628569000400692505594980040148615030026000604280d10203664440540308000c00c42d1122402e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 602552985 1250 602551735 602551739
    0x50a270b0a1701240c0503090a1712030106090314030c1204030b010b2701110709020703140f0334031d0a03050a0f03140408040314010902030304060c14010507020313 73
    0x10003c42e40701c0310401d4040750060b50401390890702035201e0626440c41407059074100031005000c2110200541e204404c0040040400d0030888428410020805e107003800103071441d03040540142c003145051100074190700c8000c2002c114902d083c01a0342080c2180419112220f8654088240e2600305000c00d0b528008070030300024101d1030a0b001c42d90400d0740b00c50410400e42501d1b44141a81d296051001d0502401107010159200188202005000305403801a01d0f48800e00300248002900c403550301e00d2540811a401c1c0b203070040070036030307501003000400300446408000c0300c4207070307c217000040803581e000c04011400034a416800c03840c10501d92a92110b421580d4001d07450343d80001c12406000b2072000c02985941620480320701710401e00c507080100d031031522400018500d950850b01a02c8030080410240100f0000683d600c4211001c10000d0152105d1078000a480f0b1041d0b00c20181446610b80d02c1d0703002c01421540c100480035403a8020012403030006806504c81d0700410b400b01c05203d06940c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 602554235 1250 602552985 602552999
    0x8180705031005180303070c140f0d031a060f04091808030c030f060105070b0412020c0d111f120f2304030206060607030219030203041a0a02010c050a270b0a1701 71
    0x50fa80307e04419030300c4c000240350340c0e01d032041d04040040c1044000c0c01088140620a401000141c0c0055841da0b00000d002c6020340b003001d00c0085565165104820810103806003004280940301900c1c00c55000250440982c00d4803074054003402001043c11002000300141581c0a1001d184643d0b442c110003101c55403024011a01c43c800c4e07800046c013900c400c40110300402c0850000e00034415850040742c0e01c24881100082da08001c0b507004458030340c070076807150b103050a2600d4002c0302640c01c5a403203030015017401c0018188e2440c1c84410b246041d41c03019246501d90039038200e00c2101000034580000c004030000c040b04888401c41c1c0542c094441c0c440440c0040c01c2081c2210013081c1c041c0d010342007290940d922028082003200c0b095045110a100100303003000107001c0e000031080311000b51035854103002c50181c02d486112000c4014010144034180c001034101c0620403240c0120300180990384000e216030218003101d80c00401f4200404501c088046812048981c0450b59080d4008a140c1ea9424 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 602555485 1250 602554235 602554237
    0xf1e050103050106080a091e05011505060301030302030a030c050904110d3611030601062718021315021f0902060a0f090302041b030c030c081807050310051803 70
    0x225140000300c1c0d8100040000f80c1b160b02c8001d81c0c520512501254826102c0d240c041c01d0200f2130281d81d240d5449041c2240e61402c3c10111004106c191043d904544c51b68501940742d00440111405040e1a010460704062080003103540c01030b4020030170800b84188007192003082d0045102c0100803450000c500700341e9074003144240324100102c01c210300340c11041c980b40a0030145101d01268090031641407500281e4040c00054042c0015a903a903800d501d2400b080741030a0080e000800c0e207280c1e828414060b03c10920f620b0403151f0900d9801680d580f01c00002810041c0650b40180c001d040c4140c140ba10040c0c0c04101d602c0c3c040018000c803415200520140c0d002c4898008000390b20030810000044002d000c0c614010309201d03a410040000b555a40205083d80c107200505018200c0d400441c02c903403901813103402c119000600c3d04000a4a42d410013900042001e0041d900901d8082c28500c0140010403441c4042c04c009400d8940c40d290b0038281170040c0a080da00c12513007407225002841c4c0014000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 602556735 1250 602555485 602555489
    0xe07030e0708100b0604050603130507380d0f0209040b1801030b070c05070801021b0312060603101802031501020319140702040504200114040e100f1e0501030501 71
    0x901a0030803d0410050794020714150000c180c021406200005590b030380d03000034512400c0400030115100c81289005400c196281d0040b950b012400000c80c0c10782980907031a440301401403400440e108000684e100001c1c001e2203c030158080c01d0101121962000c0d8002e0800b0010a860501000101500700601002d44040101e9845055001000420490100d182d0441d0b014100710a000c041e940b0341c1400c1203120341080006a400082048503000507040a103142071148001c1c1d81031411211007002900f001800c3da621514011020501d50618101032038020300d1814030507032070703603174240c0890001c0d4200b117a070032942e607480500440040d40084122900c1007030580c0c040c0b0030440401c6080d42c1140415000028002050219400580f900e104c1c42d80aa07008444c0d03c1c200b0b00d0402110710301101c58400700ca04000d0884080d408518040301940d00340c0b2007140c0d41100f16603505a85001c3d020840e88030640030090b90b0b6001801c0329a040c4100100030072004802c0305251034a0040d800e0b52070138 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 602557985 1250 602556735 602556749
    0xd030e01020105060a0513110f0705070f270b120f011a0301020a080a181e0213061514070606150f02030412141c030e0601081c0f0309020a0e07030e07 66
    0x147d01d8095055040c1e80c06030308001622400541845901000048580c0000e036041f0307522b501219013440040040300513076000708560200c14040d40c55003106401480100d2150000e06900c03400303100f01d640c0d070740c01602022a41d45030444e40b85144218145028025216004400401d62100c0100e541818021141c2240c8a0345811405440388554200103284112014085d0070741000c4060000d00c4640380240d5004000407130f500c080355580100034580d400f2200005000b440c1000c100266072000b901540d00885505040141d209a80a0a05c162140708030040c03409142410109004070703410b4500c45405000d40e40c5130f100d000c1c2101e05030307624840c500516510000d03061443d8000350700d0b05241e01e004040c0b002601c0f2441d60843c02500120441900100070907150500e8408140c010810a0b004148000041900c00c5202100da081061010664400c0190080d5503d9000d80070350040e034160740e409400603080c13a0781c2d6101451103610569144002078200701200c809030000054581c107407001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 602559235 1250 602557985 602557999
    0x70302070e1905040305190e010905130b060a2102031b070218091c0305060607030c0f0b01060c02010801080a05060619080109060906061517070e0d030e01020105060a05 74
    0x240320049060381d00040c0b03040b040745508041c52188907620300840b40140e20075100e02d40c4842c2c2c0020384800108418900b4420844c10b015400c50316130740301d21290708076001600c0c1904c3d9013603840100c80240c18501c440f65004900002c3c08044150301045081c1000c0c1882c1000b0b619901e4001c6220a80c4415101c500d4034a4140c0c101c2c20074042c481c802040710510007440102070440c101e25101168030300b1242650103400c1110a41900e1b00c041000d01c040e100d0500c0e081003545014000102c1c1400341001c003901704540036050740200320031103820902164021050341d22541e55540c0081106041150490000da1060b00015000d000010822882544800075081a69030324090006201c2d404045c0282d8621103100019002030038810140964007e4a000c0342040b01420480142e5070303680d01440c90142646100700406900c0100d205080d030b29003102d201181c07500c0000f114600703084180c1550080342d0242100415801c0125580407003000c0c1c00910240d607400c010040141128843c0d01c4d000310b8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 602560485 1250 602559235 602559239
    0xc03051e0703020f062503020d03020c1005040c05090406061a0301030b0a2c0303040b010f360f2003191d06010807032a0302010804020d0204021c0b0607030207 70
    0xb0340b0302c00d090f0004e03c0c007a180b07900f010070090072440440005803001c13030361616150315007092641c140301090510f18103003820b524103082c20981640e5140c85006012600b42e82c0c102007420488402e00c00402400e008100410508107800d00e28014078991145010310304c05140e11b07020054642c400e803412640c008918000710360b02c5003d250042e00c551031000c2a90481004007003443d01038500c0c0800c410b81480c00454403494035103000e401161040c5c200b02100d0030204810803041d142e040c030f4840d84800d2414400302d030320a00113034071503810250003c0582e80c5e030401064501d42005030348017424092001d0365000c4c00303418104003050385100554114122070f086c0810b000c203070f580301d420894194180180e245204055112000d0900800784c1141686801c41102002030012b010000d080209a14400701c400c11540c01c1000c40701d040c01c2c44024180944640014107555a407010b001609401600556840e254144111800c4952464040400e46040124400d90903c10181da8545505400a10880e8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 602561735 1250 602560485 602560489
    0xd0e0f060a120617031e0405032d010f02030a1505090615070b070804030908010b0a052b030f030609090b04020415030f110406051815030a08070c03051e070302 70
    0x1024080c0c24025182e11020b001981007a00c4040907000916100910344a0036a10506c1802d0820842400c2c51110144014406503501203103081c46a4528046502201c855200381c0e0301d42040000c5090f4035501e802c05440c000f42c2107400079441850118001c001c040c1500e07130840c0c50540c285c003596400c41d07844400035440e41094801d000301c6858450f030f0203060807099500c3e11481d003021940080010030b039806010800d600668148080e200c00f40c020b01c0450703000004500455000d2003641c1c4100c0240034000380c041c100c440d9014150003202105002084c00e070034044c040254070045200080e25003000040d07803d0340c0384501ea40c5140d121840700c045444030740800c00603081d04903903140030b00c0d885100080003c9040d40c0541846104406990381c01040f0400c010072181d290b031025008070500c60001d841032071821040390780000800007001401440c070380441d1408050740740017084004005240300c00e000b4100d8030181143c1c42031040f82c9200c020041d640c9501c006000011340d00d44d0007083c0600040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 602562985 1250 602561735 602561747
    0x30506150409050d140715020711120c06030601030e010516180e0c0702060906030406050a0b0d0f02100201180b0a0501064401090b1003020310120f050a050d0e0f060a 73
    0x85c10079950b103810100c003034560fa54000c16418494060a50014001042004070060f803018900c0c215084108070380c0700048d00d0703201c0d40c0c00c0c1c5201c2e00c10314000001030010b038029400300404004a800810082c80c3c90348004403c1103080400b200800c400030000203180403100801c1051f141c0c994829141ca84a0307500f00351058102041c126801300c41440100d046840f070360051440340740240c0000c20f5901740407804404803041c3e9202d0300d0042d112140c204002c00c200303481203c64164142d4000310b0171501048100c5c010814020004a024050a80041802641d1140b14000c2e18074035020802a60f03904429211017100c000004134611016030411b518038820851600c608100c18100c0e141d01111109030710b18007500342c008880032943c40404c076400d8244403041e05d5603003075070b401c0441c80c500700b2840b103461410081c4161080c4c048410012803c101c00c25226502555018007111110701a40c40d1131038485503000100000076180e210034010b03510f0400f0f42c50708604006000c07603190a141400071168 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 602564235 1250 602562985 602563007
    0x1502010b1305100b160803090a17030f13061104090b040f0c0f0c03030e012a0e130b01050912010606020616050f0313021513050105040b0306010f0c0b01030506150409050d 75
    0x1001740c0a448a00c0881c10b120f0003948100075000140c64251280d10b0135541e6070508400403103403030030144100030034861104035103504012215080560a000351801202400c200c0c2000c80c11382c4404200016541c40b42d82002900d13040858041c030010041c01c5606c8112464441604001a66800c0e0a000c59000d21000c001c03042c0a03240c045041d220382000282034070380c0b250340c9103000e040c00c41c951940c031700321050103481c100b0591074084801c4455000207121444c440d00411205982c40c41c203400680c0c05101140c03803010000c0c00e0900048003072403a143c02401305124804c0513028100000d81c462648040b41d221441c030f161a07990a200350303c041c1c5c003203503000105000c50350820450144003507501c43c0c80140604105059556865840303070801050791035070740c0c0100d050090070b000920000c1303401016664007450a1800c070703041d0b20000008032a5032442540140c8090255000401409804619944140b107000640124150844140821a200050064542c0e0014610403601904c41c0301f00502c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 602565485 1250 602564235 602564257
    0x50303130b0a0c0f29280608061003020406061b060b01030617100e0102040f150c0209010b040303020705061c093905041518061502010b1305100b 64
    0x101c281031540c42c5110703c13007005002c0d1403200c0300042c0e14452180b0b9101d5a84000240035048800d8202569440e0060072604140d07403c111403400d94408a94040d4000f0f0300030401c25048500d2410a40d8404040440e40d0009078000e900f814130104103e07002c9d084c2c8603440c0c000c0e004295515042615110020107003160000d042544400d0000380040c2d205024110303102c0c0d4030000d08013046001c007040040340c0040310700c2402c0c0d0740144420005480000e10f60001c41e0190040c81d020f03480c641070300302c8040740c41c204000e41c04000140003184281814002d8020349119400f103442c050313203e008000c10360190250f0740211500c02180804a000756810241015101e0401901c003481c2d0080f18a03001d05a40c20120504400c00c80d01c1c1c1c4600d8208844200140410b44081041145450500c080b45083d030003041e0552105144840011340e4036884440144801c0580303400401c0a5500280a0035403014001d100e238880417001103024009200780e5000b10844e181c4600f143d0f1400c603000300981c0026100d10 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 602566735 1250 602565485 602565497
    0x60806030c040e010507021507141e1902191110030f0216050c0a081e070906030b0103050d0311030114010212120906100609050d051009080d06050303130b0a 69
    0x403050b52a01c3c020108401c2c4200700200380703807514600003440c100fa0701000c0584400d00805010b9104d0300300c0050402340202c127018955500e03c048030070148456003070701212203003400624124030f000065072301440030385654240e03281036038180c0154140e00c2c042039001d04103948514000410380307003401c00059450501d00380070421889124060049800c4a90058001012140b007201007040612968210a8084580c0e604440c00e0001e82e07903a0711038000141030722010911014030002000c028500c011300c02e802c402d01040791a8a00810100740a100845142c07003040d04c0c02d0419800ba0051001d001042c0f00303007a007076a18043d4900f04100f070315036640b41540100402090207846842c0100011a04070076140c0d11410240000c44c40c1483c0180142c007940e00344882889071300d620283c000c0407a501140c0060034080d140c200075080600c0540012200307403400e0320307203400c02c02c103d40070b418410038000003045400c0e81d1303005064076442251035030010743c0c1140f4818840001c02c44090050f98419107800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 602567985 1250 602566735 602566753
    0x32401020a0213020c070914070309050f0d02010906051302011d0d02040501030809010207170c041119031a01110c1302090a0e04061a010c0209040602190918140106080603 75
    0x1007101120b07034584000c1c0d441e13000039040c80c02c86010040c040003064407000400c548090b1020b040c119140c0500380d5020142c540040368207102d410414242035040d400b0a5545840b047c41c4003030300910070600c00b125600e0500c4c00088022403055202c4052580684503040036142e202c1102001d9602231001c280c2c084880c02520303001d0380700ca00c1203e001e503200341d2540e5910010200060300d45103d96110007003082c031800b040b80301010003007000c40841405440215580f041070070040401d0081e803080c1030301040101d11441da084d40c95007281c100c4681b074008081071080d41f18011200814005901c0319542e22440ca220801d051110200007640f00c622401801c054406000440c14205507008141c0038004a044c0814000c2510414080c1c4040605040500800d000081c0010510300c4010748502c94440003c2d051001c04d804071144040442d160f050502c62682c005002400e40d80500d618002400002c0c0c2958480c5100e510005801c03056582020f038680802140c0c0444001e05550301401035030b0311 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 602569235 1250 602567985 602567989
    0x10206071412090715020a02040f0b180406020415120605031c0809010603081603020d1b0b3c0a02030702060112050304080106062d0905100908150103120302032401020a02 75
    0xe07181c005c1680e5405072a5903500b600421050322002c181c940344a520300810340700f445c0d44a038a64904990100400c950503900ca0402d00000e010f0707a404010403220000c403101503941d010b80c0d0b46030195204a4200101c5480700300785503990b1702c9840301503070f190f50710950143e42900428003d0362003000e0600100302c60303840755158049908014290800d401103504c071041050303018403100d0a014141d02e0000e030b04100b8140010300c09000c07086c0c05041c3d00c0c01400030440b00004d0f22007003600108100c0c45460100481500c01030a07440d00e010b50904030741043c0101d010501d140c009c0701e0103a142c560041c404c0d6400d10031035605914101c20101c0e4144810070000034001c6081c01044001e00541d12a54141111092110062182c55554a10381c0c0428403d209032075400196103001d554080e00c2d0700a2011904c2800c0c0d03800f40c0d1a030042032180c410f040180e0050f19120f034549050720310400144403a000c00e03000a034285d000584104403241c1041d10348248c00c52003010102c01e041e0051045a403d4569030b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 602570485 1250 602569235 602569259
    0xf06030210030c02121e031f03080408010f052e03060c0801090c030207020102061f1208031608040b1501031b030b0a210b27010203060102060714120907 67
    0x159081c08a40c40355841caa540e80c041c4075040507809005c0b03400e85490180510210003100010542843e02c00110100d8041c41203008213503140a0442c54441007980c5a003003011060300684103045056080292505000219010b100c0c000e502034141e40029054084480c0603000c8a5000544025000325002000c41c803240504901c007241c1c0c0d00e0b00d950ba541003042c1e910941e07040312010010305004008010060740e00003400c0368801d15800705c1141d800915072101410a101d50300c26003054251481034018444510300550050324400d044075100e5400840590348602c1c2100d0181c103040b09680024000456441800c2014205140000d02c801e4800d9803144840c06460079880000d5072441842440c0c02d00c841d02e84054285812070054210311000d0880b259401404010582d820b81c402040b01295405038201e00341010100154410315034940c194007e410440301c0301d005102d96408550104e00460103214202c0c540994180350504140045c6446640a4072109051141c3c00c40042c410461503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 602571735 1250 602570485 602570509
    0x610110a03030e07120218071101060f05190e041103120703020d080912040909050a020d0b192307200c21060402130902060307120e060f0a0f060302 65
    0x5100010400c454140c3d144c600061070b007003000086a030254010159441414030060804610f2042c0120341d100e0408442c24941204d10845541c02d1032400700d800030424007410195041540d2404000341c00c45400340d449620b500c1019000c20700d010200d030101381c940c20181081507003c1d00700c0b01d40f1844082e21040740d0740301920680043e003204234589032040d4045540b076001500e01c0000c180000306032075a1602c0b40309600c076942c086a507a41c0c10004000080c0440c05115400501c1842e00007010306080400e42011640742c1098103004080030500760445c4580b0760340c2c0501c4030700070f48101140303082502407840180c0024240a1200c1c4400011600c0c1ca01c0caa15980c100405010360000c14024850102c800d540c1190000405103d14110f0120001c0c1041d03000b03804680c5180781c00b0260340444000c198a4401940000000040203079070303500300d00c80c1d02c00c40d00c0b4003000b0440300c004401c20350780743c1e03006aa07006800c001c0d51010868400150700181e071407600c203c0780090125541d90002d03080070020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 602572985 1250 602571735 602571737
    0x2040b070c0e0a09050d0e03150f091e0307080f09100504061704051c090801290d0506040b0c0c06090d080f04031b080405040513120306030b0610110a03 67
    0x80705101c1402800c4605030403080c2008107100350742c01551001c0e240c11019500004010080005a16541e0100601010442e201d010340090b810523076054810201c0440b0320343c450344500304000d5223811444d80484410b0010714040c604003401544c031841603500c21604c83c1042c02e401d01000055560b071059185030080262030f403d90b00c82c607008003c1d1401240503030f8404401c800c6c3c000c0102095001c2901c001061070300c04103000c4050100700a488030259074010b5106903103020001401111a074000b06021407154030030050602c58082000007000010b04003d1440e0007250112f00002d582d40b40d52074002604000c500d0600b4100d9110303e240141c2100c00748120351000702031020300d58021822a40140480e0000032643c5001d86000d0120400c08820140721009126840148143c2409643c041e03c0700138410b010906080c1c40312580314407050001d6508911505865540342d00911401c0203c0f5807000c4913030502d80d2080200544a070300d03140000e050200070a400980d800c0c00740440c4100d1442 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 602574235 1250 602572985 602573003
    0x60f0b040b151b0109050a200d050c09090705031002031f060903030509040f11030a06170c0105250c0e070c0f020d06110406051e0403020d120302040b07 67
    0x821042005980410304460b000d200c155010749010b11a403400c803140c083c803c0b50324005101c1c0d8202843c0c01804200d6019004d8021b44a40500708400c82001e0503084281d020a80100031220080110140310b4030300084c0107034006d01c10b000d140c0c1000402940c1c40002c840944a00654a070040ce0400c160b9003140d84010740c0c00802c010f602d40d00084810310b42074244a0404d459424181d0181018206000140a0043c0401e410489540d00e80101d4210046d01c2c60510000c06c9003007454425400c01e445600249041c66004910a50f9500c0340d0106003801c0d00041110322041c81c01500c85034010a03003081100310821501051b01061080c11001500c6801c2c51028145050075840d44040060710710002c20078442d186034040303502d45142c602e01c0c540445000c100c1c500d032460a000204641c1c242402d20040200300007520603004800340505810b018a00481b4082c0f0003c90342003489a404000c0d402011405100086030141c142c03c804c0102c41e0800502d0162592126109030704030100454501c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 602575485 1250 602574235 602574251
    0x1120c0b0310061103040b070b150d0f0210020a020a12060930032c1501031202010b040510090c050c06010b04140d15050c12091e0601150516060f 64
    0x2500c4082199615100009941032909102c2101030501c184100a0a109a00340100d50f150062228400398864001d01903002f030b00d050b20704907098102e5800140d00c0381e2000c0685c1442c0034004940d078882c1c2607000f000c80c94014144520300d105810101d00c1668600d0b0345031001c84c0000c01060640c1c003141d13810742804500c0345e01381e00040b0345c0d000740007241030816040c544040743c1850b00c0c45a004022010410a680980084d25451303d02600b064030481e588001c5270000080c0500c0204032000b9034500d1380240001c049642c280426540301f500d4441c1c80042c085d40c1080510001d601c881c120400b20314000e807074441150f0056181c158213801800210a0019081100003030b655041d0310f800c0710543e04494541c0700390b1030b00f04034500c0d401d0070007414507129800950a84011812109996854841801ca034100040b081350b480340409901040300c0d0f0103045039000c007040010340703d048030202d07400040c211284c0754048036580c1200f00a540f0b4a80100554000190395004a0798080e181c2400003400d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 602576735 1250 602575485 602575487
    0xe0709091101090e010608040f05010c12051e0105060a09052107320a0b07030306090e010905120d090f120e01050901050f09030c0d1505150901120c0b031006 69
    0x80715244495051003c065410401015468102411a00d070740c00c121a5a030380b10304018078080e40e01c3d00c00902951800c5501d0b0302103904081d0022040c22028420415640d941220341d2a5000e160440740035400c030500100710524189004112444c5140381c0480e00940d5400483c4c51000080c03450000070b2240ca03203440140c04100190f10003481c654050f0702d0494880100c4041203102410750700b41800346285002c2c8542c4440c4a2580104551602d256a44003a13050003401407015000345e01e00346082038410011010140a000185500040606612540c40d8160000b40c3c2c071249228140946a0151070041610409079000b0703036024246044c0d0350304540710020016507412403e681480010300802005036800415100f292000c401300c15501c654443c006440c0c043c2c0410940c0e031209500c2440c0c41080694135001c2c0c122030480e601481551108107180c880308041d0300300c40303402032400f00c0100a05e8803225020300c1c01c0b90282c55101d642036242c010421140c1d00480f00c41111000c0034504006503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 602577985 1250 602576735 602576753
    0xf0c010e0f0a1d070201050f0f062701080a1406010609050d14010207060209010e010801141e10020703021903030c0f0602070f0308060f01090b0318030c0102040f0608011409040201080a0e070909 85
    0x4a23040701030119941c07405181c024181e940280c0000d01507002c2400768201c112404c00b05102450004062207020360b5528000c0343d4071000c070013003200d503510f51a003132041d0001e001034194180c07a1141c0700c54821506001c10f00003840c1c8516000d81d005171070b401844480079020704c02006458007540000d66a2400000003502958409013000d0412000c0401084904440c0c0303503003622180d04075050340e03141c010b01c007650a1121002d11059032004840c0b40d00e25010750005010f00480c2e10a44070107044041000070110f0181291101402040f03410044000244900d01212038580c41000018101550b98562a46401e010030044001c40d15417828001d05192000603580540001d291200e003450901180032214000904404d1203c9074081a456080c0003d000fa81c40032443d8900031500da83d540c2c101c8100e031740603c2c80fa00002c6544080041490803440325520440c3c0800f0b0300c000b5060301c481d4011121004010700840700165201c2d4412040001030184200620040d24085500000c03410701c1004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 602579235 1250 602577985 602577991
    0x30d060b070221060601140714061b12010620060711060109090809060a020703050f010609050609071d190f050a0e0906041e12110f0c010e0f0a1d07020105 68
    0x81c20300714000e628503a03c002140341d4003d1080c68404540c140c1c0e104484440d00643e54003c0040c1c420b2542e0030038080b40024100d01c100d0107510200b540300c1c42c040f060407881c8254400c0c4126080c0600040c030405005c0d2074a5400750400d170298505150702d4041c0e442c1022000e0f01c00c41e001411010803240002c40403c40d103805072078280c1040001c0d90450740e80c0c0c8561300c909c12516001e0100425420768490080c029000190307001000d90300c9808440b504030f4001c1026019500b4035900d0030000c1030140c1060600103214000513203405161011480503c0c42070340f11b0420040c0d01000b1110034407100c40ca10038145c1c00424941e61440a02400d00080156000107500112030446ca03040401005020000c2e526400c641c22040c40711800030850301c00c0c0e400408851000d01a030418001070070f011540040c40f00b41080c2da20381130b9182d201d45102c4083e1295002d070f80882c001045215019080d01e040c03905414802c03c001d1000d5441d942d96200300010185041c40080441c40e0f03001009201030302030041070741c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 602580485 1250 602579235 602579269
    0xa1e02010e041b1413080a062702041a1002030d0614010e1903020619081803040902090a051002011b0309020a172d0708030f0a050c030d060b0702 64
    0xf003480d080f0b0f052450040500c20800030031014084c8865885030100868440f0014100001070032500c41171069950030708000304036041888c000345126a94804074001d200c02c13410b54455103200d072054003004060180c148045d404501e0a285030b1540c0e5850549480700303401c4603009191190902580003046425903400320005445a000c0e403207660ba800814411001c8081300c9141740380000485064520780705800080d0031500001e00f08820010b24181c40c0842c0c105542c030503099a95160000034040c2021704421b045610602080c454051240c014011091001d064401c0080d55480005e070303900c080b00201c03400340c0d44d101611183c100130020710b1035130401103040034400c018030f640c0070840301701040c400d03400080c3e801000098180c07420300504544410200d4103600e144010f150021803682d060300c000c100c0d0710452100258040002c4140d90034429501c0d102802c0000e010401c0d0f03001e070701031101006140420032032211400700a21602d40600044904035499449600c14400f840c0310701e4110361 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 602581735 1250 602580485 602580491
    0x90609080f12070c090603060b0a05060c0d231204032a122c03010608011e15030c0b090301050604090210030b0a0909080c1603020a170a1e02010e04 65
    0x70480103000103420341d0101c00140071503542d68450a1628841116801030f04510307041100005c18801d0381e42003042007507000c03991242000e6a03001004003d00c03070303030499032213030380203052928a505e02419410041c94007040e1807007810342251002c43c0290313214582d031007804402c80060000741940132400c0108010702910301d80201004518100c00480003400051410801c0480105410701c540e11081c011750019480007074020b40c0d165608200e4110b0078086c0e001c1d619010b8002a245814050b2255007904031601a001044144e11440540740c801c483d2403210080020000000d0800c800c03440080c940c55140c66150300c504010142580c0c00030b03201500c03403400c101001016a030360311203111a00d041810005400005203001c83c10496082c4d02040c801c0d03162904560620540d44000c24100c030030082a039159010040b00e20000ca03849000c040e420040c903190a007c070000004151082c1041d1008450080c07003540d8491804403a6100c001c60076014280c04ca00031542c01c14648050020221014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 602582985 1250 602581735 602581753
    0x32010806090624091303030b0a0f0506090301200304030807090608190603060e07030510140c0c0109020603100e06030609030a0e010c080a020105040314090d080304111009060908 78
    0x1d16030340c60300949000c070800304240071810407003084403035030316040c030068001e88045c500360341d544030448003141055001c01d04106d543c050f02c1c64188800010388010350880010300342010280082e0780c104011068056580311980001311240b00100c0c0070b0803440c01c03841a6240391502d4000c04410300503000e54107114881000303005464011410300c0d40064101c085201703070304010404202034141948040d01d000e1410070f0a400c041c0340403d80c103050f24007a40894102c00d0b10b0103c0c0300e044603d01c0d905103100303841c6400407078201c1d14884020010192030200224401642e41c00241450380207580002003454911420403440000f040c084d079009800f140034100603c2d04c0001182c8030300c61050100c0810210620390200360f8020025108440d07000720540e5250f51171200040c1c02044207450507070100310260300034022400c10400322104848003504c3d503048012960f48005441d04050070490b00c400707080303288071225103c20766501c100368074a0380c4099545207059000f4202420640149445400c400b000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 602584235 1250 602582985 602583001
    0x1b1208090103020a17360c040506032503020a060c051005072124060e01050a030b091e060a0609050d240207110603041e0632010806 58
    0x103440c8034040c01e003030150b5640b40000707040b2410060f01c0c00c075403044894001070001c03a1007950521481d40d403901c140c030607441402d500c25044400e8000c150311820380c031030380d0304042c10705168101135040300c4060101c0d84440040603d1440042c82540b08160359105c2c101c00b001540b8041c13a000b0000d14490a052100700740703d8a9541e160440c0f440210b061035120004a035105102d001c00b54805900c42c2c1e121100042c40c2041d42000d807803c9480d65002c2854601388a2b401c7e181c613002a403c580b0a5113030710080f406040700541c0c0b6608803681078428540c2d0752003900c010b900c4240010f031264601d41d4030b060344107442d0710b42c45e1201c14014140034000c4527882018400241c00140c00c005503603049540c80da0202c0302d407520001403002c01e064881c22480791025109103003201d401810b40740f4803412058050000803014005540030884000c1c000d4200e01e07100c0450b03078050308041036107039002c2d89020500c18440d00481615100746000260041206411038021241000c0350074090301041014004030709003100c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 602585485 1250 602584235 602584237
    0x2d060509060304020d110d030801030605010b0a20030d06120606060518040f0b030a0b010602060105090f01090e070911070c05030f0a1b0305010c08010503060f0f07120f0203041b1208 80
    0x8070017030107000701003009414005110315030603d40c00001c000358584c500a140080044400b807004542d55400c0c50004506100042e064502c045050f5440c5c044c045070103500d04108404489401c225800304000203040d00800e800b80c040504102c801d49101161686001c03411614a644943d04109040c072141700385540d040501d244d03480f411200824200081c151645c02825450f019903803500c07681803403038200000818020f040f00d10035000ea840c0e503030741c0780c0c01d000700030004460000000d01c070580148804031540d8407103203801402800300c9500c941ca80c02400c0032103100380701040c010b4002040d890100442910508040d02081d2701804080340010101c980d01c5441c464000e11212080c048058a202502000801560414000d0200c424110b4001d00006000e0061900034050340f00021545142095103a00581071a148003407169181c01044034036400034980c290b0540e0301d826812429103034600180d070042d401040d00e4070002c2c0c0f00c107403a40e41250b41684911031050042c4081004506554 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 602586735 1250 602585485 602585491
    0x30c031308070b1f2d0f170709050606071212050c1801050c0a3305011403160314030c100c1106191505030a0f0c0f0e1803042d0605090603 61
    0x1208036192500d1072151a904040d09800031b00d4041d521000c0000c0e411103012000c00380f04005003e44100c0c64550500c0c1e03040d1381c0200c0302690411400c0080310006090b5410700d02241c8030070f14001e400e0015020103442074030800d561284840d0800b040c0800e045550312084940306009081c280e28004440311141c0c0c0b10b1401000151150080107614003030aa4501a459949204c00744500210301c552a4100c1c010282801601400c040013425500a81000101440c60030850300e1860b00c5d461444d911400c20081754043c0c15075074081400740b5400a842003052010f6200440c50105183c1c04401008000500990504405600030014010030f50100041c900307805058036408600900d00366024400141c00d42d200d59010710569020909001032480c5100743d251045081001541d692400081c69140502481e8a0004090003050000e401c4507642e40c40401c10100360307400d192f42c034542d81400380342c060b81281100504402107480f07482050641c0700581f581e4140305042451420104029000003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 602587985 1250 602586735 602586779
    0x6070f0203070c140415080f01201801031d0c120a1a0702011808091302040518060d0606060f231b0a0204020f0711060c03030c031308070b1f 62
    0x9600d030181c945403a0003446d0000b890310450003407035948400e041d0340c4107001800441d8039440d041900e880100c4451000d0000c04240d424541800d40c005160700300340c0310818209040c03580e980707070000850300c08058a4120314503090144c031002c0001401d20420003501c22401800d9081240200000b541c05803641900f81032803810307006680d450110580c0141a01c1d80c04013003013103003908050100020034004102032a0103403451111203141100d07900c01c0e4061401550342c44034621014901400c2c6460100d94804070041c00c0002010003929044121889600140c0000f425000a010090380056a490340986120145440d40160207000b0180c3d0141140c25984440400681114040100700003491580c00400440d41c1c0d003c000c0d02c2c25181d501c019001c41e694200217003004e08918255040c1d5512014007005180395030b4421011185503030006001d101582049000200410400c4001d003080604c05c00601c09281041c0d1700ca00040001a08000b2000304a50030178400e441410b90204a4501c2c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 602589235 1250 602587985 602588009
    0x708010608041406150102010e010903080123150c0607020712020f010201140a020901091217031b0c030703090e060d080a03020c01150e01121a070504050301090506070f0203070c 78
    0x5a4038099000ca450310f0080f11180c4100014002883c030041c120a101e020241c0081041c44410305046080e0383e01c1c660080d000c280d48a0040203580f0000c0c820700b2945180401620300c0c2c0b8035003c0052006220082700380c2c80c003040032440c546858410418550410158001001510b1410488040c06801540d0013406030124100750a8a40d00075081115850b428103091509480d00c0c6000380c0c0250440e00c0c00e02d001460a040029288480a44042c0b240307270030482428415103c40d00c04603160344054100410542511071400f5000410b41c0030f400207410280c060f650360800741c140101b00722003540050b0310700030f428401e000c0780390f440203000400247c0c02601b898a03140d402100f50007d000d06000314016500b0401d0703a100e003107a5007050b402511450030010682e0703626014451420312116000804920489801305140d0145001207580311280d41740551800c0e450308081703803d480c900041118141d114106109011760003101c00001010f19200841c184907807521244100c010521034162003041c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 602590485 1250 602589235 602589241
    0x30b0109030b0a20030708040c060302040308090d1106040e01030209150f01140405030a15150b1b0705040204230108090d030b0a03020d0b010906060e0f040515090a0b03070504050708010608 83
    0x450480d0283c40300780b00b036081320348134030306084c02500495085404545403211000d010403100c0c0640300381c8082d00d4000e00304c4e170304002c1c440342441001d8209010a5486080b000c40012007981c40b00d00400181c1000c80c4048150351462040c0032800e0310141180c0f8120009110303040c01c94640342c80701e044441092034404c0e541c03c030b0401000f2152150b9000143c040c002c25001c0418010070301500c142040c0000000c224505001e49442d1074801035000d40d1b0100300b810442c5032100380300000b8512103007900409940390b04e83c0d1200098100d80c49640000a4450003e100414001240682e50090760342070801540394a8840e5020352640f014000e19424140d40c0c4c108102c05440e0038500001455000d0320202040000341002c00340c0040904c600c599030f0b41400e0020414034030a803000c0707440c18006410704445a20910400024180044c035504c40700080c02ca0b010010750b203a40500d4064a6105400180085903506141c2011700c1030300070500841c20001486512a0320529031411210300d841c010b0781c40c0d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 602591735 1250 602590485 602590511
    0xd080c1f0603030807180f080c1e09060d0501110d0606020c0f031221091f060501050a030c032d060515120c120a0b0a080604050a1e06020c010c030b0109030b0a 70
    0x141d047e00034110003032480f040814602c500003080042548102c1d49000d80b07ea0142401c100d020402c01155082001040400c00d01d00300b020217142114030400020800241201d465407003030b00000c0c1c286143c2600c03410300700105074040c0814841218180e4141000d40c170f81001003a600c1c242e506180034000000034160030116030003d00c201900041700d6030100c0500b4a001d4055803441c0c401c0d80403840c42d09545c02c80c0300d003100c6845000103c03031068580343d0403c11b42e05070917001404006503070014161101e000000d8902c00c2d219940c082d94600c200c10365640c2d9054012002c880c07054000c54058020707146c2c100e00b4800d00394240c582c0c0c2c603145580d000190f5109a0040b00758010003840142e102c604a0a0000403038280d0003d140c008020b86564094a9a07030742059502c46040d540601690020b43c140741c04142c50071180d100e4200320710400c0c0c000c9265640d03580700701d034811403425610b42d40d22a00c01c4039060745405051480902440e0440c242400d40d11515104140600240c0c6c0702940c843c1544540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 602592985 1250 602591735 602591777
    0x151c0b011419090624140901030e0a0b180114041709100804052a040f0b060f0c151e061903050303041a10030f020d080c1f0603030807 59
    0x40400d140100c0a01903642d00900c3c007404072402000003c40080c041c1d5041d5000c0701c40f44180584541c0d0f40c401c1843c0702c2c82c42e45102c0da8840500713281055240d1081072814031080103425100c500c82d00d030108a615100c20031400180c403010060301c09134101100704444401034100c80340c0080d0010000d65a9034010b4000210b00d204d00728480e600320b48405211000d054101440c20310450060007a00c1040d10a80326840482c10918201480310b0780e00c0a21100d6828940d002c24074000204d08000b4800450f00002142a0410030300d40703000e60b400060240c40000144000503280469410b1810030b4140740107404c90b440c106215540c1440f1101000a9903a03071181281c4002188403e0034903540c90710b9003001520381d801101d0030340302c941c04084181344030390b140003225101300c000d5610502180c1c21a901c001d1741c91000c10083c2da001c54101840408611803000030205402d02c000200800c0d0941c1582a00400c00b0207070b2501aa40f6001c001c00c0402c0e0410345803640803809140c05501e0135203a0280c4440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 602594235 1250 602592985 602593009
    0x20706200a050f031305030102070305181503011503140f061005041a070b1509060d0c03050105130212060601020307110d150c020c040e0c010c1703151c0b0114 70
    0x83c81528410012580007000034500b880c11321501d8003040da11a024517082c1c1c86100c40040004404002c100c3c101f4a4001d026540c42d44018180000d441281d0824030030341e0000e800036201880d0b6090000003e0b034040c45102c1800c40e064500448901c0c2c200c88440c03004c2402030410b07024401c44101141c41612400450700a800014104000605043d42c41000d5402000088a41e45103020110303107071128072940044181c600404250403580e030041071010003810013004072104540c880c0c011000501c00c0c080c3c540314080b20141401d8040d610f0040044594900c8503c04268002400b4416507907400301c00c484545400840c0007182e0341d1440c0101d8211000007a02034a0000c801010707040b011040e4129000284c20fa030b007181d1949601d00c04100c102d880c0c00c451194940d109500300b942c0c55000f101e811100901994031400da00318a541c000c0c065a10807580781c020042a0f005e0900c052415103483c1d00e909204d41c0079034807401803c2d81d580030080d006014100840d102c13242c0d40f0307046e030f0b40c0c810103281 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 602595485 1250 602594235 602594243
    0x24100503180a08041a19030e03040302040609091a0106080609040f0206070302011a0307080705120304031509020907110a02040914070602070e011d130c0f24020706200a 74
    0x480075042d82081080c03030b0030a01070781e180c200c01d0f000b24400310440b550540f680055080c641c961050f034070300001d03070060a141e190100c0502040c003001001d0b07515885032000906c0000700c00701d00b440c0145800401a01103039041c0c10384000c214018024260b100d1a500d51100042d1002c400a48443c203014071242895900290322a100103075000070160306411013010134501680c0700840301310440c1099107611441c0504012580003403801c01007481e00c00c1c19111000580001c3d2450161203840c0c1c1c3d60200c100140150000d606d5610502c00c41c2001a12035a20006500e0320743c808140760b41c005515240c4194000c1e10807616240e60400b4006015150304040705014100c2c1c070030b61b5440c0700103920b4441c18400c12076120f40c510000690010f0072480c0114000c0e460001c12072558641144881e64004000c2c01d61f003102c01b980300442e0790700b440d000c6000a454480d40240c1d15001c007610f69081d410703030610490115000000204000c83d08880c055a1035484003021107080340591b44c90b20300e0302d040600068 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 602596735 1250 602595485 602595493
    0x1b04140408070605090609190809030304030c0e0a0c0503010320060c070e0c0a020a080a030605130b1c020f060c010b06220618050616050a08032410050318 68
    0x42006082070003881514841c0c1400d00150f075072008003540b1040102c0d14110710b80c011015030700208070700901c03100381b040c0700d00000b9081850a002007450f6070095082129050710ba414140301502e00351624a0f03118074411001d224110415100901a00061000805d0300c41041200c100342c0080460310200e4107c00342c4070f42d886d03591500300d4a41d11075071361107591142c89115000c101c00304915011141492990740080407a10195540c100b42c07940a490240b0405551740000b03d443e40c1e803100c03c20751803c0504e6022610915490400c041c3c07144042e0420840703a0071400391070058881d400350b0a21040100c0c0c0b855119441500800d001d0030190340c090f940050001400f50070035a80c44c03e04140704110181e600781068440c2c5055540300614a9081c0c0e1501a1842c100145c0c03400c000281200c5814a248030715023085603840710300d040c0038048121a400320100810204403019489520034610030090030050b002518003003003594500c0c031041c00030800d0010001c1c0019420115406020001d44111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 602597985 1250 602596735 602596741
    0x2130902181905040203031207090312080f0711120f04052d1806041802040504050c030105060103060b09130e03030c0a030f0c02061501021011030a0e030a021b0414 72
    0x1080c207030204a0740c0415940300c5161400d01880380703200300c920807039015005501c0c1c400141036850300580c0c01802c034000c1245501c40800090703140750380c0745102c0b01e081d2618005420000c0344000c94a20003021314080000da4020320f014000001040070b5030290521106640307288400c42c50055100fa500903a03000350700e1001c03852001100b0920080140d0090101c1d5941800000410082c003e03d02942ca172074450450202e00c803458194044211000b100c2101092500300b60701140941e0300441c0c1c240d034290001491030034641001c6c0240d40d8000d100f4078040200c20705020954000c1d008082c81c260291844100b50304280301287e004424100c1c08104890316447c120008403000c0c2c1c003984488002074241046c00d042c0e000c1c14003421200b584560090330700c954924410754020300180031514110f100700c01c03d80071005058491103020750b0144080b50740d40c3c5810240c2c0c030241c0e071000607e00101d5204102d00441c01c2d40c003007003a4108240c659511003c0761140c1002030082d2041107148102c0c0d105410038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 602599235 1250 602597985 602598019
    0x1150303050c0708030307050706112b050711030409020309070f030b0405011512020103050901090b13020913050d110115140f0409050601051504080703260c030702130902 75
    0x80d0180810400c01c48941d40c0e01e0b0f400a07621707800160b8107a000705406101031000204583c000d801404c9041400da410403101d02d071130101e1003801e00201003d0205121403041c894200f4010f03d98054400c3c10b004d007900d07403000592030b981d00c1035205007d10147c0c08004160560410f00424000f0040b8040711103509441782802000b84900350f40444040d80b80405d25450045529401c108503880c0c040b00101600142c0c00540107000028140040707950f880c03e804001401c40103405024580c0e001000d150800d07a841480030418003e440400302c142e003022460000b401c00039898200c200c0c5490951038414950306110302419140e06031241f01c4000200115845c2c101d81c20031107800004507882624007441d0000e100c01c0b10a034090141103604401c0062125050040032046400d40f42c1841720b2805545280b402c2c14401c42e600202d401000702d5842521500011003018a0305540004440c80c280c0f0840d0a01d54a22900400038080c0c5450110703185c0580d5603500c9004210b402130b002d034002c00d40e0520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 602600485 1250 602599235 602599237
    0x904082512020d090f03031e12050a050106090914060409020604030b0712061401021b150c0705040b01020f071a04030b150a080106030f080702031c050705060105010e010813050115030305 82
    0x1d500c9002131007081e000030305806030040c004d0459801d62980f04c254500d000d01c40e54882c40c10032000381442828949803220000c0c501c1242e100e15a9038500203415410508000c0a00360694041c04065007405a0168044c18070407040342c1121080340d0025170000c0da840421541d010303d030f001070140c82d8000e0401071fa09400c801c01d10300400303160304108240e030f0715480d980c45915a25441e141c010f03480001131881582500707100d141e0303002c401402d40700d046440b0554150303580d0102d154441181c1100004111600b0139001d110840c2e002400689000700007924015610758491281c1e000c0c003074501c0341c400800e0052108807405150000d440c0c06c3c891914400c80c110004203003050502a281501c0002500c00c018441e00c0244c07944841c10240c801c109849103a6150017600050b0f03814020384911042012807001d00029040d15504e4841e140d02060804500f8503030143e01241c18001c20502a20702a039100b20740070f41c09800403580c0d00910015060807401005200c81310559000f06030408000d042d0014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 602601735 1250 602600485 602600503
    0x70c0209040503041a07080315040204090204031b0920031506160201090e070e150c0d090303030e0c0604270e0f010615140a051c0218090408251202 65
    0x20409000d00c095404140841348500c00000d087c1c80ca061000c02c04c90340d01c0c0c0d6840c004540300100302506150711f54840000b2a80b003540100e680a0900426034112036960345144010150003404002c2d90706818a644070480120203065079090740000050341d404000042400c1000000d080180c540083c40218400401e1010003a408100c0c1c3d10800110b4441c0340500c1c605c117000b26900d5921020250b030134014468070342c2c4114180b400c0180540f21405400b00100b50b0042c046955200200b49181805000c448003a0600111030300194406407031130b254001100c0444642c68920004825600000d40300035070316011111103a82000203510007810002031102d15010400d008004480c0c0c1d441c044102c03154120721940210306088a1661032003400006410030000600f0410f1070101c01814122003c10b0100d0f14004030350340854042154695030b100000a02c41c00e40b0681c5c558140b540352170455029a07049402d00060395096031500c1d080b45501807504c190300000c600d52aa81c0b181d0081d407294034413 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 602602985 1250 602601735 602601749
    0x150103060605012c0409050c060f0307110c1c06020910090510081608090a140a031101050f1803120f06030105070f0e1005220e0a091703070c020904050304 68
    0xc1d8140344c00a4080d040e40740080c070114603801c2100710400d06002c0a4608108162058061008105480d460342070081044220040030341e0343c2e901c1d14880260030750301800b036490110f5001c44494503d5444a0140c09007000003c150240403a0f103038a0201d0203403180d9407407a038010700d0700c100d80d22103503400225490581e9401c03a5048650b0b030603980c00721140300b0211036410000001082903090f440c05554642e800440034070558414500c50741b182d0f00744176401c0c84d40120540c801c900c810149079110b418071035078045103402070104d42404009003001003409000c81040c01e11802ca9980000020400c032802e1031081000e0230b00720b16204008880003d011100c25009500386400608283e20441c604034401c0050303200e015230781c2c19403010711446625000d81082032220070000345902c03010012204020b8200040312078141402c0014405204001030940711040342030a03420000104400156840b08c0e000000c0c285d101d81c1d81f040101c0d0300004884002c0d401c00068024003040c0f06001c80103000ba2401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 602604235 1250 602602985 602602997
    0x506040204061a0306041d190326160e03121b0a150207031205010b0a020f06011215180c1d060616020409050712030809010e1c0215010306060501 64
    0x1459a01e510603c1c40c10519034041141000000c100340741c217030b200d0000d60305600588601582c24010040c81d0041e0726144100f8850b00002402c00c05911025140364000e4207541860a607200b000200111032000d042c944d581c01c141e800c2010040d104040c0d040103042c004007101d05400070566044281e0f4000c512003403041d0705120b0701080e19500015414040b907400000d12102c03202002c00c020003500105001c40420080a00c854510704190180c103004c2e18a035003d05503944000b41010740f81100c03121a444403504488010002c015800020035000b40d0031180e501c480c85900d94502008090040344031242101c516114003e010000443d40c06a81005545c1e03809000c903000241030941080302e2450380a942048048401e01e84420690b60b214405080031440408a40d00e040c00c0c02d04581158030305500711903112050550042c01c06820000405c000c015011900001607100c0310301002030008651500c190b280454820805c800c00310211510200c1156160303d4908043c0519200d42c2d800514 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 602605485 1250 602604235 602604239
    0x415021222170a03050706140c21040302060106110a0b150109120507050f0d060c21330801050c0a120507091509050301020711040e0a03020307060b1c050604020406 72
    0x501042c20080024060020a20003100750340488690303001d6881120600d1301d03080c4440303050320390070781a500501d400021540c54400c4a200603a480030b90001040d900304141c0305200c04650049071250548040c0d02d80000c0e0903006102440c6070a004100040642c601801001030100b038124807072010007006d80c3c41c0072010395501856100d0060700403020308541c001050400040c5840d0100b4059100302400134802c0b1b54054513000200e0300708103959000300303605240500d814601040d800c22610006e240070042c001c070300c098000400b01040e1480e4100b075a0890b840401038241000d840050224000034400c0b442c0c88052070300c4d07540010498001158020041144032055405964451940d83d524070300500e06d0800b0000042e02c42c00000006d200d079405000c100c903102800240720b524010b00a05000329403103400d01007124103110241100360400480c0d8400241d021040780c4c055500401c020a480000d0000112140f0190f114554000031440512042000100e0323294400c0b4001c80381044596 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 602606735 1250 602605485 602605499
    0x507030605100e01240306150305071806020a0b04030302071e300c11030106030c05130504080703050a09150206070f090b0702040f0b04050c070b06010c080415021222 73
    0x54001c0c001c05424810044000c2c5c60409a0382da094885c5010307107404a691030369400c0d82c040d007811001c200300c000b0307885008028001d40c210800030f101460362135120411915084000b0740b03c01ca80000180804000360118040c58881c0d0140c0c1c200c00e03003000c40c43c124442480d4035101080310940c03085840440911401c15030082c0c50000c2282c0900412001f00d039001100c0c4200c1e095016440c00700d940c803844903200d07c2151001d21941000d14403500d190400d4500300420460444002c0304440c0314942808100300015003c0e0050302c00c1c0a80c10304000d03031501c4458805031954291500b08803604030540e00791585c45640000d517035005650759141c0103420a041c11048822071a14010f00860701c000300a4040181000e134400c2c02e400050510000e120781100000409030b034403e4034540b4900c440461030b4410311150032002504202d00b400c00040e0900d80d0b80e82c83c0c8244c0114460b10704d88501000d00c84013114001c0c00b010a051514411580d40e502c8083d1244510716130a14a11081e800702040115400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 602607985 1250 602606735 602606759
    0xc03030a080a060801020a20032a01060305011a0a0803040602030405130b040c0507140601060807260901020703110313170102360108010806150105370e0a150507050703060510 77
    0x34843d5680a0ad99141084140f10700c032064490480300d843d0341c2c40c1c1d00000820f200384908165070070980e078510125849130307040001003030305504208107a80081100300f05141d0000112000c813441903424500d0004c0c81108040241100d5280540150a00e050038040300d42c04401844101e111b06051100c24103000c0d0700350398406090182501282101e00410003060180c140c500f05400705040011441c0c142041000c44a0780c15201d440450b0740202d440740405d40c10550544103003500000460500c4401709010384045034901c109894460044410142c115003034040300d0300c00442c8080000c0400c2c1801daa07000e86003420760042c10641e02201e080c461903101c0c1c0c3c6c40e80d04880c40d180081c181d589850341002c40d901500940c6c18188401088030a04040c40310042c0c440c0450400f0301035100150110822170050b002800c8078041244010703d50402d030b56100013070310986034000005504425003210940d950301c103500000e8150b11070542e00000708002c0c0c0e040139104079451b0b0501d1205907a9512400a6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 602609235 1250 602607985 602607997
    0x120b01080a1107060608150108061315020c031c0b040b011e18030803190207120c05160e06040e0a020303070609150e030c0c030c03030a080a060801020a2003 69
    0xd080000407039940021600400c60404003107001d00e141c000190380c0c9108450b81948412186e400c250782c55040129280312050042c50303154040c280901d82102010504030070340400a0141c24000a182d070003860590580d10b41e091042c0840343d031000e01020841884080180e5103810905240e0001c02c2e03030805000d26040300c401a15103001c081d40703201d0410b0b070034240d000c19207041000344559101c00308074070000c0000460003042e0007642c0b4185030740c807801083c40000c5040e00d0140100009000280b0580d58499040098035104a44000b1460502d041c000c0c41040380d051103250070000316007442c0000102d401030f40b049800301704490040e407955848042c40503002c0d626400610100020800503040100b68912410100c8545112030303c51200b10f0720042030700e01c02d40c0e1003c01ca04c0940071003002050034050049000700303108450100020756078840e0030140d07410068048045000c60005170442d0001c2d2507804002e40d103800c820300b030090420030304040c0385c20304180794013000200c03c1000c011035807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 602610485 1250 602609235 602609237
    0x312080928020904020303130608100503010c17091006090605090108071a03071707030606230d020a140706151d0403050703120603110f0402131403070b0a050a120b01 73
    0x81503007042e8082000e91400100300741e8050100300083c15040d8482203548001d0403030f80d2a41030140c107020151035402d113416000540603070326020840761032907001418401d038100d14256000241d6200742d203013810000e861898445150400c0303008109010b181d080541070318010ba8101407582e0780c890401d6030721075552042d0345000005035803040a2004040c0195440441414490034210b104480302d11140c9081300c4820010ba6552414401d0390740c802401c070305138803480e5200800000b078083d640d0003030302c074012003e4850b5500041d52001c0c1401180341c50b00ca06007492450780c60f18840d081460181000c65142820752030b0304080400c00b482800720300f0404030180e4551003465590f90f5002c0e240c507070102c80c0c11760510ac12000e000320207026601910011310300c02d140300040d4072162414019000114440b40c0e01c02c600501c2195444010301d10884212884007103800317024814400443d042c045103800c40305910800203059040c00b07801030300612240704150788441c1c400034141c6901003100c151106241c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 602611735 1250 602610485 602610553
    0x8030a0c021f0929220201080f090a0b0a05040b0c0a09060c1106031f060c02010215060105120a020909060f03100507270503011a1c03050403120809 65
    0x120101000c3d074880030f02d6622544006003c1481041d44001c0d02c4420a408042282d440781003000300040203691034841c000c0004440203003400c0d540040c2c603a4130010584610403554200003a40301204000c80001260042407a000f2400c01e0300c1500b000d04002c98040d10720981d03c001240c4089841030895515101c01d54406031a0380c1000812904a2000001501d510302440780b201403039a41c940085009505044103c3c0451803004911401c92400d035204a050100000098025076008035082040e40002038001d24103a0319440165900c0c0280080d40364070318046800c02056404a030700405417003200700e03500c5045946000820151007078000b80c19405410207801101483c5281e0403071034016071282010303500320440701007030080c0c000316a5040b861a60700e01d00c00c20003401c1c288900c503000300e40041c241c0758400441c408110f801c00842e02c2505501100050101070621910546010390352020600820036600030000f404c203007003507481d01810300450480301020803a94480944a9815003207203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 602612985 1250 602611735 602611783
    0xc080712020f0f0409020c0609071206020904140403080708100312110c040c2105100b0d0f05070306080d02011a0f0a03120203030403090b0301081f0b040908030a0c02 73
    0xe000a50400c801003114200240200003074120114050006070540c0500182c41c0d850149695103001ca014109491903040360300c1c180020300c0049210012907400c080096614403c840c00b140c01401e58070211034030011054240700401d980b0001c09030148a86544020640d01c4100c002401b580c0c4500c401840301c01510600d884050056416800ca02c601105503089a04075a000c03030252429a102000041c200d840710004060003060480c0c07040b0b0b804d5208108070315180707280d0b803018021401551040600440d03500b002c088640c01070741c86a66018401d014509103d00d02174003400c0c0601070310000b806081e5001c1c554910511500c1c401d020407810036030b0141401818443c1c1c0d0740c121001103130000354a43e0080040303505042c5002c4185107c0d80113507501d251905008124031030540046d00000020070040080c00343c00115084d695080080490428115000210051440d10300c00b940003424204040140811080514070808240000f48450840540c0480c0c50b07600750003904800382e041080c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 602614235 1250 602612985 602613017
    0xf060c03080402040b0d0c2909061e070f02010813050a0204050702071a030a110c0a110409020909070303030b180114010c15020918150d080d0c02030309010c0807 71
    0x100760b082030018000280c040101004240c5429002c0015150140458010042410040465a14000c403a80d0b40320342607400300c4026a06100342c19540f4401c44002c144030900c42400c1041000544540301259038441c5249003000351003940d120181c2c003040c149000901e0f00c10907100325100e00c1d9406005058449059400c0200414020f00908214411040b000c50364008013030030505014030316001141c40345049420882a10742d01c140f800c14100303042c4a40304040d9800200c220b041980b020400c1d00d441d6801010800400081c10701130b610401c84020f02120540c00326400065070f0003a0303400d1100080100070300c061640348001d00d040306e03012800100b1040c004445096118001490113650461070b0351200080c02c102d00c4560181c0c2540000c0d11400d52800b100d8510449200b42c0d04407495182071010070002e200800029402034500d010050f0810404204076a000300410004120452120b0030007542c0b508120f50188880d0300c0d090440313120a0250408a200708600c2d0b03612801041e001c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 602615485 1250 602614235 602614247
    0x5030406090303020915070c0b0c070614070807081222030c080706020301030b010f0801140112031416031106010b03070c0501020c011416080108060c09130504110a0f060c03 76
    0x18040c0c2c02c06030b00b4001c0d100c5e195100410042003040058540391111202d0801000c441201c3e8880a40d4501c1013016800c0f0560208040c0100c2e0900d0405c0c0790300e100d03014290b5100784103c841c0105405400280c0724108500540607015014a0004140b020754403040610351030480004600c0e40d100c040c0b00400006403158007000400d5103e80c00a42c18180c040d5a82d0042e070b0802c1c0c000f00d44001051005202503108a188a0000c214000003404117006280c010781d072204040c01a14100b03002d4110300c1042c94040c02042480500302e115540d075902079608281011903800000724001440640000c01101000400c0d50603244110000340c911344411009031050440f1803000c85041d5001d01040120f12000e10403811103102d403058a000900e4208044403800c408080b4120078824110014881e001c00055107a40c899900f6401c9031b558100c210001d80c135280340c86184041e071030502c01000104161184900b8084205607142a0044d4540101210079900c0e03018900000305181c00ca2804a8800c0c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 602616735 1250 602615485 602615501
    0x20903030706110403020913020112114b032a0a02010204061106070905010509061c1b08040b1302040e0a110112060609051009150e1801050105030406 66
    0x2400c680c0341507803a560301d5096800b4400801504803001c1020415410141200b5503c161060000c030001c90480d800a01105684a00d00d880e02d503460303c0340150300085400b1520940402c00d03100510945440010384624580741107900e0310b141403044017840c1c56216400841076409401c5543c2107580b0610126600d01040d519140f80f59002c6022914071844e1400504401c240e0307500150790349042400142030f494071a0750f84001540002c0401403103c0d40324030448280c423000d203030072176032000b10a0004106005105040c03492410040c100b20300c042d615800700301425020400090140d5228600340e0311000704850280070310341f030303079000450940904243c50401d82c80144006000c804000c0418a09951100c0898454041e050032000075a0007546804000c6400300041c03080a0070620700503c840110b1107520b000b0003040c0035041c0300324052407848014024400414150309035401c0000c110941490460340900101c203081c13440b1102442000c1e058502c181c50f12880c544581d0f98900081c103e003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 602617985 1250 602616735 602616739
    0x305150a02040b07050c091e0f06010216170c0d03120509070e01060309020406050901150302070218070915180b07060906050709080624100903050312070e03070609090209 75
    0x2c00c40440c03400209409402c05034015401440003a25030f4040c050107502c040c3c83d8034890507441042d406411200c5c00b01d80e034450521080c030419500d8110060b031070f08001e091a020a505064008148a00600c100340454102030085172460000d440034402028503400c0702a00081c1990882c45c01c649054000c0c0c2d03040310f103000898404030b0b078480c0042100300f401c4c1c0144000945880c1c1c04011b52a06028010151104540d0380b049545000406141c40041e008501c09058010400900755550141c1c241000c501d145250405883d1500008110250a00803007110b000e1000300911700780c0c4900e048400b002c072808443d4007058281600107100e50031000f4102ca0081c1c0322410b039000280940111801152141c403200b40103030a0650050500ca00140548141806d11788203105460705c0c04003e120b452001d43d501c14140900820464890721282c00c003900714030000400903442c240c40080540300d10655510250124026400c00d502e03031006225500001e00c29513018042c40742035a00510481c000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 602619235 1250 602617985 602617987
    0x31003030c0f02040507170603010b0f220f06051c050601062d090611030702130902030a0b0906180c0d020112021b010c08060a0b04030b04080417071401090305150a02 73
    0x82d43d40002c06980045481d03400140c0ba0741c441c03241d984061744241c0e401c064120002c2c4003145130900400c4207200a410b280b44200301610181400358807046e070620a025a52906200b00c804109030b85000d000c0600c1035500869060340d15514000c00502c072503414039804800340000b640780c080100c0d8110f2180d240b01d8080782c0003500c000501e8110050300240c1e00341503142c0c0c042d1321b8034018000d0f2a984011900c040346030003c21a200041e0750308039041451100d62000000c4903d12030021034581007202500504424020090041912002407510321818001442529040c039440b80030303445411401c00e980d0030031114149100150300426681001c59038648005041c140000c2d604a003240d00e02d89074085595440500080465200700314961104050b1a1240407030701e0907010140c40e10640c480034015981c079a0105040140020456006045c800500d509200424500c41d4440c0d01d14814032044400313584242100d03500075000c040840350000c0250005404842154602c190300825000c1000d41c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 602620485 1250 602619235 602619263
    0x40f031709060d0b030c060705061605040503100504060f0e100b190f0e070e1e0621060f040606022515050c0c0402041206090201020109020a141302031003030c 70
    0x4030b0710054004200355200103e0818a20ba050504202c0360040460141600b00200c0c008500001420b81e0000340d810800c0c0c1804802174000c031664003541e001981c0c94000c5210885010340e035504014000c50040e001000340784154079260b002c0750b91048548402e904400c3c145190f59081d82d0160100e2003011f088500d1000040b10380302c018580580020b1504004000103100c5d144010442e10b42c45006428005211003603000001c026103480403d500382c01d03a80111100e41901d0780400c0d10184440402c0d1103030002c0c41105030518042003104c1050090503250741102c0589041d0242c9421104079401815000b20000140201c0000d0800401a01407a95800144160413000c001141c00c03942d55800761186000700100c0d0600c1102d0310610b124500500c81440b0880010081440700e503030140700007400c2426480142d01403c0c046c0300180d4082281040000c2d81c0159010465101d40115002000340c0328801007003040340425940ba40803212110130500010703010b5095412607a00a201c0080942 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 602621735 1250 602620485 602620489
    0x2090108060f121606021b0906060c0102040f060c05010c0e0a06030b0d0506090a12030c05090103020a1704150b030111120712150e06010e0108070e01030905070e060312040f031709 79
    0x15003080e140e0b131030100421800c100e41c41e411301c0b800c181001081407903188000048001040c600000e040d0910480b80000d2041442c0e1b404d504503401000040804d16150741d9030900a04170301c0b06071000380c2d5694208049900b499214800303030b4207002001441c45a100f400c081080300108003505d546c0380c00521000840c40070030401c001041c444c030309240081c240f44100380390007076080d010070f2010801c4c1800c003d081546190005c1c1961380b07651081c42c1c0141c5583d650a0102c1301c080d0300c2c003580c40b0742c0515a0180020300003d116031404134485c840c1c085c00015480c5c2d05150880e91000d000840e43c1034140300598070140d8404055802050518002000c0da50880c04c40084603030322841034180300c0ca03030201003000000761a5000d134400408d09049070103007801070010304880c10082c24082003143c144003ca43e540c2c0030394003070b100b0701e074100049805054503000549000401500c0043c40b074424038540306051a808800c03582034410031101001c9280c0303140c0d02e0a5a02410100713940030124140701410301c036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 602622985 1250 602621735 602621743
    0x20d0320040311120a050304120c330e1c02060c061005040b010801030809010809161205060a0204031a0702070302090405030d0c2f07080312180102090108060f12 71
    0x5140a02c0b0f51400070b810400c00c1100d01d0140b5441c8100c5034000c0c0c03104001252020054030116001e5840e4035502042501d4904803154050704034000d1140344a0141c0200d480520608264100610b0850303030802d00f86500ba00e0071071854003c280c0c440d0320f83d020324140601500d609141540302800250030701c0803090440c0d050440c01c44003c08400c4100c1002c20442c0342c94043c0344603c1d507081c01e00e41070079415500d80c400c040c8a02e03660035050285440110b444d0304403c01181204201c4060142c50f159210452090000300b80403051381c60340304280115400d88032034406c4501301c0340c2c000c4070a000c0ca11030000f00c4c0219400201000e042d4000c18100201580720300c0c81d1180b041e0f1043d009142d580d0240710042c02281d5002c48840c00f0031501840019809014403907043c05e080d900d00700035100411070310100d0315140d102d07040032405000100d10b80b150079100c500034901072810328295042c0d4450701c107203c40c202d010b4144c0403130000e0640408124507051247c81c0481e0380c0170261032034944411b07100d540c07468 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 602624235 1250 602622985 602622989
    0x10f030201113f12040201031e0204090b0103050f010b120c0409090609050d030603020a091e0c020a02030601150c0b13052a0a052b0501180b07030507020d032004 71
    0x48141028074000c1c000300700c1200452070821841007a0b041400791135a03070710b8488005200038149551604550001071717288404555040240c0310075595035031520040b0019004400035a4042800d0201003070b69110850742d4a81a11500c9040b141802c1216209040c2c0c42c80207004080c11003c104808102591640100e41166000d0180070a2000d01d45c0b603c50324240981c084a020140740500c1400160f54080c15131040314c030a45404250044000f00d81005080c49605811440b0300d0480034000280d0045a0f805240740202c00b50382c1035030b0303854054950a5490107070110000c1e49100118001a062007901908651502e002c07004003121551034902e00300600904001400040c1109015002909805070000d0f4040c2d40148401313142c000414110451084d00451003070342c074211409180302201f5412061a00800284034501198030b00b841d580b000c1e103e050312291074100c009504140240540c0b40201082e03070040411b880300390000c40084c442c940306001d21104440140a104201e64040c0c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 602625485 1250 602624235 602624293
    0x603060a11121611010209130c0909051e06010518060d060819171e0a141309050705031e04080412030e0a09091a25170c03010f03020111 60
    0x224000740e84000d86a16004d80c2c03601c076660300420540100c2c4e1034076524100e10315010507000c02c50700000c2d60180c400e80e40d41d402c04000c1e5482e1000b0417642e900030420100c1408034529a0355256120b100044a80e4418084001c000304480c24081032103003003c400078944448010740001e040340d01c842c1242d08140c03010070200001c5001410684c280164070328026284c03030b58400c2080c60030340d010085050100304200d03111140b11011a5460f20240240e40d03c00d08005903010703103035940c5201c1c1103228006119000d00342c2c3d094034150024503000c7c02030302144d019410b007070303985418000003200d05c41d400c0c4802001159440c43c00c0c880040e224040003004a1010701c82d0310307aa80b4001c410b03014800745000660100c01c07010700703281d00600481e803010058070303500c81050300d0000c0781e42d155038001d002d0741c0d070b4900c0003034100e6060410701400c1e03940419000b07038071810241030b00c48923210440b007455540028012103003a42031207031080006600070f04000c00044034650a841042450000c01d41844c0c00c0307144141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 602626735 1250 602625485 602625511
    0x80417010515100c080903060108030a08100e0c0304020a05040216020f030a081c09050d030905210d020c010e06040b06030d170703020901020102091f0908060603060a1112 75
    0x19665200030700030580d12480002d04102d02c4110000000d4506460301206020b010b45100d4580610406070202d0316407120140480d192543d503402c0c3d0982e80d51000c00d981000de061303403020417090780b014565402103510040200c4103a8070f580c0303c4a04a5800030704200c1e40000c881c07200094503225400076240c00c45440c91400203000d15401840030311240407500c0c9100303070003584444002400700c2055030004401407265042d0641340c1d514410080542404c06401442100f480c2140980e050308440d0b00544994103546a091503034880002840005c204910702440510003c880d4400d01d43c09090182500400402c4100c1c0c3c10a10508001c41680c003074442c4105802005407504080000b00303441c00541c6003400c0e00da420304208181220000d4418410150001526445070b8403d40507a050210003c1500c0070b0300c61520303a8002c80c18007007100e40c00492410b0100260314680031901c6886003c0140150209540c0c0ca03404000070b004c5000c5560340d810050190078a03034152101c065201c0d003900d0703402c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 602627985 1250 602626735 602626769
    0x213180f0f051807030b131a090d030f150612021303060203070e06070803070e0d0219140307030302060c1303152a020a0b0702030c0f01050402130b0913050a0804 71
    0xc80d06194282e4100300c8203a01504c0308200058040380e490368801d613003504414801c111880c02e80103000c401c0300210b80610060091001803c0081001d540603030b02078404000b2001044c6180044d600711400090150006e80170402465008580145501801001c0186495042001e5000d540f03c00e40003920b90b181c0c04801c0002d08c43e0014141ca4600108803010360070030001da6a00303070035440300402940800c0221000c1c0c04858031100664402c1c2c0f9401441c002032000d0070590303d440c00601c0d1013801440400c50301240100d04006c00d1120503282c041e800741c4484e0303031250310b5005154019940e10722280440c000000100e80e1038855031f03401c0f50070a8004950044541a079218802c0e103040681c0b55110f0920003444901d4000070072201d41580103851032106d50301d494099041d400b035800c01c41c0d4240600c8403046110039066010903c2184216005241c400c68101030004648503000c905401081c9000428503c000201d2a202458811401c8071a80b04c100d598406094010364464929525405a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 602629235 1250 602627985 602628001
    0x201110c07090f05010b03010b0c100c111204051e0303090d0305030108060f102d0915090c02030a0507081c0f1d031c15060c14010213180f0f05 63
    0xc0c3ea80c0c10040c44803e0010f03505040180003c0d1106104614040d4800504030003015024000088489060502007010058061024060b201ca0880700c0d00e0300d0190706000d0486429807810380f8155100a09030700140d8408440301c0c004c05001d1604294188028025030100380c0e210400e22501c18481e40e80c003501d951401140c0b42c9800000362004480032003980801402903c0c1d41244c0044a490381c00c1075064406030030200464400c111040880b07041038140102c0ca00c01c1d2900151405a003c0d94002c0c2100da4a583c03c034119014020581e005800c104a0900642e00c110003820503103000c0d603602450f100c00407010088030045607484c0682103032a1743d4007105080681c0b168002031000b24a0002102940912807500e078851440c10300400c4003441e034102ca06107003030f9124807045070301c031034020382025110302020300074800802e81211180c1001002c02d050b1601802500d0740c800c00900020310072820b00841400c04490804c10800240d178074200e07402e03200c0305406820001e01a58000144504040c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 602630485 1250 602629235 602629241
    0x391e02070e0a09080a08041b03082a250905040308061e030703120306030212012004030f08160b070801060f05070809040509030c0d1e0e0319030201110c0709 69
    0x10000c2d0103589491442400b241d42c010845440c001c0e0362070840819626880c0043c656030312032442c5403c1403070110002c0204107010000703214500101140c20b81d8096140d00c015018003801840a01ca0341007030052142c901c1d0041891020350a0207810115115110030307110b4101c500c00c40b030540c00500040103002d40c504001182113000d614a04034085030100c0000425a1954284001082000f00000240c226403180e445500070315030041c803c85180940010300ea0180001c0202022280b1600c030034030304e03083d110001300e4084941c00081284003403407135220381449800001100c212200d03021406c3c0c0010712001144d41c401c0096844020300c2d541000c80080100444000d41002d01004100c03000c042040d190a540c0e48443c02c46000c6100ea440302e8000d81580110100000c1074030801c0b5008070082d40000705d00d0416002840641402d40070038034201e82209010f000725402d034114070340c0b8901c4080b440c0d500c112694028000800c0b084014400141a0307030000c1c02909003500314400501081c04680 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 602631735 1250 602630485 602630491
    0xc152009040b0a230f03010908070c05191202041517060105060a1b0206130803040303080c040b0711030f060106170a3303170d391e02070e 61
    0x5100306481d5410701d66010805040350441820941d940315181c0c1441c5c1d0380600d1400d0340c0300060002d0192192514001100ba005004121400b21100c680856903041c07140d4010b0250b00744804100c1d12a01d04050000b010601d84026a0015261404d810399284d00240700c81c02011600200744800e81103c043c117007004010307001380c1c1c4160f804000d101046e5502142012800c02c0505003c56001a90310005102c0c0c0b080d100f100c10300c905c0d5242c00040e030074008006001141d00a40f5080e002e9a20104044507a02ca24040c00740756060038400c0102003a880c0402030001d407005001c40b01d40c0d42011446a1420300243c1c030807000a1145440ca4080c0902e1000030303908204401002d200320303c183c00c80c200944800d94411001080041103007410110000180c1000f107402c100d0147c0240c503c0c00001400f980011202c070782c4241825400100040c902280c1803001900444403103580d840108800e107000b8602c42c00300c0800040480d40300d502c218000961242582c01d4000340a414940110300f80408401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 602632985 1250 602631735 602631739
    0x6090911090a1e0b0604050a150f0e010c060b040e01060b03070f0305040b0f04050715020a0c080c09150f03010e0a050f120f0a1704060618020a0c152009040b 69
    0x4420301051805a408810040c20203d01011801d400004045001c9010f95407140c1d5201c0d40d030060010389846108102c108880d0240c5c2c81c00310f142031070502583c803000760504541c0010f160346c8495010070f8190380096070b001070061012812409601e5090309440880d080718291100020034086201e03007001105e0302511883c00d0a114902e896220061200001404810030303030310550000f01004000d00030b29028220306422040d481e800e1280083d40c1d0a440f480c2110070006144010484000006200d0452400106042d189035209000e121402941075481904400c1c2002003144039039080c080c2d07465035102500100700c020f82c0c07401c0080c90110342e2034038514141c02c2000c581c3c001046020440e103030103007c540c0d5079581c2c0c01042800c83c0c4841180b2036030000031241c0784c00d100030008560001c200b124000d0f040104c1202c6421220b208a110f009104008a031003406c41d540010710640014072540c070141c03400900003401c2402c0d6041c3e043c10b01d48160140b880084e030340885141c5449040d03024881 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 602634235 1250 602632985 602632991
    0x601050321041701091203050f061e01140d021815030402090103120c1202030c010e070501210b060a080412080106080f1b0c0a0512190804030306090911090a 69
    0x4034209010940c441c9001d54583c045001c1501064144250040b003801e95001c28034001c442d680950041c010003054840410780c0407144041401490310090350342040c0313030507100301c07604e110484015140c0e146a002d854801e0710050181c046000b0583c8017401410710440798012801c5c14040030043c50f80b5440c801054402000d20901016894034020981900d078441007095508811220030b0340d4011042000801c1d9520650b06c010744030768040050180c44890800900600d500d80703d070507480710b249005081c000307002403410340c48882e040c1c071090945080da4200003640588400c085032141e4042803041000c20300250610007004a10341080019035964070303000c0465410860010050403005d030000c040c00c41c030071001c180040c0c0d4405000038045d104441107550ba5119542403a00c62010420030b680e240100c0032245018031000c400c030b8043c40c02062441d4000c411864040c2c500c1840608154101a5510f00205110140f8414500c0050045900c015410383c190100800344030300909110341941 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 602635485 1250 602634235 602634283
    0xf021c08061318080405030f010e1b04020f0307030c140711011202130315060504050105060a05030c1306050d05010504021201170c090f0105010806031c080a110a0206010503 76
    0x1034400c00c400c0c1c0200d8112a00b200e1080900c4881014100040840c1c8088501c030481004000c11000103100311002503040c2c801390728030210742508a070602c00003155a5004079035488520300206c2030500e20003c000f040107084c44c00040c00c240940e0000c441c3c0c640426542e001e01c402c515040b0b12540f038003008074103006240030440c0c3c0c1e03420301c42e80700f040c68941484410744e50440d103c0300316010b9134100c2d0011003a41400c0c56903801c00d02000400070304e00c81640c0d803802c48081250b00303050080300c0c103844000e40300e075107008400c03801201c0c0d9500091102c1d40218040c042d0034030000e82c104d041401490b042d904c1d9522200b0759a0500112001030303120510a510400035401d4884002980e030781140d6010040b101c642405003462810202c581c2c0d5020761050b116010800700310039190446043c2c40c402e0303071040301c10350303540702495034a2410244070302205102844001a6601c079a0745180e010f40d0000011030402c11804c004c400f10313003040c0628800360300840010300003401d0400010752048281d80b07a60750144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 602636735 1250 602635485 602635487
    0xf050907050604140613090507200c1c030c020a0807030b0a0218010c03030b03030d060807061715041e0905010f15030809030a080f041410090e070e100f021c 69
    0x2e821009503020b170303002040300300310102d880391960018410708006220038582810010202c1940103107000158040e54000242c800c00017428404900026110104040110044c84410401ca010442c10000d6001c4000010789400c145035005040120040c1121030071031400341015000200410703a943d20501c04861504030303c0500080c034010a09000244881c035041c100c01411007001c010381c041c03000107007001c8000042c0d0700100c210b82810b0300f652103981e1941400c407903526000102503e840900340124000340381024980d0010000200b00169010110014017403102c00003040354010b9075141d03120700a00c00280124004940c1d500800c106e0841318185005407070566000203402c003980828200b5580d10108411811147c02185494840b00581c0394100607074007501030b20000c41505010740300d881c10001c1032295212403a4a07207e080c0b40c14040070480c00c8600809400070000f080301e6004254580f240f04154201e001c2d50b07640b52000c0803040c042c0c501014404103030300d80402002594030003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 602637985 1250 602636735 602636759
    0x603010203070c141c210e0a03081e040614070f0203030c0c0f060c0702031b0f0d020d0b070f020106140303071113060605030f06040905060118020d0f050907050604 72
    0x185910280c40101d1302c144c12082c80c81c001019440c00d1100500c5000c60a030182c00c0104c1d40101c81100400506c0d1801c001103010030358290007151650f0380d200b490501d000a003c1c50b00c0c0d135448a440c3d24155100340110462101044058030141e583c2a0749009103042c03031a0840610303078800104e00305101080c41c0d05500079980d204c000c007001c401c40000310343c8445900050010480740c1e400041102c8070b40c00c0c910f4032005a6885820106e129102d5171000504a01c00e100022004c08001001800813020040600c0303180c00d00c00c68100c4c0c7c04007055403158001400700203c540a81002e540b00c0c0c9819a1015002c0e0864165030804801c0800782d94900301c95035000001c0701c00072070788100b21400040c4d00c8400b0841e042408a034030307900d860404002207245d41d4400301940c480c80a585008510340c80f0380080c40304031071032900003078100c0e00700f03000600142e20030950800310f88030044801841d003030a12403400f0850303c40207400c003007445c1c95100340b12000e901040040098001280d00d0362400d454040b4245171 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 602639235 1250 602637985 602638007
    0xa110f0a03121503140f120307140702132009031009050c09042603010302030a03030911120a02030f06060d0609110a093806090a1508010e060301020307 67
    0x8000981c0b0381d150a200c982c0e0851011600725a111058464891401201c6603400b00e080003a14480c1d80c9561225070b50010b02c0160041070313200c44500d140c454090441d01d045044080000c2040304012180042c0c0740c8038454020200740704400107824000c884107640882960710300d00c0c00290140300c1950240e8001c1242402c6040d00480010841e200c0d01d02241481107603000c440e4022800340411003440700e0307240c4200309c03c084c080c03e281d960682429410620b02080c0006500344c0d00040e480b200003030080c0e012500e603502501c1c59810528081c00021a07144412458400c1034001e081381204500b0200b200501c103c1110300070303005501d041d10100725a00030008024102903213880384403045c4109003500700002000030300780404c041d84541540c03014240210011980c03420500141000d007001d0010004000b0104640041c100e5540040051310780141c0c1641da40985050300c0050800842c0c001a03039400b881d81c45440c00b661400c802480c1b5410010700e07440c002e0740100100162540d00c291a01c1f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 602640485 1250 602639235 602639237
    0xf0e100603061802070f0515040507150801170705030601080c0306150d080f0c010504300807110c03070e0f0718091a040c1809060308160201050c0a03050a110f0a03 72
    0x317100d12980c2401ca00d0801012000780190084040d41e41d1a0303080c94924038841c03402a0200c58041d56281d003003500020710081e0301e2000964840c01403101d0400c6c0d039051010308004074126841262180002400c145003a40b00d0b82070360b40600080422406d0502005a00c501c0b0007042d03400b252178a0020698050814000030b2030b14100182c0d00703544a1202e010b07180d11100b42c000070030081c030305403a1002d0102c000c11211094500c0c1090500510090080f081121207996030300d0804030b448840e03090324004070008502c1c0e032501a00f0315149807034070100200c5c030050441301c051000c01e04080d081d030800410058421410040d507036038184c984909540c42c03001284c54021000440b00f040c29848043e61030110142a8803d060400000c80541e100f0844200c4804424001514a982e500008200c90283c400105401410b100b801e1303030b4907c5000700181e01030040c18810b1500001d2071000c0e061620480045010440124588100d594401c1010390a891108004c10f1400c0c07480803070a94440155030010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 602641735 1250 602640485 602640487
    0x120c021203060d02010504030507030b0f06090402130f180f03031b02030708160f0501050115030c022d030f040f1208030f0a020408030703081b1905130f0e100603061802 74
    0x131648540d040b10011a001429181c5041d01c034940880c4c0e1440c01e550640c07070484118081003403850103248850145900400400381c5141d6501c13040d0185c0b41d80750076441c07510b036a0340416201d00342c800c1c24404040c2c07042d29000707080c800c41e11380a002c44022040600b209048221140e90517034001048901094100640341e80700d6201c076a0b142c6003c00c1c10b071401441401c810301c070882008815000380d41616502c009000c0e4031408202d084040360350000103280168000350562005c0109914800d1800c0518017201e0084105c0301560352640e4020841a5640c041c000390400100710b5006200c0041e000400f6800605c0000d85c6920445000141490001a540c82d020411650f0755038100c030001d040c6081903a480b04a9070501030310101049882440400860350303a203807101e44050403105c61f22031407201a9001400818101d4050f000310508182680300ba00c000301b944c1c120110401c000705500e0002410b14907142070b07811300c40c01c0c41d40e02c901c0500d41416011b110070307090409000403015a800e001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 602642985 1250 602641735 602641759
    0xc0307030e01110a02010f0b030c06041809050313170307020904120c15020d15051f02010b040212070f0f08220614040b090c150d0b10120c02120306 65
    0x240140071103803003c81100740020305001c40350380640006030000585001080306006110505486031408081d0360391002c0300308070a02841900c4900c90030104165503001034442c0c00e503961589181e01203040140707000170890081080b80c0410703c010103080c8c03522006d18200900da6001c20101e0ba80940003c05104d5039a1a00023060320424240e04029002480007030f40b002090989002980702d400d16001041c18804c03080071034010b00071b201080f100041d000f40b91196442c07100001d0417100556000465413608801d00c2280c0d51400034000d944030300701020b529030520040281401201c101c140e400c0c840c1d20300b5100c24068019418940c0841d116486466582095a00000d412800e62009040629200c0f102c603840e201d44c07410b9031241d4401c0c5502c907400d0311400c1c035242d510720282c00e03030b55845144080389000c800420740243c0041043c0d001e01040e03040c40c01c40003a210362156000c1c0800581284019021841540204001d540780f1380080e09002416070f402d0b4500e44070050240c2c0c0210031701540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 602644235 1250 602642985 602643011
    0x23070305120c150a0f0605090411060715050a1e09020321090303180a0503340302090a09021903020f0607030915030509070b03010b03150a120320060c030703 69
    0x2d28a004604a1141880c038003520144d0042060900010700d01d0301e00140840c07541402048035008a4122810a000000d14001c1214039030200c50212101c051a9841e43c01e2019103005e00c50068102c0540072403290640b110009055220301c10a503000c2e82041c0c0a0341c0562401300c0c80c0414110056107801101c1010041c3c0e940394441d56803456010312000030b0005440c0103982d0700e0aa20801180d1410b143c5685000b01030395030b100c0d002da80d42207800001d04000c680d403868103229031540002042044036645c0e600007030040c44003211034000380c1e40c884240c1002c6260401442510401e8080700c60045801d40e0007069049007a000600e0103000001011400d16004464102c0200203440113203841c44200c5038001e0182c60306a504603d1442040c1010600f62004070940e81038500c0028050700796510040031204004500c500642c11071803505001ca0b400016401d102c110901075282d5000c02042da03031404072010b491514141c000d03000792003805102104441120b030451030a01e0040b4091114110b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 602645485 1250 602644235 602644243
    0x81804020f070807020a1509140f270a020315011b0b01080f071d06040203070917011e06030201090b07060e1906050714040611070503060423070305120c 67
    0x401d0201c0701d400710307168003004a150300400e1164800e550b41b46a1681e1000c00750b240c4141c44648001103040070200340040c42d16407903108140c01008200b4540c3c00c65680100d0804401412021910f00380c404200a00010006600c0c1d0080d1110008503e1440c103004000d0082c140c17400e00a04003e62204e140714a86010498264006c1d00100b0800055075206400c45d9500c5680c8903031905405521400100c01d04c00e000d21105486c039100c0030401035034840040100941c402400c80c011310244000129580d408480c4404101c030049000083c20344c012021011141c0030706603005281380c20440d051006076070002209007224403440c0070304c0e10b5910611f000c0c400340032800342c8038466108400d40c0051003440caa806008160049200f04039607150340304210364803801621900c01480041100f0861070b849602000003940400065840003600c40c4002820003505880a84405e442b008903018420800041480460150b8004000c0f00d440d6548507030b03c80d010a400d4a0007940c000c64a2295044288 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 602646735 1250 602645485 602645497
    0xc060f0d0e1b0d0606031b08060703050c03060904150e030a032a0f051b0a03080603030705120c0f0303010f08010c05071104020f160506090f0a03020a0204020a2a0614010308180402 79
    0x181003800118008007071100390381901c590208c2d40301d160045403c4602a10816000710030170752100b8615035600c002e00442c4000070703004840d19000c4031041c4040340c10720702c18200100c0c010005555508010403000f8141c0e02e101829462403801c9150f2401140d00e44030031184c40769020b00b031822410380d1002e4152114003446102440c1103810481c4060107900c0811030211241c030075180d0740d81d50386410b001e141c1e5130300400c8c00091199004040400662400e0f00180071846130302400c45403004c20002e1824150f800c00e81c001918098015400d000d00e100070b02a515114204c4e10384981880c800b900c4640744441400481405240e0014600103080c4011084444c0540b824032000920011071611580c0c2e100304884451950140040a003401400442c0800c8816010384c01001c40c80025001c10009512114407041406000c1900c445406840e0030608100c0105d1452403004806a00340301d03080e601d01d20512422017492000500005541c0340c29a072201899281072160700840c840440e009104003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 602647985 1250 602646735 602646743
    0x703020c0a06060e0f06060a08180a0605060f010201020a090b130f060c1b060e120309030f0d021c05180315010b040f09050112030c050c060f0d0e1b0d060603 69
    0x440710310700740206500090110b641d4240040c8141c0c2c0d030104550070031001540c1072540400104440c2000c18400d51000d40c0104010500160f51400420350600d0900c4010040300d000f070316242004121300c0c0982e5207000142c001c0c00254036001005400529081e0071740910440c0c2d01c4089804140d1038820000c135009000704000d01c7c0080e9480b6540039000000e1000c044900001024810201c2e03582c81814404941071a200c0c0841c5004060800c40c0c0090a20882000341c8814400e908a5940c02c12540d40d070b1440c0d0304050410a00c0c1c4403c003d040800e06061428041d2181c00300c82d123403560003000c6071400030401c40200800d98100001a003040e0f180b40200e04c0c00f4811100200d84004404001e204540c0481025041c3e55550b115032819103000b44510300900c20300d5102d00c40460701a006d0b03031701c4140c40354094905e5003c0302000945c52b034100d800c00c40c4040c03201290011003201c907481088014400740d0000c0c0321449561503c10783d5204c0d410900390041c03004064120030840e003504600099540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 602649235 1250 602647985 602647993
    0x102030a02030603010b040c1409040f1a1807080f07051c0f0b0a03050c0609130603060c110a12030c05160f020319030c081b060703052710050703020c 66
    0x20190284010350001e43d1928440d500c1d0560b07090481c0f516125003800c88a050300d0f038801d070303000ba104070851071342003181d41d16001510b9036000f080c007124500c250040410034055103007241022106000c2c0380240c040749540500d819806102800f42c00900303103a8011660501959650740b240c1c0125654080c641031a90074071003892080540c0c260503088000c10300c9480e07008002003c03004040210321000e038403018020b40c0102c4281004c6041c404d00600c40000302034041191140307921030100071103a09600c1645c4195a03038002c0036070b06a021007040d18400e034101c0100805c81007925a0305203501070540007400c1c10b584564500843d40a0b000b550124020501450b145050a050441d901c0600c64001c0f40300e0b010300b00300a096882e00501c20780c00b80343c06580300d84181240e5600d05120358002c3e084041000141c60403034900c42d108125003482190103640c00b24a074140b40c40e20f215020180710406007210880101186c001000040b000c0002041280108041c2c90707491064000b8401c0e000c2d0803100d801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 602650485 1250 602649235 602649241
    0x9130203090a0506100608160c0b0702010906051b090f01020705120f120a020d03020903031201170c030c01020a060b040612030f020d080c070b06010e040e0a0201031b09150e03010203 80
    0x8404a03401002c10f02410955089607240c24500031034007003a000c0e003004101c41c4404101254184145400e2100640c01c0c042c6012203a5102c0c0000c1c00c0c4d0445201005030344403008101044110b02030b0540003003406108108422840e40c80280724001c5c030441078000c0415072801a1160320800420000b00720140600010345005020540c40d5041c00300803150621644015540c02103101c42200e0041c1d220381c0c00f03450f80301303107000088000c0c0d44080380099161006018030b412001c0c640b815680209102400d00d020040421085030500d406994218880d0b00b184480b003a2990300450901a584d0384042e00003002c0d0403241c0000c00400c2e03917030091040003001c60035820405800c61101c42000c1d04035000c8070302941c807d6000301e850303400c2140d040d00e55407030502140000840e865151034000505041200c0c18500740d5011030121680e412046800354801c00c03440341075581604c2100801c40400058486031228400f0160054215100310019020f041d03101a581c01d2240c80c1080c40e9400090007996241 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 602651735 1250 602650485 602650501
    0xa05100906120b16140304051c08090f070608180109060203010803072d061e09050106050a0603060e06211605040c08040b0f0c070807060c180b090609130203 69
    0xc0b2080c1c000c441c480801008070381d82d0242120940d00701d00f81c1d80c0c0d8241440200303850310000741d04060402c641034450365007888040881c03a00c11802150140d51507180c1440c01c040e50300c1c980b6040540803416a0401c050070b0000c4d40d44200364030751006030743c0c000c0c400160a99811a004080c50000039180d1071000c800072658000c048000e208450056054000c0c0071800d12110721005e20134150f00039600030a03a440303000142c10b0f03007060b520950822540010380c0749100c140c400b42c41c0d030301d0401c55841e55a070070180b2241c9064a1010040c00003450704016007802c00c0d550040010028141ca8420106100600800101c500d2040c0803c3d4050041d1001e803441c481003030b55610118010140b03d035040c50442c6810510a060080c8215040a4291240d0b16644482241070f44060020007960400300002004245148020417550f880b4000001e666528004000d00401001081c180041d0b14080100241840c400a980795800c0883e01d00c0e56036100c02d000640143d02c0100468112800072003004682 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 602652985 1250 602651735 602651759
    0x30e03040e0103150e0303090a0b180d0f020628020d020405181b0a050d091e0b0a0e0c01120f0f0e060405070603020901270b0301031b0911030a05100906 67
    0xb0894040c0801070f045c400007502c901086070413507410361000c160440070030000c81c0c0344c50300114825000481c5003d60030030b017410181c51548a00200c2c900c0c20501c9100d65041201d6a80328420769902d2a4440441285c0c00007407803500c0c1c910781442e130007060050b80b40c0f100754100c40091800030400361071036140801d18115540111a4030074642440c89840840c005158200c8559125503a9868580009082a03070300404070342d1800c0e00d001d003030541c1700c0d460a404084032040c4a80900c01c10000f911b840c80b0508180c07628059580c0081c0c0007840302c551aa60400e40001450f40c080401003050364219141000400c0c0c03c2c0a0388140504007210051002404504c80d4001ca01410035170b1006619290f064041c1e220b4003007228000f41c040d4074641010324000c4800f060007407403104900d2030165940032012040c2c10030303003044e55078041c1c002c0d100c500641c02060b2240140610703142807008400c0c0c2451100d65000003460300989548400005c0c1c071103486800703240060100404100004e40c0c132035010f40e01d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 602654235 1250 602652985 602653013
    0xc0201080a02130e150109030f030c0f0501050703020c0f0c01020a140f0102030709170105101404020c060c0a02060108120f0c19030e0f010e0604030f022d100c0c06030e03040e0103 79
    0x100e142c903000e41c00e006d5118540140980790068812002d810051b40c0440342011800320559003000c0010740c03003001401c03c0c059680a81c20594000d0303120345a1141403070800044803000c2a030396002c2c1c42034203950f98010603056805900701800d0000f88203003400050504468245000d099440081000280d641080ca0002517817904009803480034154440d40d0300300c030401c1d5400d0001301d200440400113642c900d0070384107074500c7c0a0009804c041000a000d4600001600c06131044600442c05040045e0304203d120300610b20b40e002030000402d0b031140151070b40b1030f070ba0b850b2106602c001680c00d001c00d8108030400c03034140c2c9102d4200b02502a0305008160303200900035144204a100d9400c0207641c41003803d801d415400400d224a0039145540703904421502c50401c0340c00c101140c1d90391164240c003001d40d1174500e0715113409200044904041060803080b191501d01807121501c540804034891202c01c1060700c030740b41400a00300102c280503a186014a6100d10005940180003108012104a801503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 602655485 1250 602654235 602654251
    0x3060e06180d14090a08030d020306090f0c18040b030d09081e0309090a18050c040c050705061303091205011a0f03030a0305151f080a0506010c0201080a02130e 70
    0x7007000700c10701e21541c0307a28044200a000030b030412940b140038034003c4003c10001c5030080082c00f2440c4e6807203200d4110f41110b081c01200580c080200610381c00d00700d40f03181e4080300f8401c0c4008a4035020014022034082d4010645401c48a031a484c3c0045d112940026085c440040131194071613411708004209910a010b405d60500403542e416148003410050500c881d40403a0140d070805100c60140041114001c00e4010000c1c0c50b84490310354010480c60003140c3c54000c0005e03003810507940307041c882941c148032030850801070104811401b080300443c2c40c54202e203103084480001c0c81107040490721071141e030304004032010b44001e1103020003c055003d048a181d0101445008560440420010000780c0a9844d09074108005256019109030b0240f90701c910040c0e6100c20850b000800309440c1e04581101d081012040315840c00d0180c0c00c008032640c00980301d182403185203814800280701d0f54205a000341409140f5011606800c2540c058070180300102200440969460790500d0204909540c212 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 602656735 1250 602655485 602655511
    0x60207050a02220f0506010903020108101229061f020a120207031e0b3d0503010f05090c210f0106060813051504060212040501150801140106080c0403060e06 69
    0x1044c0c11280c0c0c000c1d10f214107016100e54656528540041d030365580014400c0e220501006008140c030b00085a04000b0075028001c030a445003514408503c8005100318000a03822010701040519942e1081c5c11601e550070064101c440c0342c00820507407404a40140c0100044003441d03000011560004206040701d015903040f41490800e04408059082d4031100a0301c107050b020001080d4005110424030240f01d0454000d04000c4d80104040e500c0c100d0882c0d01c00c21f40381c1c101c020051441c09004100c0182ca00002c1040b442c104400c540c1d80d24070b041035150340203486114500500310781180440408030155000d5944804034020f50703500801076030140e000415006d4022a000181b10082e545e0841d602100134481078500c0020348107008402482226030903000c0100c0b018076a1000d41e0035001d03611a8002146001d108416640c600c08103400001d00e070307813500c0c860450556805400b18111100c6050290383d0b510f901007084403a10803508080c2c03140382400761910320010001035040c41a002d1403916 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 602657985 1250 602656735 602656751
    0xb131a27550513060510030507150806030c0f010e06040306110309060c03240616030e1002030f03010b0d09200102100b0306150316170106080109030c060207050a0222 73
    0x201c1140e1003920b41200c25000b2070001c4000441d140d1100350040400c4120070011646c1c2c3d0382d00351820720703581c02094801e400c1c00b080944080e000400c0d250450800c6000e0300e4402e05410100e07051480543c402030400c008040461150340b82c12040b41c001d150400da09214422160140070f04d0f5900c00d5a00e400a4480c00c030000360903902c03001c02c0c1d034021201e00082d11100c04c13110a00c7c081e200e203a85451540700808100c0d00002c1d82d010020b00305590700c2030322904040024401041600d11100000e5410754008201c0340010b4801c0e04c5c00c49065400444000c1d480700030082d1000300070014158000c140b20300c00070070607442c025400c000d400303141002d90884034035919200c60310042d10704224019030145c1c07240c004a9901c4c0c404034601502702c0300c050300711002d4280100c212a44042e066001203220090200c0c0000004402e00600011f031814100901c1800351569000b4a0001e4100020702855804101802000b10603c00e1a49042d0010405000c40452081040070680c0c0c00020920f098034001007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 602659235 1250 602657985 602658151
    0x37111e030c01170c0904111909051c14030c0106031b050f0a230306072a08090d06091709090a1a040b131a27 48
    0xb4039140420705404000f443d2101503200c40c40c1e07000440b4003903015845481c81e000d00224000908000c46c620300c1140300e1a0199036010b414690346400440c05a140031226141c8440020003241540750303c407212000231100d502c0c00c40d003940641103181141d5402e1050000a000c000181004d83c9550740d030440c81002e0355981006655088560020b40040450004002800c40c1109818000c401c0c01c0409030052044400241480b01c01c48000c0040740240c28400906208800211400540441041c4480030300d40c40b07441c198000c0b0b86207507100380c070620410fa0401000c3c0d044001c1c031980c020141c210740c030350003200140b46400203807600b802080750342d000078100d411314028000d10741c0a00580c0640b00c1d8102c01404058156070000d50f030001d46994403403e400c9100e00c940c0e50110000b20104540d10102e00c104031150812213103508146071164000440300306648002c60300104410803c0e402030989203862080c81c41500b8807882c001c0c2e4118901c6c0c0c01c0104682c684015001c441040b02103204442503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 602660485 1250 602659235 602659247
    0x1104090e0d0203070c030b04050a060504080c0f1b0d02060c010204030503031602160905070e03030f04050108161e030621050705120705041109030613030237111e030c01 74
    0x150191407514454010000f01f07000030203080d046405031082d81c1d995001900e0b448181e4406403421038800000007412030190b041400f0360b18200c460b402c06001082400342c502d07200c0c00c102e400d03168030540724113070010110740d140e9044075424504000250340300c1340d407410016101d41040301c015075900e058015a103402480032a0b82814150b50300103a29806080c040400d001f00f100038480c03420f0082c1400c0f0070480c1d40d0708201030714001200102003941c80d410800010311560000e0190080e882e80101c45102050304820440a0389003010702d0300d0302141e680b5008801511745940407410b4a114503100d000700c280e114800307891660107203048171107180e510000d0003000b80f41d4500307114041c1c10042c0309020501c1d0070b0300480089002003000500b01005500000d05254007507452010109103450700d0710425070180542c194004000003030311800014640421454100b00300101c056502000f080c0081140ca22802c01c50f5a038007420f1680704841c0c00f204c01e0b11402d06240b81c103200c1c5c0b14040610740c003584544 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 602661735 1250 602660485 602660497
    0x2010b011d031c030b060403151401080a060f020f0c0d0f08090c010c050703120207090b040203100608040f0b090706090f0b071506030f031d0102210d1104090e0d0203 73
    0x60014a4003d00c4054080d980f4007440c00060101921030a030f0108030781d034146c0904051800383c9100a08079460003503210032111020f40d20b00442148100400c900b180114500358015000000401c24040802884009101d2005e1460b1284000704114402040c001041c1d040310100e51140d18480003120300c1903648550440c4c090020b50701110411180d54071070501a104d07503201c1c4088400098803655a0340c620100d01e0514801a07101d04000c010a40c1540203900c060001618114954140b0200d0362950380c000740103040a000c4040049400c00c9580c403052a641030b04007a554455050001e1703000e45401d414803e50002444800d00480c008801144200c1101c080b4801c861900b80d145e80d030342000041803108104c28582d03e9000001217480116024042d82c4a44e84034410000a41000c140d038036270500d0082d04640c452510310320f1580d010043e9801ca500c111705010348805850b03e84801621a1940c0c1034400080402d0000712481140c0251400d00d03440c200baa581c45940c0a0201d03a42e0181e8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 602662985 1250 602661735 602661739
    0x905130c050f130204030602030f07050403080f03130c080607200a0b0c0c070902091008090d0e040b0a1503050708040c180b030307030e040509010204030c180b1002010b011d 76
    0x1a5500708410b141c010480070002c440604107440d1010000780f21412038110343d0081c0d800e00d8002040040502c1011300856201b003607414818101030554842c4071042c040d40400741100c620000104810028180c0d08683c0c0513849003011601c95181e00c0c849440340c00c1640d0f144003003003440360811101406c42c0e048240c2d90941e1740080c410340c1519210345132080406000c2d00000c1f035042081990700c080c00e0220202030419518050395034030340c1c4014840204000b140c500200160381041c0003040401042194400a1f14507064034006d03400400a0000d18540c0820317079019a030b10fa0300080191490800f016014460388003006a540c40240c140c9070702004407801000803407460000d0001e59800200c03444000503129000130b890310142c01280c59035220b800c0540200d540c0582120303040c13405000d400d61010840d0029800c3c05e1031039a0b01c50308100c060140e440001006803203000314007841e80c0010901d28000300301106401c00301501900070500c200e44140001c140360603e034401840c0501d070b072207071082c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 602664235 1250 602662985 602663003
    0x13090f0608030313080f0c012a050307080711010f0b0411040b16060b090c0706050c09031f0207020a031a0604090209040602090102070b040f1d070f0503040515010906090513 76
    0x200214104c1458501500b25445c5c0e00901514010807500da0107081441d4944000084007002c1e503005100c490212141c40100b0006190b841880359400300c15a45c00c110303581000d24050311400000c1e100c030b0103941006d40310381d07103030400c0650b54000680000d18509011303202000103800c40c3e840c40205d881240601d060b01c080c1004000101a02d00a00c0d960135400341000044070ba80d01700008100e17a4041c0d5510040c0c400c00b1034010203000f450b00c10320307400051170700c0042d1504000c000400d4884901d030046c440ca00301e101c1080c640d070b08001d4040f1a042903005121080c010303103a141c00d46d0400702003807002c200c007440c0000040c40fa05051180e5100250000e0251140307a03151f80c1d41a02030b50004000b141140030304038000a511a900c0d002d0300107081c82e0041c003105c260600b0340b40ca0428603032403d00381c0880400f00c11f000c101c1d07404c0600f0a0140c5064138005550703a450b070031701a1401c4140395002d204030044000004001207164000e80a44d4203030350007841a52949051103107081100c11001c6c0070503003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 602665485 1250 602664235 602664241
    0x2030616030510061e09050907030603050d020601080d050c0a08191e020307020607140a080901181a07080f0d1401050d230106031a0402030601060215010b1e13090f06080303 76
    0x800c5c405540c01115103803074210716865401144800000b90386000110f87c403103106008114040c040040a00510310040500390701d030080869591005100c01001c0c00740c0007800107001c04051005040c483d80240ba0942d82e900315613003107401100503504100010314280c1111485c0c2c03402e54140d98902800760700850070f212441c0c0070051542c0c898813007140d49034151161075040c00302c180903101c0c1c0103000ba0822600d039040c00c8000344c09242001c6000080034007610042c031500c008007031001040c444034603031191104028548422644145440317a446290081000d104082046d00160031915401d18540866641d84007030022056404074024101e1030300b41c0c0544640b040380d41800f500e44101c1030020071030656a440e03c01d00301d800c2050140030a000d0204020941c1410001c07240181400d10041c8691071122495802c9000c041c0590000c4400016462414240d05074100d8110000b8140c41aa6645280c43d2005110f14a02c81c0a61590030035180048241851041004440540e07020718a035076 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 602666735 1250 602665485 602665517
    0x240503091002031e10090b0301020408150a060f170d090501020a03030f0f090803040b010e070f110c06030c180a06090e100905010e2e0e07020a0203061603051006 71
    0x3400c000e02246184c030300c4515161084030b2600c8014003440c60343c91514001070804018000380c40041000a00a81c0100410084400002003083d40e0520400707503100c0a03280d5103101800f8160300e03401034100f0610080c012558104103214490412000380c01c484600650f000c0c140e9440c90288211409a0400d80f1444003180c0250403084480c0d8800500040d0b0740c0c40010b4060072699140d0050360ba42101108002c00c00102040c0f180c054242c0302900c044501d4500302c001c0568082e40c4014003000707280c00c40810070800030404000c0d00e0700300404242d101e16007008100e510340c00403c8517210b80a0b5100000c0d000d0300b44202084299800c0d9902d07481210b05010f95a1000080500102c042c04030f01070000641c0c290510032680640f1300900034920506000d00841ca50b88060350a0035648001d421282c001624051b055a00702c40782103800b060fa40da0b56981c162308124000b81b01139014081d0b041044108601c050740c2226440c900d88040040c0c0c1c80c0d010887c258030301b141c044d00d40452880c0d010b5030100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 602667985 1250 602666735 602666737
    0x150e030a02280f02330c100b090c0f071a1909020a060c050c1f020d0509011209020105190513060504050a060503090307080c010c09120f020f0415240503091002 70
    0x311107003403c01702d00e42e540c403030003802ca500203400d14400030074020540014a0200703018040040d49200c1c0140100504880014130840d005004c00c280c1d140c0c00a27621101030751070000d0f5013140fa00040c01e640709a0701150300260080003128500d2100040c1c58504500d03001a101d428400c6801501d4861990b0070041e09441c5080411019a80e0b0b10401151840b240e490b2a0380d210f2403200c40c00c00d000a5100b52401074540b24910070b40d50f00703100c2e040c4450302040c0d0f440351560482c1c08544101141490300c0d4001030b140d40c0318000b1003203003013421180c40e910100d802c280101307002c000c020902e030001a40c9000881e0035003d03e0007002d40c8200055130402c10135103d0300140d50401591800e5a1816190755a9200036501000d81350302d40d65103904c3c80742640d0f078004184500420031140d55001200881ea42d07540e5851504000078854801da45c8440784548880d40110403155491f500040210b0311075114013401c03d003c4050700313010313034078564950b01003840380301580e001e448194024251503004401150103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 602669235 1250 602667985 602668009
    0x150103150e013c0b132126160303180c0320010516060b0a06180b070222060504110403060e0a0b041101020a0605071701080705030a150e030a02280f02 66
    0x3548002c044041140103101180e99100c01202046840e107290a152140e0300c0d5040d603881f014a8409000400c40389029841102d503400d50380c0300100c40700d009510f4240c1c01000d03c40414141c03064080c1c1d618042108520020041e07a00030703444080c9000351098030308100c0d014500c100e800a1001e1090b0b8465010000007a60900e11944000c28021807450100d006000507910100c0010059241d001d1142c8641c1c0901c000341503445261403030140c031600818242002603450400203100403800c00c858000c154080000703014010024444070380920240328654006000560b400e910b00084c40448800c0081e04c405e400d0b51207050103049230b5440e1668032001c10044102410b40c00b0742401540012620b02c02c0070322a070155107556403005c0710454096942031050300300390781c41d9100001c24042d5540000349560465405242c140140c0f1304115414090b044800164a0600c000704403844015004905c880751480c0c0500210102c8c4008041e0001444031042c000e04010100310540025040c92949841 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 602670485 1250 602669235 602669257
    0x40602040503030c15010f1a1804150303080c04060c0213020403120302030a05070c05120a020304080d020f0d0315030b06040b0a060206100e150103150e013c0b 70
    0x1090580d0750700803c0c110350058284003001e42040c81d960001c159689402405044001e900d03200440c03c0160010300b501c0d8801c81102c4c560702c0801d207010b16600c1c00011000c0781c05d01030130500600340c2644940311041018001100401d03c140300041d095000030081d54100c0e2400e5960340f005142236028003080f80d010944058a880c1c00300b0000c00465002d4600c642507406981d001030341c074500025410104d5030003400303030b000700440080c01a022542c0011030094004c034800c8015500d5401d072a05030300d9480f0350f51001045000d203452854240f80c0105180c80c51801030b4060f148050541c5408400f100e0050314031588c001c0741d03007001340b000c20031514140d6031000c0091300004100e103154001504403030940d4820001031344254204020f484040c0d1209004000c480714012290910100400c018020340c2e0f0000d041503560b0680c0440300c100040d10038010044002c0141195031148880100410007010300791070b0540110000100c0a07050a0221039103418031018040203091a040b5101035009011000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 602671735 1250 602670485 602670487
    0x307060c0908031201152610030510090302060f07120b0d0b151c02130b0315010303030c080c0a0f031a040e03031803130b0c2103040615150503040602 66
    0xc2100b050400007881000040d520702202585401100382d00e19410401c29010400e04500401c4103040b8822a80340959052008901c43d5030313444c10301740700c411250b480609540b25000c06079803d01199488000309034003a0b03080d00c00954034403001600003001a10501d00244902110084883d040e600060560300c1c010000050b02442c1c2d100c1c11801002540c0c08500c81c10161b028520f10303c2d1601c0e10600021988000980418450700018411805180e00030101d546603054040a907134203104031142e0803140c0c500c500c119610b83c1001030007001510f075a000487c0406010880b0010803d080d903a00c42c00940d25451403c5c1403145c110007034058030204014140d5605800455640e89000d0f6441201e40003008646038682250700f40c940c020002041349081c0c104114520403000000c50a409466044900a41d50040701d540700d407030a41050210006010006030001046a0b0390f40194012030007200d05110600700c81450710030074401413203440480f008040c81d040c0e443e80a540510740c024040e078001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 602672985 1250 602671735 602671739
    0x30506010608100b1b25030807151d06060f090c0d0f02180f0a0f060804050a0605100e060a06020d0c110312030103260304020616051204060906110307060c09 69
    0x208084d81c1100125802c050946062015100003c100241010100c9111803120385d000c014007403000d200e00d0102401c0fa40c400141c00e003c0c4012861001e40c0410020010080700415010724511000f40d8021014034ac043d01c0c01041d014030703004a50389806000103040d540c440e20380403c1c42400d03610403007400003030780e4071100480c5c800040d40c809031108406801c0d41c10004030074a8200203441b0722600e1602d1007943d1040302480910703850a42802078842d9030600035055256030806a15000c03d0082c0100f8807400c20b0108511302c10240701c02011100100c0b5001c00076250721040116149040c0a4800141e0108102c03c0f070380e030310600303003034103040d002d800e141403100c480102007810020244400d01c14400300100400170055400e6120301c05180c011200302c607040c07200c0c0e900f84580c40007a002a20070a80440c034022a00a0a0f0100100c5540302046a02c8004407a000340303405e41203441004081445c09000207a13150103460b040075100750a001031490040740da610701c0c00801c108140603081007526240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 602674235 1250 602672985 602672999
    0xc150c010b0a0810060b03010308071209030f0609020f0108070e1c020d050615031f05250201051b07051203131b0503070f060206070c05010e011d07090603050601060810 74
    0x140107880e2180107040515004482e250a6a0295000e401c103111b04000410105c2d4505043e500810360120640300000100ca07412218522190009400c6000b00d012200812a40d60b000072210303842500d012100714000340040d1803554084520074042600802c010b42546802c0c000c016165600790040d08181d42542c001c54210583c0c6041120294000700a03c05061806035249080400440082440e550000e081400e4203550100c0101c03001e40710000f082c1108030040f00700c20703060344401c1d85034949100c54500034040c0005481c00c22410704580c903501502c038010011038003800c0e00800103002840e041414141c5030392008010301e03e0544000c00042c0051800301d242c10300c030000b254455080c1c0741400c0c00c05041901300da00c1104800f1207045d080142e60340124030940d020225003440d40f040c0340c0e10f080590140001e90000800b951a15400aa925400038403002d050902c04003280c121a8680b15400100c1d001d6000181c4079038002c00041107014414411540c0c8558448517a60807135649101c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 602675485 1250 602674235 602674249
    0xc0a0801090204030b060d2301050f09070609060f02010209120114060f0607110d0606120309081518011b030603110d08040510050909010609090507091401030911100306170c150c010b 80
    0x241c1c0e234a69440f1002d002c03250707180481d4260403881d01c40180c1061880c2580252007100d147c4600c6040c05004000d107402d040c001c1d4141d074065800541010150030714040c48600800e444078031406001200d0021980d40d06040b000c2d07070780e107210241516203846140c0c1c44242004c462900100c6e07200a002400200240300ae0103041e00030409071005498010301071030081c01610290304a050164080303414541c040d80295406604006c190046070000018800303910b0140c40c20044070704903810b503243d1811031564140d20038411607000341418140303881c03010100f21a441c07031428003411010042c04140aa0310f00f052507464458000c0c2030003454a540c4a0114401e100240c3c0440c000c100d9201d81001110014001c3c1c80d4010807914000ea009801d102c00345039913030090b070340d068105981c514980e400c0040c5602044400e40b230080450050b050096002009051940914801c154010707084405010000660030382d1100e0040003100c682e00070340c42100e95074010381d104a03a20364807030740790711182c0c2caa06c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 602676735 1250 602675485 602675543
    0x19090606030f050715050c0613080d1506020712020d080a171303080a0513120909020c0c03071703030c07230a1b060210150506030c0a0801090204030b060d 68
    0xc0d02428181c0c0c9804a800c0c1e0341e417445404101072013400c001c1c01c040c019012500d03642c0304802c0ca132789468055190420b03040502401c10712690451420b940d071320350310040c043c040302161403d500321000280c0f22a201071043e203850070002c2d0010384000300c0400061790000a00098821864080000700022403030204481080c2c5a00000014581103801410b134000482035000d0307000e803001d2100707051000303040404030724800c0b010b04825050401407610798400c02c808401419640b1066440d191490401030302c0758400002c8034440c0c8940c0c074001071515408081000191000c401850031990b0b0700c141410f61303038000701080b240e0750078801102c030f0064101700fe1000301101d01c00c001c089002d120718000404945404145800a9400c841008556400185a10500703103c00c808240504403200b019540034060700025840b403c08400c1004018003403002d80040c8026650300141641d17078013840d000700d218500000e049006990b0001c0c1003414141c0b10300300c0031441641d146599441c2e074206400340e00841 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 602677985 1250 602676735 602676743
    0x121502160303090204060501050306030c010f020f011a090f010b0409090203010b1017090f370b0403030c030218061e0a0e0a0b12070809010e070b0304140619090606030f 74
    0x180b0440f6041d030401e0320038403010301402e0070443d1440c140300002a948050164802d410000d540f119000030a200380445076507840240028010041840340034482c038400b28142900400e18000050400000108101e04a58041f24001d140134108207008001d0003680030309a1f0590b40b07907030517100c003501c2c4c4c2505c0f0303000c1c27503100d84c1c810301409090210380b40b8590020300348000c2980451103c425401c03000c00c460715803200284070031180840001010395901100c0d40c013412881580c4090800344000700701c000d8440d6111fa541004041c115078019070032405080004c044080b410206580c02e4284080104611590000ca0940e00c140c0d011060741c03990300914140300092403095080d4007500302100710001030070340ca000311810840c01962a40040100610000030041d040010072901310007036210845034101c50080e500511348582d06044141c0c13082d90116030741e002040c43c2c000140c4001c43d10501440d0a402c044d03440b9403544c09858041c1c002410180c48486ea00c003000070010304280d00801d161481 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 602679235 1250 602677985 602677991
    0x5070203071508090f03030c0702040b06030903070b070201140103141507090501030b04061a0714060405160603150e0718150206010e150d240b030106050604121502160303 75
    0x1009100400c220f5019112a0213940400b4050000a0000c01501d81c030400745070140d038440c0058000070340030f045010a22500708500205020b502d031000300040000e2405410381210a45411b0360803070884813603400c419240300b9988014400220403103020600c85004100311a60500030184048480b0016601d89001c9444804104110750b0580540e5800201c200c07420040a464800300c0700100c0c5001400036820600010980200b01400004a1881240c8801c4074120725080c40c2040d90740301062242c01d03404041380702c00a5114424000c400010300c0f02400144007500c2c0803503040c211b020103050300003809a00300160840107440d1031060024684402685005140d00c54003a0520350103800000451103540100a201c0d00004141b0380310050035942c1100305903550426201d010501c1020302108060344200018220042e0080391000800700c008014081d940c100304211845584182000d00c070140d003124010800050152213a502c180d117015141c1760721311400440301c0600e60320840110356 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 602680485 1250 602679235 602679269
    0x2090a020f21100f090207140a0303060306050a0b030d0e0609030d02070e01090e0a080a090e01030305090a080d1209020a030803010b0d06050d15150e0c0c15060603040209070507020307 81
    0x12040c00302a4100f04400390214030309003046101210560701d4011011036503000140e210400c040ca54051000c2602802075807084081031900030090b100070310003965a1401c080c0450071028180c0310300540581c00800a041080c10480c0594001d0890b1326a290302c64001d1043c00d0a42d1400e01c00001215030a41c042d180450800d40341056916040c0c00c46808640707803c0440500c1c00b0300040b541c0c1025080403000b13494135912202290003e4ac540c1025040d100c443e000081015000405001c11501c11681c0002003a11041c405075608403003544000000c0c10303403c102074540d40e02e512660b43c003800641030103003644c1c503500c6440c086e50080e1b00100781c0100020301800388441d1031244201034982143c00c200c000030180c81ea491032000e140211541d17a075458000c1c5021040c1070348020010324000041038923074030303000a11620030f81051803245400d0107008007105414042c08801d502c50100208000d05584560302230000c01440144180b0500c10208408400740e941040800020a60030015244281c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 602681735 1250 602680485 602680537
    0xb13020a0e090a0204060e240d050403170601081810020c060712060501201e070602010c0c1509052a1f02060408160c0f0e0c07050a02090a020f 63
    0x10000c2003410303c00d1040c0003c1c000c2d0b0f503010101004030901250340300724215601b50554400c5804c0c04030b466a5103c0015600c0243e05180c01c0548141d0084d240d60580841c500b4038441c0c00c040071140b1070f000814a00010300300307594210106011440d00011254800c1360f40b03190a01300e0388600680e0703550754000400c0088141d48000420110302c00108103000a070320f80000030705641c1555180e2600590070015500b102e120401030f940b0070410300c1d40310b13442462107050716989034400d6000f00001075003131001002425000790742070b1111950141d03251031214101d0b00302c10014a072544d0308662a000d56501400710300c00c0c600030003402c00544240750580c01481c04c2044603541c00002600741150642010301d22964001c101c0d01e500542100242d0780d544546d001802e140314088100900300c0380c0c00d42004c668241c001440000741d60318100b500d405070b03d8140f803125940c05584801062903005140d080014208441c040d90041d01d0480054100001c40041d10100d411040240c942038104606d90f032120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 602682985 1250 602681735 602681749
    0x6080604051b0d0312092d0605011d06040207050304030203030a05030f0117030901030f0e100f0507030e12090f0901080309040b100512150a290a09090b13020a0e 71
    0x7110b0200c0381c041004043d59400390160000c0d01e180d03096156580680b200748409107006042c4020744030140c4c94410010300c8001d416a140c07400070f40f00c0c0c0d803070400080f91942c030034003120f42541d0b003040c00c206450360754100b040003a50021804450034001070100100680b8200090030700a00c440d2102501e0786040c40360042450416488401788495451180c955454040b084806002003841c0118040d101e40c0b0252003e445c00c540001c020344200454860501655848111000a0500b051140c0d440d000800ca040d9410035001544a070423080220324140ca0080c000e11481c4000b81c0340c00c0e004081c90b80000d031607400076030040805402c001581d4030b0518003031141e82c0440300e0840b0b50301d0741012034041c01805800346092100c2041c0740b05001ca9400800340f08004490030004100407102620b411451104032101c1da401d0101c030042100d0441e1a025040c10756445600c50780c4c0342500b291401e040b00000d4941c081049402c000c04806c0c410028145000600221549803618a0f060b142c41d4240415 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 602684235 1250 602682985 602683033
    0x170709062315030105121f0c0905040e030a081008010c12140114042c0106060801121a06011e1809050408040504020f0c0708070510230d0608060405 65
    0x400c1c2c0d084480c8510003000003058a05480095440f040310b17034240d8003050b01d010044507150007a000780d0040341e507603d01142c006081618080d030b55402c46581da0b000703000544100960034002d5820600900c9402407140800c5a40305130311045191041d0f54820341103003190700041034034001411400da4481050b101e4000c4549000416102c000150b00d00500002584055400948901c2d142c040300b4024517901d22122800c0e03a20030540e250a0200700700007e000380301510903140400c00040002610003542400620f40d140c010b107007202c56020100d00304e050510001d1589040c08409034845642d0062080702480d00c0c003040d125010380704031104900658591b50340c040182181414204400102002c00340ea00f240e00c1920301684034800205241d03140c2c02100c02085551082800004071881c00140341b4044036400c0e2000090f20340d0884003202c680600503500088170b140d00d65403c1581000c03100410519400d1200001d81c2600c0d40010b5051550550b029109a07026800e42141280e840c442018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 602685485 1250 602684235 602684239
    0xb1f020a06062102040e03090319020f010801060512071403040f05191509033014150906011e03050a1805060f0709051807030c090501091707090623 65
    0x102d840f01071000c0e900d00343ca8000f40221b455816051400c2030400903560300c604003c09441c8025180a80302d50700ca955084107911030002265040c0095010b03404c4079050b500b032960740d0f601d0003414140242c050340000d80018104a020b038042c80e440381480015601851040164a1040003030782450703407a0103610920204510340c1040c2d030030005606100000c09040e20342c1408180549103040a8901d0303145800307114210041a000110010740d00305100f40a50f5916900b000050038003180c0c502209011a01c00303480c060011022400c0d403502d02d150075484081490250302c1c4555100f03420709031030300c21400000440c2d200c0040c05440c94040c0607040d0105c681003000c0c2c0e0b0307901481e02d50b01c3e81c0313001c040c2440840040c040c0c00324030103510403280c04001d0000a0042883d40b0100d1aa2240e04501103807580002480c00c0c1201c030036984030395164411194140c1d242c1041ea41040005003141001e0740520002e07100b901030000e80801c1502606004010004c804c142c000410514030900052421302a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 602686735 1250 602685485 602685509
    0x1005070c15020717030f040605070605070306031502030405121801033b1c0801030b0f01030804150e040c090e09030301180c021509101505130b1f020a0606 68
    0x102580ea40040c2d400100e6502c2102c0404e00700f6000c100c42e043d481074080103d4070040005002c07880c20b410800a04107103101c1d2008105c15a150a0100c0840e02540001003049501c020007500090039500903542050140064a000344104107883d90b80ba442404101491215160070050f20342c0c01d88200f85508019080a104407603103003100c001d6400001231004240e4164103000304050108111051714a804100f408074010122807024107035030b81c00d00c0100c54003003402c400610000b078a000c4c003604a81d80075000c90309240c00c080c461080c1c0e8003402d00e00d2040105048208072103548034000c00c400c1e00800c0c1c4403064440e04080602280420003030018015900030001001010b560000301156035070f48960020710500d04001c124140410b9a041c51b0ba00e03590361090000026020505510450700c00b54200a0a115440d458002d50410b1085540c40418621100b0701c1d41010b41101054600c0100040031141500d80010705040400900c600180c0c41100781394200080351080d038020b40085031000f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 602687985 1250 602686735 602686769
    0xa0c0504110f090d0f08030702072d030209060105070605010e06030601060c0c090c0e04231e19090f060204050102100506222c120309071406091005070c 67
    0x24400c40e114803d81075010b01180d2020f4030a01c014400068941c55000c000a51b84e807c00040c02540c0301418026000300103800da000c00d0b0611400555130350b407180095486942a07245800300f00903501c0041050f418841d00300580c0000035807500c59240038000c2ca80d144001400c10b071040c0351a001058004005002c54060701e000811103004403001101d00c4070030046a0308141c008200d4103142d071172a1254100d420300000c1380102024501402c4d0304042240d0030b40081d0341d1068426a001600700e00f02001ca050703230300030401d02e115040b820690300c04a00c0c03000c01c0901c1c0690300e024000d00024015540c40364049000e104035a1305014552454601c100280002e040405c00685151540300303820b41280d0700264189001c0809130014583c04020240d00388182c2c02091040003034050710034030000d40d4050300b02004980310781ca0003030780e000346204401445007605204603108000c01c403000044d0320440502c101704259031142d86800880d070540d078585403611154503000d520485140c221070032a5600c00c0b00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 602689235 1250 602687985 602688007
    0xc0106060305061503041a090c040b241e0f0409061e0909060e070f061701150f05090d0602180405040312020f07020a0605040f0b0a02030315030f0a0c050411 69
    0x103042c0c200254100c2d02552a11940b600e040c01c01c82940030340d007c00c00c07070f1010880302010201d503d041c00403055034140100c07050032017041b01860fa03000345044c42c134404400741d26000302140050103800d40c4240810024206052660706641c2020101050402c0001024000b5100500540000780a501e11501c0319041160081c60301641d28003401030b4041c1d444840c0401c0c07200c00d4214400761031100007503a65481d02c6050f400c0c1d0360704440c0580000b0550985409000c843c1001c4204d040340d10240700c941c0c403009a034404660224806450b802005400e00183d405c0e55100264150314074401d410040e9100802e210100801190301250f5208501d410204804250020103031251810401c1c0c0060b524041420354030120300400c08007070b411400040b004105542c00100600941d8100e05582d40e0042c3d8600c18030216109102c91400141c0003840820401c000201c4c2c03001c00444002c041e030f00b805030b40700c0000e89480354103203058803640c071140c40401c21401c180c82601000e80940d000c040c540951466 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 602690485 1250 602689235 602689249
    0x603050309041a0a15030c02120d150e0c03072a02090612030301081b0901060f05131e15030e07170c10030203070e0109141e0301060306020c010606030506 68
    0x1040c0a2500c8540001d0a01450070303e4211030840140f20354166500c0ea00004404c000003174402002c2450a580030180c01c1c00000c40414070900020074600c2c1802c0380360880c1c0580b895a80100c0001c21002000c0390902d6a400700620034801654065107a26003c00b0041c84204c0e00c0044940034546017031458800440d0300c441c4c40c0703401c0d019a00406940c0364240400d00b05a004d0003810f199002c08000800c00e480082003500302d00003107542c0c002140e10804c007080b6002d002845484082180424141c5021b8050805011f910440c202e080c20704a59510030001d01c00002001f104098203503c00520209882a070a0040710034580f42c03c04c11014405026036031a42c0c580901c0c40000b4035204119030940341001b070303201c0042c80a000d00355813a10030b00002d4003030340080e00c1400c045000c20000c800154801c038162011184460030b0200740344034101c02d02007076190003003901c0000f1640ca442000c15860074010800254440d000041c0e07207682542001e42100d1140c1c10010816042c9004d116290341e40034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 602691735 1250 602690485 602690497
    0x915040608100e120a17060102030412060905012406030908070c0806090d0f0f08060604090c020318090c0a030911031e0709021602010f020f0d210c0219060b130207051006030503 78
    0x7030101c0021f61036210060f403444c0203952002d058011250001e10800c9a035420107007001e4801c4e4001d02540c0141c080340e5001d040c41d11007035012200c0d921003c1001d288139401407510580154071b11803901e035603034503640b000c060309801c201d0a5500a20601180c41400c000c3c06815610b2480c1244000c000c151005020400d00302d002800c1040380008aa1160303520350486008186141003003008035612003000c0d4480c1c001001440c0504c00703104a0350110308000d46c85900c12003103101c1043c40d210fa0714805400803c100801954090005e1540da0140e850410404506c0d10201c04407190215008502e00d04d400c03802d811800070140140218012505207820508125509003002e04021011000492a0005408844801c0d104003414030400039040700c1810300025140c501b00502071520103514054030030a56407400180d00c01c0d00040e030030045a4044401451007900041415508071000440840b60708030140c19180e80019803000300704041000c112041007031042031055034519145d03182c5a024075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 602692985 1250 602691735 602691767
    0xc05071202011107260102040f0b0307200105220b0103080306010c05030d0209010f0206060a06030b0a0806150901050909101a0904060b040612020915040608100e120a 73
    0x103922120304681c021aa03401200810728101d0b011942e503400942d004000213003082c1400614000c0c0e034030b800c110600885064503010ba40c00e129803440c0c00440540760380001d04050070010250600b96040c0240700f40c120021000800100700340c00c020900104688078203190a00b121030310b0b01e40b8400146541c0085045a802c40c0665849035243d00050380c200701d2441c0024240d020003e01740c02e42044c10b5020700070405084c1d0300c00e102c0f041344985c26070360b0b40020703102c40d41d00c40301c1c81604120703075803090700065050f041c064141200f01d42c0d6070a405242000581e0550241090419001d1560600b440007900428007101d02c81820300741800241d0700d89001c03079407031307801a501ea40604450300360303204074104448006004500c0341d00c0d150800000611110a01502c81c030705005001404000c0e40d008041d83c182c0040501e08145c50f0f210341202d46c48104122190410344540001441c07040c00d001c500c0502c0b400d103402040640f20010001e0410041c240c40c05400c1078140300013040d159100d08015402058 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 602694235 1250 602692985 602693009
    0x8010c0906031a1c050a020a09050405071a031311030f01020405120a02100f090e0f0702010f02040521070902120406060807060c030e03010e030c070305100b0d0227040f120c0507 78
    0x1d90422500b1b1440101d0040c0d041107111200090101c001d40c41140b0079400360095848040e156107140002d1801540c0c0780b52207160501c0070541440841890415452103079030400d030b010756480e0100c0c1c200310031410b81c1901a540800d040000f401c060b441d40884002c10000303080040519400921032075214540182013001140140180c18041c90514010702614a00e00c0b4491814003180030703080c5800c842003030042d400c1c00200b407039805c0513009807402c1d61001400c18401c0c201d100e004030508544041414914447c81b0000150214580700130035a40ea41c03030351604810314090800c441a94401d41c40b07000c0544c0000c40804c410360f803201e0a85800c41d410b1802000c0b0120140009001d82800b1801c0c028901001683d5960404001a40400c50f44900140e800c4000120b2092084071046c0d02c3e43c0d82c009801032006001442d241c1a00d100c0358190700458400071030021050900c2e40c0c412101141c1601d44440c445051101d61400203c1703201040c81d0902040c2a00e0b5120368540d4050300c24501140d503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 602695485 1250 602694235 602694289
    0x40b0406050f071a04050f010c1b0c0f081c08040506180a06050a020c0d020705030c041e1b17070e04110c03070602070624140a08010c0906031a 63
    0x4102c40490700f1181e000010405140c100c4560074407408401e607030480d442d101d1801800e0744c3c20b138180120300e0840707929114034020324035030ac884215465030f840381162801589080441c440c0325018410010305071000082141c00a02c100075442e81c500500ba0394240708140c801c100004500052442c3e2020003079241b0307021815481d01c10341c03800c4a82ca000400702d03414002084032055056001d08468040041122010890700b01e060340c45158600400d0381681080300650840d003000c1c1c1100807601104065084000707072041c1148102c1d006c0710401c50303000c0d2182c030000d01d1203540201d160b20f4030101060074486900700110051f0810107001d06803406151243c030000c0e0001000000e5034085c0e079140341565600d01c02c61524100030740c46580200da583e45840d0360901c0d04400c641e00c00500525451b0204002c505201120310403085110a10f035115013032503030106540c9800e020304014902e068a0b0900c44d075040520190694001c118140c1c08600301c0c0c10340703410035580d000300c4032040640b11484400c444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 602696735 1250 602695485 602695507
    0x300408030904200d05060a0b070c030f02010e09040c18111e1303060902090a0509060c0c01150303030c0e040c02070303030b0406050603040c06081501090504181514090102040b040605 80
    0x43c0d1003800b440290840818101c60065258014501c2a038089919100c05134036400e0a907011301490f00b000d07201030503e43c400e00003e0200714003071703082070b00505150072015034503400244030f0308040b50111800c60380c020b820040b581054507040c2442840c10710502036140526400c10300382c011003040943c1c0717031030810201000e2103449c000c64034822068090700c080782d0f8403814940064154020200c0c018650b80c400108089468881c407800b40c40e40002030611610740c5429031410b40c22803079480700c03203546c1c4002021b5101081c800e40c00045110303840100d0382c51003503600503207240380d4401d081d8000c03414100911081d0b41c2c08101c0c01d003620342c5401e0008513011898049401030166403c104e8014000200340414420000840303001c40f040341e542e42c0155170340c00e80085040022105c0b0180440c1d0f801d0820700c0940b80c544c0020803400441c2445c5050340e14940c998031010b0f40101c00b52001c135035a03251648868030001c05640d0740001c0b800000d43c5800e01d0502d03081d0305403240348921020032402082150390301c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 602697841 1106 602696735 602696771
    0x80601050307051e180405010b030106080c1e060a030e071505040e0702030702040c08010503012003070f12020d0203100915031211300408030904 64
    0x3450801408800c076458100304078111107106010b1960746511355030f04425a0f030f05407485c0207405c187c10401d084804007071520b80240d05090040c80303034032000200082d58407010f46140140c0510342803440e21030203c0b43c0000e90b01c9180081d0035803070194981c021104203c0548260f890b0550b94075065941e80c15244010b10200f203060008020382a02c0850281d40f1003401d005a03898101c0c964001800c82d030040c5500c20104661200501c01070400f41305190a034036039903042d0441c440000802c14403d000003800c80d010017249050a4107030720301c80c8010f074017000000c59096446140e03404111380a90411201c6140e0b820018a001030380e4a85030251005c0c100800083e164440d0950b26000034008c00d1080b440c05000b0400c000034582d6008101d031a100d2039660790b43c00e01c59241103003440400e000c1808410f8101109000910070640c020084991106e4101c50009000c0001d222002c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 602517985 602697841 := by
  have h0 := BRFrame.cov_init 602517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 602517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 602517985 ≤ n) (h2 : n < 602697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
