-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1432
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:57:39.469498+00:00
-- url     : https://prove2.me/submissions/1f865846-220e-45e9-a02e-975a45b24f7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 257374100 ≤ n < 257553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 257375350 1250 257374100 257374141
    0xf08010207050304170f150601030f18020f1203070b01031209060f080a1410090b03120f180603090d090f0b031b040b0f21040321060306020c0303 64
    0x344140000000500301000b00d50858104181c00e5186180305240c0c58140383d07070060380000d28410a000e40060880c5583c0b503074031640090700c04210460011580c80c05485904641e0200d00403191040383c014646140e80d00c8034a08040d02c04001e078509900e58914581c001602503501030b07030072030041003001620902030f0104501480c0210b0030502c1c091002d004107544210890501c507440001071600402603100010800a588090310301d03080400c0e00a920b28514090110002d042c607698242030700b0005181c2906c1821070610030b1500f01141042c032002c0c0c01c40b83c0f003591b284c040f41038101c030107a580d040a540501c40300c8000e89010b00b041a00a800e58003d6030101806900b07500040242540740c034140ca9020b4400c001c40f02c18980c0404045055201c0c54220701c0840a0201e40624582c0416000e440d8401c00e4100d04030f0b108554203000360000c10304442c02400078160301510000b00f512400000f049049a0801040355a01c9030f485000742c2e08164541541a4800300412000f0810000d0f01361880 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 257376600 1250 257375350 257375353
    0x3030204050319020a0e0a021c0b01020709020c030a1103090a0602072c010e0901090b0709290406110304030b010b0c0d0e090606090f10030e06070306060e130902130203010f08 77
    0xf5099501141560f101445162400240000024041c10042e012101034001e681d00b00803880c201641d082c0000c0a544600d14014402d40e0340218141c3c005100701c80019500070003c604024241004460f071140c0f01084401c1c0b40070510050300e154855104401c0038000c1d54002d040c0c1c0c24145045000039901d804600b0140816000c4454581e880104040341524400810408180d55864800e405000000401480c0c040100204800154400c0380c10781074600300800c00d1100790750300d81c0c6a1131400300e074100e80c09031038007c00081000d18010004030f401c2001e01c0003901d0034540e49803076054041509034405100c510340012092960001440100101c003a10b082c10f4009440406c04107080f140c00800c15806924005102241c0d541c462503002c1d1038541c001d00f0717015201c41c1d03e0001009407035079504204580c41040003061660b030090040c4015145155180c4500c01c2c642402c01c03910340c0302454000c00c001c0d918000800940c80e140ca043ca445a517000d80540e99524055040c51041081c1e80079a050b03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 257377850 1250 257376600 257376643
    0x1b050703080406050c0918151806010e0a21140f0d200601090b010912170f0909040606140102030f040905041109090a02010e06121603020d09030302040503 68
    0xe40c00c4988503800540003000000c0b43c0ea152031152030f15100d8504a558490100490b100051062441b040e03c40c01450a00301d07140da203840240011f01c6130340041c0e001d01001110004100d075104000c0030000203402000c02003a02d42e00c1c0348a04109120104400e02c0748000b4140c401840360040c400508100480001c0070364a01850714a5150341c0d0800c224001c003c81c013503141d040140c0c4403e400181064960070748285581d00d0a524008000c48010103012403004c000020b030b0450a141e0304450960014039400e01030b4034090b41c49031180c3c801041903940f80d40c00e00c40c07000c0a465170340302640700d10710402d000201c02e81002e4203100f20b52569212a4119441044400283c0c54040240c0341121607100c00440d5545561030407514420b004890b02d171f00046040200003600310f0028000703401500030b0f00c1e0000c10100300e100b0700200b4454810781c8130100b00c0101c00b00395a0030300c8600c50b064040c5680740c0181002480a80041a84c0403200254002500030800340101d2805000007001401d071407000122 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 257379100 1250 257377850 257377853
    0x9020613140d03080a0f06150215010e0c0a0f03090c03030c05120a0509041a030a0f0c0608011401050a020114010803130e070c02100212070819030b010815030a060f1b0507 75
    0x4401c1d001440340102a441d020300c002c44c021b00350804005070001c150300c80034840449000954420a1804440c6000100000001c5000509201d280501d012044d041d140417114013050b24a401c80d07038116000c03d991099008081005a010140030314420364584200c401c050404501e00074021098101c00c9000f040920703107603600003003140c400c07400942d400700b5012400100d0360000168448c0242d01801144400b00401a070002d0407200c240c8544601c0040303540b80c80040341c0101d400d02070760003546050581d50032550301410142c01055018400458110041c10391021000b03403e03449695541e0000c58550766482500d44c8101c0640304902405c0c84501d45800c000301681601035029000359102120696890301c2401100c07000d081c22802c2ea6940c480b030b45030512850380400c0e4030610088036450700b00403143c030074003d07542500300580d50800340d5214800c00c1c605a07480400b038241d1500c550341c00203002404500030700381040300380b90700012100080c6101c00c40414808003500100002001000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 257380350 1250 257379100 257379107
    0x403060b10080906070c14010216031b02010503010e0c0c12030910110307050c030c060709030303050f040201171509040b1512030708030a020403150603050706030b18070309020613140d03 82
    0xb80d00203c14a4500034486243c00c1c5042e21847c01c250756211540001103a14004000d0706401c010301d40b1950b107034050b0106400d070440d003929441d07100030f00240040004009012519901c0c98008020700340300c92405141c60180351402c007a9500540f0440c40200400c04846820301070004820a10140ad004442c800110241d013440014507802c02e003d000300d803c0302034000800548801000d034600310703803550038404000341c03030003280d4403044001a08220000e001d142042d9640b038001c0c0d40c1a110b5607103200752180804140c1c40014040303071f408100610101c2d4036540b0101b0380ea01540c003400e0a6852070510440c0320b84070b08a921903060007005400d0107901103240000c00c0302c100301e4001d00781e29200d4070b500104201074401c0e031344054299141e1030304101c803a10b51342e40080110303807180b0308070b80c00240e031208150152880d21104941c8010034003003511610a0141d0003c0e8000c2e0a80360000362450980d000070741d10340000f507803a03030510034940c3d0a0000002400d00038110b42c1088a4641900342c2554004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 257381600 1250 257380350 257380363
    0x150415020a0905061b060f0907090b010203090409030e03011401090e070503060c0706090c03080c0105010807210804050a0806190231030818010216030c12170403060b100809 76
    0x1402044d000603050386007001100c1011140c21040240c07100d81c14071144000850308255112150750081d5403000801007082c1c8104e405195060b00690308250b030305d02c20440285902d000036414003600c0c1000c680c0707030b50b421301c00c2100388185000703005801d504102c030210854403000280c010941c00981c05000d2a60b0010345203034000062040c0503a681028505034000c0c106003080100346282c020b5002c420400120701a00146500400070860360f03076100c4403666200b04074824100b07405c038820341121164a04020400d001030054007028070301982c59010400c20b044550004a02c0d4000340c0a00a1362400340071800ba455905010035030601403892000b500001003588054110780d20b282c03e410502d100c0c940381500564115880c0782e241d6140740604405844614041b41c010b0003500443c03440b1070480614082606d40101d81c1c2803140703043c2001c200000d5040070040d54000491183e40600b607500000034809544146008200c4643c83c405001c0d21424403140030050204c4603007004100c15001410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 257382850 1250 257381600 257381609
    0x31b0a030e0f2805150103080d0b04060e010b0a0306051f020d0513050607031e0206100803070f080a0903061a01092408070507060212070e0904080f0702060c150415020a09 75
    0x4803010f0030441c54602e240c01c00b025a160721002c41030f00000240440d1502910200140c0c00d010b00070219034104100403105240103805030404020f0042c0105040c00010700300317980041c2000140980c4903c0054481819100b4a29441141e42045802668107011710441c860150030b01a0422411050155040d00c0c2800340b58080c0e000420b540b410702d4030525900c032981d0740011900440e0810b90b00025101c4030100c3d4140c2c2145080500040c00260002c21602126000712485428003059541c0310000d40c0321b41025002c1081040b03020010461034480c1c061044a599058184245104000b400d080d8a5500501100d07039030300400b2304005401c40e49180408106c0c50002007580e03c0741e03c1070b1864050f81d10090403442c0702090240c0c040c041d20710b415000c0c0d02152100c07519000c607002041800b441c1210000c021030303800c1c0300c40d03282c62241401030020144001c1101c2d0903e405040b90524142c10380a48101000f106d40500083c0301c402902c140c040d84035014150725102000e13002401c59841c500c01c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 257384100 1250 257382850 257382913
    0x120204061e030312060b160210020307050c060d1103091f0c0f1110021804050c07030f0e01020316060b040509010b030c130b120601141008040305031b0a030e0f 70
    0x181c0401350400c681c8035102402032154080d0f00c03084030746c8502c0340c0008150b41c128040c0aa0513540b051250000007600c10b865441401007940070851030602610b5048064003e0803680c131440c6600f1036455607030203107106260404c001c03c1035024402e00c0d01803165402c0e0000070140c0c645030207561f486034010b6801c618200705040140041840b80300e21460120f4000400010381d00c0442c103011080503060070900f4000040314148242c0c1c4400034400302622400d038005020541c030491054546d8040c01c401d50007490140141c07070401d6004040e401c2a450604011220b140da91880c0550031300d030a200b05038014055400801110344c240c8003103580c030086004000d2259907030f603061a10b0400c190300049802c0c40d016203012500080d41131081d5a0342e201b0f000b5900682d11945190b0045d0401c030b11050b0039a402a43e40980580f00e41c0c0f001d90380ba920207052111008001000d4410111103040182822034065400048200c84004007034100311000d080083d03181c000c2c030b00c617030700b9076400040361080c2110014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 257385350 1250 257384100 257384117
    0x31205012103050a1211091206070503041211060a091b0b0a140705010905060403090e100e071106010824010803030c0f04080d030b090a09030c11011206120204061e0303 74
    0x140030b403844010b2029400c0b2260806140c030300e06511b00306c094411220141c0305525528040300c0f100d504c9800031035210000903401c1c4006000310341180d8070205d0020860901380c0741d19004419507803c021045401d9132040303894000b074030300f0050b410b0b608451050450340040000c505046c00b070507462250780d854034204005c00d980c00c842a500d81d01141c0340310354003800030010724580e840d10030744541c0101c806070042040b118000802184012480f41b1911000c0e4174807002e00c0c06c04041e40d1045002502190400c2101485440180c00402a00d80601038006c0246145140716901150400c0c00101c2c1740541110380004004516000059a802503900786010340c440039900b0b0390000c1c174001c6a2102900744101319180c040150550f101d640403841c1a64104944c1d51601c0710f841c2501c0c8203c0c4002c2c00143c1038020000851403070880b000300034505141c40381400c1102c2401c80141d0301103030410704040c2c0c4504018130443c40c0078402c8030300030088071102c1c42034035803800000c6001994500c40a0709210450 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 257386600 1250 257385350 257385367
    0x10e04020d061706150901063002070b090d0e0f0f06090d08030604051e06010f030f060311040b01020a0209040b1306061215051501030906150303120501210305 70
    0x160000d50240402501500c0780c0f0020005075559104281d400300040002c8141481150805081542c140c4000307494400c0e50002d0348074411042c1c030048045044540036a10000d0b000711305400101038080c02410503c05c1410081411800d20740c42e2001fa1052100300e031040340641d215800403000c2804211100c040407042d00d404542030b4403612501d10340c0000c2c0ca00070304d010818580080d600418082c1d40810a17555420b001002c0d51003041c440754916226900083d610b9881541120481a01d07840c000c0380b15040d160740744041c1c030740e40c3d00204c5014030740c41c4844060381014440e4000e9150248010101c01c90642c012a08914000d00003400d11100040000c2c030b103012201d8291030315035203d541041910b94030f2145c41c0d005403a000c800c441001e038141c107407581d00085004190044540102000c09060310200650061072011811590302e925404001000600e4400090085020751540c00c00c10400c000030000b100c0e016000180092018012805880c008084011180e54141001c56454841 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 257387850 1250 257386600 257386627
    0x91509020c01140c0a020c0109180b031e0102071a011208030403020309030a0b220804090c03180309030b0f09030a050702031006031202011a0f0103230a050115020c010e0402 76
    0xf078803003419140ca4148180070300101076a00803d0403080640c2981c610a40e10001101c07600464800c40c0305005902401c000c100e20180e100c02d0320054002c040f42d42d2081408001d5042428090b070032055030350b02140103c180148540e90205424080c2ca04000303940c10812200c5e030201c80c140018100190110010342050700800498941280040440309850180d00d8496040c0400319100d030703015981204180960805800000082c030b5002003103a00b06820220504000d2040303052403401c0685900f000c0e0350f01d00d07075028280000740c0250b90301f4a0f514254100102107400142c840d5070000c210300e0411428070b001105907811580d00740340042c4d88417070500003e864002d400410300d102e5440c082c8000200600390111072001c40c060340003401407a00c0c007946041c2c40c504c107a000a40001400300310340c120b58400d030f0220158480000c0d4100582281c4410041c503024101e403403080c3d1a554400500c46080d12403118401c800c90b40c801031158198640008045500d0590f44a00560700400d0170b020300c0342c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 257389100 1250 257387850 257387861
    0x304091e060f030201091d071d090109020a0e150706091401050a051501030603241e0f060902031e15121507080c121015030b010207091509020c01 64
    0x355104184400d58492002c2c00d106103051000301d01142500f6400900c458200b4443d80160f00010741c42461a592450309858a001603040d4481c400591349080c1401c2e500e850711540138010100f0016100c00c465040540140e410a500c144541a0b6034003002c92000030b1011100c041e07a002c280810500e002e481c14408030035005401000725401c0204000e912041544142d01c90a1a02c6840101240b410019821030381c003400054a464030480340c610107849540188210000200030026080c41c04506078044025107407051100700b9107507982241c0b800b00d6806920003900031614114503600304a2210a031a0104e0039000305404e821000141e0f0300403010a1454805d080544040e990b10411505141c441d45040a0352000395801c8022905543c49500124070803052a0045441c1c41da4040441842c0c0c1d00082c80304c060041824400725074001030102100d100c45054401003030351928038001a040c87c681c0d401000d40c1034504551045000c2d4560032042c101c1c0c40316900107a4035144044024007521 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 257390350 1250 257389100 257389151
    0x30618060e0c0103050105041509021b0106080f060105010f0906030b0307210c0b04030c030b0405030403021f030e010b0a050d0302010b0607140f0d05030604050612070314070b030108030409 83
    0x1e207410880080c455012402c020407030003d9800f0019030381c07a842000b0031584502c1003d840c80e06411014482c43e90386600070440c0345111106200006ca10400c40f50a542140d00081c0c8543c000002c04c0c1c4520a0070005c4c01d01400c02401c080c00b02c110000002424003c1e244540001c154840700c00c8201503c0c1403000e04090950b81c1c00300c000d6092a450702c0240280f44940c2101da2513400240081e00d407045000341c400b0791358069076150503986542c451252203403002d030003a12640400c0100000582e121903440d980451480105031984c10b003070201504486030704004840903410880c8800e1f241c2d807207031106005c1c0c2d04100c410400c01030407030900700c0c01004142d102a0300000001107040902440420650301540e4100c1150f030b0038031045610325218141c441c1c549000c00c81c10300100d03240385419000681e0006c07020302000000090741c010549400e00d5a8001d5880c42c1340300200c43c101d09000c1c8003140103000c112640070b1a40d4540341d803441d942d2207148619909a66100a00c8000d8204040300c0c1002a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 257391600 1250 257390350 257390363
    0x7030c0f120315090e03070308071115060909010203130b1b040e04120203130302040504080705032116050306090403031e060816060e0409050c1c17030c04030618 71
    0x20006007001034028801c807440780601c144065000160400580248010090060050350030800d1a5500382e0b422840600b1a0090242c3c0c211807a1401c0020002d105230510000c0c0e80381c031030b82000340c180821400050501d94499004004001c9418505011903c145904c9100120156a900081c04060758820745041c540d00b8001070000e0203490f90b60507103028900458a120401030411400d0342c3d02c1c0729200c00342400c240b02c40300810141c0380582c0a291f000c1c1c0100440d9117080f001c1c6d41d840c1d00319400074403c0310030500c051048080c0c450401c28511340c01004283c01d0020840c400d44003409600006058a20420070400003904051180d0415030b499803a00d01c42070000700c110f030244c8029086a0084255a02c00c642000102d000100502c1c0304841c0d0549454003150310300700c103000182c03d001c03100365414460740c1d004e06200e40701d00114001018481d00e110724003550394503051210040b042400c1e5803a07d07043c02030103442c03418003080380c04a80e03100d1800210018005e01c4000b2a491484025201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 257392850 1250 257391600 257391623
    0x20d0f091a0c1308010e0c010c1e05010b06031303110304050d02150d050907090e1605010c1a010b07060e060402010509100201060b03042009010f0605070201170907030506071407030c0f 81
    0x607138505400401c1468000303416200c0910050004403400329540b6405040b4100ea66150140d0340c00c80c0411500d401d01030b0b0004030b5007d002101240c100d500660360350039280c0c4100c040700d0500d54032031006180c00b07602102541c5032901d0200011034034683d400000c0d100703031703248291110035020031001c84610040c90103050003076150000d403113070300d4000600c252440b8500700303510341000b0003010414126840550035002040c6092100466203500100c0c02200d5204606514007020a10040c3c1140289601403c00e40c3e60109072400c40309490407100d0501e000d0744400e06020041c1e07000f40c10348039500015602c2a50218400300c0c1240508000c0c0d00120304000c0010600c000c3c07001c0902c1c0c040210304e9210907840f0100600040c480038041c240308140c04508004000d100d1036101d0002000d11a0052420149000d44425803015841042d240c1003c65070160904100f005414400b6a5119003d400c10703070036038441201115064030980c00000c0c100b00c24000c1402c00c118a1404102c00e268010703600e0000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 257394100 1250 257392850 257392859
    0x2a05030d020c01141e0f07060f0209041a0d1b150e0a1e1509050a12050c01050708030a020703090b0a02010c0306150c12020f030706020d0f091a0c13 65
    0x4540405580483c000b0f0012011540901c08110071640d00000700726004a0040c2c3c8841218900c1e00002d00d1029440390800886000c1804d5001d42d00040350800307001a6601d52113002c0000300d5044081240482410021a5025030391f607107503541c3c010745c00c01c0300ca00789112540c1b19204402c5490300001240091581800b20f0642c1c81082050104003e81e60a0051a03c0c3d059200503250450b0703040075007018202c420702c07200200080c14440c000030341c10710020309070321040003880b2076070150800f0800072442e041c0c10044c00f400300070354000b80b5005c0c20560315002d01d54442c9490b84c80014401c3c002c0c0c03a000210041050300c10040306000b0004404115164081220002d003e01105802c4400103401c0040104006a080f819590051a1920354a28118a0742d440c1420204440c401d441940901c0344202ea0082c000d000902c40103206032001a602c40c0f141c600c5a00b01c030000da2611021511301407604000504260140e4481c141864680304030f0381d10801c4000140c81096601a0025007003980002d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 257395350 1250 257394100 257394103
    0x50307030c0906090605061c0e1e150601090611100609050a050114010f0c02031c0206071d0a03030804020f040e07050a0914070807020a080708030105011206032a05030d02 75
    0x800b07848860009000059940c4400c0d4181e40d050b0083d1035100404115800720881c01c107641d01940c038083c0310042040c88102806a003861840f815020082c001c0d155000d4030302c402400491100d0300d441850111604140000900c0502680280818042d08101d010f203800010000b0803d5203042540c02d1020607104c07030042024200c15224000d005050100210f02d082442100d10f13100030303040e580c0030140c25400b082103c1c1c0212002c0c0598060017000c5101800c407902e00952042c07000c0719002014107003840a0010458610014009903d000c100c4955240382c3c0e0744101001101e4052401000648841c000a64000080c80d40160b006140c110300f81c00101b8081ba803071003150011982816003036030341d5402070b05641000a19040e145c0348140000c200500a42d1003a80004a6104603003004816564203240c59110038011b554540c00880100055030340700031031050f210369044090044034074680daa41e070304403e001a090341d00e0140c40c40c240008010b40c0100b000504000b0100c03482070b0320884010317 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 257396600 1250 257395350 257395373
    0xf0501150216050102060a0209040605030307050102090a080c01200c0904260909160504080a080702040e03070c090b0607170403050106120506040b060103240e090a050304050f030705030703 83
    0x1003001d0b0181c0011040480041d41602d0304031501a0003500c0a683c1c0c0c0c4510380000c0d8014241c240d4850b95520300811103803010405040036500c50310005a1700d07a4074030100481b80e451a0310510450740411800c2a20b66130040a201c080c03401400c215030306802441429092840480c96903410042c290100414803c1c0000308142d080c005480ca589220070242c1c045504c0c0c883c2e000040d801004003400f061610000b2841c000089086182c0716042ca45c80d0200719003056540300c01502d20801c003060400c154600b80c85400a20300c0900d006610701134043e42c40381c40b84c0c1d18034851245110f0f0741c0c2c00d640310552a0030080f41c0d1555440302051a9000396190f0500ba03a8015010a90b060b43c41c10303a02040d4468000342011b15160400020311856840e0707030720070341e040400400c0b8030304054958a042d00d0019140c007040307002c64410b0005143e0503081007280d0980e500001c05d030a003070394820408000443d40100c1180e0548806a80070041140304501003494145c407503001603054800c00600200b840382c0340038034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 257397850 1250 257396600 257396639
    0x109030e040c180b2803091502070302061f050d05011a03030f0d02030606041205010903080f060d060b0d050f030c101a0f0415090e12032205010f0501 66
    0x4100c55890440112040140c040f400c19240304018402e0105090342405400c841c400301c59005c41083d1860380e1440701083c44802d20700803039151030620b0100015840c1100360446290030071803e011160314020758030700d8050115080b81d510041d01c04c0c10600c1c41340c0d40b80090480580901003504884c500140200344c96071a40024198a03080a07246107004001c0b50000d0250f104241d080c04900398045000798005042d0641c407003020013000031595103820500a840d8050800040ca400031414082e28000c0020045280c82c2d01d4642040016521106980c91643d00030b000080c0b60540c1c10041003149140d201c002c0d01502c0307442030500086900000402c2000f00d0a000d690740184007115002c05c5e501c44600ca00f503880c8401c801580c0342e0030f005400c103581d12001000420340c1c0e91041e911240180d003c0d005070356400e444246407078414004101c904010400b2410041c07071483c140707440c031608a0001c01007059800c00380002100b440025040074000c5050380c001000355503500c180901c0d80b503100010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 257399100 1250 257397850 257397859
    0x319020606040504050a20190e070e0109090209030a02060c0a140d080103150906110408070f0305030d091505090a0201170f0a11160623130609140109030e 68
    0x185440c1040e014450050317074040700030061425980d43c6ca070f010f8480c2d01c0d1105210f2120f2101d131400c3e50740f010300a9807103550100c00100c07039500300b03a042070198500800050034001d6801040a0590b801414a0102c4444040058444103050300103800c0c506500406540209c01007083d56008030003040c1c0d9202c0902c41c60042c01191000c1600603100c0240703420b82000309410100400208001e049441041c41e400307800010915180c2d9218000c491014152440d0120003080c1403100c141d04114090150114442030f002091541c0d0b103481c0d0364402c003482c4da08000e840c2c01c144001c01c4011548240f80c0c3c00280400c0c4002d20300083c500355600b139480c1d0306034009001c40040591100307200142a010381c2c000300036908a6580d108000024203582000080380140c01c109001c0346c10000c1d003070015404d1007072101042f560765100f1840b01e400b00c030602081501c200c1d48280011408412031045166501200c04900140c00342480110300d04607162512841d401c00c10304208140d804800c444400e0b1040380e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 257400350 1250 257399100 257399113
    0x20211e0a062408070b09011b02131b05070206250206030112030e0f0f150409021209010507030605091618090504021201020c0a021903050d0819020f09010806040905031902 75
    0xc0f40b95690b92054032801c080c55200f08032100c4594440c41b01d031038a12055001c0398540c940194003041242800040a003c0d141c7d4480c45649940e8111a0f60b1903940b91500d012030400d02d41d0780004282d841342452091039080031105c400c0c150504a8500141150000d0409440f581d49480161340900820400c0b070018465450384080c42ca014420030f044158003030447d081411b0040244072241c00c410699600e080c409000010b242c481c07500040400c112603120074105414109196800d60b0070140c005c5061504000b001d10064175800c06113039000301c000b046011444615142030702c41200c40300f01c0f030450000c03c460100750003515070030080c001e81c82900c194a008a00064072400c07030042c0d8421440a0b00b00c452044090b190003d500b0000c0040c900c41060042c1d966a40d1515025000a5410210b24640104a800d4843c220b0880e450b00003440b0652610700d040c410002544a0010a2418005110b0105920761141d90001c0340c0160b01c0800c03203903125442e100e01c040c8900c100352240018030912 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 257401600 1250 257400350 257400359
    0x7140708160b340303050105032b050405040f0b03060a0605130209060d0501080607020d020a03090501080702030d05071d03010b18090a20211e0a0624 66
    0x50440003a0098001034900c1400c2c07514001640d070045441c000d0600d0b82e80403c041810070482c41600c0e0714580076422481e00007030715014050741e5050741302d640b083d0000e00c2420a214000802002840e1402c41100c60b103c2082400369080d0060f904a550031915000c0103491024555000c0c200414080303003216503a5441c0802c0a003524a030740100c5420041d04900900c980440f90050000c51000908803810f20a04001d5401180c03402d9004010b554801410702110b15010722060071803840c103101401c145021510040c01450080c03185030704200d200400a80c0716803007071098904990600f5014041130500ca400105003100410600d00300c1034030211601f810345014424003100b5100500044034010030800903444840e070052490a40d8010814040001480031000000103081440e0400708c1040713980610107986c0704040854510400d0300141829042c0000f240d009240c1240c2280703154051224140d801c1c0000703100002c1c500d40c100000817406036102403507440b0030300e6451741000755240c0e038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 257402850 1250 257401600 257401603
    0x3010905071403060a0501030b130905030403060605060c031207090503100f1a0307090c031b0801033c0201090902040e01080f0303040312050a060e010603050405061005010f0507140307140708 84
    0x80e50400d6000105d483c0400103075000f0380160007240002000440c00008003006031040d1002c1000458142d04001024820824a80320f1107001c0c140507513106003081f4404000c0c0d507491096400312102c211003040081c00c0c1038490100c2a01605015065800304a010b9248034007074440e04014200c1d072814845241c12030b11a00945c3e0400000050040607914035003208a001044da000c10081055211580c0360401c04241840d890303806000d540e07210340c1f58910f04000c0929220f940c001d8260110009605008031620025201c41842c9241c110341c0c003040602c0180c0c0c0c2401d41d64007171707042c1600102d0000b0f880d00c181c6240034103c400500a0341c1d140c3e248551103d0b22448100d034014046103404001c040c842d000c542c062607114141c004d000400039251241495041c0c000d03401400000e031110100300c00c10005110683d0400000d038a0400c20600300320019084040c02c071007010401c10301044031001cac0070768221658145e50038441a00d41e9180107040440d44650100700341c00c141e00c60301d513000404140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 257404100 1250 257402850 257402857
    0x12060f150d060203090c060418060f050603010509090a05100903020f010507022806181407080c060a020106050d0503090a0e0601121d06012601050112021014030109050714 75
    0xc0062080c11075407002d9030b40344000d4201030080300e018841c04441000d1503c40d54018006082035000a0340394445014000c1c0030745107560403520250050702c500700003070345600c015a0b054400840e0402035903580c05000c40d2401c0011113000e0001e101d040c000c058800081c0c3c2c825001240030b0b0342a10b082c6200000740a00340d070001e80b00d1000682c03140e25000750502c07000b00a05151042c1c070070050300020040e11000140c41025506101c4a100c45501c0020410b0390409046100064030251500a29006cac156403a1404442b10900824002500d017640c0d0307100f035010b40090000180300c0c1150070000e08009a42c0c4d000715035003d0082032000400b09000c5242600031303100d40c0e07050355900e0700780900c030f16180c0107010000784150501180e200c002d0310940d030521901d8040c00c100c90402e8276400300804101c1d00007200b4002c0001e00e1745480c00511000780039521400c0340503010f0b1a0003100f00c6c05117104443ca01180452902900c00100001c900d5000c01e4000740d0094610369503048c194004803401704010b21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 257405350 1250 257404100 257404141
    0x1017100510080f3103090501080a0b0d1b0f17010e150705070804080f100c052110050a03050a050610080d230403050a020a1d04060b0301020912060f 65
    0x5003583c0c00549007415074400408040000020480e40c015001c084041c108100071003103001c2184c201c01404a075078401c100942c041402202800340107c1c1e8804038507056000391005d0510700032417000d00d02501151200c04004c080545410000c60b0b9101c40203403402040e00010b00065081c0002020f12143c0060b9030b0102c4071071a4445511515882029910755009400c100d6400105000006560307000f03215000d10152030300c010f072040c1c1c1c0074a4400422528180302040a008040c03140804444a48280740051190311142145944503901811004038a5501940c2d004940400110800c140030501030350841c412000c4540c2038071458200170400741c01e400385c0565944040e40788206070b8030410000d5400440260241c03841d0000d00601b0015900641003034420303078004040d10741141018030b100002070548942e1281c40a40b415a56490742c3c801601c003030310882d140e480940e03456400b035048408080c4000c1224041042545c130098a6946c00c4840002142a4130700040820101d60b4412241a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 257406600 1250 257405350 257405371
    0x23191212080907060e031e060712061503110c0d02071a16110109051e1306060c080708190e03060a0e1c0e060d1e020a020c101710051008 60
    0xf41c01c0c003d00300c1d4091411052503a052190011812400fa1311000b2840207241c80c1026150615180380c014220b21030394140300407400d140000c10007003d03a0f81e00450203001501e14000c40d01662141c0305c00140e029080700d1000a0140c040802100c5400041050407104005c10060450020003040c0000b80101000140b8800c103100154000130b000c01448036141030141400b02c596a150760110340000e00d980345444821000d80500c01e500c0c5441100b0100e0020141c006025942c207103d00140700c0b40c5a83d2008080c0301c0c0105804080103100c900366070701c66031051ba820b4084268044010801e00d4551207140c0280603071404540d44525a01070030585d10902c000902ea5600e1015190107000c60814401d010001505403240b695500d0800500700f4a02e40c0c8004144105510251309040e2441c00d0090966032040203002c40680d000305401280200c00c42c1c0b42c010f00a494034040e40d2040c600070180c01d0008007201040b12481c5120001d4041d14010f4a02003000c1c0d046401c144c071003600a55660000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 257407850 1250 257406600 257406613
    0x3020405091513020702040e060903211303050a02030d0e060a0612030c031d0402040b03090c0d050a15021b011a0a0605040b0a020f030304031d0901231912120809 71
    0x541c0c3c0ca07a00180b42c0544054000101c40e9031408115042c0032080d600c000850b0000100281105080d250200181005440d101c21070701b4150000080c441c0c0c021001420f012010a0100c5603a0013802035600c090794030700d400e1001004002185446600c122910320445191030303008603040341000c01d00c40ea02030b410b8550a0200740161001d49001c40300158085100400015500403074541d400504001c011040c91151641800302c0900d0a0160210015028060071400700b000b2420020f1a1540207802181d1081d0031140e001921002c0e1085248540361301c8124039040700b00c1c00056011200e1400c941145000382101401003000400c028482c0301c0008006000500c40e0f15540c0005100c070011500498050800c081d04060854108880c140d0115a0003072400707800c000b600c000c0e540845001c5a6104056040100030030b644282000304100404443c195510305031640400040080c0b8031000c0c0e442c40c2507461544c464001c101108c1120306005848190f000344c1d02503c41a40114500c82c041e044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 257409100 1250 257407850 257407879
    0x906090b1b030903010e280209010612020909160201050907050a06110a0215040e09030a080403051b16080c0303034b0f060117010512030c030a030204050915 69
    0x80341141c030464603105000c10410410103036400d1041401200d1400042e041d800b0710034224111300c0501e5000c059001e404400c1c42d200607a15801868191205828020040300040b0b40240082c094003c200d50410300400610a4602a8018040c0d022203a64024000c940da900c10003921502c0d184203d58000060f000244013a070b0194281303a242041c907a04803007085800760002032078003032074603240c3c1c0aa010002e020b00910766440300059010348490011443c0c0003603514000d00c0c81030010400b42c1005008102e0040d181110003141c6032140264046a0301038001000d050b0f14441140f140003028841c00c1c1c0d02107840e05000c000e481c4500705040303040c1403009002e155000d02e203c4801d1f4000d0607000c8903006030502406440d01041e43c4e0400c84421156180140c5180e400000181400b414400250784d0b600c408002c0c4e00ca01c81c199802541d02d03481441d41464441d1071405a41d50041c1c543c00041210502e580e1f05602034821200d048465281c10b442d10004021800c40740001c01d41c200c1019500c0b00c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 257410350 1250 257409100 257409127
    0x1309031b0f1e0c080703150e0c03010e0d12050108060a0c050d0203040309060e01170a020a09030203011109040b100503041214070b090606040b03070e0a09050607030506010906090b 79
    0x460180a0340101d058580665a9216003440790480b5214078041c0c00d0840051090520000010b400301900a0944508646942041c0d4080c1030080d0040c68031014481702c0c0440c00d04c0058100240940207014140e140c1c0c8205171207190070411000010b40c40310820020603114000e140c101c1d007080c005041c0680352071540f88043e1030b4244043c0b09002040200012211a910042d8825406603942c002400e00381100103084614030280b103030421451010000e441c0254010507034004804407030050f80c5025039002550002951f620103581940f07061005200d000d14507000f0190450110327800c11010b46205c04026159011881e140d00080c1c00707000143c0000c440c1030000201100600345401d004c400c80c09090816841080d00b152886c1088003402840c0d082001101d4111030100c60a000e200e0145010036600c81241c4240191f080050021801d4604030758840c2c1241900001926424034240c203000c1c1c081d00060301d06500055010384002000707449800384209588102c851149000c2020401300c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 257411600 1250 257410350 257410397
    0x605030f06010201060e0103031e030c0e0f0a120b15010f022802211c05090d1e1b080604030903110f12100f0606021213030605070e130903 61
    0x1681551768894001c2280c00c601c25510340210712981e54620220151054401124001c0305c1e44004d060070620f4100c60306421507044003040c3c50903241100d07104003500001e81c1d070001a17030048111f175600c10141000d1003889190f0a100e086a1084a554103c040004484607801009000016006000d43d4240000c80a82010789031104072030400d8070390459000580b1408002d542c1640f074242d9000480e070354040c184035107084002000b100c02442d00581601400324420403070803034440d0700603188c0d0300100701c041390745145029600ca80c5103480d90540d29004060003000c8059110f610b00d05500082c1c4a03c1c0010300c0c0d1310581c1d250b07807103403505c902e580d13505d200c503400c140c2c101588921742d00c010070791688402e14045035044a00340204420042071596904032404141c48001c86410010306104003a0001400d050180b21000403d139104c1d088403000b030302e4007050742004200d681482c0900c0140343d0700c184040d080002c03ca0380001041c03401514001180e2031500010007007109025240d034080b031200d1a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 257412850 1250 257411600 257411611
    0x1e031524030106121e0b0102011803090612060e01060f080c07110d05100c090515030c04030b061507030203072a0501080c0c07091407080903090d11130906150605030f 73
    0x440e182da00d501180c400d220100300e00d810800c0c0c4c0c81c01b410b541e5607424000e821201c03004458100c500240c80d2401090501e0328020441485109850704440c149194000c400819100104905a503191720000b400c4600c007684883c001541540030801e00134140c41100c50407503100402d800f404c00c0441c140300f05001051402c2d078041c015040419030243c6140207101e000001540ca6010050800042140140c00122800e1201e05c0a10400040038103000840701a039030020220343d4a45e5a81001422606580c0744000c40440089804c104050700000a0083c0340e200317094040d2100d4410541484c4003c644814442d0348c088c040c000c12441d406500203e410450070840c4614010a8440751842c045069110030750307680e41c0345c5420340ca0300074544c0703802d421042c0f51512a015081000f4040e68a0252602051240119081000800c00d51909045110001405414024030342404030001050801400d4070f00380e00b02a03800100c0441a403842054030303029100c840c10740e10b58243c00100781e10001d16 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 257414100 1250 257412850 257412887
    0xf17160c03060e1b19032405011712070f021f0318050a030f021612050c150a2105070512061504060806040209151905130b1e031524030106 61
    0x40110202d41184c4442074138040460004c4181147d03c1070b60401c50700c0503400700c0302c006240f0300e0ba1000720001003030703a005c03680d500e9141c00e8494242d13051018680c00000310003035000c02c90341200d080500011f030704100c4000302514200322601003119600c400000c6440700500715004401d41c00e001900400c1e581c5c402204601c1114203403440703e0705101844640c1e4210540f8182010311001c00c10004001150514006403099401264007051501c468040d60214030180001025141c00e03001c11107805101341038500f2400e003c681080400a40158440889194100d40034400520f00f81003044000d55882c0703039403804624041c43d160080b614040080c006940c40b640802c54000e0039640d00181400128040800c9540c4c1c68800d1140c0003aa0040d8034400d050000074402c1110010000e200c40b41103a0000819966640c541e0300070180f80710a029010495072404401c0c03000c80f16641c4400e42981000760b07844c03910001c00d014112a141100c9000840341c080410040c807402d403080b6058100b000780c506 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 257415350 1250 257414100 257414149
    0x1103010509090709050a020705060c04050d12031113030b100302100e03030c0706030510062309040b0310051b04080d0e0102120d14060d0f17160c03060e1b 68
    0x7025003c5d10420b441c1c00e05500c0e008240074050150a0042c541c200c02d18001d1145420b10b0f20001c240000c40d20b1b0740180c00525003d81c403401440c0640c0001010718140c6034007590b83e40500801d075139031000502041d20309842031000100b0700c92200c0e8503007090341c0d00149000e00d8950601d00c12a011a083c58009030913000c00e00c0603403c200800c03c003520150140743c6000c00c0a10b00f451540c0640c020903800b0500308491914034181200b25110000c80c0c00889445659860072840080b402900c1e160300119018420150740404858265010303500070708100840c2030f0b20000036000c03005d0364003a60040c1031041d0010303411690344034000c0ba041a06600c040c01a103800441150710070b00240c00183c03c0d0f1f42410348444014004454554520344d00507421111074807040070f1a00e030400c032080e40c1c0000a010103009000641c05e220000c00b99082038044290000b00d00200349010030b400c2d580c2d0f2208544050402004000f45000400e640c440480c0c0070301c020307078908024020043c010768402c484d54111034400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 257416600 1250 257415350 257415359
    0xf1205031b030a15031202060f04030e01030b06072001030605010518040507110609070608070528180603060905090102030f042a060c03090f1d15040606080906070311030105090907 79
    0x102d0a031301c001e41c003034010907089180240f4084c2c00d00000400320907006040004220009820892003000c840080c80c1c0040d56001d49400718065100f400c0028110845000290039081d0300056031569415080e40c041c031019564074010340d07440c06201d404807071100303106821008605041d4802c0c1c0d4420040c0c80e01d000c142c00709550071824014190303081005034114130300601c8000d401506181d0001054584640f400f0f0114603680c000c0f14080004e24003038840e50302038940c62841402e50a0340f404005903a000010341e1104090028151841002c180c42d04100c00034140900602c2520300c01d031610340210380c080d43d860ba0341403a0305042d000030406802d074480242540c0240c05201e00082c06281d00c0e010200903080c10040c0450300242e1004405622100042c0b115000c00300c0600009810303201c008005446401c00d00400d1800740361070fa600545000000655950300c81030080c0600d844405940050300c406000701c2c151000100b148078080030400042019003041000150310014078401d80d100941c03034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 257417850 1250 257416600 257416631
    0xb040c05090c0a031401051f0c1707050105061c02010f1b290403092601240909020612040f051b010f0e13090203030d05040f1205031b030a 61
    0x41d900041d441c1d20228540700e006426110f0307044003c00221290246601d0b1100140241a40d40240c0310b1004d0b0070341d803002c8914045c038010030b0300d16400b411001407022b100304201060f0300180320a81c0d107903080c00081350b1076040212901b40d1800118203070003400207203600151070f151018004070f010007130480304500c1d9070b40d000e41281c0c080500c0350100c0d8494603484140c007240782185000f2003030700300381c80402c2c070000a40010304401244c83c0c1e1440101c01f9070901d00704001c203222440d500726480d4245880c20b4482d0440d03180d4086903480702d10340404580c0c1c440f03441400f25282c0000003900024108112024194034449070b60340319105211051800440355111802e1244141200030ba00c400354030209a80e41c3c120111550071190392602c0300140300003c00140180e01240900c40e0880c1d502c3c2008000d54400380101c070501108886c00b80701c103040924110b804d20400319019252641c1040522116030302c100b0859004414080c68489110107030141e100c0c46a002528420a0650781d07070303000109244 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 257419100 1250 257417850 257417869
    0x1140405190e070303170f0105040e0a02060d0c03110c0706080c19020c10030b0a030206071a0705040302041a1e03010e0706050c1b030303130c09060306020d0605030115030b040c05 79
    0xc22809819998079505d4082c0400003403601d0b02c100d01d100728081100daa4100c1301141c0c11908100e40c0801c480840042132810706580120203500000009206e040b0452541c00070000c240d00b0350380400c90024001d01400300c13801580c00c8010586c0111000300091032080d0a001c0c0c000d50b40540480c07408800307075800111000318500c15009600b01c20303410748441c030342505002c400c1081c0e41002c2c088950203000180000c982c03404028031402021810740305121601c00c174040591204d0300d101c1580c0c100000060481e82080c4400c070301c510b040141d2000d140c0c45500c00380000100c003070004407001e46109002c10440096803d0540c0566030359580d540f82000c2080390074018860b0340c80e5241d8480711402c0580c00e281080a001c1d15170800b5144010050324000100c03680219a101e9098482800346020740814509038085102581042030100601c149503000b40101d071003203401041038554070700c141402d070342c00ba00c0f4011035030f4040181000403841404540b54000d2040340a00a01d90300c42d40000e44a84 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 257420350 1250 257419100 257419121
    0x70b0603030913090507050402030c1209010b03060106021b01020d05030f0a1b030b010905040204081c050d0606050301051e090c09010c020411040503070b0301030b0c07020d021519080114040519 85
    0x203455a00c544e080c400103210b40070191400361020b61952030208141090344c0b25503143c03284200c000900084c4410000e52000001000041c2603490721b582da04d00007596600c12400405010640c1050b5500d1580000340030072184400d40c66042c150754841030b1050704014000c0107440c41c280c841c0c2540342008412422010008825200000c0380c6550303100040c00255240c03c5a030107903204000c248900300001403c61032811407000390130740e03407984544102c0e514001c448008000900381a00440c0042d000030245050342c0054500702e0104c404002c5040d20260404103c4d5049206100030803410805c0d50010b00314650f060400081450291b400300d800c4611607641006800c0b00409d0600940c6001e124981c01007410840761400c0d5411500c8030580780b04041c00140c030803800001e01008545941c00d00d840c490380c008024030000310029204a10b681c2c80a09521100c181e01d48424044a0049020b581070b00c1d02807201440100003d01480001c201c05040c100e003274908400c2d110410800c500550b400107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 257421600 1250 257420350 257420389
    0xc0f0501050415060506040803041a0d0c030504021003020901081f170607020f030a0f050d0e01140601080105190b070c1503090501050f04020612180d0309020321070b06030309 77
    0x9800c45880c50101d4055805c9a4490300c4100420000c82d1400001e44090366442980d1007200c1070201c2c0c41699500c40c4904044106040141c10f1250540680c082841039000b5141c0403e501f40d0303c90100e08920030b080d11680469002c0000c208841503510a50500d00c070b540700402e171440e0710391420001035600ca01e40012941d0003007040090056040c005500746401480044d414412458005844501180c801108100e000b14400d4003500d0756400001d543d01c03280008000c900c0c8190301803161000c00301c40f40380c00f085448000003000d0820181041884c0322042c03081d03144504203a400d410550209000303944e04c0303201c2100410310540b409000031380841980c8002a0303801c0a450100c0c07c0d200c1c01050703000c840303011404200160b202d00080700c444592000c140d20f00c0d907580281c4048600d001901460384c51068207400b041882d055840708a006000303c0c1202d291803010020341c05442c00c214005c050040c81401070b000003684042d003564100794000c065a007410f00318400308141841c2d200850300ba0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 257422850 1250 257421600 257421623
    0xa05011506021609240305101d0c121c050409050a0c0905040213090c05040305071502030f03040c120605150109060905101209080c0f030c06070c0f05010504 69
    0x544200c04040001410340d80003404207a00812014520f648281c482c01c44410303140e440b01001c020b200d05240d503051410a0017040b042c1d4032030400d99030741c15a00d0018001103142071010420340702074200d1111982299002003400141d50f10600200800b40d2000c0c0c0745a11801c3d80b9a0300359807044e4407600f5005203907600c0e1034540345401806019030701c0c050109030345030b03103002e040c4052154000e0700780040c1c3d038090343e0242c0e42e1440d5124500c08001d080c1d00a0140707a10b8028030fa600c5c0b9030300800401c11240038008485543d9165042441d403002d0000c500000f590042051601400c000c1002c2c0d80c1c070500982d1042d1006030740305501852008854011034000360303103c0070080c00704036161400428000a181c0200326500701030300500200c00d103005913403040042d200c010110620481803120000d80181003840700c403186d844c00154070f400c0704488980c030b4086c07400f00980f02c40001040d64940e4646c480100f00c0360312500010758005241e420160b60801484d00c0940100b8401d004990281b0f1203400024030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 257424100 1250 257422850 257422871
    0x90b040b07113301090b01030b03010209091506120a0f06060806010c060e010f09060b12030703090b07080909040b1f03170a0e0a08060403081506120a0b030a0501 71
    0xc034054010800d0040c003a00b0800e0407408000051080b103e45080d242d104240b002084909603001c280540c01602030025400114a110490708241c4c1200402c1e00d0600403080c940c0d04040c01c3c0d0280c820170982140c0300030002504524002100d256100001e01004e203060010b01c20a40c2c5d1020494055842d203854844e003680340c1400e0704c038942c010203840c5002c240314200350000070841c07881c540c0040c10203911200710140e00c08003940a03110354411100c0c1040740666a00c3c1001c05802c480d100188660624220350318001c501200312143c45a0682c0c40d0801c02d410440401c0f0310380c00240050703030200f000340300701c2d82d4588aa40c0020702540c00b81940200518110b100100e1040809030104100c1d4820441080016881110000130581050307040ba07c9080b0050b0880e27400b0307200c40360b856200c01c1d04100015900700114000b800b40d80256180845651041e20760a040c1c40c0685859402074410011110108513901c2c006801407120381e408283d810b1400000f81c80e0010703a00066446943d220b5403c075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 257425350 1250 257424100 257424113
    0x501080a0203090a020f27060307060908070909060207060203040f0213020901020c0d0528060f060302060a050747041101140708030c0a0219020906012001090b04 71
    0xa9004a00c0002545186001c1c08050b441c0c10324404003d001d00282c1d82c800506580d02c51040000c011001709503924070001d400601011981501c8250090082c01c1d030120381c0c0742c400c1c40e05e0000c0d20014001803400501c1d10000d00c008000a2905070f501950a02210700001c0c1c4a0000314016401003003a040000d0840c0100159442c45265841041d4030403c010341d520b0360042515000440d0890350803030100f403903050007401c11149401195030016000034444c06c24117034000c0661041d024800801c0300040405c0848110b450501001c0d41c0140c0911200040600c284010040e45128000450900700f8a41c40c020307151112100e90030110504495483c8500e40400c402d840301d00300c22011803103900b0700b0f40307950628000c0c4002c81410005422a403040d43d00d280000c403200c050340108005d42e41e142c180d01c2e0b00d90329001424260014014004250500c0402c601c50165607a0014404406604c8804c0151803406000c00e41c1c05108040c20040c1780405403c1c4180c4462038040c4031071104510701032800d0b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 257426600 1250 257425350 257425367
    0xb07050f06010e06040e0703020d0501051e0c0405040504051c020c030c0d0f06020304051f060608060102030a02070902090d1b0608010509010305063409030b0612210c030703090501 79
    0x8041c1d8040e00042180c1c458200b2140d0700a134050b20000782c0341407420507a50408120703800280d0401f00b11000389040207030550106115500d444401044803139036000c1100020802d0f40d002551070300900c418885490160301494100d485401204c0030100301100040400c2d0780e2220a0000d03802a078400c50b135a040c180a642547d1340c0844131a0307140d602e1590f845480200742c41011f029241d0100000d01001002c0042842c4ea011044040c20400082340c8414068203613401070341c0c001506140030424a5000100359000403d0b0343c3c0103000303a1820009204001c1d0442d8544961108658855201080d4110150351807440342c6008086103504154001d444110181e100c80c1c02000c0c0200100041000401c0c019046600f0002c10025001c2c0605c2c9424056000b080300301c50701d06480144207045401030740c50422a442000201c255a4030002040b807180a40c0070141241e800c4480400c0803082152200c1e0a00084110150304051100c0c1074685542c1014404402080124106100541c0c001d800c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 257427850 1250 257426600 257426623
    0x5100f030f02090d260d090c050405010312030e011b02011a01020d170903120a0f0c050f0702040e07090c0906080a110f090a0504020c010f0e0a050a0b090a0c0b0705 72
    0x3075103004904008509202e00810018241502c204d04a490399104802517181c4581901c1070191681c214954a000414480c02c1c100c0d8440d02000c8000b9041c24907008507030480e5001035071002c0b901460842039001e40ba0000c2540341d0b6560b0f6507030a0b003108030382c4200070801107071170350000400780882e0268442c40c544e4450300d00c2c1503510000d0100903480e0700c0903004070316110615010b55542c950341c40140ca140516034600740800d01d014200001c100d03413540320503181e1102c00701c03d2081150544090303a462041c10569038400004004a2000d414030341c002109461142003207811956482c105001102c190b01c407440002401001d0800826a01200c1642c0120b0300000c10000c00c850301004030b010f842100a0401085404039641404d070f41c409407880005c000242003507507510010490107009020304d00c101d001d081d180c504844940d03d4001107034804154000000c2c018203440307455803c419540140200b201d4451000c580b00068803150001c001042401c0d20075803120120314046051071720f0f541d034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 257429100 1250 257427850 257427881
    0x4050112050607050d0b09250c170a0207030203060403030c1e05040306180c0303050408100204083a090608060d150b0102010207020613060306080613080f0405100f03 73
    0xca4402055000c0750064000301181002071759480000c0c508400b5000d0810840d03031002042d410480c80f80010f04c60481014520450070081018001054400c1c0c0b402c1c000280c150350b880300c1c841c824041150700403d940b5800d401110381c3e550307499001919000341120201d002988500c4040702640c0c1010302c031034401c41000003d140c0302c19035000042c90390046100181c448c640b00e080c51520030400b5041c0c900d00f5500000d4540a1603202e00380508903600034400d003038540c8541c0c1c01c0e11a106100d44255000c0e544840040c0c0021100a000c0e034210001c80c03446000d000f1494404828448100f00c1c200d00c0c004602c3e120000f04a24108000e01803640041c40c41380070f0400360142c0c0380041c0074409002d500030000c100010301081c9060040f4024018560002c4d0401d00020f1103034400729a42505204981a5a500707205441c0c48049040d1206000d484801c902c5040c10f080d8400614500f002d000801c10341248941415503c1c03001030451402c4451903000315443c0c08003400301c2c0740d140c014061020203101c0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 257430350 1250 257429100 257429129
    0x1e06010609030302060c0a110f0706090801060617040203030405060409140105091905040c120b0604050603030a120b06070204020a030207110f150d0f0203010b0307021504030503060613080615040501 87
    0x120065145c007001014041e043c41c000460022181c002c0340701c071010741070300e2040740c818100c61160240c0c0c0e1a142e000e1900810700b030705800178481c1c0c0140681030607074202da034a105401541c4240900c5c02c3e400130f0812a40f5000501c40801d25032504e0300075200030440d4500128442081e00130240c1041d0040e00064010410ba5080040bc8465144000444094100b0018460341c860504040b504480d8000c08a1015021001010b00100400306400381c007040b182045142c0301d02c42050754030320500d0b1403400480e0f4400b0400c2089070940c0d0111480d841c1c09071a2a160494660004003260f01804183c00842d0303001c05c080d028491202e454190b001c000387c401e4250607140c000003030406e03c80e510086181000018020100301c0c6c05401065071b014031182c017036480307507141c007030b154a04e4100f22400401441030303140050840c2c40d090602070040d41c15842c0c461454075003e06211042d8401c8054641700402c19a00180204003081030340e2003001d08a01d68002d86895804102c103490040e8411000059804c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 257431600 1250 257430350 257430353
    0xf08070e190f0e010c02012a140f07030809101e020a0c060923030f040b030c070c06020706140708030a0504140106030f03090602030a0c0201120b031e0601060903 71
    0x40341500104524400c041841090000d44003074080c04444801031030805000e6981000150070038445010301c0d400a01c0000080b2004850105140c1503038510000601c404800c850f00600d5682c02100e0214203603454180714540351403050703100400440000310503404101c0304003424002c00c1080307907411006006140d0503040080e58940d840e00809110341e03000894100c0c05000c0e03500c00348030740d81c8030609000304a05030600041d01c00d0f5619590300180e10031000040742000c0803003250800021582e1680c02c02d8244480010315400042c020009098108500c01c00305c2c3c08190f101008140a03401001b003075051200007045101a8001822040014456000001d580f001036a5200103e4507001803650f0b203074100390301c00b860319816050b013035480c0042c003000740f1482c0c60508001c0342c02034032103035000f598030b540880c0d4034031408029500148040d14140010762140182c0e22454000010104800c03505100280c240f104501c2221043c440034031004480010a12115006140e5030801c0c04545207903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 257432850 1250 257431600 257431619
    0x15090f070501030c0e0a2310050706050601120207050705030f0d0813061407030b0f010c0b0f07110106060507020a0b03010317070501180b0f011406070305030c0f130f0807 75
    0xa40a45410b251300c8031a0030383c1d1280b14007940c1a50f400c000304000c22242c0c1d01d140c05451840940c42400e0105489120b0116505103040100945907195651902e0002641c441c480104000380055041200011080b92084020f0002e80907035030041c0080c0c8a86490141050315281c03441510f040d0075003103c1140380130941c111410a0780311451035280d14140b80507107022001400e43c4001b50281e401e480080c00403d643c1680001c0394003c0943d55041c00d01492001500c4038201240028003512039400000c000030300d8034114075007019090900c061010303c51a2001c1c00c1d600146c20840016801040000662510b00c2c0481e006041a41000d8a103504648601001c000c0da4034a8084090000030700798101302c0250b00c001010b1940d0304c1d01241e030104918081007200700c140c4580515901d0800085030388602c0390483c000703442000b4441c0385010b400c0c1d035058030103800050680407040414043c8000b6005001d00514202040c000c051010703c3c100b0524042d51141600840400d5101c4042405440350 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 257434100 1250 257432850 257432863
    0x4200108010609030b0c1b030c010501050603040f06020705100606030c0806040212010608090a020402070b040b0604062409081c0f020111071515030320010e100b01140c15090f 77
    0x100003406a003286d480c4030a040b1203200d0344a000840001c0141489044800480600b4544100000a200c144d030384200b00112030200b524040c211900030785405000512a03402045454880d0060f140c00e0350b002850b050446d92030b80d0000e004a6110f41c070389240c02e640032400355480141100d04606050050951703504800050007000c1c24810000d01160307a0740c2042240203105a0b000300259900c107241d14201c03c5d00e6800390707811990005000c0203d4401d00e040d01500e41503861102c0950f107442d01082528020813000051141404451034000c5001070b010b1162880d4880354080002d1300b000c910301c1c010602c4161400c00f00859241c040c0c6c070560700c50510704840340301f9001800e0300d8003401c401c1c101000401102071f22000400c3c12a8002040503045807004500000c0710000218410064464600381c520440c04412644c0010580200500e100e81c0302503d400010f2402c90040c2c0070300c98000c0c041d90b00071102c00540f0360101c20210080e04840100551160081010f4032014100288040c1d4980 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 257435350 1250 257434100 257434103
    0x100611010911090702030c0a0c0e09010c0f030b04020408030d06150c0c120201030f050a06081e0703021302090307090e0d0e100807030b220609050705040b07020102070e0420010801060903 82
    0x300d0f010494680c0f0030816102c882c8040b00039030721020214a880c0b6075511440c451040d14034400000074070049410f1084c80d14070031850721520401e080000707040300108041c65166601a90030300000c200340a0801c0500f0f038000c2c80f41c0000410702e043c00b0900d902070410803a90780c10004195600b40c0010146482d00088402d480e0f08003486410714401a0094842c070481240181c0c0360000b04010390070710340c2188088070101000d0790300c100c000148003182603000004180841d48100003c000500340034460040e21280c1c0c080050620310703a240002c0c10421150b1140303ca058a0b0010750715884000e124030180c00b0034604012010180355408103207550319031042c1c03000740041900001c59050007134220501155004118014420550524402c0c0b100000204072100b8600180422034645522036203001d0111a164281068a0300e550704019a11103136049046000740d690000e00144855000c9016a02c581c400c1e241e80c00740705c902401c0780207951040a040080c42e000400c110744d0030503800810359 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 257436600 1250 257435350 257435359
    0x1d0327060706020307211a0111070e0604060506071a060904020f040c0c170d15080a080d110307080f070207300506090f0d02070503030f07050c09100611010911 70
    0x3da0310f003841603546c005035641d41010f8018040c2d10091183d015803140603084030002c104001c146903480111000f050390800310310268002e5406205503400110038070b0303100d04020000300b14540c07220701007103140d085120101c0702030462500311b6402c2a2112001580700c0010ba608035000d1619400007031100300c1d00500380780116035440c00b0b580390512034034214040c20b130400f03242d15800509080283e07207030303100400e5042180c0c41e100990f0f581c545241e040ca01251140c02c010300c2e6816140d11400703000e0344503010301e1042640e907410888031500c175440618070030320440c0c0710318145180403440c144010034020420760441d008040c040c001c00d4802c41c401810162a18048441042101c90083e00a8525800500148942c208220702c0110001e04c82001c070410b01e0035900050480032303059039501ca00c2d01806d0381c107801c20b000040080d0a124054403100c0e004104580c0100880008544844c009a541041d8410786607002d1200c150480000700329410910b000704026a00707604d4026940c50130b0302825214 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 257437850 1250 257436600 257436607
    0x1e0a030305090402090d0809011407020a15020321060a051009030303021e07050c040b100c032a060b03010c090b040b0c0c12010501050108060f180a1d032706070602 72
    0xc586499045d5014104007400038902c50019007040e82043d0003040e040c500040400c076188181e40800c400303440d0080c2d4090104007074182045031201c2c103050124500c0c000c511060005640482c150702102004000500304032072103003003032400e028a14525800c502c2c0107a11200240884a5100e005401220f81600d00181ca8940d028403a403103198100078004268000132610005101020441c104501000c440800111504805100c1000301400b1a840840e508541c803034007190188400d41c804e16400d900c0600d844601c03050b10f00780010301d4a800e036912075a4040c0d80219090074481c00074100c8a0b8100005002d00e01080c50030350384070768010140e04020200c2c0041160800b0420101c0c502d000074103541d01c0c0b402410b00c5900802d000d2040b86e0005035002d0101d280707801e0041c120324072848044d141d100e009d205509900c110740e0001d445080600d40c0c45d0780d030b01165203107080a40903845007a000b5544d1015105441150f1003802803130700c2108000b00c045041c4075554041200d05103640b01002688 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 257439100 1250 257437850 257437867
    0x7060c150507031d060a0e0706050a0518120303040b010b03090304230406060c050c01210506030703050f0a05100b03190503130b070204050915011406040f141e0a030305 74
    0xc0c4c1000004900042034610503054903080114210388102d9042c0b008110101c400d403603aaa4a241c40d00c901c40c00b06200700512401144140c002b01038400303e0307208a241001c24540071540d00941c0c080135865603040070003400b04000c00c02c1d200c42e0042c0300350000b50307041d410502c075060340ba4890b6200c2c4401d0703000c03503c036010742c01e0302e0110b410080c2c210014010032055903680d10181004681c0c203000c46c4c1600400400c182d940d80501d0780e0300c0940c813299400300d02c010400b4014100410018083e50380c1403141050005c00136108001c0c10041180000140c00c80d06c0013450000d142c4404180c65540142c03c1a20480440d02d001802e00800450440c0c003050a09250801600310f11401c1d00c00c0e9250750b10b40c000487c00c040c000b00107000341c510a560401c095903881d600184c0b10340050740345a4200000d040100848041c2141241b89250024505450250360303640d0b0f8003900d0484d501c6138106140e4042103010b80e14000c0d400840c0c1d0b204480034000d0340791299001139100c01c51800002e017400000b098400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 257440350 1250 257439100 257439107
    0x21504080d17130615090e0d1403040b18072303011e110c06040f12051204060c030f050a06080d021c050d060306020706090b10030818060f070b01030507060c150507 72
    0x184500748203900000e01900d402d0a180a0107002d1f40c40340741d03441850141e402e81d52180788810f407800c00f40c12205040d511565030710010f211000e00301e5000030516071000c0d00c03680b4051103001c00a0102803a6041d8070b0261641c20400300d5000040c1500c26490981480b1a640d045080c120b034070041d4000006a0881103402d0186c20700445010b12101e00c2414100410402c0b0070010285043c0203030741c000c19248600c0802c4a40b80718001c0c3c024100581079020400140e83c58104080c81e400d0342c140815000c07845001c040846034125650502c16445210401c00300c4824010242c201104d4400b03044003c1c52640c0c2d034540304c8840226030040000c001111102185294058000b6560203c41551f071514070303060240142442d02e8040e16600c0b150404143c030403441101c5030086035070010400341011070000b690b100d2400c111118a40282040000f080011655001803010310b00c10f00365810310b54150b05045103881025040703002407011410103040815501c00c0035071080c04600c1c102155540d6801b4048 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 257441600 1250 257440350 257440361
    0x7060506031c0206040b01152f0d03021b010203040503160c0f060c03140310060e040f050f0108010b030a030801121506090f18030f050f07021504080d171306 69
    0x31100324451014100b04140c2c040b59081c01240113405003042640c0b44c89030a2100390701d06c001c0e01b010800001e0f940b2880c5401c0342c2256060382c4005204031507407040e10091800c2030483c0b401d0400007940058400700c03140203880a40c0c10569614000c50a5240c6951420f40c0c1e0311840c03e124080d250030011a00400c60324500e540003500c0000303c081221941c800020342420f0055004070046000a030f83d0a1b00402c0d00e0701640d03c2072142ea000b070995a031a084064400c3d40c9044040c60f0071039281c5030310940801c068060680290340800502025614040d0b0090840c0c060010151280e04100041c50200b903110702554159910801e03244010841490184d456140c0718000036901401d2480c0090100e195501141c080c080c4c038401807000c141c01401c2c292003607420901c001c02180d01c5012031008984510050810f6100c2c68503600d107042c503640c000071418650701c0c0305641c2d198000502400303810014040d60300103070300600b021003209180b2004460745c428001c0c03400c0ca00081c0500410284146500503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 257442850 1250 257441600 257441623
    0xc1c0605030a0609030f0f020c04020d020c0f0d1218020405090a02090c030109150506030106030c12060e0709140307092013050f190501120b060d0b040b030f030706050603 75
    0x200e400210192034020050074041000f0740125007426200d06e0250300581646e0400075295001d40b0f0322154200c1004002e4021000011801d0381c2840600c0b290201040f030b4080c404c1401009107001943d001c0000d104242090b0000500e506190150882d203a202040041e516812540405c49540d0028454a000305040d4065400262030042c0a06446028020741c107030b410750003003800031078150b04800c1581c0b00c00344680c0c0d8212200b000100032552081d07004242040d500e02e45521115904404402a41c185400c2706071b0f915242c5050000150308224140c0060940d04191301c039190034500000d4a1750040d105800700142c807000f030700040131008210300f507845080c2040c0688030958030301c43c024980340038001c0c2c9010342e074002c454a166107490b05810314085481c0100680460800c401119034100a00c018100540c5401e91001983d8840300901501211400300041030f40a0324200000d80e41000e51140c000d80103002e4544440a01004503071005400c58008542c903283e060110b8607100c240d60a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 257444100 1250 257442850 257442853
    0x4030e181005130603020f1306030c0312081803070303050c1c06050901083f030f0907060906050a0503060a030b101d0112020f0a090204060201091403030c1c060503 72
    0x4014010010380700d4041a51401e0380c4500d10700328490070040803101c0e60300019501c211012413170310280c600140300c44040c1d2402d10011410340d5072640c641c1c010980d981c100b2035180d4104001d003500580d214001691194080c1c842c040010740c5d251101d81c60b841403110144c100750b11180080d00403130088044500d80042042c10036881d01800940034000d0131103010305449080f0356400095803403000030301100301008402c0038144c50302102c08111440035660604c445100311981e00401001d030300b100590b20590310b0480044a5140902040d0b003014441d800080038448602c50038032643d07610005480804684e41041d558a46640d400500c1e1456254001072284110008000203201c401d90355800700c40c0c82d110002d4038408180b050700e40040003400307101d18000109a90401500e007140e214500e03240d0107060268019201c8030004280e078015004600540e4441050b40100911100c00006c56212500698114103080c0c1010b8858400d00650750400d80d14400701e0300e04080d06520070700003440f0050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 257445350 1250 257444100 257444149
    0x20106080d0509040f020915030403110d0c0311120a051c11040e010b0922020909040302010e0c031605040e0f030426010c08010302061c0905030910020f030304030e 72
    0x31801000c03540f05420a5001e58140894420f898845000b030315010980207042c0540072500320001107072500700074020b508100d0403442104485200b400102000b80b07241e903400c038100c540f07800d000e40702192652034080c0d5a401038020020b0100c0b00010750718001f41514203207540e013183c10200b19003d8062075604c1c0105251025486490802c0c1000b00100d03444071160882d0781ea43d48114061501030764aa01d90007003191056000808982d1300c09040100c2000d0005082603801c0b00800d60780c10084030110f015079900c04100a00d00f00c10024010126001c0740208050914007008030f52968591040c507020f80c1c0ca41240071300a035802d00400f451460036030101c0b92101d42c1c80c0c062414022509001c81c50144641143c084164410302400300942d0a035264142e1691860b801c0c08015030006455204003014502c00005040250080102c0c0302c2c0141c00558641c84040304106103000001c1280f415540800c08051148401209582e80a905400c0c404020343c03400b408030f0f500d040303180b1040d4905030040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 257446600 1250 257445350 257445373
    0x60a0e0112110901060203191b0c03152c030f0703020c0109050406051e0a05121023040f030203191d0a1d150405040503071b030b010308070302010608 66
    0x40c1100d40c6140030b4408010314400c04020300048220030f004a90041c3c2013040408202c40210140b60608103491602d0100010114003410812018880c1112280d018520800a0061100b20b10030300d0280e000c0100000714060002e104801d207035200050f9440401034120444072428802e8984440c4000020399070b4515030b00d002529000038410701804200d032084c02060720f0038035208240540d2000741008081b88504032811005501c0c0301003556001ca09a040400d49840c0e05045072543d401840c000e0040d40700d0320504038103884006808400380c60490342201c2d07010030072111070358015804c081480c10001c0242130403400c51203001d03644401c00c05284a0704890303580c4005440024100100e5441408090108001007102c3c2d0307114080f07014441d10340c411000901c160440d40c00816040000c0709a4054001050aa400c2168292030640020818800b444030340003000700340d41c260000c821000380c21a621164403000c1030102800011020482c442010b0017503221802505e060ba0031030740703200d000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 257447850 1250 257446600 257446619
    0x41110080103050f060c0406082e0e1b070308040f0c030b0601121a01120e10021317031206030f011416030b0306011a0712051e0909070503060a0e01 65
    0x1c2c4011603007449041841d4000620100e0300501404034440341d285003604d03040d0100d034030040241401e0000b2007400c00d9543c0400d01541e403840c410185102c0910300351325011000d840e03414014441d010102c450300c40c400c66040e0140403180d9260781420200b02507151070410030032079a4200001468001500c0c404000e00916014603440340100343d80780c000c00003401481509603022105c500780d01e022031007806841c56010324407520512405110000d4480c142d00f020340d00d84294603503544995580014050324042445041c1c1c0b000d06800d50b244010480200f4290707641e880b40c3c0000900c800d2062000c2409507130280011000d03162140700030b000350141007a40c20720f40316041c1c8103002c00f1034058291044031806402020034254004015003031030380ca0b00c048840140855503032240341032810840980061021407000001c02255544c0c82c0e11040c001c0c050084a20f40e4122100340c455081c030650402e5035410210f0b07944180c00b0710b4802c1e03c030b803507050100d0b14880d100d8004001c0d041d0550004500c0028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 257449100 1250 257447850 257447867
    0x71403120703020702090406381009080607080a0603051b090a141906030b070c0c0e01050d11130c050d0b0a0303020703060c02100204080a0204050f0717041110 70
    0x2000100c035140c4501009600328858120300035080801d610004001c500c860303000a030003540540f82d01c0401015401c0044070100c0120100e400c9512190382d0540504018400702000181404c10768545410002540c0e0745040c014084000c0000d1180001da6075003980d00301e80003d40d0301c5411581d1010012440355200600c11200714080c440a00000f2000c1905000d03905461a4a00d0070304440d840d100e114100382d41711941c09092080e110340e40003000502c0700c1c64140c890b1000e641c41e140444c40e5450201c03030800040d84005500004400103014a980303e400b40d017400c50b03200d0a01c001c0c074199003002c610b07040344203095110641d1415207695441a0081d000302492030b4288020495084010100003c2c6103042c00050b00580c0000000e000168150744145607082160044070410002c401c2c3c00b40590340280c002c3c0d002504988000c03030031400c00d40034003900603800c60500300c0b01d840c14200042810078042c40c0329000c250320b200818240720384d00250000c500c03406070008102c0042480701406c041c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 257450350 1250 257449100 257449117
    0x80f090301140c04050126040f11100e100e030d051e030108070b0315040516020d0206010506030a090f05010f0b131802040207051e0d0f03050c0703080c071403 70
    0x1400d160064012000880c0c040d403207201c60852030f9041606110044583d050b4203c0c5600d90747c0106e1449400c42c500407404a0300c12885403120340b06501c440e260042c01084a204014080c80b016440903040581180e01c00780101400d842004c00905505070803640080043c81c03054150140501c06070025500400912540146410303000b036503d4103c01c2d501d85407000744500c8620350031082003400303c1942c030750007542c010b01d0940c40c40314240349650000382118001d80b0703011108243c0003900b1110b03907014002c040d0358003214000390101e036242030007050881c07000030309850310503684404240411682d041c10940180d0000004c0200c8401104094018540d02c8030f0309106405502d2900d0303102d58a40036805000d0b00c8103900f50f084020913030030f0102a420800040381c990141c681003107183c40095030124004000540142040c0030010005003004241c5403441d02094103290030420481404c00c11070340c1341c0341d1500d000d81c030075500d104515205001e2050014151108202d080510490000181041c0d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 257451600 1250 257450350 257450353
    0x90503090411091c080702040b130c02060105040c080405060c031f090605030f0613020108060a0b18040b03160b1b06091b0d0b0f0603030408031308070b040e0103080a0309080f0903 79
    0x81035404e8405402800040d4001c0100c0001c021200c01801d140e0041c070306d620806030070605200040c4a552042c2c99482400100603800900104194503240c0203c81c4958401d0600c00941e0415449123500d80400074001803100d50000302044011004203010800480005110000607450300500c0024210038890113203e0722400e8600100c01d0300204010b4012490f465002e03000c41d0752075006480b01000140b8950b4015410140000d0f29510300c8000c221007503d01c8050070000c0c05941c00c02048a94074a60280a40d0003128140b40e043c00e191003c0040e1141030001580710703240c8686200030f01c10300e20310100c145d014540c20700c00c2c81c2c1000503940300c41100c05107507400000b07130301c0d4144580e511207144090021194100401c00d000045401c07142c0101001d015245069180c002c070525690290582d01140c100b80c030b508001d070200902c040000f4013040c14036a454107142c80c03d5085d86100600019144000c000b03091801c85002c0d40c081c3c000c203075100c0e030001d17194022400c1d41d0f8070340d810109046009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 257452850 1250 257451600 257451619
    0x9081b0a050c01020312071209060e0303040201180f030b041b0303020307140105071d0d2f030a1109070320040608130201050415020c0d080a2c0409050309041109 71
    0x2d580007005840160251a8000195030b442e804219040c02015807411541d555070b54098020482c035028040020442000440d600e044c1480010038640300d41140446000c819201030018015560048085030b030480f4851f425600c590a01c0c0c41a151019407014132004c07603200000130142c002c00500207681c0159210300d0510a1514090300781e80048272100c0000d50340e403000c0034140c104410b01c14440c04000d000d0b0042c0300d115540350750030f540100003000100071000034035409112417080c1305115800d0a038040c0c840c0401c03681d0303a905048540102c0358814100d201c002140c0502c203500110340740307440d00305082e41c0600c2d02090b5071050703200d8011040094005030000b0710514401910b0300c03143da41030b074683d8505444c00300700700809103c508078a4118011102082c03160303505c118401144174003850a090355030a5128000c0d1403110f0301a0500a9203101c00d64000c42201041d10400c02c01900383c4020030054103a15002e8114480c1003603407a8032902e043c0c1c1d0600d5045455018201070b032425201100b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 257454100 1250 257452850 257452873
    0xf1809070509010c080a050c0d030204080f0102040503070501080615030a020a0e10121505191e0e19060503010903020a030306060e090c0a180b03040303180b060409081b0a05 76
    0x40c2880303048030050105039070160000000e9000d90090140071b1480c42c00e00d0800705500032150812442202d4040002d40200f002d200e00142440b60040d0000100000c610302403811001c01d848250303503c941418030802100007070310703034480c0780b003078000980b82c0261585d807441c041200364000d4104c1104600012881c640820290030311080c80b140300c4e42c2545032084540d40c45284036000c1c0901040f0101c3c1541d00035800030b0b15446e0751410540038160101103600c034500b881c0d486079003111180000f044403110301e0000c01c4083e845501d4039400520301c2c50a040c0134518404048058001680b109805600c6c1210308414940d003c41d2000c41e0501c240e40501000d41d54000844400000d440380d250f21981400c0400c0008980900806142199040401d203112080841e03500011107076201c0b0b620100000f003080100760b0b062192484025068004903440e440d55107905c2940c41d0000c00c090b003d141d0f5000220f05004019080c1c410035554131800d500c01d0990028074545840d1402c0781120b00d44200414100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 257455350 1250 257454100 257454107
    0x2019230607030806120c0406030803010503011a0a0303030218060a1215181a030601170c0607080403020105071104060f0303021209010e01230f0315010e060f07080f180907 75
    0xe0440d0b4160765441c0c000d4440700e0410541017003a03c0400c440b403280c441041c81984603405103900840c01000a151698544402e150039200e41c1101c6d0120a410340141c050f40d030b0350b88111501036903014900140c54040380456140c8c0c0c1c0054502095101101141d07101c40507900c890751410602c9800d90501240ea0525031543c28950180146c00304c40710007110030b8881ca15a03900000340f04000d01440580706c814100070a0a002080c0c0048030032565104600b105160100250210380300140c502e1498800f454031190840c0c0110b000003810800e0020345001800004040e00d52811801402002282c0e0340b10316104407003800c3d1000320094060318030024001454201900c400d0300301a11805140300b030340c0d0011200d8100f6101589020b500302000c040d20a402c503030241c900240e102402603600d08200c2e940c01940c11000d1382090401440b8040d141076034507900c0c16543c00d0b268941401d91160824074052890740500e00d4444c84006c0d020545102c0344050407440030050b40c0c2030340c41c50195100c2c5142203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 257456600 1250 257455350 257455357
    0x30c0c03050a030f090204060b0a0908060f01061409090c090a0b070b01090506062b1103090d110307050f01150501110a1e1208150d20192306 62
    0x30340421810301c280c59060380a600010f5406501900c0003030340c0c00155000030110342c00c1d90003455241c00013042008000d46c2020110002d400e00500400c114a0012071071108200140510b00400400d00701c03c2407015402c2040d1814020010a0140c1c10b10302a92003614a402144484d44502c24054000402d4910f12040303883da5900244420300d56030800c0c070a240982001b418868100c3d0041058186c101c80400111190054a00c0c1204036041c00c500028103655200c1aa510001420418032000d140c0000301050924010b08019000040c52464181540035520024000f40900c52401c8460007040d13002c0c5079403040c0724a2864507151501e0045602c0c8080f00c5a10785030303030f0007643c1c0c640c003160001c141c1600054500000000fa40d51686d510400c005a41e02240d0200d095001442880007514042243c906410348a590046003c0e40340c165109100d0785600210304442215581c0301d07103607000849a50501c180c103030700406503505d2181e02c440c880d210018003102091031001e1101c2c940407048 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 257457850 1250 257456600 257456603
    0x6040b120a0b072a080a020a050a0f02031006060813020f1201140903070f0305090427150507120915050709080106060f1e110f030d051602060f070504030501050109020703030c0c 78
    0x1d921104c141d965403603160360f00400d49242540b1544869030000b407020070005580501c00e03125608412030707510505140202c0c1c07105488001c3c1c28041c044c00160380c019001030b4411406803c0c0340d0300d0304081c000b14155031321206413583c0011807610301520181c41500074104403041c04440c0b2009581d1f0f042d0150300e074050b510006104980308140a00802d2044010744032000d0000c10006900d01032107280101105100d40c1e00f09500e00013130320203003480690754101c803034840f0b5171070180b003503141420000b4001d00c0052407a074031a580e207c02182c24010200758078520810041c00400c064102503801410041c040d04c00c1d10005c1d0700b0500c0105506100e00c260070703034403283c42c0c03200000350700100c2004c8444040a160380081050a10600180c1741042000002801d988006103980e90400442c00d000c2e40d10051420700d2100a48480c42603083d400101e0aa002029514030350040e01c0d1b40d4000c698520691740080c040b5801d00001254080c400e0780148170143c0701380c4080240c21210700090b0ba076002040e10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 257459100 1250 257457850 257457917
    0x3060f1207060e090631060e040f020f0906010801171e061b070209010b0307030b0406030b01180204140f18091b1e120709150501032306040b120a0b07 66
    0x281b01100350750900c0e181c0142a2076440200350b06413914070070701c04034408031000d490300b00e86250a2010b6041c84100c4884242c021f5885250901d84080080c000f414103104401c2d035650a84041104880c0031300c005000c0030315a00b46504981c03105c04003150f0b141e1055400f40c1034603225007401a81c050041040b50304903036010b081441e50380c0c42d1854801c1640c100030b010406050b22000f03042055500c07881404050341c40385e104155103505090035291016403031514007003020b204000500c11150310b44d844c02c900c0c20b821294401d041c0000000b007502d02d0400d142082c0c540e55080306024502801281000c0481900d96a41c14400c1c200000c101029420400c1210f0380002541d901d074880c00d01e0002c01040c02084030856091079610304640044030a0f105000040d1410300341c06100720f40e49070242407003084000401d00841c0c0204014080c07103002c0030303164510482c0e48219168003910341d80d03500400d0702c1c64541a01d490302001e04025448910854050000950310903944507034884540070401c19180401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 257460350 1250 257459100 257459149
    0x140f030a0c0f0606080f0109030909022b0b060d023a110f0a0801081011040b0304030905060f0d050609130f02032e1107030503060f1207060e0906 64
    0x403601e00e01c40242c6201503603040d03100e00c0c000c141010100028600d4103601400000c444c1182e0500070610b0b6100e402445401c0c0c0100152040c0d40c080781002ca4503421903141203a940111210080e005169a0850541020b070110301c41c551030055a01070400d01c2040300007508d115100c1d0103241c9451000c0031440d1540b0750782585d540a00c00071075118a45d0709240240c05480c1c00c141d00e071640080d070070a203007980000320b0080c01407010500a12001401048540051245080c030b41d00c548401d0060340a1416401000310006c2c0c145440b0380100f06c01030070042d020341c2d41c074000045040c003940d110100d030401c840d06000c00700c1c4090920300c140398402c4913403868450015100e42c0da01d0310410f0000034242d0b8140b0070220703080c81c8410315031040704004004808da19114080382c1c0103a400d50303490302c80f0040c680340288800030120390440c081343c0d031040303040703c80c8103815440600280342074008648000d0700b4812580301046d2550403c908401c1c2000480b5420a1950703400104280707640da00d4a102030040d03044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 257461600 1250 257460350 257460353
    0xf050607350c0c0a08190305130b040603090506150306130809060408010c08070804110108040614011523040905061309030810060e210705040504140f030a0c 69
    0x79100740c10031a90181e10350040180d02034204600d82091580c0000c0d90006145074103e46400355512000f0610344001d030980b41c00000f01d0720a41414503d02406201000403907080d03610b10303005020041d14541e240a81c8031a1201c000400511185601710307030910409000c2400340c0340109880b06c120030010014906607949881007006040015822107100c40244a1050103a890310301510103800706100026000300c0c980c0c801004180b028128509200082092201140c1e0b0104000c0c1246401e0030301c6103068607240780c0f0000034500305504e6048410140c0000c5000e081800f0707003422a0140e42c0e2445c4000d0603000ca00d44030040c9444080e811580d04110030096130352587c20141c1e020a0040801000e8a85c00030080251001150100d0010b00580c04103c488520105800082d00c80e40c9003a03049190200c01240c0c05424556002400d180962001c581d022002c02410001c2d10380031b00103000d2421315240490115424590031002405451080c0360522000001d0b07072465102d5566a5400a003207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 257462850 1250 257461600 257461643
    0x30e0703021309020604090c0201110708120c090909010c030e0c030a20030f0601060810050f0d0204060906080c13020309191b030308060306060a051815090c040f050607 74
    0x100c40c0c40b510300340c46100d0b18001da45d80c10040c200030180c4038408200491031070002070031154060007a400d900020b21549011900d00420344a16030b40e14407251400e919111903081050242146d81d550000024041104c1040103400002041000d51070600040300c00c520b1325900c2d0700d071001c0100e03016444100c0711004525043c11894420590810700110600164082410080031100604290340100b004000e2980c1c0300038040c1c1d01a54084c102540d071814035002480081c1c045104034420030844072650103641c3c076540400003d2811800420515a440c9160f90711085034900243c442d422003943c0e44080e8281d0f0088a101c0e045040160000da00c600c0903030460050f110a081c0d82c281620341403072085801c40c04141014500030784420103545800020941f40c070b940100f2650190424100c01c00080d12002e00c403408402080c0040035280e5038180303180c1c540781c02c003161050b8814100414820000301d00e2004000b42d80707103280080510394440040c05524854501d00602407145030881d40c81e00b0704c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 257464100 1250 257462850 257462869
    0xe0907020312180307030f1202030402180a0e16050a091517030c0304181503020609040b040b040c08010602060903030c0315040e0109061a0906031b0111030d1b030e070302 75
    0x200a01540d80d480320303c4034180b4642100200300d001c10981d1a00741d40098010407409141024844194038500d001e502080d928075020424030b141000c8800800d070340030080d40012205500c1c2d042181e000701caa03442454000369280c41a00c1c0030320300c042000704402c401c6000e95054069070303401985150340342142d1101d0303030100566008030900050201d484220024001000107004a40301c0700201c0a00055560132100e00300702c10003194500c00700c10801601c594081c1c0d00b820300300322000603070080e403040454090000060801d80c014580119450031640114555043e43d40907030855140c3d548071246503680b0310040d01c0c10f8404c1d402c1840082c001e4080c080d1111a14600034201169840ea000036581c20b4030350200302228026213410140f5040d6a894440040080d01100d00c10010300b880d20101307807101c00d9030702a8003800d0300c10140c5458507405a09406214151841120313900c4403020f049000502c1200142840080c0780c661544c2214031a004d0a0035510120015005291969081041640 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 257465350 1250 257464100 257464111
    0x11030405061515040603020909010605070312020a12050f070f0207140f060c03030f0a0b04061a07020414010905091011031f0506181309030c081c09050a02010e0907020312 75
    0x80100240b03080f60409800508014412030710050f8950b1902c1e802c008458505820a4042040034080100840ea003c055600c10110302030b80140e84801089048428107034400910a08031304020521414800c141040d0307106003010398038040e5211500c0c108980f10500c40c41000c0d85541d00000181e0a460304008100c3c0803035009090515100d0041c1685040d03400c111103c10000d1104810082e400c074880c003a45400f0001168104010f90900c0c05414100c1145e820461003011f020840c07104544655114004901c4088424609580e481a44a02514084504650f00c2c010903113642d0801400380502c030482070044a810f4190b56070905110710400442420401c400e250700300014980d2110001080e1130208098051020700402050000c000824896194207500d840484e8001c0780c0e0110b61014240d40c024002039861008031134444071744011040d42e114080ca0500f2110400c4000155498028402e0b2607128015000ca01000204c2004550010250304100007881111003000940c6901a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 257466600 1250 257465350 257465359
    0x6030105130c170f0612010c050d0e07090207151b0507020d03090e07020304061106091f1b1115010608070e0409050d210c020d050c0a02040906060504110304050615 72
    0x3806810340c0c401650041c4c034001510040301013800080c0c1040c10300314041c421100028061486450b0b4010a00c0c40b507140048a01aa552584128401c0a01c40400208a000c2c001e40d103d50450824a440d02d140c1078018240d070b4a0070407030100200042105030b00e403091586641c0e00340003007a0240651311140d130400b102000740350000491865920340280e030058105d94000e684850400501924641c4d140e14a640c450344030404100e1003202c0040e5a403461441c01c0d026040c020001442e4401414044158980210f0100ca2907403a5030b40c08070483c0344501c01c00307003240e2402442c070741c1030389100c803086c00359100003502031001a0200340590352961040c2ca010f000016004100d071203103801c16104002c014001b842c1942c0c500301000e102c00280a08100d003020400125040a101956030706d03004400c0400d002001c03540b10210719050000c0c5d0203040c0c015106024152552070181c0003010280500d40c40742d4581080843c8090f2140b05603445154414000d1800d40c85a01c0c98292301c004500015600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 257467850 1250 257466600 257466617
    0x1006020a0b041112030c010f09020306011a0403060203071809140708060307030c0308070b06031b10270905101404050603070302130902010e220c02010e070314060606030105130c 78
    0x40382c0f134600a440c5003a000740041c40c0c6404000720742c1400e449502c40c0d1101c00c0c5052400000242c3d40c01b00c3c9060440e1264a01003401140700412100103000d664005800f813403010041100b0640c000341c4c060304004d401148002c18036115540c2400700e4001c04e440512884109001450990280715501e40110004084950301c13645c80c2d0716040a40c0d5240c00444140802046080030030180295407074103e0780840c058000403000141e481540f40600c01200c0c03256411002c1c0c0b085540c000c06c7c00415516001510b032841d1580400c042e40c0c0310290b442188000da01d08000280304072300a003081825100c1c150700400c01d00d0117031402c00010340f4019010340d616000340c000000041c4d484a209000c0038a02c0c040108001c480b0f40005042110f40400c45070060384495402c1c01c1065031700d00002d25010081d51b002900c008403030b400720300506e02059001407510840c1c0d0040305006003c68864800b0714032008662895031607209011550100b841056040b2207412010888126650401c2c030880c81a85403841c40c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 257469100 1250 257467850 257467883
    0x150c160804050a080309041506120f060e01080a02011202040f260d11060609070516060608120c0601380d0609020a1725020f0607171006020a0b04 64
    0x90100850340700134190303800050078200b1030900340a003180b1407801e40c91240740c0c0c1c0e10b4048058000030b030342c849006825580b141c0200c00448554411006400c000c005040b1940c4c440c6829540c64481c4001a40072541aa490784400e6681d8001c640030f4414401e081032110b031500843c02c0800792a80c5410b1812790400100000201d420072405000c110305694282890300032140d5182041c1029240900942c001001c03c07081c1500a8111746030192202c426144c50005400e024004002d25000740150303009203448826400c00311405008010709000580d480790340c6c2d450002d050341d0320484030602001c102c0400c2180380e000803405152800601141146041d9480c4011030450703000307030007040d0041d601048110115034800003003200e49141021107031107418010400b4140f103c2c441c0c00401d2030850070300c0700c2d00114030a0040401c041100400c460440c10a280003405500d42c544418101020100c0015104800e41d0310080c2141c1d40d40e000f8010841d960344a00400c208020700a51b0300480240840c103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 257470350 1250 257469100 257469109
    0x921061d1e0f060c0a090f050108070e06070c1710090c09020a35010605130512010608100603020306060d0c06030203060607050f010b0406050a181a030d0305010305150c16080405 78
    0x604c9844aa1003039035441d0403000d0054084600350b004591441c44139501400240d8000b91896080519810036086a00b61803000906030b1240440080c0f100704101000030f2541c0e5210301300001c07003038808162824145202080e0044a43c03412001e8900c0841c0f40701000740d11015802004881050f140090380f080e00e084407080b01c0460034040c008519500034004800003000c40c0d545000d03003040c0c981185450f02564000f61280e03aa4011148504154600d1286500c402d611441c010702059068030000d03050722220400802c1d5502c41a4007e00031308001404a1620307141825820b644181c1000c125420050118000d400c010b000c4c40d0030440401402003c244200180c1c621241e00300008141e200e2030100f40020740301564001400b80b5076140e0280302c8075280e42070500341020000790000b50340d00300b80f04104400380c401ba10300303405000d86002c04030300300d83c0750300241d060701d004100300da2200c05000040f910030f034030461300d0b11a184018424064006580d42c1c000000b03038001d81d80741c0e061544910014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 257471600 1250 257470350 257470363
    0x30c0d0f0b0c1201170c040c0306150806040c14030c0a2003070c0b041d09070302060304050714010e0906010e0f090703060821030609070921061d1e0f 66
    0x7031800840200b25500f00e4860284024098145840f000700c04e0700d2031164a580e240d215005a6201b00d44070064510750714030a6012900a04c2041102c0c080901500000343c060304050360f410b4052424040003900340c0c0e00031040080c43c3d00e2040d0f05d0f140380d07030f90780071020b01300c2d4224a0b129010800e100741c06007061402010110552444880610741e251214607100045400581c88200d00c9502488100140102e4405105c8001561008041c06548400d160f5040100507000250721400c0030080c8014044001502025110120015030010000d000191519075402c050990301c9a2018002203241d44291243c440b494000741807034811450180025011550450b00303003000a6a0704d1040294002c00c10484081044000d00c0c803050940c0d05414240900c401400240180c0554000c18525449426088010020070b1300100348509021920806000d14080c15280e4908044c5402c1400324412401084502e511000b02001d40b121000381140c2c8081d6400207103a800307490405e0307483d0300b41171062 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 257472850 1250 257471600 257471611
    0x180106090507030b010201060f05150c0715080a11160f0b0408090109050a05030d08100312030606080a1b031a040203101e15030207210305061509030c0d0f0b 69
    0x2007924030340107100408449a4030100c50442e81420804c0001200044031542a10b0044d2110961b00c0111404441e02e4481e50421004600c2010b40014141804019526020540356162000c0703440b105c4000d801d4600c0c4e0440d107010b40c402000b05281107903032603840140b00d500c200608103400195455480c808c5800300c03400e070340d114400201d000b10f03980e2185410003d440c0454100ea0198144804265650f200c4403c18041c4000c0c440490380c0e001c0414090401907612803200d03105050356200040c048c1446100382c50104107100003060030b074212130140354a400340203514440c00e110148002c50140010441094613040340f885045120344031800110310a41590800f80451442c180010007241040003203601c41808003078050005484020b42c4410301c4040e85409620b81c011070400310036003d011011302604030b0083c4c00101c21540c141c0c110a2040e0740840781448030a100b5000c1140602c81c00140c039500d604400c400440a01c1c16120400c0c040f0f000300030000e21203006a844020361030040d01c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 257474100 1250 257472850 257472869
    0x170f0123151c03170c0403150b0102071203030204080727050406060b0d0e07080a0c0311010509180604051810110903030403080c0d0f090311011101061503061208070b180106 76
    0x34080e07031360740e80c1d1441c041d0801174581c0760500c0d041c03a5880d02c00f0f00850b061130100c01c5a031220342d0380b10030340c1c404c100480c0036114040c07807000744050b1480c01600030352140c85158081e025595000074440c005020010502294221403242c68542c8041c002c001d050041044940565540300811001444000382c85022040113001a910030070352480d40c98841c0030340c42040e1540c0940365040008200085020849501600381a030130352980005070707441e020328004240c004203140c03000050000c170315030401d004090903501000181c680413042c600011450081c1c2209038840b030501841010305074800000014860582420007585e00006420b607405684281c84c2e044001c01c410302d420b08244414451003034581012401c00310404400341c100c2550f4400600090007408880003164000d0840111004115008101c00c5848080300841070b0804091a0006454200d011804c14509100c1603502508890030380d04000c903540e128001030030020b00500e591a18030040c1c100c04842401800c024044401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 257475350 1250 257474100 257474117
    0x12020a02010b0102071e180b04090807021002060907150c020a09050615120c0c0307020409050f150405060a020306060403050633010c030e0a170f0123151c03 69
    0x600084c0b40c1707007182e0050700f00c6500880d114a0001c1940079a10100c1e00091290489914000b0050004181c6507991719001400c0c211082e04010f4644000d041982c82206e1840b07401c140030400320f035036080440b140441d90380540402d100140c410140c1300e106803114540740a00504982c08654448001d0384a2840c5076101c60074083c0c24503251010540781c040c807609140c204185076040010071000038041c0c507941180007609a0ba009404e0080307496103038000d08203100e1400c441c940290358a041d001621160302540b1004e407568125002d0040c01250040c00501d05600c41001083c000e40c03001d84803aa204104010000c001401400543d1050110107250703150081001a00e11000180c169050048000011030562582c0c12040d200502c5405103000200441c070840403071903417103091700030403010240422280c50401000908800c0228414000e0140e0507408034801000a100c1822080d03401588002602c0d495070224507003840b01004040b100d03002c2a0500d100030071120708030160001142e40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 257476600 1250 257475350 257475371
    0x5030621010212061c030c2306060312070503071e0227060402091021090503070615030b040b0901060f080c030d0801050d061802220c09030308040303050712020a0201 73
    0x510105600c010b050b1000300d41c401484945032070012107032a00405121840354000144155034600010541d08e07845050558044107030b1880da2303400c04880282c032a104048803902e0f90510b000a8070b96442c0c1c010003c0d414401d095880c0101e40007010200c0268942420404025942d42c3c0c2400041c0c141099400c007580ca0311403080d404461006003900d01881c010172800040361a20074401c0175055651816a50681c80400f0740d40d0a18616440c54106900342460041030000c0400140082481980100410b40303801034907080704003080c40080d10300b46140c00000c01017052951703d540e1000b0070388000603415841380c4490b0030b83d0302c0720b800004180c1e00481c82c400c00d0341001c00140c4503500407824610410740c50b000000700710820407071004040b640c40344144107030810701101d95074885a004141c28008c802c040e02503c450010442600d10441c01e08422603c2d4602032190315044c1c035010b541d085150354540e102500034001c0604140200b118400461010400b2440030700903a1070f0a0f800440c2403c000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 257477850 1250 257476600 257476627
    0x10b060f0310060c020924030d0509180c0a200709062916050c0d060510091503030503061305010303112104090c02070b0412060606020f0607050306210102 68
    0x360416018400c50070704140140e606d4040840c0e001c6031a0724007201004031858400200e0034810610390301440368503014244140c11101401d0758207000d50f9820540b00016041c031488003000d0310030390301c408420091104014031413800701c1482030321022007915001580e204203203464403540c001030031150354082c02d1120110303004004050b2440080c00500154900c0702a400600c65103510b41c00640c1d481000d20101b00041c4124480ca400040c802c01c1c00d40000e041c54030140000b140c101000d01105000420402041e106698034210049150480d050940d0f4098419500103881690700000340000103503c1c008902600c1e01170340c03084e51407203440e440c90754029140070003802d40202500b4884050b0580241c46109440845820f00c1c8081040350710858203900b0030700b880c0c01c62101484006004240700019401560403188108000c020f86035541e01c049840c0c00b4020800007103a00208041104540308601030340c0c10a10081421000c1c460849503990f100304246400c10469401041406200d105d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 257479100 1250 257477850 257477881
    0x191e02010c1502070b130201171003050105040b0912071718041d12040e04080d090b070507050c0f061c110a0e1003060302131e05040f1101020706050702040e010b060f03 74
    0x101c6c480d42c4030300b205040e0700103040d18101c070030041010028003000610702000307111428001c0d41c110008100b241828202070302840c00850b480e040300e102d14243c000901c3c010900315544540c010081c0b42e208028480210301680c810068480d6580d044141c1400f80e95407403107604c013150129040424044006400c5c0743c14070111000c20106200c0920003013242e00703000300c802070f8803a0380041010341e1107a008141c20018050f08030007402205625080280c0150014018804140a00111a401c0301441c080148501d11080c500d500a0300c02c0c040c8810301454600c2201950000000c0031400c845c0040d094030483d08840c4002000420303180442403075051440315804051524a07090048508640200e040070801c50b8240100c0c941e1940000c1e1041340c420303000d8054040b50304080c449420241003140c0c0c8005844801d507082440328107250115800080d0000c1201c07030303944403681403000503000c00000346030100d48a941c070b5490350304a110a9070303084020595000e185120a40341d04200c0640100b401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 257480350 1250 257479100 257479111
    0x60f070314030108100f020706051f05030303070e130b03010c0507020103180308220c060f030f05090c010e0613171e0303041514040b09191e02010c1502070b 69
    0x1d00c10001441005808100c000380068040c0021807170518281000700281b04044000d04194a44400d01803600030026099440400c03603c140803c00d521242010340b83d21040e44d035031000c20f041008003000307070a107a00c6822113462001e00000c0c0ca6910400441d094504d440344a80015000007502811503815218450382062000d40300c40e0041030030307038000d0840305000d0302105901c801810014800f01089000d80c415a9022101c01c20300da42c0c9203009408039030240384840c0401e05180301f1f1a06400d9034429644100c0b0010020b01c61a04007100560350321200c5142c1a4200b2404c00840c00d1540036070b084c0800414009001a0800d60300c00c0b005c609050301e4894004000b1092640c03051031140000503603400c00d8001d01000c902c184020001c100030b00c0e60b046040818903080082000b84840c1d14a1280b00b05844402d0311102c100c6600c10385ca1900305103900134030380031882c15640030b18030350590401d02c030900c1810724103410311054803070420001441050408540c2c00160b49401c0059140c0725a400c407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 257481600 1250 257480350 257480387
    0x80406110a0215090d060606050a031404050c01140409020c06090106171203060d02030f0c030f010c02060a051f080703030210091a070e130f0c090b0f0a0509060f0703 73
    0xa00c038980c0064060f0070310341c08081d80300d02c2c0803441c03103440ea40303031034154001e268030407020089603540b503501a000d40c00158a40c00031919020740c83c0400038040300c680d0b1195521401402c2d94428010040d9041d00d0601c400c00e02e840070a100100b09007060f44003c04005502d000100441c1c9070035070390745003514140c3d0080142044500d40d10300e019940000c0007091508426103150300d80d07039640c001c241a05400040a541882261610001c1e0400032440f03440187c4c080e000d4034009030140140d2402d13940300c1d81141005a21a20008550702075a03400142c02481540c0100c40d41d2220060014420006800841094115480c200109501040f15241d207007812007007808003030003988840c071840b070000d4400145c070024140020885442440c4446070058001c0122050003441141171000f4007520a200303010f20310b806410180da6000e016038104440c610004c0900c0d0640d00e04070300a480c0c00940e4088288001417194004583c0d9001c090b10103507a4102409072601001d0078014004c40c0c00410381c8051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 257482850 1250 257481600 257481613
    0x10f1e0903111002061909021c0c0b0a0c02210609030406090602060f061311160209011d06060a14030c03190c12020f0405121c080f0a0e0f0a08040611 66
    0xc0782d40105e14140c0c44403086000b42c0089421000341406400d6072440251b04c4458120342d081c00a80d010500f14456014104149a540d11500b10168504c41d14001c1808034044c80c00d540018540010321101c8040c01108035400d000040010500d85403060314152042c0d040420180b019652004e0210010200c42c40103003603030700709070180c4101581d0140c9050700904103000030003c0f01c400f40c0c004190030b9002c031141580d130b20b144500714240800c5001013240303d08500c0000040ea8000b0306141c040030f005100032607003a51034107020044190700c001d0000c03080c01103441c007015160503894003640c07017088016092030313492402c1680401c19401004020324050320306408644087d81c001401603081081001c01640c130011103400341042e000710380c031070b9500c00100d090b070086030580403030705001d1900094900390301c02c040b1100a03a144001100c07511035000c88140010000b01c50b0780c010603041a2442c064480d403100d0071000718181204141d080d105841c0000e800c20119038009800c0790a1450324016080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 257484100 1250 257482850 257482879
    0x19050a08090105100501121d060604060501050405030c06220b030402040f0912080703020f19020c1c1e0b04060b031207030c0b0603030415080103150605030a02010f1e090311 76
    0x43c1c4103050045c0c0c1c1c1008003005088040c90160b601caa80303920b030848038118010b01c84c03580321951400104c03090307405039080c078000150719401042507800f960b45c01009007943d000c1880503c01c3c6500804580b44c038040c65185441681c1150614110203004032444440d0ba8ac58180180803e071805c0500e103400c16440c140300c102c0440d03a403044210310000c070b900d40903000351282c08044001c0e0044004100252000080d2403403c0403204008001781c0c92903800343d1b02c1e41c80945003000038051001402e40d461141d18042000000c80310382c0d0421800d0141d0790b0400c2440c00686802e072200004480440c0c480f5520150070140d45010010500301000b051100780c40d1071000c2e0340043c007550288500410580000300820860b56041c400e0740c011b040a9880c1040845503080010100d20081c070054491465840c401c500c00b20b0341c0e00401095400140040003800b8040d40116213108241c01c2450030440848101181c1100340d0a1000b0044003555031006000e00314180014111a0b24800d2403040250006400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 257485350 1250 257484100 257484121
    0x9041104050d0f02041d03091f050f0d060e0a050f24041512210311040b030402190801020c4b0a060e06070c11040b040219050a08090105 60
    0x2a190f40410083c5104400d0720120f405080180c03070014500c07220944071001ca040010142c61808011a090100c89214841120b695200d00b50050f0004a04004642e1410003240040443c0000780d000010619070f1b801800c0708540c001c3d2003a24495850300705106420784880503180d0440500e2201d00e20500251441c1c102030500b005c1014000c81e01c074900b045600501f40c40c81c1008100c100c84100304454540b40801c8031001001909051174088609000103601c24410300348001542851300e03190900345140f185a580000308101d0344003c40128520034800c1181c20103004024500001d070702c40c40c44000160901c1da11709040d46d92400b641103034041501003600c91108400d0794910321001a8a500018000c40240c0941d002e814450503490f00304014140d131000042060804c196003250301c448404490307802c0e04a0703000d00b402ca03406d629401e0b05d240c51b606c2403040c450700800c0103181c0380342c042c0740050300d410b00340019001c6100400c1307400700c2940014007941d004012100800c01c501c0d0451405 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 257486600 1250 257485350 257485369
    0xe0c06031b0c0a050a031d01050304030503090c040c030e0c0108040c0e0603070e090c04060b03100b090d02031f0c09030b0f04020d06050f0103031101090b0c030705070b07050904110405 81
    0x307400204403845010031010840758100086002d90343c4051042c00c00c107036107a0b01000100c0c0001ea151460320b40c040c2e0181c581c80b0b18000140d403240c0c40c540301d40d20222080d410207000108980588030301070900d966603200f2401c0c05560381d100814100308480300d4905005800144c24144415001003200086402d203541d0103403502560b14060684958012910f490340d03541000c00084880e00910040150008410a00070011030b02481041d4540482e00c40c00d0009a580c0700700c08981c10001c4c03200485007409404200d101802a4400004a4000a141c80803c4081d260541a0484402c03a20041c6000da8650612241016080185965128a07100100408400b5400002401b003011035a481c41c02800711a004101440b00c1e05210030100c150701800e203c03c40100d5403494501e0141c041c18002e800c601600059000880d5440c6082c6404580c8000c1c500e400b000802c1003200000780b074852100d40940401d5503420303200c1140d04188400c4500c4071001c000d040c6000d1100708815510240007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 257487850 1250 257486600 257486611
    0xf03011a04030503040e0603060601210c02120a080f0115020d03022101090b13180b06060f120109060506041401051b06010602010e0c0a0f1a040f060309060e0c0603 72
    0x150000410050044051402a608010f089000002d0006501c0c8280107496001d50b20483c155803445c0c83d600010b48094840c42c0050344102c003d4041c003a03c0780b4440d44810f008140b1801520500041001103500c654000302413440480d8444060240c80050717070340202e024003182450500c3c0512101e01c06075032031f401c1030224410550000381c2c880c0819001440c42810300390407480c5128558498100e000507010545603540900b00a2080308104a8240206010f0a1483c592041000e00d60348071440480e1005024507046130003000141c450340b210f04001c00304501c005500d01110b5040100351020354a803a8041d80c45020144401d01072950701d0010307298941c2c1d007420002d80d10030140d40b01d910180041c5000302114028507000140194040d00031503112080e0f4070507900900000d604115107030600b4054020680c02100e001c3c01454008440a00030700304008026040942ea401060305618468002d000065210340808003040b200303014090610003204098131a400c1d80002103052408010031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 257489100 1250 257487850 257487869
    0x1704020109150318030504080d0c02060d0e010207020d08040509160203030a0b01020f010e060709120b0112020d060218010807021b0402091504151106010e0103111c0c09050106050f0301 81
    0x1410b0602030090380484c1d00c111001c05000d0301110b10f824080d100342c0040c4030b04182d0780515480718904a2042c03005002c810350040c5068101002d10140303400425410540311707995982089071902582d00c10050840380d030301ca00050ba42c2c403401cac035090114100024101880459080110501d05500441a25840103840d50001500500c0c440101d14090861a074004079501e0a1070f0501f89a02c0441c60304d00c2600b09840c0c0020f00d07951034a032010203503007c40c1c0103800b414000005124107844549900c1e842400217204840307a4074941c507440100d81c0400a681c180e126248807010341942c2180f88150710114a0002e403070000c0025422220064001422512840e0b00040220032591950141006294002000c0340c40e55103581e64011310101d102250380205480b64000d01038000300244150698070344001c3c080351a4a195156440383c0d00d41d80314a0340c4040c07088400c0300070161181c0ca6040e104c5c00b130b101d5441d1403031501c0060000c07143c043c1c0041d403c04c0300070044000011141c10499044074045403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 257490350 1250 257489100 257489129
    0x1809011d0a08070c030b04060608060112030c0204020a200d080a0b090a09020604080f0105060f0d240204030623090606030a0f1407060203030a0e1501180b04020309030a1704020109 79
    0x43d0009140c4505e4000a200105010501c41803008a5002c8802e0305c1a91084800b60b0740c8642d0f0300152500f121000400160242401c100141840c0c0c000d0300000c2c00c60306006000460803800141c20440c400111040d6500c4080302c0903206500260223608460720002c100684601c1c840400d04040c00200780540c01c94607150f00700e04645a0b08129002032203417a00343c9003042e0881d0303e550f000c0c14082e80e107030780b08284050600025260440281c208030358407070044442d81c8040d8034a54403440441c5019610184d080c8000000318109008607805510f80462603c1c1d0400c0c0c62251980794180076256441c0c5600c11820080729440004103d0300007900006820b07018002c074601b00780c9450404400c21018050940000b482c160008069401048042d105008840b4502003855030389400e000301418142e0410700400c58041c194400381d41040700c2d2000880c0c000e03403803008075003664801d4034680025400001c48640b40e90344003070f425090031000b04042c101404d1580009014403e076002d09000c0403101c6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 257491600 1250 257490350 257490353
    0x61808071520160206031e06030c010206041205040f03030f122022030c0806010602030c07140f09070e011403060d060c09090c020a0b09060f15030a021809011d0a0807 73
    0x1110641d006940c000e00c1c00381c3c4c0e0715007410340001047d02d20540c1c540380001039006c1019480c2c0030941c807440b1001a03000707207001e0f41c490300c0303690000d090000d07040d05000e130401011401401c0e43d101030740a103001c1d4407a1604060504002441c0c0000d841404050310f151400084121030f01c90403600350b411001d030b501c58442e9205507941070341c9109413036000c0716140c140038000200022008000304642e00c403400d907503240c1e0362010143c0e124401d8102c07030115500001000d100c070082401c0429001440984a01080007004021a0320301c0410742c2d0303030800f00b404007905002035a0b00c034800c54015030000c3d1003036003182050804501c104550180081c22640c4502801e141c01c0d204030031b03c03801071a0460081c081c108138450003a444402c0424203843c810f820f01c0c005135a130140043c40b01e0145a4101d40780c041c80da20f455015034039416079a02d195041c016030307604002598420841d4242550114074030f450b01d0030084000ca086549080c542c003004c01e200c0548001007400031408181040e000401c890307031090709 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 257492850 1250 257491600 257491627
    0x5011b030209030c040b06120103050a020a0518010509041103011406030c0307061b0812010905061003022a030d020c010e150103151a0924010201050919061808071520 73
    0x800c230319038101510b050000010300c4000590300d9607080c000d0300c02d0342c45180c60300b051011490f10030301e20090080440c0010007441c2015a4242d038818014009150901c0c014130019082d542002d11500d10421004140a4189010701405075041c2c0c0c220010300604e03190a8014040904407550001403280030740001c001c2c020035000321402d604d0005040b6881d0740e1174079552001440b0a491070380c000c05190317280c452014040d00c200d80b03100001c0368000e0288920b481e0145028802e40c4054a91408180170b0300503468401c0c0041e1a202001c0c0d0004144812980e402a1807c41082942c234288000d030170040021134044400c8904540312200c0110740e2403c00c01403c41801c8105840760b8002440400b009510320580a20a12411002c0c1c0101514104d10004a0a80c1e00c16154255142c128048110203012000384030b9006501c15003012504840d4466100c82e5506c0f4a2810340310240300081301c40802003070304240c51155008240400402902a01c0000d44842d140c4900700c001c400001c1d5100d49024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 257494100 1250 257492850 257492857
    0x50c1005390a080a02010506040203040b0a0e0c0a06093213060803030705040608090a02060406030c09090c0203030f0c03010f050d08090405100f0608040f0308041e05011b030209030c040b06 83
    0x100c40480707081542915009202d0750010000e90015464180442d849127801e00032680100c2e0002092003041d15542c4600004103054000c814551082464243c03513925495904c0000304513079207820011528090f015010b104811100220803047c51001c5141c000b200b15108036080010b03a4045507140175001540010142c03078014510b18070011081000b2142d102c2c0042054030015075503090760791078008a4035550b0070282402948400c0904c4240801c6219900c2110294882d01c1c0c0605015500d6401c141143d20301101040160000020400007000b000b102580140b15070381400e2540d80751005d84560140903016683c410861310799101c062120031802e507403103010002d00400c00d41c200070b101c1c2945521903104481d600260607000041c101d0144004070300c940d81140e151f031070211081da4121000c01000343300f240c1c1c4600010b509031102d010f1180101076240704000001c2c40c1c001c0308988002460048008074101801000883c049403000300b021215000300b0388000c40c000c2d68110000f8140d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 257495350 1250 257494100 257494207
    0x21203212a1308100c030c090b0d0902090f15030d02070612060e280b01020c040b0a15020303040302012703030515030d05090a0807050105250609050c1005 68
    0x80da8000109201e0030205000c1e1031030711040b0301000f0b801040f10046c0c0a03100007051a0000c03c243d000b04010000500009080d01a0910b2000031030410641c00200300c0201981c090041d201c2c0a003c20181c0da1160b21100da012100302c0c01000c80e0307112100002d42d2001c00f0300900301041b0041e200c014040405810190180290098040c0c407490007000b0140c251050750585040c0c500004003a906550b1984507103a0008010380c0501036005540b020702001e41031740000c0f45d4020301c0e1142e0002e0150181c80b0032040340300290f0701650703403030815090003403c0d1080c0203160114015180c0000e00a480161019a0440c0d030509011880e0380d82d440b40c01e860b107031f4510a42c9401d070080d8802d4141c480c0d072150042c0740c090021211440c0036619148160307564015805068040b03403007000040d202950398940c00d4980c01d140b42e21100300011a545132825200c00e03500c21161079011042d8064503141c42c0340300c1d04a440051800c58103010600c4120341056181d200050031200040c1074440900206a40510706c4c44c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 257496600 1250 257495350 257495377
    0x717010b12150604021e090d0602040305030304200a0603050426041a03060d02011b0c1212080412030905070b030c030103050d08060d030f020307021203212a 69
    0x280000c42003034481d0354000101d4400810b000005440e40341501c280c5c2d0f03040c82424801003800c09011448885030b0311070b014580d405400349110380d000600600040003c2e51007980a9512800c051074440504006180e03880d410004c100803c5071603440d10003c00c4115012454081402e80b61400d1440840907071202241c2c90b1810080c00d040910682c074002d10031111003100b41c1c100da2400da60588250700003690341580c0031401500d0035015612504918054680c1e9290703090300c56525681d0583c490805a200001d146203242c64003086c8031409030605c010140e0380c100051f2714545540c8008130504a820340d10107050380c401c44c000c00e0000c10842480a001c2a500706945c03820554030352016500f0034441107030b1901c1176001e01c150042c850011540a81d0024060101069069030161504102246180210701c400e1004102513603e0742050761401248101031942c808942340001807980f01005c0042410086c0b0090002c80e0b4100700300304104440002c0070404200355092a800ca521030310741c640525 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 257497850 1250 257496600 257496619
    0x151503060f18090d03230403090f12020f100c062c011a030d0c02010f030e010c0e030c01020d08060405060609030d05030f070804030c110a0807030c0906090e0717010b 73
    0x1c00c40011106028854043c1110b240c0e07a4030710000c500f6250010b69420f0041030302400444020420b00c00305400501c00e0402c2d084054403250800c2c554070403980003a004810101401c415130130408d940784107c040581d03074500682c101c9080501681b044400c0109126581c6141d001c0250140e45642e100d603180382402091a0316086496000c3c080001408500984107000c84500c2c0c540003130400901e0205c1d4680c4d000038091a00191404000a9410380c107140c0c07180060b6903010028481c007071100c100c0e03440348444d0360420018540f4005408045c1c906543c0030000c1d0b0501144c0040c4c4041c0e00060172200820603680350b2010800d28010360f500070345c00d803049400005040750082c01641c070942041901020603038a20270105d550740d10958010f4082420800240045960911300c80e0740c5050160881b4070469803441085e190091961040d00e0700c0c4080c0109015600150040900600003050184541c100703c544058581066218000c7c0c0100c25055041c00304c0350a4110000c0314000a0002c0030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 257499100 1250 257497850 257497879
    0x306090403020c1c060501050f0d140c12102004090213080303010609081b090a0203040302011104170c03030a140328022109071502030f0307090509151503060f 70
    0x109041d079030108175001810807001140d103040504081d80d2030b0200410a240501954650000c20b82061541d8801405083d0624646440d81400000082e0181d402020b002449402d490100d8901100c9064165002000d080e100c886020a03181a40d030b0740c150041e42c413440d0303603205c41070b05480e0350104030240008400040c9054001c041c000c1254048419903030405801d4620b020201e00c5000c2c1ea640c0101003c5c003058030316a00340e0146920520a00000440d01424204c00034607402541c081e40a140349081c1c0300381300d00790034094855449800d600643c01d201c80140e000d00040c401081c028011500840010000d951100c0800c0040a40944d50240600781310b40b003201a41c000d08007055580000184030751812008030903240301d6140740c00a004402d0900e030000d0307802912203880004510007440140c0b042c8030300e400114010b441a072034201c581803170032060000507400100090307a041e0245403042c0307107a00ca00214060301207645402c0d9560b41ea9081c00201c10000004010360040b070b00322001b10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 257500350 1250 257499100 257499139
    0x30201081512150108070603090305040b071104050a0f06050108040521130b0d06080c0f061602031c030b010c050a03030b010c05011a04051b090f030307081204030806010f02030306090403020c 84
    0x90507034150f81c0503200b807551205070076010b82d40c1049e40140081c07004c001c1041018a40400b800d111071044c003003c04c40200704000903066078015550300407010b545004002c20740c01d4610841c001407900707090410807460540c803619158007200702d40b040514107011010450302642022681d030070543d1245040c00c50b8481107130401681025001d11103407450b00f400455801c4000480155400008005000900b485c10910105400c0b12001e03040051507404000d005a40070700007003405a84206e0780c00c50305020746000509452100900d5810302c8a0000c60402055003c40c020301d005426081c0404c0421403c0e00499034118070b000081d1440d460a4409800341030764051851580340211428402b5071940c200f40e0541158030803206064140412401c203a40c10540760008920354002e00b41d84c01d104941d1110381c06648424148d88101581c10108001c2581184e4a180c010707d00780780080e0340e82991400696207102c00b03400e89115001c0c600010781010b108128030309010b500500b55041e0802c461702c009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 257501600 1250 257500350 257500393
    0x20a0c030309031a01051c050309061b0c0607030c0809010912060e1c090501140d021306030c030902010e0111070306060807260303060108070c0218061306030201081512 74
    0x2c4808a143c0413100f40091100d0000d0780c1030f01d000801000c0000c941c2440000d031500c0c28181250640418442d0036501e5a4400203400300c030f4004070746031442820b0032440a08200800c0c0340c0c00e208440910482020a521600760f45900e50b10109440e030b90300076003005031703149000c03644000c00c03900c4401c1420082000f43d40020341c030645804c08a455160300030248000501d60581c55000150508604001c1c2e07600c00c5520992003090390842a240401d400b0800088e0303400b851543c03044001c41d039003c1109961510031490f25a95600e0100102e400a5000810b06018800482d040040c14114001000418080c034001507500c090208000759032854220789a9055208804101c51800b903d500340740000e90424243c84503a4003e5491030f40c8000040d2001d80307002c0c241c0e02c10881610f21400041c2c45030103060310111300d0341e00c1943c89031034108200040743c42189a8031188130f0403c3c0c0308100603600680003581010260982842c03450354400810005c015015140f00c0b640300300704404c48004198601d6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 257502850 1250 257501600 257501603
    0x90219030c02010c020d031d010c050403170306060403080d0e0a0c080c010801050d06181e06060501030915020f0f04030c0f0605070809090606090324160816020a0c03030903 76
    0x90003007078442142603003200d80200d030303c00158210b00ca00c90300c07143c0719074000c0b903002c1c81320a40a041003070701c071159a003102c1d0031b4041d1360040f8100240504c207106902d80c46a408100b14041075156142980c00b02d038890149100050a98030b020880ca510030040b9003108292030041c2046501680c0141810741c1440d00c0c82c815140d0a001d003002185803548100102130598101900070041c0d8003003503803810024000c040000800c0c006084078100044d0101601c0d44d284912407141e180000d082c0d0a04500702d4030180c0c015410f051402c80908002080d81c1480344182020071001030300e40c40090004071041c811540c00e40b082d080000f0300401005000902d51090320303280c01c0342492003034072081c1c1500c0b188169940605065000d20075500c03d4070b0480284c9a10000c003600181c20081c003031010078500340c00c071860384550850809107412213101600906d90300c0b80558034484400f031074100c03005d804944083e0410003001000e05800d00c40500800c0f50340100e5911880c00c60007941d0740d04005242000d103000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 257504100 1250 257502850 257502857
    0x20d0606030b0705070b060d0501090b040309090f020304020f1e13050a06060c0b040611041502030a030c1416080f030906040302060603010c0e0108090a050102031512010e031c0204090219 82
    0x3140380c140c49203007680c0c842ca82c005190000b03030315047e04200e503071807518004564640d04e507078030000080e403107102c99405584280c8804110504012524042e507040c856003807030b0248180304110142e524070a070700041e00015914001a201c40c1a038209010400364803c0d40c121001000c46101e4506907400f451041059000400100e503c5102c02c51749100d4641c0040c0074107501102140c0400e1180d480030072001d10712404e42c2d01e01a134644034010301c1c41117001e5000c0076030401300d039280c0400d0b0503004086140300e107460120103c0f907441d42d17008954080c00c45d800c6101c0d80d00c40c0c2c4450030880958200c4021590200c0d040d601ca24060844c50340c2c0d540c084804800500034000811030134101406605091380d07040d01d650101c05802c0c001102c4034080245403510340c1c81740b4282003020aa007071004500500968803442941c2c5a0f510601081a0307241c00c0500c1035a1500002035104400442507944142c002040390443d0707080e6030501d5001c0c0c005c58000e03c030054400280c2405d65500d42140752401e044a42303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 257505350 1250 257504100 257504123
    0x504060b0a0e0a0e0103170c060411240f09060412050f1203040b04060c050d090c17070b030c07050a060e01050f01140d03050a05072012120702011b020d060603 70
    0x1000e0140d911024841ca13151481c0c8031006000203001038284803403d50003181309904040007280e007a4680b21040c2d07015205010358100c00c0d400c600302045a10329181100c1c0b02421810407041c2c1507845803049a00030944010080b492180079a40c0b40219802001c6600c00c1104a20143c1451030300d40d0010b038240c407118461100c0c40f6850302c00700300941744965000070f98160f05946d03684a81c409040694201c20400000f0807440000760720520503810200d019801d07441a050900d1a521310040f43c122801c14143d1040d01c0070465145031004913a0b008800d40070043d15042c00f880c269141c507008640082085050180341c00a800701580054410080d19190078103503640d4901c442403040417440100e0b04444804041c0000c640144020043c103800c500d80249800f10300e44030400f00184004002c1c40700804e404075800300d0302e022554a44a85456009005c0300d0300d4444121843d0301c80c600d030080c184521802c0026212211840301c00465401030252180e81a1600d4020000c01c2c050201311750381e45885 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 257506600 1250 257505350 257505377
    0x203030f040f0f06050f07020109090e010c09140a050d020a12080a020105070c080304030818070303050c1005070801120203120415030e161202030c2e0201110a0302030403090504060b0a 81
    0x83c0380e110f0890352581c9516241c115100740c3e462003070384100016418031880400004100280d407151030340710a10200002203040c81010000c006050b6680006040c0302100810316150b52142072481c00c032102201d41030480031051011810400d83d9034003003081c03106a9040c000c14406ca00d4004c1c0030404083d4020002c0d591201025030380c0701042c0700094100759050001900182c0106200c9802c04550b0304010303040e00000030098600310b5590000c0340011008541081010070402802c0403101000000b0f02692400030b100606440c4148100008600e11400400c2591028020000260f040c00c2003d17a0361a141c104100d11400c0c1c083e1036000003441e141e80138200003000b1507034149000d00080c0030000c031843c00cd94450380c514080d03002c0c1e9150013200c01015155a500c014600969200050300d0450301c2c40000e0954004410655401175904100004540d8403c0f40d0440300318000c0e40c10300680300d0b00e4034142182d5500064010640062a040c00460541e03152800340415a42c3c1ea520202401041c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 257507850 1250 257506600 257506619
    0x6030604030906111606020102120f06030a120c02180106080a090b06010f030f2417060105060f07020307080c030f010618020c0316031e0e01020c100c0203030f040f 72
    0x49802500007036010506001c0640f090350700071811000d400c11199000217850389210440701640c40100541c0d40046e800060091012030302d940113515180800d16071825802003511090403220040000010380e400300b11890064001d158440e402404a030700305070002001041455084c0039100201e400c070800280c1020b0180100c1076441e50040f801080c0f619500d0042d9012001c1841030b038103241d2150f0942100c0002c0384100540340941c03205032001c4220000b56401c03e0545500032000400341d280171040e4586000851604446065441f1a612150044006901d0040641c020f605015882c00020a1880020800e5200d03100b2415070f10400e80c4642040d00f200c00601c42e46070f8045601c120040071015582c040c005100440050b02e240c401012021009448a1001100810046600780380303192403404d050140600b083c2046208100d51000103581c485e02c25800038803c40400807001c00031403144031060b6003c0d030301404030790b15005480d520300010341050040640030040e56a000511a50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 257509100 1250 257507850 257507863
    0x901090905131e03090e060a080105160807021501050906010e0301020c070501020c030129030109050706050705010b04380a12021201090b0a051f03050a031107060921050f060f0603 79
    0x3419111840c0c040e161441c0b000043c2c0000307007800ea00000c041d01c00a88140203004441c0314421000007820740860220cc041d0000d4000b5101104640c0081c58099418041460090656a04461224040c0c0c0c5050040750740311055540141c144d400890285010a00040d034a419100240c081c0c400da111890241800c0707030811041040c042020440203000c506100b0b01c8094440800b50000ca0074160580710079103040982d03800100020000690b1a043c09030a01c191400200300712000c0c4510a80701c3d403091208010f00031802d1048100d0b4000540340c0300c68450140c01000040c10b20030340b10f540c42010a82d60440c03038000741e000d42c024128003c5c0c41d580c103202c3d05104960041d594812520b44a1402004060040449100341c4807091054040e0400611980c01144600000e01d003030700076450020000382403298500e0090748078820a0280c2c1b5007040b00181550780d498505490301e80c450020741114030031a1000750160051090b00817109801080c1584a000103003444800b41e1281d00a0594031030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 257510350 1250 257509100 257509103
    0x5160812100e090a080717120403081605040501051309240b040803070f0507120b01061d0f190f0306090c08030c030f160203061006030e0a12050901090905131e 70
    0x1c01c44001c0e80006136440010f8544c02c0d0207644100e40b51107c1054891640e48070340180581d0a20708020001016404145290320409403c81030903100c40200024081c0e0145020300e80c107103c80482e20341102401010048000c146908007441402e48041401d00200385000c43c0360400c0400207004500c94042400b120111500180214070b081e1841c3c8509000b2842c03290708440d2800f0700b101c00250403440c1440404801d000b100d42c078106514020020702140021044039440c2510144484202e40c5c0b10060203100d440182c2e4030130030000d800c41a040103801d554100140d0805107901c04001c2c02040c0e8081e40c08180303d142c0000499448201c4140d136070041c01c490349100d60080008000b011040c0015103034650882c81200b1200c0096030010b803c20504071103c4c0108a40003100300201c5501d4010241c034600803101a081c40300300ca4840c42001e0000110031380c00d100380026140d400340d2180d01c00750000d0030b14000400113428070014060410401c01c0c3d05503500803116145c00401d4880c05400140c03079 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 257511600 1250 257510350 257510353
    0x21903060b040302040519110415030c0c03140d060b040306061d15060705011d06100302060405061e0a0e011e05070f14030a0305160801030308010605160812100e09 72
    0x1d14513800c000160400404450408039134400c401c80140ca40d004122049450b070300c24070b80302c50821710b0407520006480c01d0320040505006030f04400d6500403c0f079041c0c25805103401c1030310700504841203200c2d00c105802680110f152110000c3d003007003c500500241c1e0b206100034850255038100c040380f001401c5880146c5c40700e080e00420788100000104440c12600940024240300140d00d1b25401c442901c059604040c0c0032039041c40f00444103000c1140e00c170444c0154442003606580100d076650282d405030b41d005004c00a101402d1084c1d44000c0c1c0c40482d40500b10f181d40b8241d2580051070202031040301070100d000803000c1d002850801d00340c00c61080550340c60508182c11502d0700e035140c0038410800c0c0c130340340241700c800424864140000c04881516407808981c6051252400018961000e01c500402550f100103000082d4090342490445100c1c0c5807080e121181c0074030b004118950301d00002d046940000e06d4200c82e52050040700c2c420b0503030559043e0311a544940034001e01c0001c0314482d03881e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 257512850 1250 257511600 257511607
    0x10f0608040519020d02281505160507050307081c05030105010c0303021804020d0902030c090402061b010b2d011107121113051803120a0e030715021903060b 69
    0xc43e10203002140b0700f64002008688040b04e15000b180c80702d03049840c03004000200c8100118070484a90b102d000510030030520940e00300c4010b80040081c01040307594100c40302081405024800100701c0c00d800342000501351109950340d16a207543d18404180c0194400410103a4244058054806d6034101c070710684409440d41590307a4110b00944c46400840880c413240700c4a40041d0300e961028240603915000001205039044c01050329103044035090301e220348000c004000042e00ea09081d0f03001c161001181c040c1c1d4808a420303440c05401d0032581240c1080903818400303c44d0101c17114107800044030400d03152640e40c054004651044c2912401e01050f4004a4100010400d60a070800d142c0d0044225040e43c6a42d44e000a0005d003141c4000e004a03034654003403242ea070700c03680910800110b41400451805285448501c00780e000184000035190f59920300403104001802182d055552080500781201131041c0418002e410a1000c11540b1a074200340c5e406280c0284110000d840f071040080b403c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 257514100 1250 257512850 257512873
    0xd0507120c0905060307020307140f0114060f12070308070b0709121212020f041217041d040309090e0d03060f050307090b030f0703050a02091b1801030209060403030206010f06080405 80
    0x241031340013420000c11071200300b12715008925107400c0f81d054200340c10040e00b10850103a08a60940f1228062030440302119000c0c804c0d00e80c1e6010360540682d8041d10840c2001981c100120300f8034919600182052600280b008100722290104900c582c510380c44502d016510307201d0500e5032810b00c800040840d988186013400080c040c141c0e020300041c0d00f030303009440c2610b0010180002c0c1c200b5408100e04030501c10004040040369510300d11001c00d400d8040c1e00f000d07c0c058611005459982c10681128034410126003414860a1182c000d042a0f6a040c0031401c0260416a07845050b02c0b800c01c0000c1c600440805d2009400c40c50b9011580c008000304229814101c82d5001442030907105070b071520031030300201004041801580001c60144014104541d1700e8018044010001000e125510180b0304003040803c6601c42130710102c5454404c40704c0e2100d03400c40140c00a119074684650f0003840840d0000800d40c1c0014580e0507100001e0344404650341d075610640d40410309a40040658001c51459174 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 257515350 1250 257514100 257514109
    0x50103020f09060303040f0f03050609010e1b0102120a0c02030c24090d02090f010801050a051312020c04020c2d070510021501030308240603010b1804020d0507120c0905 74
    0x20f40206006094034540383d0341c1c0045c10300800b841d5110541044200108200f0b020081c4405a0301840a400a12200180700131494aa00d21200e054052424070a003049030b030f910810140c0c0c600401000d0107a81c0f03030401c2802808620034a50120b10034800c0402180c882e09011900580241d050041f0302d14140d000d9180c1d0030146c0040341e045400540580c10940540e5800f85000d0203007800030400c031200e5040031030311801d4070b000074100301c803060070802880f0b288030054000071145600480c0188007030b406503a0032030411008684241e8054004140203504900204000f01e6000f44070032030854468060480030303e03c20f4521034442141d0040034040003a800c0010744940c54080301e2040d5410020501d845403003241081c0c0055000807008007c1000e640140c400b0703021242004122400c5204200c0d001a4181c84140299401c201010540d816001054100b2000e020350041c8217546030f0280050b50340c02021300b00e40d5100080c604058044c00b1000b035208000c40e0f59030a1380e682e42c01030f00b800d0030710 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 257516600 1250 257515350 257515369
    0xf0d1b1107211e020109090510030201080411030d1d09061c08040b03040303020406030605030a0b01091a060708130f0e06010f0c0f050a050f011a040b120f0a06050a050103020f 77
    0x600b24002c801c400081040c61a0351040c02070004404295140340001819219946c118208003482c00b0103201e40c1c20381103401c0000b143e6091811303044a0745d8518089210024900019426101740213007113603d00d8114180c0e800c0b400120654018040301d542c10000d980406586054000500b07601d988038403020508401c0045010f01f020501d884d9030b0742040750459004440c00e03800254003050501c9280c0c0d040c0101e40003004110000c007140465038a403030f01c440740c044c81103195032961203400d04c2c1c00c150b0150243e00c480c400141441d4540303c0a080504195000e0252201c40c8104001c02040c0b50b0880f5803600203560700199000141d6469070010740c0c1e0380820342440c4040c0a6240700303180015188003141c441040c804d1002d080600030504d440707450304400701064003140e4100103010a000c180700e42c8000360714130102c501140360380074600481c07031000901e00360b42014002c031103011440d07240015180900903c600002c21160399039040c0c1034100c85003804020740c0301d141c02400c0c00d118948207181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 257517850 1250 257516600 257516639
    0x102010e0c0904110d15020c0d03020301380a050c01050c070f03030209010507021f080105030c010e21010c02030a0f020109020d031d0603070201060306050906040519080f0d1b1107 79
    0x84005d00407145c48080b80c004449201c41e1240e5000038648080b40c100b4403507188214117a080540c21541410915820320381c1000c004141d10801035011031400c0c001750520b4bc500e46440c80615030760b41c01540024166417200f130351800c9640c2031601250707802e0070000132500d08540161080c1090402c6a800300e010358400c0f41071904000b0203000720700150703441c1c0c00d14a00e1900100d030344107018051840c024010000580c4014401c0d0048401c1c000141d07008010a00076a20854203440301b102d00c040c08070741e08015002100c40940c80c101203544c0c02500000200010207042c2c41c0c101c0101c021120490aa13102110025000a031046042d40000e0140e201445204401660305000b00c4640000c40e4442d0400c0310103100603911900100180f01c4a4843d040e00500100c016014502c0e02c0c0d181c2030b50300c1001098420301c4182c103198040c10700c0000b60175a0748415260710020b5860f00c09900110103410318a40c000008000c8120303451050380940e0031b103c4054082d10280480b0391614a81000a0f00420107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 257519100 1250 257517850 257517859
    0x130f120e03010c0e03010b0910051201060e070e030f030a0c03080601020109300c2612010e04020a0e15010e0a080114010906120c03080d0e010e06060102010e0c090411 73
    0x19000c281c1e800703000b0801418035956816140f1020b0b4401c0500759240010101e00841084050050103411750102c074090b20410b840c1208141030140c0600c0c01041d4039031142000e02101414000515402010030343e18000071812540b440d130403c1003107601da1203103d00c0080801d145004020029015003006940b081c014000003903c6502034445506c09004440802d038858071036064400070b1100381d01022000095440d007400c1c41e0301c10740d8400d4014848854008400c3c0040a108031100800504540103581944118503c55175603402d080003c00c1e05807400c0344245400c0380003050745480c0d440014800e0904003e12404944464015501d45e40c1000360b080c1c0040a03000e01054040d13090140040305041100c500c00c0c15854150390b28102e900680008d080021a07450a8000c1551102844156500048540c1c0d88180002c1c18000504404110104550a15550100b440d1000c078405106000a8001b4030409041d0b801c00d51b1109000c501155000316100041004603000043c00300c3e00100140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 257520350 1250 257519100 257519117
    0x3061815131e060e090102090a0b030604060f0321030504030806040b03030906071b05041803050a051303080703080f1605070f050304080f010e011107030302091912020405130f12 78
    0x3800c0000c06551158440d2552500b008104007410601c4c080d40c8041d40c1c1c0c00840c1881500c60000fa01003505201c7d2540038000030010031000e07641e542c424030081213017402200c031459413841c0c50a0085000382c01d010b420701160310340303924640c001d0142c284038a03499994049903680b00020040103213440c41d480d90709840248280301c81500e920000b02135060080f040c09161300c41036415030004400303581009005600300703043c100c0d800c5074040104030300d03640c0750819a84540c64841c08844a0060203046424684d5006002050181c250300402116000b40c3d034030713892603a403d02c40c040b00210540d501d80550740400400400c0a01ca0f43c00341500c0352044103200002c040c541c40c0c0502e1900250042c0750640c00c0192451000c000c03d1240c0480051005d0090101c07420400030f090391801028406814140c00155001d426900d80c41c001c10744044514030807680c3d90315007001e270800c0c8074000401c9000360319083c0451541509021032944a981c0503610300300111050b40c0b216080348108000d80244082c18 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 257521600 1250 257520350 257520371
    0x50109050d0512010f030503040e0712020f0403021c020a0524040e071101050705030c0a03090f06050601111b06130f0803030f150f01030e03070b04080306181513 71
    0x20700c5107400041456949a48541d540f05036a985194183d10440c1210035041003000090004001d60f800c84031100d0b802e0700c40c0ea0f034030003003034442006601000c031016100040c0129080c1d900720140003074034000d5030301d0ad004188940d484802042c0c60440a9442000b85404015500d003107200b64000c20745e0f600301001c5504100300e58030800d41254004045480e4103a08100c1c5984d07000d07580c4051025400028405420440c1e0040d000340300140400400b440009a0114000e019421102c070581d0301c0202003140c1e40c21410304a0040a050b1400340c009100c11040100300c03a0005a02c45203c40400410200011010100911540115080c0c026200c010303034001034000d486100840200038038409103540b440c01c201c0003414a03400429070040c1611941c0b100c2c807251078100c02000440801e0a0010700008801c041d14610b020710034000b04400c03e007008210400203188083d40c041c6400b0f48440c41962101800041550022100500400c00c42d0002003201d05d0104806055003441d4a000201942079 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 257522850 1250 257521600 257521603
    0x1203020912060a05160c03030903110a060c0318020906090a06030b01060825020c090702100c1806090e04030c0807060c180e09030d09060b1017090c0a030f05010905 72
    0x101c003210350180c11035420403403140224041c180d4400c0c0044000d0058400b40304c8050101c04180390301500305941c2e0b80d030210405000700032288407400072408851107800107180070000380c4600481c8000207820600001885039104804c0e68059500600b121700c0355568205000d080c5800030403505040f0707184e18001021481150140c0d0280203180d9812042e85003001210710b10a1a07020280f000351b1204041000305540440e00010740941124410403031b4036021030407450040b29640f1302d445940b40c003014640207a001130003141030f04403034005460044e0359840d080e0b0740b405203131249240b007150060010340024451b03189050806d104480041c20054143c59000c111001c4c40c50401c003040703c90803201c4e0043c4030140070710001c00e481d0840c5007442c0b40c2031543c42d441e4010114a658076988403040da4080040640040c00c151102401d94400070200110050100b602d030901c0400654019010801200b004100b0145001c1c01a00c802c80c034600d10f0b96a02c80c030301840d19003030764155620000c907000181c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 257524100 1250 257522850 257522869
    0x1403011b02030705060c0301030b0a0e0c0603151203040b030c03040512030709051c0804050f041b2106050f0d03030b04060603020c010606020f0d0507170705010218040203100312030209 81
    0x203560300a50f2a001d551130a513140240140100c20384420900041001071900d160300c680c004659000031441c0424442918a8800d20201c1c15034498404001c110310003030549840e054142003210342000d201401b01031291030781310390301584101e400200005101c00c48000d00958025200d50100c0f003880303404032000b900c6500140c55001c001162076030100641e240a0180980340000064078285016640e55203400602c51885a00d00403039881c0403440040c3c1d9158030040101c000c444540c040f500c40c0d0200207240c1c503552450003a080070b88101c25400c050140c0715079000d855010702620580c1c1080001c0020f00c00a4a40850806803a0490a41e40d41c4880c060180100a261009a143c08040405509454132074010004550000c0c0d031711903510500050840200009050040d900c0c840c2d82006806810941d05a035407580c03000805004001c0c055008061911307849402d001d507582007604010580c030042e901d00c914121051000d0011038120040b641240c00c2500300186000b200b070000c00c40440c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 257525350 1250 257524100 257524151
    0xb0f0907090f05060406170a110103151202010f05030f040b0414160609080c060301091a060304080a030c030e0d080a0f0f0b0f01230a030f0e0f0d08060604140301 71
    0x1d80780c0043c41007904260107481e0262440c4001f2000383d5070b4601c0340d55a00e808041001d492492500f40886c60760f40282d108181e0300e070459940c030f0720203500c62000341c0c1d082881c524102c1c0010408401600035a01c10000d480c000d1080c01a81c030003035102c5480380c80c4010401b402c1941c1080c624100821080c0d410802681c0310750b0102c5010b5002894900d002d0904100d0341d02002031074000c41c0700881240c0d1076200300ea041d100300c600c0000b0440c8c0c040d11100403000349040c946030014000400c0c0824401020050700c040d83c45135500f400b451401d42011402d0302c0200c41140500e070301189101c041c10303001e148815402005004005010b01000c0c1d00ca000b030390034070401024401da8032076140401d41803002680105c01d10030701b00481c0f546594600310240000c02202c44224220100f50381003414840e801910304901400014860a4080002c494803130428030040781721440750040c1107420328020541c10f4030a08002700818280391a201c04101e41806d6051019410b550f09c1044241070100c6420440fa000b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 257526600 1250 257525350 257525381
    0x16050d0b0c21070e0603011a0d0204050a0305060417040f0e19110c12090121020f040605030901050a060503060610110a0308010806010f180b0607020a091505010c0b0f090709 76
    0x2030904810180c10340c14003509071341c06004108014030481810500c0364005040720503001e030b95507000400030300007070089402c40b507800080c1c0d4000005000d000588140103500500c00030030740b0702c034214003800240701e148140301030309440c0c82d01000380d4410f505010340e102c81020516200d0004900c401340480392050307204803840d10003050081d21403908016210f01c020402d61a41e00c0c1254010000c4c264034840c0c1104280c001c25070701c501191070943e8040d515000c2c50304460545540d00c802000d045a001140c000c0840e600c1c200000e1444040350194408591019003c0c110035200c0c0d10902507080e80f20440e442c180064016100c6c0721200411040a519000790f546034482e50411441074140881030340300b0380b40d29140c00018000d140721815600f10341c3da01d034180010303503200043c0406c00a00800001035130080d0010f000048080c89074005a920801807100d802c68541c60784010b43c0c803502c0e84034020705091007440004d0100c9810384401c3d0f03002064407048503031b4160780382e6400702580c1c0b0124502044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 257527850 1250 257526600 257526667
    0xa0b04021306120f06030c0e130b07030209010f020613030518130e060702060106050d0203071b03090503061f03080304020105040503100b03151306110c030705010e16050d0b0c 77
    0x150103036441341015115000b01c007403100ba859070b15280c03000006801418204821030000c00c3c0c80c61010994411002c1d406250009e40e4a04445c001c2d00039040207103510302080da41c13020711041c1071000c1903040c8a84150003c1204a82d2561001c5849400c03100c807c0b003200c0c1441499039966503c108405140300c180344000300e4089110081070781070100203048882594030860050107602c0d0400c2c140d4110050b100380050b22a80c8005044400b14144044100c1e0803603040f903140c080c1075000c20b440c02505c0e015001c483e8152224030303042240040700a0050300c1400b10320003c1c80000c409a00a5400070300500d4100c0c24a0b07140c1c00001d05101e80c507a010036580350350b203409040300d06003070105034828410031262843c94500707091208010800140010015940d461034044850640c80c1601c0710f0780c0c0d0708401c69484031414075015001b854040254641841004e0558000c070301c500751010282d1303401500b00c100031040c0d50349070705107030342d0107030000e164608213100700d0015424038050400504060b0104111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 257529100 1250 257527850 257527877
    0x2070606030c090e03160201050d051e010608100501050705210309010b010e0609100314070c03090b0a0e1e040203040b010302120a050c240d0606180302090a0b04021306 74
    0x50041c46540400b03e40350919120300f04c4c0030390110076600180f084e16001102d880181c8012a41803082c82d80c00d0300c40910740310030310603500f0400c42e000040c001020218072445c1d8039030300e05540942c411512144604002c0400740300551182d3f001d0240107204800b15180c1d5031044907122502208454113000784e076030220800480c10b00902450489420a0803c0b030094600e107008201503101d8480040d0140a4442c07038140039510039408406408111214916907041c84070008061464000c1e060300010664240810310040317200c11079000b0a035944803000601061400c1c000c407007110440300d9414442580e501c66042d01d8030700081d84194400e411100c00d540c11403041260b56044c210401519070300c8914040e00199001070300640c0c0000444031060b84418441c00000c2c842c0000d002450400700204403c465150b8a400c800203944a0391100079028403007180f015250220b40c07001950000400f030101e115030701560300020606002900c09841c01c6c0e41a502d1400d21601640702d400001e10003d00f03102e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 257530350 1250 257529100 257529113
    0x4090f050601020d08010509060d050a0b04030503091b0d030c05071e09061d010e090309120105070f08090706050d020d1b020105060a0503120a0c0f060e0601380405040207060603 78
    0x20138104980c18449140d5062201007408a840208981d004c1d508014922091100410210f1950743c3c0c4021844250300d01031800030032580040c2c8503803e0302d12032aa104401c000076100642030100340500800f92210f582d4400b100d51a00c03603981559507000e01900401d80c4400550726072020f003d0034941c4c132415442c04c01e5281c110351540c0d2000076038840341030a20008501c544c407000e044402402903803070181c55840c00503040d403040365005070388502100100750f00346406403c411301c11200b50f1074410144010102c1942e0076070044685500c542c210550034800c0ca4055800b4003a900034800005041015111203041100c00302c07004041310042400a0b8820150309008142d40440161002d01c10030345040c02203540d8148529200030704410204100c8031192190400e040416003011400304411081c0c1083e00007480852440c01c1e0a008401c0042030400c03644124001c00040300548000b04040c0c3c0e05640e400e00c4c80000c5010340118104000552a9980e00241904078015000019014550719010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 257531600 1250 257530350 257530363
    0xa060f0b0a12020c0a061109061219060b070f0c0e042109081e030d0603080c0d030507052a0615030f0f0d0503180102070804060201181e0804090f05060102 68
    0xc0054600400c5841c507032600c0402d100b900c0540c000008180c549186040050a000e230951090b00184003050b500300e031280040150f805114213040d40c4d07104203c920b03446010344555020b17202e02020100704080002d0f040710b0f24011441d004006103650b1644810261449040c1940c0c141c44004904409401130314a410b01c4044000242c1828401e283c58000f6054413045810360665000c2401a000c0681c03031018403c83e2402401750070304010030368807407805000341d4224a5600d5994841c0c0d00790300c03291a00a01c503041c021172107030301c400c0d0504007450914808459505864040c50031012101041c0c403800300002c90051070400003009000c081203050614051120015590540c04420012850b8002064009018045252156403592941e0440100201008055440d0341c400181442805088005881910304580c001c1c440444160303042801c00c14158005826038140040482c00c802d000103003000d20611542000c0c0c145540c5122650840303818003d0701000c103865104016082d84d050244 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 257532850 1250 257531600 257531627
    0xc070605030403120b0a1a09060c011401090209092202151b0303010506031501090305030f0901080f280e0703050109121701120f02040c0c03030f0c05030a02030a060f0b0a 75
    0x100f040e0500c1100041059100d1f2080e000303503a60b080d5602c08040503040840f5140702c1c000c1c140c02d582d000c001d149503000303048000400800030b1400002007082c01c018002c4a1180c1d00081100074207440f032201c0a9919500b00e84000c1c2d842c0b0f600080c150061310b41d448070a10030002d030b102ca540c03a000c0000d0041d9501c06c004151074210f8000304014003142d551881030360b40001905007510201910240180c2e0151444d40001d00a032001140d07101b48544440024901c60394283d0700c000c050b484003042821403043c15288090903030306083d008a110392018501032602e80081401261030300e00c6001c581d08201c016001510b03242d44420030b0005010700b14191240d640c0b96440c0c1010101e9051800b003803141c1060150f240c0d540b010802d40028460310041c00070764039030028010030408015210180c206184c1e0345044011030304005108110304e24501c10010710009545540c1e103150f456030203800c020750004201d810705035070740c960204907000004041b4000e482d01d40284e9503550792140c0041c00015a4160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 257534100 1250 257532850 257532887
    0x30e0a0309032013020d0e03030115030c0903110f060f07141212010909021f030507030b010f050403080313050a050f010e06060f370504181101050d020c070605030403 73
    0x20f8842c03525001c1c1d160482000b031581c010b844404040c1284041c1c8007a0110790700a2001000100d000fa880407501c44000080391000c00803218800b1058400181c03174403004d02040c1c1e108089070540d00b01041307ca402d07400000c240c107241002c44072020f0380303c0c0c00014056400300000b0000d804041001c0060051400b01c400166080010140000c10b00c05014090180055121051103045450341e08030300c0700002c2d916820820307407079600100400030802202d19200190400010600d103500442c0b981060f880c065603883e103080d0864079100019840a40920001e1600c14400c50201344203002500d0311a1040000e400f00340042e210301c0e8250385003c04000e1068000a051151941c4d90a01c00300c405401a100104050000d01600881e2a14104c1524080600072030924201c413400b1105401d4800484041003140103104070078807182803c070340061495899941009940d800761016240f00104404c000d40703000d844412290030410103a0100020a41c040b040c081010b810609028100300c0000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 257535350 1250 257534100 257534153
    0x30c03010b0d020d0c0e0c0918040b0114060708040b03100611071503020903010e0f0d020a05070603020304080f0d1406060901020a14011d06010314030309070b0a030e0a030903 77
    0xb0b092001c0000009111340c09551119041080c1e20f07807a44c004100d0282c1c40c42552520b00d49581d0b46070321860074584524541c08903070700a501410100c03400b460b0412130b511034582c01c29083d59400d417600605150b01030414400c10001980c0c50000f840940400200d00da101e0421105160314805590864014070034803940c840414600041c0381411030701010000440d8409800d8160028411419090f40550070540220170004001840c001840c0d691000c641b01001c990300201c0c0c0790041042c0080c516080060100070880c0300e60007658011303001d406402d1030700b0180c52410803158000c00c1d17020b4526403201d010440b100d60810007150f21510a851312840c14100d140005c0d121030107180024010555901c191344080000d6200190b00303800358400c2c0f9011800380b410307103603a0402440202c46221040c0058081d852021040d240215441802032499604140452041c1d801c980c02d8041056517903101c82d06411000c00100f801c6c0f500907100c0d44507030b0303041d070400c0883c03008034004261300d626004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 257536600 1250 257535350 257535371
    0x1209032e05100605090f0604170a02090106020a020105090d02010207080f070f06050f0a180801060b09130c0207030f03180e1603050603030706020f12070f1106040206030703020c010e060114030c0301 87
    0x840780525170440324031004000400001d0060b0007117401030f40306010521550000104005082034249008803034520361a0b036a5201240d4941020b10001d0001d0418401c0e01e002e403c081d03000c01c01c424414010b50340d810752240c82582c038000b04000c0d01005a44148420040024100d4022018102500c1e1080c0307841a0300484120a20590542800b040010a080c0d01c03800031805010016100580c020b20402c6c5d43c5d0310f0581220b80101700700c3d510845041c65440b4461178070344259280f40f03180307801038a43d140c07454541c2e90440700384400683c00e001c03500e800c810315003001048000103450020042d1006041c140c0d10181d9510b0600e00b81414140f0740005d01219070390020560305801c1d44035001680d103512a503a480c605000d0381c140182104a51400c0c44169a0040401c61040c20f040d6514108065540640c6540310b40030354000e0342000040002c5143c56210f0f80013070009404010022481700800300d034107071508009078400ea0104501d094241094030f0107011b040c00500c006c4000b884074070480c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 257537850 1250 257536600 257536607
    0x6060b130e220803060d060f0218040b0a030803090f07030b07180602120c150a02031e0106090501030c030e070b0306010207090203100b1c05040605040b0a0e1209032e051006 76
    0x201c0c140030f0101040800029020340c0c3c2c9200030b25071a9404a0107101426420b4005400303500a498580c00c030a40c400080700160a15104403840044014400c00f802803950312410065032000c0e00c1d004c0140a0382036492280201040450000e40c4110030045040c5000800100300d00540075518034040c3d51801d081041660004242aa070000b00008981d1060b5400b981032911700401c03d0880c04200c0c0a041013800c08060b40911301c540c81c2c0328044007035140b20b40c4010090361000d0003500041032200e80148100d501c650f1201d2500c689a040019822a18040c0c4624044880e80302010350240002040142e59061000d20001c1048010540c1107003424204a1200915030007030f0406404e010907044200c064110b60003a252001c0780c010072043c10325041c03503009424215802e0701c4d26a0804d0204403082c0061040600464000001e0030007805440380c151042d82c0144621545442031203207484074026079007020074280074500112240c0e0b1441c1c10920007507800080c80c0c4400040740d09420001b5640 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 257539100 1250 257537850 257537911
    0x1e200310090509031b06070f0f020a0b010f090501170a03050a030204081f0c0207080705120a14060106090506030106170a0b03031210050312390c030106050a0f09020706060b130e 78
    0xb2350500350000035924001b207180c1100340d000540a02d400000020b80c14a02441020680e030280c84240546c0c0c0c0c9030300c2d85807091349a40544000b154828500000070912560251540000529001d460036a9400d038440c0740149a1069403c401c9007664901000030080c4903c2c4002122070000e814034600c2e0041154503075130b041c400c440c043c0741d880036061120401400100e106507803201102240c032172480c41c0180d844809024031800304020003404240c0d0728184003507134101d80b10781e03989982c45c1401200820807680d006e04030600b06500c0302200d42140e50b084c80608410894449180c02a01c1c040345014070394442c41e40054003d40201c0300d5802c482c1003a20858280520300300d07041411000d14500030103240b081e200c04844580e801804184e0b0b0300f201040d001d0040c03500320002d000316500d0b0010001740020714410680e14040c0f4050802068180740c0292903290b006001c0012050340e2090107460704c0d803000d9409909031a50190034000e10024035100da80000c0090031100e04520440d06c0900c041c5d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 257540350 1250 257539100 257539127
    0x4060b07030305270714010c11060c07090606031a0406050306065b050910050c030724090f0b091f1e200310090509031b0607 55
    0x1500d070000030302c6002010301814040158040c0e03800a4035041413503162108501e00403004030198400000d00070b58414001091000d4100180002602604080000e65132002503203039554010324000161283c0c480c0b04400060419071000309003c0c044001c0c00c1140c40c41270798428440c514140c018045034500140685e40220192040441c80d81040d02030714030420044020300030700500880036180c045480346400003041d00034000d10704d8809118600350b605221106514002802481260003920307000e44e5600b00ca00190910500d084e204840041c19684150029240d8010001e140294203030254450310420102c2c0300308001c1c0380359580e03e41400301e04c10407014000c04148008220aa0300500400c4042e904082110182580280311440a00001c1182d80e4040b00240c44581e031103110703405503500034103055051103140550040407903020341010300b41d64124038040f00045420581c0b44600c46c007880c00c0000079500c44c500d0007003030002d107100d440390454203402520900c50071507040724040185a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 257541600 1250 257540350 257540357
    0x213081f0510150c0b16080f100e0f070905030d050a050d020c0a0302010b040e0a020306010b0f09030d0908070b0f031303020f15040204180b01140307121103010b04060b0703 76
    0x584074101c002d400720015420220303558400052804103290000202810b240c418030003451030381d4035812101049000010070718080703501500001e00030400301c20110382c0050f001c00601800c03603c0b01b801d02c0321f288040f56048807404500050100c0305810016580040000714000c08060100d120f00420500640c05003206100021413402a07002007501034444407900c1e00212010a4098103009001c0c4c4411104940220315100f4845d281010200b8560750450300a00248040d900e000030000c42e0743d010728005030880c1c90603c04084690f40c01d01c10f6900c20710f61a6210082c0310308096070385040c503500368062002d444041003001003204010041d2035000c1410750910801610500b8180d08281410329544468065101c0341400c011081005c41e0185000703940c20400207905003010701d90044d29050180c101003c4500400210b101d41d00c40040d404006003c0d9047c0350366a0150b034645141d8110115942441c0040c10300c0710703090910480211190071070301400160310b0030f05800e4692184030303006800c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 257542850 1250 257541600 257541611
    0x507050414060d0e210a0905011107120c0305010507091a0d09020301060f170f0303041b052d01030c2012160506180c1c05100213081f 59
    0x1e41c0c0c2c4000a0b07030800303100100d0030310400c4a22516241c580121a05640314401d104000102c84084a010389401c022176854914140d81484019121150382c1c0201c1c4540c0d1040c16008509a0038281c09070306007601c9074181030901800c40c42c016003952001059141000803004040049038070610b462040f41030382442041e541e003100440707900603190025019400d5800c00c8000101d18414041001c100e031500c0140043c0751001a001980352004128421119481803001c5004140756074032480040c00c04051410307441d42e694000c11003c080080000444000e55441d0f0a894190042810300d85442441d00700500c4488030b00141c14888500302c103e5024001805000d0514400c202506203000d5004a41340c50700e00c601d171a00f54120b80881e045495004200120350804400174071000c0f107110800140902000c03010503c16980d81d000e03945c0102075405010240854400c2c807549840404019001d607507032954002050380c0322402d521160740b59008045240d50303e10a000b200d80c0c0c6d010707501c001042c0e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 257544100 1250 257542850 257542889
    0x902102a022d15040305060604050c070b0103060c2007030602030702030c0f070314071a030601030605040c02011a12100c140408070608070c1101200a060b1305070504 73
    0x4140404000e8620a0203001c2840c40140c03084035442c014164115100c151407160801c03485120300030fa101c024134582c0070340003195251404d90006a48000f21814460901c40c00d91030f140d40d003420030791044da080c0e0b070390b450513001d5a503000c0b03012950f05648500d40100780d0b681e10456659555a44005401180d0110102c5d6900d4400e02c00c50b11003c00c0c9400f12608070a024884540b00c03101844101c5200c42032043d0319840e043c001c02c22104555403180c0b00680141521002100c6a000070065810581c0d103000c04144d03135aa40c442c0c0030464866900000d5501c55039040314810241400e802c03481038205038000e005000340010344540c01891607402050f14402400d050f41c2c0809804420201b6000c0070a01064000d0b001803100100c079104e82e1400d00540f21100291881c0711840005014400700064045040d405104e41d9500e00d515802c004900c08a6040700c02e003000080d44081718000d441c0c5220500c1c61a040802040107007552000b001142045075001d8200d00c075a10402038240314a441c1c00c01d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 257545350 1250 257544100 257544109
    0x4031404050307060e09090c0307090c032d0b0102010e0a020d06061508040318050627130207060614180415060303080f1e0c0913020c010902102a02 65
    0x340202009401c46151640381c0001901e600501e02d0444c2c080c008040000c0d0100c44000340551122002a0103801c1c05070400b07100c10f001c1e000340d40130f0b00c061548906012000807141744103e0061030b10b14610381c51750100f254000b0207481c8c40034071a5045a06041c0340c481c00350f801085484001d075041703c2d030f041da0342c100d450b1801c0034180680c801d50380484003103010000f0b540c201400b1849248030780d54502550a100903501c40c4203000d8055603030042e0080c000c8201e901d4090840703038400101007800700450b00c42d200c001003850201c01041d1060a8006c0f68007010401039002d514050a075003045011422000300100d807840f440f20070f0f503001892203e0082002d101c03540307424a0122420610038807080d81c80b8200580880420381d0705000b80802500065a602620600e0030f40301c0498005044040c0c480c825512034036040080001da0009000000c1d00702900d007440105500c001070000481d058070305004100e8200c21104501c1c050004a0340606507240c0d180500141030200c50394440460040e600205 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 257546600 1250 257545350 257545357
    0xc180405010905090d020703050c042403050706090518130c03050f0313050d15150b0705070302010806060f03040609170a210608060f071106070302042c040314 70
    0x16800524100001c1650041500324501c180c90b10012140c4030202c0300c3c03040766203500c6031001401640242000c4617440c60560089a20050800162072074148196401a6502188da000311002d038420381082018540200886004000440f00180030701c5e000c80c01842c40003401040c402c40f0002da0641c0c070003000f86206d02440035540010440340d0500801140b96540d5104442000c8074001c181d00014151030b040b1250808a5444410440c174030204100c154003420300211081c03101500d85401285c200707500006400c03032341d00581c001d01c8564554000544140c0c005003006002d1001000031410540c040000c403a000b2703500100018116249050003420500703240303400b50464000196002c002a48400429401104424420b0384080c0844248045400c0f03407050400f0760308450b0000c0d081000591a0301d900c188a420000c0e12030304042c8890f804c20300201c4641c80465030100701400040d1000f1096003848860b694448411585045100c1c0c581030002d03c01010449900c180350f440181a1096 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 257547850 1250 257546600 257546647
    0x1110307080409060b030106050d1d100207060506010806060f030a020702060c060604050a2f040e01030305190207060504050910030501020a09031104091703280e0d0c0b0c 75
    0x25aa2a080580340c035110a40c400e10401c06024107140000c2000010442103904880058880c1407601660540e420050603141e84040900142200000c400c24070502c294080700e6110301005030749030340c5031900700c04996014118a0410500e8020000c65440310002c46400701c2c8200150b5461342e58400301c880c0070344501c0b1030003504001c001c0b407516008000014194081e0710125000e00c5203a89120f2448115400c2d844000181d003045011403a414558060010140303581402107458182c45100c0c4440e104001e81c011000180c0c006109090780758284080c2440c121944064010705241010091480c000d0307004082c401d81442c03010540041280150200855110000f03640f506900c20000d8445802c501c800e5401071940030b100d40e0b030741c80c20348140c1c103446a2201018003007644060007408642c0004050482e4084108281c051010040a0700150038035400c0c00816600031074540b40d13091248004946091104898200300018020320f600da038440203426842d80c90350b018001c0d040070003801e0b0b10f2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 257549100 1250 257547850 257547853
    0x171510181e0c020607140906070618080403030f050901051e0702030f01150b0c070605070213050a0507090e0709060503060411030c07020f0904051209040b0405090d02010e070e04110111 81
    0x11001c50208068100d04411141c82d0291255030f5143d9406036042142c081c0740200b0390200300301c40009843c1c003002808482d801000000b402c58003110300c0f05120040101c094170000c80200c4c040003010380c040c5514500203c1441c1c200d08006c0c5220001e8624042c030248246590b40075400e082181c8407440903900300c50740080c1154401c02c0c40c3c0074054002c0400c00b0700011101c4d8568800304145a6075400c803410750340c119000346401442c0c800300b2521600091800c03039019040c41c1c05403580d005103004280c008c00030f4803c00583c5060440010b04407900707682c0300c5038401c8421000c009006800a400104903001c50900582e6070f613811000034010500d8120b51211a030011040c006038298035030140110301c0c42a9608606c0d55070000410403856012280140345a010103c00515802c600024001e000c0002c0d00102d181315819001070141d94007107520344c1c4254030900d440800c41e0307824003e241c0d542d0842e03009001c080d804c081845e0a01c80300144003520507080d040b040000d60341f0506032602c84040c10030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 257550350 1250 257549100 257549141
    0x9040906140412030e0c011b030e120309030712020303120c040b1201080d090b03011e0f140301050a05070c020105090a0801050c070c0918030e03150117151018 70
    0xb0f40441250742c5085003000080c5441190300c9410800983c550a80c94142c694401d404074420b6007000c0401c403039a04808000120300001c400d0344176010204040b2006c80041e5855441d2a02414030340300c00c96010307910140701a104100581c0b004401c407a1485081c0703000b24071a94031120701c90494442da078003100340340a0004038a00c6a58400b50554181d450000c06e480c002c01890b00200c0c0c050a490280100d006420401041140b480802020420503044000c110807942c84c12a250a10520b501c8034090749040c0600c0003561900f8030178140d1101050000700031604254000070302c20524010000c4c107110002031040c4c02d030f580d0050540010400300303000788464a130820305e14280b50030561040300d80007000030b408202a03202e0300561100024040d0707826004412b40c1c5044a0108041e2364880e0940030f1452101245040000040d000c0d06820301c0403c895000b01c405a86480b950682c0301d4401c1c0194410b0000c25000592031004880c00f00303103807845603003414900c44001d1055002002ca81508803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 257551600 1250 257550350 257550353
    0x40201080a0c2106030c05090c121008010f020c010f05090d0c05030909090703021c03050a050f070b0f060f03070b090f061603020c1e01080a02160b0a0911060a05090409061404 77
    0x35040a820b45e840f0b415102d8110f56180203002c100c2d002607802c034500d202d090100b043c98000020b01075510603041c814010340c49655519090071036502080d5140859000580d0100b02c0c282402502d8020212881c100040c0c64112621502c400804400c1810024948141c2c01404810010399070001c800a090492030300b0a24815076607004c1d5884124001c400700c2c1c0301c0d81401c1646800c54441c039505500d0701072810740f0303082040758103034010140c80c248600d00703000f0a80400e241c1d5192038803510500e0581c0d41c00e0b05083e030030411030150030784801e4880d0780044024407000f83c03654255041c0a9040e11415210781410000603424044c810303050041500c0000c5003028035074001501c1d5a130102c20340380703540200e90b95910326000686c50030810f404500d00d41c011541d04540b640c0248003150140c45140c1d201615a070303038504100740a45102102c0c940300c00c801c03010710000813400041550210750b018a0300c1000c900141060040703014840c4225611a41c040c18030149800075110740c1d103044150364503807810307 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 257552850 1250 257551600 257551667
    0xd060506041503050f04081603090b070c18062709020d0501020706050a0b091302041d0a02030c03010b01020d030e030f030a021306081e04080d060b07110306040201080a0c 75
    0x400c0c0b0a10002810840030411210301c0d2000b450040350030001c0e0703501d400c0c0c0c03510116409004c11710086081068658000030301c0d411240c05010b480b4231913001d0004007403038908a800b03411103000f400d90304039207003080400c64040480c0441c044680c0c0034580c0c00c0d0116a04000500401071070300041d400074802104a4200441940200b200b07174822074040105441d07949000c012142d191540d141c2140c8041c0201d200d1102020000141e00c0c402000410040702480395050410744040a4400942c000301c208401c41c50144405598044160006c11551140b440001d41d1104004541014199621001c09603180d091041722085040c402e5504e940b03090100000c4025405148181c0c26080c000d4404107c0a01c5480f8082c05181d00140c0c0540708003e1609a000e03400d001340085402d00360030400c000c000581400f070200203012601426031202c2036810078402c0c8400440107680300e03810503401c100c0141c0e003045e0003a030400a0042d0000c1c80e21015081900e00f8200c0000038440300c2032001c034826004a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 257553956 1106 257552850 257552879
    0x1050609120d090602120f0f0a02010905070b0306040b030a0c05041e0507080612070503060a020c0f01060b0912010203060f040c090b07050106060f08090a080d06050604 74
    0x100000312525180090410b240416081c4400708141a0144040089407200300f2115280003010444510644100f49150000030004944411101c2c0300358410100030380c1c00b0b0200c68403540c80f44e020b40c0c1590811034480344620f0411800742c0281c100441c400700c40c00d61050031648481d040400700009010300517403211888120580d400740009060246a0066442e0307124200d00d41450320600516241e0000c00c001d896000040410858070000361a55000c10380308401a00c4d002c0c0329103118200720107481500d403250708028000c00c600f6030302d17002407869041c1142d902001034045544503090340001c0750034070b9000300c40200080c400e08140c0c0007403409000ea03140000c06962901d1b130b4074040e50041181507400d60354408007880003c0d001a107420354490b01c2c0c100b84e0030b10b20300080700303560314815540000c00c07410021400386100c1015804c11006098000c0c0880d8456868a952025551 = true := by decide +kernel

theorem cover : BRFrame.Cov 257374100 257553956 := by
  have h0 := BRFrame.cov_init 257374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 257374100 ≤ n) (h2 : n < 257553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
