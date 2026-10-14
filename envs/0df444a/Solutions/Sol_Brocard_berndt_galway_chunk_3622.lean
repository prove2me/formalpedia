-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3622
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:46.172681+00:00
-- url     : https://prove2.me/submissions/0f1e068f-2a7f-4c8d-ad20-63e0c079a492

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 651258992 ≤ n < 651438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 651260242 1250 651258992 651259043
    0x19080f0f0414010206070e01200f10050c03090d08062707140705030d1d0f060a0b0402160f060e0a030309110108061e01020a0c060f09090204061b 64
    0x18060300064184028024000095482003082c401040503151200001d03180c2e4000403020340c180041c640a041c01011003599114018228905982c040219042050760b02c400c4880148801802c00001031001020fa0b41a60b01c91034a9200404100c0b11030503040d1005c140c058038580c2c0092900f00c0e0900d603051b0040d04030700448030000b400406417410b0540240940800f5000d0003000c0c000b0407583c000f01d0000016182072104e040c00c0041d503010300c0c084800c51580044090030f032601444244e1036400c040406e00070b100c1c00d148903003800301d1031a17542000228411500d40e2198084c081000001007600c52811441d101d11072180014030014104c0940c1c030341841d100c8110006619040102e081020200461009030400e0038250514141407001500e40b101400e10000031a900c0d2011010f243e100700b02031130742160000f58602c20f568542d24010f00c01e20055841a010400c0c14100081d203000d00e10031136040f0f0714282d850314444800c050f8002c0c5802002ca000707450350641c0b9084d0b44c0a4072014484c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 651261492 1250 651260242 651260257
    0x8180d150e07091d060a1a041e05090f0c03032106031e03250503042903010906080c0a0e0c070204020f1201181109010c030c140c010306080f19080f 65
    0x1000381300c100c0b100d145151000c010300d10103640c1e080907600700800c020614284e50201048030081070000800c540d61109003500035501110768107000c01c0c0b2440c04030104001800c2c001c5081138500d14064481410341da07104114214419000368203914801e40c40c04040107402001c010305880c0141c40b1026842c0f01d6190f2054051142d420000c1c0945200247e035a1488a0260b074100e995518101900c40c03585070700803486441c050170380b80090040001c1001000f6860403188403442600c9503120f12103032006181600800c80749116005803801e4034035000404008480f240c07150710710705a41d44001080c803038208441c100d80041d000c1c441890300100c0c10000d0040f5080c0240361b0368040d8940803918004100070074103030302100e02c1c03c604114941e42d800101da020389004e08061200d01e00a14003140c5102c0c01074005001d5406000b200c01c0c600c0c40220394140f00340c10036a010f000d410389444101d40c5500e91002070446591060b07a2040c812003d1101641d002e90151800c141002c503562042c10072640306c2c09 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 651262742 1250 651261492 651261521
    0x4080a020a05070b0d0c020712030c0507030f0b0105090f06030d11030c010501030605070f051c05071103120106111515030102071b0504061a09040e0106050a0308180d150e0709 77
    0x1a9034645c1c07030300c1c0d00c2048030b04d0f4480d200a00c0c5ca0f615003041d8056242d01484090104110500404140320007048190025540141c016003c07042e50705001c3d61101084c01111321480740c0c540442d80010a0411181c02904000c011300800700d18220141c0b10791205154101190201303200d015814142032103058005c0d8003855020801b817500200041c07503030032468050300900c84240403560f00d90a41d11001c048080c03640000103035688400c01c040c0c0761148000c0c1d04480301d2000051055055902003031840c100c4080d52103280781d0241d1500000d0329003e00240075440d000d8040e0005410401d404d01f1544c180c2d2000c3e00061810720113854904115821200070b8040054401d0204683d040c5403140200409050903000d040c40b1a600c800f5103503204024000b071095891b140702d03403100340302076100c00f0013894010120000c3d15034034a4a1610741e00000c40043d180d841c107039904d00050401102c0c40034126800301d201e80408003054403540c01031040401c0c01c4220300c110303000411500082e1203028074429150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 651263992 1250 651262742 651262747
    0x618150a020c03010b0909060a05060109090c03091a09030921060f0103050705031203070305060a05031605010e0a120219030606170d17060f2205010e180604080a020a05070b 76
    0x18814542550001085c4034096098842009148040130a040b0340200007010302007160744440c4012207001900707410960308180307400e0100e6000c40e0035901c098a4a03129100b900385031390540c040c4d5507080804841440080d041080034210a14140d100d2061000c020510b080c034001c6181c03d80c40c41e044086950300680c40d9210014410b05c4010068000101422001030018000f0f400001d81940800b07044a010300d034450300443c04503500c54007030318080c007000390480341448600c614409101001d0f10035680869140c07200300000703042000d81041500e410000e0355400402a50034480003500c025004451969499000700000b184d40c0640c80c01000034514105090b000c2603541030802e9410601d040a00164046000e0f0522000d0301d4564000e1080b1070104801902c02c010070f003004541e1000c07010840c9280740c1110382d064943d0006040e242401d1100650380c1c2d0300103030520001800c1840003441c3d4402000180000d003240c000304114070561064030990001c0356a86460000b003900070f0b03100310740003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 651265242 1250 651263992 651264013
    0x50c0304030609050a15022104030203070210020606040e15010308070807080f04062703031407050304080607090f081225141c09050d030e03030301030312060f050618150a02 76
    0x30b1842424069846da00440c9884001682c2c00f0301310070901d1009809480d540001002d0500a1007a84c80040d00174110720000d14410400944980d01150054455840c0108426400b680040c2c810300780081c21007041083d03401e64980b0070440c0c001007821100c0360402c001d0300e8009500c041c042c2c198114035030b0400c0e40b114104031010b4000402c400c030948200c0540c81d403101019040d148450112505403c007103c00d01c60b680217030113041c402d001c1301801c0e038400000c1c0000c00c0070740054a00d10525051340c50303540d0a40c4400e00c6101d042000c2c49031403202c0c0d0101da8400000254200207101340b4000400d14007412902a0182080e141c420500307440c000d92010811041807014007611041c5001c04080f600b0302440e01d20040d2816145010709402551509d00c04810507010384683c0400d01001812a502d940c1e507450028540007010b20214200360501c0c0e400110b0b008910a503609035080145050300f0030111070f000021000c08040c3c0541d00003002c0e080d0442c0e025444000b030a8a204507805404103140c0e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 651266492 1250 651265242 651265253
    0x2a020f100504050c040906020d0c020a050c060a080f07052107030509031c110c01051305010608010b010906030e1005270604021804030212030a02180d03050a050c0304030609050a 78
    0x200360548212410403080000049010469001d422000c64000900d0340a0741019002401415000014a40303040c52140c070b501c0d000607402000038030800407511001c04400c00d024881c05a84492404140280c000c290681d04185000b45d02562503c1d140342071002c080c2c040ba08203907210b00141030701005401400a00c5a0502071603900255034401140f8009c0c0344540c00c429652501072110149030385401d45c040602c603d03030880d1007843d8010004e0029050051143d164140da50310211000d6290842c0050448418010100c8011050311590826407505000ba4041c00542c03650a401e03006142143c5000d041c43d11a41c0c0c00b03041d8a19800da404003100200d13801800b0f40c7c80b50806160720410403c80181e84000c8010071601034603000c18981e84652074140d1801b9082c10100d016910b001c0208450361905501030100c414010b00704100c050300c44014020000b80c8107c015002a000700001d03051640501c0041c5000c44200003102c1c0f90079542d8a458040300c0314108216008d41100f80d00b6410f100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 651267742 1250 651266492 651266503
    0xc02010f050c0a2d1e0201110102030a050613140408070221030301080d090e072a0f020a060e1f020f010603050312010509101203030e01050f040b010f0605030a2a020f 73
    0x5044d00760054120a0726100c40126186945810311420508070100d0110b9215006180f0144840740096482e4140300d582400507190403910301e4056075065a10110018080c010300368694103404000b034103034890f611481d806030310804050740c10448802c509441f840507402001568281400070310344035410241c01c18105070f1612090001c02c541d401e401d00c1608410f6001a40010044c100360080030110355601610024075440c0c0c142c0000501d12100502c050171110051452007140c52440d4191150001e80f030855840700c072190410f88046c80e003203607004000c03d0100d19104030300465104003900f08000382914042d030170484540e00041040b85485900b09400c902410003112044040c0c0f4281c611055800c099125003045070313064030098024140290f110464501c0000001d0000e0300c0d00884e540100482130318201c1e142201c0c03000001d40c02402500d46c1c0e090350303a40ea480314999140c12000c0c0020344104a0103427500d00e4503454040900003600d2892110100d5a0050704403507005168a03410310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 651268992 1250 651267742 651267803
    0xe06190905011116051c0507030305180402040819020637030b0303030705070204060317071103070b090105250b0114040606140c010f020d0b091302010c02010f050c0a 73
    0x40c0c0c4840c1c0044d08101440719140240c0c0c00589100b060280d009140701000f031002c035030142c0a40101d490200c2415400381c010413041075441e40b00240a10848148001c901c01c40c0729030500c03508030020031003030100c0764020030a0907030006041d1400c00c1c1443c11000b81c0c1403031800005100c180000d0742d58000031030343c1b00705d008400d0041c1803c201111100340840e446c0d11008003500100304001418100b15500c56000324091508041d00d1004a00303445420303040ba40c0608000d50310380000b03610100c000d160020344170303003a29000e044d09420000e000005403080c0c0c00c18000c1e0746103091801010048004510521074405000e141d0400203075140425020015003d061514021030801509005c80c6802c501c1ea282e60009404040d561044d400b0541c030b0060001611603180e0a00008828507240190307004070916440c03c668001440c1c6071031406000c41c11081000034080380b1484211005980240c00b0b9550400840c02d0071031400e0703e0b40c0c8545090103c002030880b5141100c44000060b6030b03210b0302c0e41851 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 651270242 1250 651268992 651269027
    0xc03140603032803110310260706210f0c110c0105120403022d010b040b1e01051207030c0f0503090a140c060f0909130b070e0619090501 60
    0x1001d20b95030000c4040d4a0300c0e043c9442e07403803840800c044520b21907406103141d80300141142d5142c0c00d01080101001c06d182c810700100b900007008581180080403802400114208000e08915141100554089030485280b10500c0c82d00380c00d447c0000c041d402810a101900940040c40208000c805040507103d050818540e500c41204040180d030800110f556000000719860416650b519049280258120040c00d090b81150b0800e268165038030084c8c04d13010400303002807110b400900203100854004010041d4013076000980280400184c4101983c84c1c441850010714042038020385d03108401080d01d1200010381d640010324201c40d4410f654801040c12480d02c14510300f06840190742e10180c0301e402030402618000450f28007801003042c0000c0c1d40340546295180c03162410394a0382d54111a2616000d00809000140c3e01c01080c8a80403880d54060828aa40d4032100d10885070500386505498100b401000311070042d40c1e0020b84031070302140c0c564462080d2810100010400c18805058008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 651271492 1250 651270242 651270247
    0x602030a140709030219090e070810110708070c21060c03090203060619050a180609020a09060302030405030405060f0705070602010e0a0f15050c030f0114090109021c0c0314060303 79
    0x462540c0860307050101c9404840f0310f0a07016411181c59400c1b41c0039072010721602c1c5080182250f404001c40c02c6801c490040050f1b0b0000c4140c941078100380d9603c070010090600c010030000340014092009400752500072203009007415202d19200342c14201004000c0c42c02c1c03062034035a02c10054680224203807000b040c80e05120803417140d8046540d070238021f850644140c031014030102c4010001c040d03040040c100200081c0c81a44c2c0c4816500700118056803411000d4140034012034800d100e4000ca0303a8800c07095035481c44407454090203c2c0250009841210307a8041080b0000d182d6407000040d001c8040002403443d034401540c42c1c00c524001d0749510038000c0d039050402240340c001000c80c08904031130300400307800303c01c07025854503281030b0115030143c00000b45003c0a0007540d022410103148149580d02d4455400e0340c032500205180300b0749130111644154000300510202400b074015040803a03842e4002c40803503201684c040180c850740c07008031000964441c041d080e42000041c29681020b42500030390f1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 651272742 1250 651271492 651271501
    0xc020a0f14010e0d050904060e070e0603091002042601060303200f0a0506040209090a1709132d0213030b0603190c0e011d16020307050a0602030a14 65
    0xd540002103015214420040a0711004242904445000080345050304c0754281d440102502c150001c00c3c0f1035004a03d0040041030300300306003200034041e812944440ca42c42019104000d11940002d01c101242e000b4000320000c041442c0c0081c00250000b140e081c4050640b0f03c8a021801010fa4000c41030341c1e0620b642003012a4000340302d0300b24495210f000814400308181e54519141c200b60f02003040d8450a4121070512801281c294040c5200312040c3c200ca44841c504141e4842000c0c1002c2c0190750800c0300c43d81031000340c900608421002030b00d04c481c1580c80c5000d2908031140302000780c2240c08603000d1000740e02d5013640e80c500710141c24141141440350b400d4003202a12200d00000742400e81c0a0041020361b6400c001c00a030740e001158010aa0440394505600150781505c100024040b8020004c60111a510034561340b81d030907401c1078031455441c4c42c090505035029100c02d40c20343c0800c100000200d0404d010000c0444c0c092140540e0382d09112320b000e01141d56002003540c16090342c90070700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 651273992 1250 651272742 651272753
    0x807031712010636031e11010e010c0b19060911040302060d180606140907050a0305061903030914040c050711041107030e120606150f041502060103060c020a 69
    0x50549a243c5040c20300e040304c0b840c0001c0308800c060300a101406031200e00600c15528441d1043c10350303200392280308510348944003115203080000b600502c035480700141400725510404991403006030500d031528001c0901e48403091340c100159031042c261501000810b00329800ca001d103070001c021464040012143c1e00b0704402d01d034001c81c00006d11070440002c2d48007a91026801410862414484c82a4440389a00d0008020149446100800c034015925581940350030244e0724030403000e80e25060700d003801900084008200080c4520b901034032021444440c01000302441d00514803a886100000c2c2c01c00c0c201c110810700c024080341c0324900b4038070840c4546512900391240e01d54046424851210a280000d0141c400030000341c4440802089510a040e4080641c070007403181074400c0030340e1114445d070468403854103d0f03250390030507004101450011130000c0102852041442054109a11007a44034960700b0714807140c000503480300c00180300340b100922416070540154001051400d5450359103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 651275242 1250 651273992 651274027
    0x3051501140f0705030c030c1b012d02010f020a090807140d0b100b07030e01080f090601121104050108010915090314181009180902030303060402030c1308070317 71
    0x42e14400c80c03010900320704100b010000d0791900d6900c107041d071762030b804030502695031110031948004a20012001e168929400b0b6000e0f41c0342414020710070320503500c81002d110800040300501e80d04641d80d03410b030f030740619010b0f2014118000b100c0e55034407066880c0010851604a864100d4540132095103040240c1b503441d000440e020b00e0380314032169047c3e510140c02c0d840700c07c07155002d080c40b40000241c000030940d014800002024090301c0b0301c2440e807038980c255a00ca8204890280082e8401e8006014a08000c0c0c95003540320300c02c80550000007403100229080d0742003a84040042da458002d01000c1100c100d04822a60460301800c101c00d55146d240102400c40030183c0c44500c46002070366684d0702d0500441c40316003840103401120044038116000307004844910a1944160010130b0194091030b40e40103040100d90018011402d41e103881d02000001d600150420072189d100b000640d80605440591f40300800324400902403107031a505041803002403d100481200030100310301c400d4421211030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 651276492 1250 651275242 651275257
    0xf3105161b020904020a0f031a070f44041a1003110609041a0102010510030309031709030a0302070905060a0e0f1b0c0616231303120305150114 63
    0x100c10000b501c0d80d00214a00580c00d400918914180c0b01c00423060101d42e2003080701c4042c01d01c42c005100e03a15854111001a6880c01101c006a00e50142010158001c020049950305582801481c0412030b80c4010803480c500c2852120380c00504100800e201c0c48000c00c41c0260034581050545103410101c0350301c030b14028080205101d505c0c05001613607407100c0c02580c5098070054420004c228205016840b01e024048102d4015800d000016110035840b80c0b4003c2243e9046d100c00d03041134111764511030000480d810360a100e1006024052181d5410041c5424241c001c2d005003840d141044440d50035240c00800c198000c2d060030b4800c00c05610010141c030b074449042800401c080d214180ea100c0c1d109240d41c1000d48500004ca1145490307040419001d010b00d1100100e06080c05004205641c40c140c006498481e0004120318042503040840017480d1b10950440c5140201c0e80b00d548030f251445c0d0010700700000a40d01e80402c8086440c241e28201703000c0702400c1200d11319200b440d80010500c203900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 651277742 1250 651276492 651276499
    0x901050604031a09070e040b0a0b011b0809030a0206130602120432060a0201140109141305120414130b0604090c020c100c0b070302090f3105161b02 65
    0x30010b031000c6030600c0100c5c0500524413121399282054108401514001e4130b540c038000780382110302e02c80b82d8040c1904030312801d40c0401506078004e250700c9881c903030340180e000f0503050f000d0080360b000160f4030344008000c4420032480c4e1098a44c1042002880c01c4004043c201c2522801c000501060004100c1c5684001894450b40b40d0364104410100128600c4c06440e0381007440840c03408840c41d010340020801c2d140d540d42484483e079036610040261000103409a14030440d84010820001d034030111585560b014000b11101400d0101300000b544c2c0c8603078402140d000340300703004441c64507000b9200f00d003c1e000d0400501800c60744c200011600d110f248183ea094980d1510442c110b41d00a0021044503040140070300c040207060000540540f05020040302c4e040910000241c100d40684282d89501c0000362a1001544002c0d0a0020880020030034a030380b0803401e0701c5407021003403034002034100408a40d4045030508103c008030796002200c4001005001c02ca0909009070034802e140e06240d540c044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 651278992 1250 651277742 651277793
    0x2040e1015140d0b1f0b0d02091f021002090f030a060f1107031d0a23010e060a0203030a0b040e0d020d0210090203150702030903070311090105060403 66
    0x8255519250340006884121424410440040c5100c03036451030841e10400c5901d0000080001008090544010300a1481403024081039402ca2980314005480c02c400828955440d2140400300c0701e500722003605100b054000441180d2030070301d641c40c08880307001e4800504c4402024a400383d2940300448503540d540342c1c0425402e500d81e450f68130122400c82c000c1d09982d100c0d0a9401c4c1440541451901070382e01c1810008452040e004010860307106640565600800d070240c58000100e0040c3d50304c210b540003010700008541c1f20101c0c60400890b0403a02d800c40404039070078002400c10941c21b504c8034400c440c02d11151000380e402004a83c1c3c40408500300040f42c2100d800040c00a00b117040b200c0d00d4501c14841c40306001a000140450b107050b01c2c2d0229607010342e510f000300080d0703440340d1802901038200c1d00503000030441941d40d55030000200c0c010f89081045d00c1004c24500061540b042c2ca40300040024031100c4c1c105000614050002035940703070314180c1540c4550148a110362031244020a06 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 651280242 1250 651278992 651279011
    0x1b15021b0102070b0f030108010b0901050a03061109060a030b030c09071709010f181b0302060405040209130e2b141b1911010306050102100b04060e0f040b010803160204 74
    0xf0300c692805010f04003041c503110240c400015500c1d030024080ca0603198a0090780e040146000b030105812514000d0010790310740d0070340c1d40b801c01030320000000d1680c52206100869460780c885028181540280e6800034112861408041ca001d04201c0f41d5030040d4807490520194a40c000c0701c5080c0c0c450042040324540d190800110f0040c080040c8190300355141407042c041000d015104c179000c45014010200d0003001c94040b0b8010b04034180f00003588400108020005420240c000d011352040040182c68410f284580c4141614000503c00d40245c000762180750745500b082c0c2130709101d080d1058828100d40d0040c840901a440c450341584803100001c10541650240c0e80d1401e4050300d2418265082c0c01138040c80c00d0f078850302c180c108880c60f5140d16050819548248556405c694050b0300a0101c03003d003519a0300101001c0749d0301504107840358400304128002058030341c020280f2140c40e090398640740c20701d1040844181c2196403150001c0001a0401100040c0741842d281c040b1800102c000342e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 651281492 1250 651280242 651280247
    0x10e04110a03091a150306100501081504180501061d0f2a040b070c0806040b0402120109050a080702030c010c0503071b090c0f020f12030c09030304050d1b15021b01 72
    0x106181c1d080e03014041420001140d005c107244425041d016001c88006841d01102c4241040140c041c2500080e8020002400030b070b80100003940301c1c00c025200151840000d0000d0000411445c820b4031144c1d1070341420005401d010034030a20000309180341c01d2050416907500f404001016140c50880400c400385072008140220610500000b0051010303983c5d84d80300c5d200112a000300e1015519180c2c04500041d41900c04607583d0f10980d4040ca850f2500c0d40c5a80c20410600e00415115103079640e100301c0300c40000e0003040200c3e44240103500043c2c40d2011881010b02c2c0c06010407005040003c001074500002c5d00000c240c812a0303074031aa44e01d121302820900c21118200030350047c2c9000b424000c04209150300250b00b41c9004049a0a5400e09030844400c140c2d5802000c2501042c00800c1000610110801740030300300100c0001d098070300c1c1c29075a02c00a03504400380801556041c8041384c0c10045502c2c0c680460001b84500c01c88e803400001e542a011b525440400220320041c8000306008142d6803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 651282742 1250 651281492 651281513
    0x2011104080a08181e0306070504050d060f140117070510271d100f0605070809180f041502090f0402090a030204050c121b22033306140d030306120809010e04110a0309 73
    0x100b11030300300a59030392400b10181850000d003944700e0318010b0007000b0410b401d1580e84c8101c0148551601246400708000a003c840f024a10301d15008a90307480108800444031442110a1080da1507810300c0d05200f076034828101140d0b4446440d152913081c00b00700450b008070641d42a103800a04003921180c010010511002c03240c100511103003001400c001c409841e110440f4012402400348014071700c8901d13a2601284907041060b54031013842646125507140c103400424445901401220800350349a0125040d50015a00040c5210000c03901548481e03840d041154841c0c009a5078840d0401004d8600c076092041149030814020404240e5080d5100d1000c081c00440d0702000c1036045e20744800008800111311082e14100700380b90340c140c07803030050030f80215402d442000407541070703114010003041000b059405c002c405054440d00006941520b80000d542c3e07640c050905a50381d040024001800310723006440c241d11851a0284081c0a0441e40090742c141c4c2c0d03810709000400d0500b506105500a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 651283992 1250 651282742 651282761
    0x80c030304051818030703080711010c0207050607080f030f010618060f03020309010209030a060507090e09070506071707050a030305130c0b0a03022802011104080a08181e0306070504050d060f 84
    0x284030010b1290f01f0158002c0c000d500c02d102030750b600304201c030000f06d405080e038602d00031030030050340218030521030351030508010b144451240c0207541c90150710507001070407500308070b440f0b809400350b5600410002d5040030031420104840400c142ca100d080c200060300ba01d032800c004004241c1d020000681e0400f0941c101c480010f4010101c0c0d00e0001140341050141000b02c94802c002a081c05002402030840d00385203000d660404080c08416080c5014040a50030168081e5220800c0b8402240c00c00c400400a1407080d008401400801c82d003428040c003600c40181010000d0254041d425003c00c08401c02e000c180e07124465141e0f40c0e50540c0754100d001e0700030744058080e8074460401d16410500000300e442c015030074a030000e01444906820f441900d00692050000b19004101400001200103006200c2080c0c5c19400c650712900c000c0129408444180e81a40c200001819075171040c5010080d20f6030040701c51400500d050b0410012812650050a00420107515400d09004011041e00b000c1c140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 651285242 1250 651283992 651284041
    0xc03030a14090d1407031b030b160201090f050a1a1614210609060301110f221203020f0d0e0f03010603020405090304141801050d0309031506080c0303040518 69
    0x403c1e04d50a41645072580d40c0700449485c20010b440710764980d410400e90044a1b004902140d25964914090641c802c66200100865684111403000141c20941d0001d20f103002e54010801c07201d00346011150741668a04003090b160007101044420b0309a00d011003840e499514041482444400c0c00c140d10303009000c0d08220010702030181840c0006a00c41c051700c1540c08503501082e64585000b49801c0310087d40341e0030441e4a0401503001c440340040010700c1860104101e007040100c002c55072401a0105410002c580200c0440036414943e041140c42c0050054a0241220140b5400c010348200700c1412441d0090300c6134046040c603654294820002186c02400511040ca071004081d516a80325000b641e00c5082c10050311644c60500000070a03803071060b0034003007a5076400c00c001c0042c4000c103200d081b41042403000021002841d03602e60000c190006042c00705102e810001c1490400c8400404140654010300003081030f561030000568a071300840c941c2c1c080319281c00d84040e8a880080d01a00072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 651286492 1250 651285242 651285263
    0x1a28090801060611010b060306030a030c21050903060610020309040f020c03040b0405091003021804142b0507052509090302030a3507030e07170c03030a14090d 70
    0x3c0858009800724698010030000b00081d007085420820389010540e06c5a81503400259400e0010340114440b4626a001e000c008c4240b41780320500703c81e05c10480c000c0400082e004900e54019040810403e078201108541c01d0140301c02d8031600a40d24090292824807554980c043c501c0031108550407580e01c004c007001529515030b100c4541c0310700c80d4042d219960040c0840000690f0045051070710740c0a8030740c01800c8440140c1081c0a10f2465900644195000410502d001e203808104001d5440500360740d25403104100c80c400080c0d94180c81103000c01d018044104120030010340080b078201403001002601c408101090051a2001e5480741c110a017800c2c80c06d4010418141c00002800400489a685510b803401b100d4900e001e00484845401802d00e8920032030031107841c0d0200c07480d8800020320340000c0f040c0c200f00c1c9041c5044040e0784210b2a603324804800711180082c0704070006075109070021880c110701d000f001819480920b20303192840b0381c04503201d0166078900d100d4412003034003c050200d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 651287742 1250 651286492 651286499
    0x71d1501050307270f08150a02071403070f2003100207060905030d0f0f020c030a120213140a0806092e061401090f060f050313050706091a2809080106 66
    0x786900560b010300d40510400e5040000c18900c000380c480c0d41903003200c0d030500c7c0d01d0720340e4548440a508110310454440701e080070945072021042000e81a071038003034224145040c486080c45800801040c05406001c116042c2c00c84498400040d082402d01e090b0200607038422150510800400842e035000f0018080003882d2034441180b5004003140d40e40b90b10040200b8969918144100d2045c01030500040d002489140b650034011560b415a84941c104007518002c11503a03400c000080c1c0d6041503010481440500c0c40714200407d228001c1e0110400606950800c120f066030384600041c9604104009036103808105180c400c1c40b0101592030341001e03c015500c880346091030fa2a40075507280001c0729444001600158100f8900840b80643c032140201c1c4e01c00c120454569000501d140038110000d01d09200142c03003002080010040760b0340e40c11010307081c40c964070a900650005266914002c3c45009001c510b0080741c684800d0810400680c0d08001c2030003030740d20000550003d90303154a442c2000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 651288992 1250 651287742 651287807
    0xa170a0b0106050d0513020a0e0a110a030603030311071a04030509060f0301140907080a0b0103020708040801060f170d0f20010617010510051011010905071d1501050307 74
    0x300000c1205401c241726903602c03c3e184010000c09204003a6002c1c1d02c000b81000b200c030380c040c46190045903461020854040b0000c4041142d408401c00800080c0d54100070011315034540b1030381c0d03007002d000000e5900e005026190002c40c0100741001554010103070300440c0801d8044d00c02c6400102014102e0b54985152840d0600207420905c1031180a940700c0c1c0ea10f20342440d210840d81c3c820a5180c41d91144c03600c0710101c1000400f241d041250600d0740c208609800328410700060002030941e10008160581480e070030065008607035004800e55040c40590140700c54000c80c07680c1801e080c8ac5482d9590600d9000110f60880084081c000001b008481600000c0d0042d0021001d40f40c101d1080304480d50b090940500301c03907045550b150b2070107101e00709200d01d2400c909102d2041c03446140445207081103660f03090071500624030440d0f490f371008204114100030b4000703824807070300b18681244003403400d5400112041001520755042010000009940501880094000e4004250003140d00c90030708020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 651290242 1250 651288992 651288997
    0x1053d08061f08150a030b040b0106110f030d020d0f0504120e0303090303180d0c06030507081302010e0f061303080c060c07020d151b020d110c0a170a0b010605 70
    0x48501a212111a19500c0b480315207200c078040c000380d0340d0741e42c6940c1d0b9080000710522042d415294040035031000000405c60105c10340d03010314040c81080c0780d19494144c018045400c0301c1000161604001e41007548a400823040d90ad001002c1d580140e51426012580c0d00240140c3c00d0480e00a8644020f1106000c00c1c4c000300360b03110f41940c664000d000589810107980b4090040150b40c594001c000748600e000c04e0404405000e07001601d19403180185644000200115411a6000176a20402c11660030743c0074041c00d40003540f0003c4504440038540000f4408010038040c1801049030000f01032150300c03010121141035540c04580704040b0340360f1a0079001f0307510080076000c447c41003402003402c40031954115070704507034002d04405810031540d0b5000c190f00703080c2c0000314032140d80300d401c1d0000c0490307031031481080c1c0c030564042d107540f0044000c0540301c803a0401d151182c44d404007071320701801c0c4c41780c24050003502c1c000c4d40403c0c0380c11000100a4036081c0e45200c001d110f80940350000900f43d811102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 651291492 1250 651290242 651290251
    0x507020109060201200d1404050a0c0f0501080411010c141005061e091302031c0f0903050c0d1e0602040609080616030504030e0904140708010501053d08 67
    0x955401556480b801203007a00d440c41038000c009507800340c9605540c3c0c002c40050401c076041c5c40010512681d05900018596021102514660490403208003001403501d0140040c00844400e041054103110000309140f000420007010048a040c000009030301a591008905a0084500c440e440884510907182c4408901060381d05007008040b40491070401034444000c405400712194000c030020070000746000161522000e80d0010030503d0240e00c090003030003440004095448010041c039400203000b01f02c80480da904101c1040c005100003000410741c02c032500360448215814004034240311b0044055101c8110802d0103140441003001f4054020344101c66030390700c8201c0b050350354640240d00c4500c11242c42d140d41c150351200108881c000d9000035041400303460300c100802054004504c000340700399815998945420850304141c0320400c00c0501409140009100d1545894003040f005010403190180310202c0d00309100000c40960440c0351b01c081d07060310424414032040e00c050203400c2c0555 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 651292742 1250 651291492 651291497
    0x122b0606090801050105031c0c0614040b160206060f01090504020417120c03270d05060105030c01050403170a0201020f030114010f030216061e0f020d05090d05070f05030f070305070201 81
    0x5000050b4100d0600c5024101c0b00040c0107031020f079845008002018504030f0800090007810700340343e00810304901ca400000d56503071a20150b103041c1420018000440100200a0614501c00700c1000a5000c180745411540c140d81403440030400b080141c404580c1e5400040d0070910110f00002c5041d00c032403132034200112201c16580f0b080d5109481103414171801d801d207903a0f5442004195002c00b10b100b004c90308030101c0380c2001c0d01021020002000086051820740380c55101c040144218034060120608029090a141d450701c1e18540da00800d089191954441084d80407036081c51050003901100d02c4051600d4440780d40b5070311541c00f001d4003030504002500060300440f60540d030700d01a1003111071071150120141801d4010703944100240802491103200f401141038800501d54aa0003001b5507000c110f9005070300d07500c40320054000c68030000c14031145540950b03108202c2035003250845044940101c2986000d1050b0705140d4910310521010f0000b8001c00501801810360000190501c3c0e8803d9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 651293992 1250 651292742 651292757
    0x14010e03030f01120209010b0f07290a06150806181303080903040308120a1407050a0e0609060f0d060806040305070302061602101a030111070221122b0606 68
    0x3418101000d43c5101c41c006c0d0000c0d400f40060042c0d91500f0040c5c6070402440c9141450038040c3e966016915148880303c5528052112051030b031207000e180c50f80c4d800810310b4002c2118038035100e0a61030000d4001515414405080c000c10303010b440d030301515403441410306035520542c18400c903401420448820150001421240451151100801241e003101c0c1c018000604140d00c120410260b00c1001d040c003181c00d9a03c115050240d00d8041244d8843c041c075403181c40e00ca40070b420300a0184620300b04050310401d010007200d101c9940e48000d5071450840360001580f201d807080380f41001080e098001401d18401c407070070401015801402080054400d0703003a5822a140d00040018144e903448003500507030001041c82d500038004d6031000022000816400100c00031080120b4212070307000701c06060455001a220003942425039002c0d0f48c501d100c0d0703a040f41008203821950340320507500a110f60f45e48d000140c0f0303c50f1301e01461402550b036440450b1510342191b005003020020403c0d445124081f80c5030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 651295242 1250 651293992 651293999
    0xd020a12051e070c0807030822050c01021902090a1104080a1110031b111f05061005030702030d050408040305031801020601090b06070f03090e01080f1b01170414010e03030f01 77
    0x2041113507100344c2d20044290610126940075515040010103400728619030143c031401c1000d50480107581640900b01030091042c1920009041901450120650101003981480140c0b5184415503100340400030008020443c0750b098042c1b840f480c0d1000c95103100d00721b078080510103010f000b042d05600c2150001e030185079a070000d50582c0c6c0e0707116100c3c0d031758030302400184041c0e805a0410031015540340c0940381092191016a20f4207a5800085071007181c0e104200708140c01c0c640c10480703500c00903051040c1140f81000c07009540340304440c0c000e120035886101040401c010042510051640710741502d8030fa41d0680321000c5c16002c4080914018070601d400007861482c02c1c814119000400b80543e0f00d0040306461b115004407000c60100c0070003110b00c80c0011840d50b180c2e0014080c03c9603001408c0714281072480789107419480700c11a0001c0d0604c0320580e41e01da0304405a00c43c04c485000300c41c20240d88038109140c50200d8035469910700d50814000788801d240120040d4412000040e0104050341c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 651296492 1250 651295242 651295247
    0x15031b0816080c0d271b080a171e031518060604030b1e090601090c08061f090305190507150f1d0a0b07030e03060c0d020a12051e07 58
    0x5942c41d000d500020020204e1249054000e4241400020f200078a8541002c0905004501281c02681e0150020340400800540c0d41c44a0005040c000300801e0450203039111861030340d044008100181b1400140f4260060011529049004030300141c162a4600071422181003a4910f0f0040d00c169500b01d407881c200800201000c0c007901020340751504082c25a82c91418141011b00500b981103080b81d48282a8150104d0032442400320380050300c40d44d450025150f0030785000c2c04110301401100e4041002c180c6528000680d588002440039042425450080d0341d5100d2540000d0514054520b81280d04814840c4040040744940120742d226551350f07415000581140243e480080c1c4220f01c1442c0c040c1c498509070602400300380610204e20320003800112000c040c0e0703001031040a000f05508081c1a080301e03100c1c0c43c0c6602079015100a1409141c40c03040c0d40300394448101080e50104400111511803006080c00781807550040007075080c60340d85529109140c80d4000c1c5010001d0000400c002e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 651297742 1250 651296492 651296507
    0x403090815070f0c050712020f10020109051504030806010507140f060915010e13080408070801091203091211160f05091e0105091b16050f0c0a15031b0816 68
    0x5400174050101c0030b09103440c030040c031180f00c0b0043e64400044c1806803040e5440c11b100f40e40741005900000381c00c002e0b070b15240e0b0074a0a0f929200c81c030320404030f04006c04a034200380031650198091038103661328402450b000d003581ba148003420b54548210381081d01e1061001a0b03c40c010030300101250035040802040b0b00c00da8109003d100703845440000403500c6444100c1503401814400c90711141070a071994121803034018142d00c0f00100742e442d8020309042c080c90000030a2004024a001c0c82042c0f2140c403201d0340800d00140303c0080080c0104443c955800c184072190324495030702c0301c81210035500c05001e42c200607140a000c1c07007081c02d040400c1c0d9540191140038262041d4160500d0260b29250800408000040601503850a40c41c81c00001c400342c02c0c024041400c081c000145042e409040c00c038a0489802120b04840c0d01c0070109041c9075079219140c1e8101d8011565064000c01b5001c0300700d01401d1030710410310208034140344c0b00311441c1c3c002016a2243c600ca4440c22400458801c023101d074403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 651298992 1250 651297742 651297767
    0xc021302121504021c0b040905030f0a03060b0903060f06010521090706020705030d030207050a17070c0902091324060801150513030f020117010f09060e06010e090403090815070f 78
    0x17401201040400f40700580c100383c48042000b84005145031242d1201400d55100d040941516a400203d482480740c05110b010b0103840d103240014281102600483d0f6120005400891200945000030311180c0c80f0b02d04680114510901b1040f0f0001a01d071000c001031015078010419001700400420340e00c1c0300160340300882ea00200108034141c0341250a800070b500400094a1901900482c1340200742c041000b81034410f95000c40666800031401c20120a6039590440c003d118010010020641e58900b840c210b80760720710750300084219600c4030030701041d40d5885407000082c500c01c000080d405d810260a50480300e88d5a206440c090310300034211400d04c138071414000030180d60002800072401c0c50340c04008291060500b903880d150300b15100c0030030039002d900440b0310709007100782840545264010600105200300c1000120300b04400080c041d050301c2a410342c002c1045000150a00d0b00c12071040d402014014180c484c0503100da8500801038600f110030b034000c5803031000340407940c5201d400c0a2044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 651300242 1250 651298992 651299017
    0x2091f02011d01090c270c120c11031b4602011b150504080d0c091409100e0c0702040608030310170c04021204030305060109030b070c02130212150402 66
    0x1003500b0000c82c1b82c10080c070388050040310314400b80301840d8003819115818010035962035504600c0e124107445003d981c111032402c010441e02c000d0524000d14004283c0d1a1601c54031584c0c9841c811030301c01d40f840c00d202001c002c88090043e40c00001c2c590a800c4030042c0c04240400c025807031400c0705008181c5020410f000900285040082d541c011204c1c07104141d03850b1281059041d10500e10910101359001614180c807124800510f002e44041c01d4461000740003880c1c1002c0200c079150040748010041e21089075400740b00c0c3c020000740000032001c07a002c0500319103072500ca25414280c841403441e0b0441d50049000d281350a2004c12030b01d10000507030380315442c0c900c0c000002e6800c0c410070341c84410140c0d0756207100b40303d18800003d1316a02c03030025018a18850302802c0c03003860709003401011303210042c0c9014140114407100b03001080c504030286034030100b1801c0014010799180b000c40e08440c42002a11220b9101183d0241c0801e0080b0f0201c2c002c4442881c88005c6081c0007040100320f02c0b8000300c0110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 651301492 1250 651300242 651300263
    0x30715090606052e170709061d0108060d05030c030703182102010e0f0303040618090e0703031d0a0b070201020d0302180906030a0b0f0a050a180602091f02011d0109 72
    0x4c0140349004080101c40c00703840e1201e082554040c0c4408400350a8500f603000c24100d09080c071040390b00c25007800024812058003030442074007000213003000310b000d0070040c02450684245401e1103820401c4484c0b140e03840e011265030700081d080c02131266525403030354400020400c100245484100c444110542040582c50005100b81c0d801521b0802e4103102e0250869480c05800c1e219030707014070203030004100d2501c1e0705243c1d60400080e04450350300741e08512070340c610748158500301140008941c41501c1d45400e00ba210b1a000f000780f52840d0440b101d00c958002e00e80140132a10300d42d500054103402e031003a003c50b084910807400030380c164042c1d140002c1d0047d4608882d031141e07140042200e070304804c001d81603a1a500d440d8441074001942103941492000007841408889072141c4162130380120841c0d42000305007050300049401a210800c044c0c003850700451850030654030010340400c85610240d44d1151035864200180c0a0300c903080703c0d890fa0040c41000d81007455010700401c41c1d03ea40c00303526401c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 651302742 1250 651301492 651301549
    0x20d05030f070c0c0305070902091c030504060c0c09050106030c0206060901030b0a09081e0a02060108030f04060f0e10020c240301121e060504290114010203071509060605 75
    0x3c0c0e0316005458183d9415041c00c10000100d44d0501c80e0780d01414409101503611300c41e5000f8444800b10800f03000181141c140b084c100425131050076181514034a1511105880300c60500d1a460501078104c1650945420000505281c0613481580031019980a850182e41e46804000c400d400910018100c0341c60040000e0004505a0000b07c01d188200092828003440c03541c030643c030310052955000c1c908800078540d80d940d501045001d00418100300207500d07103950300081e003146010342e200e0b0206000d80c2c10a1408000d005031908014900080d182101084030007000a550f0041c0c400c9160003011203071900c089900d40514109881601c10054915591801ca2120b6002c141504251801d0498088039900351141c94650b6070058001c40740860b003070405040114130820f00001050a00341d410342a15a240f140c400060304603100c8440800090003d000140d065209100c0c00600100c0286400c0c408040190f11070005c0c9401010200405520b800c10b05c42241141d250982000d9000c50124 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 651303992 1250 651302742 651302747
    0xd120209030f060a06051903051f090f06090c0609030507030213090206070b060114030f16110a06020c0d03020403081602010c06050c0705010b091026070b0a020d05030f07 75
    0x400c0c00a00c05800c980c0c0010908100c10b040400580e05000c5981d21003d00b0011031410002c2203443c3d40c51000350304039480c61603681555603403201c00c02e414007585400a0b078000807031382d0740456000c94002c2c00e000000320f402d1074503c0040c0b038500e1044600e084480004908248900009010740754003c004198181c02c5400f040382c4c2c0844030310144545500c07a0300000c0140c40340300180841c075100305024441400c0420000d00800344007100544002c2c0240104040c032505102c400e070300111208216203140c5130385a0112007400304081400100e108a040c14800c210850707000300081d0300410103640d0f5841074604224141e200300c3c070000e404a4424040c000d050024413802c4d400c980d205040c040c2c0c54032070a40c1c03620b06585040380d051015030341c080342001c1400300c280529030f032404044620a1141c9094158494801903034010300f030641102003a0804040c003842820b40040c0d040c42e08860005648141c4240e266000b400590018003030030010201301350203081503d0050480842380c620565518004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 651305242 1250 651303992 651303997
    0x14010b01171504090c060e0603040f110f120307060501080706020a0b0901020c0a0c030203300a1107080703140706020606041a1009050114120705070203101416020d1202 74
    0x10b034507020415526071100d50362070b4450075100520030b5091841c3c0c10f01d00f43c070103071507110420102806224200104400176111600c4002c4a90b407204485070442007400c00305c1c80100150001a400c080021071000300c010700000a0103030709100301001d02c804c0e80ca80d9101e41c0c94541e148506401760380701082441c0040d00c0f40703070318980c8002c2803800103041480480d0b0b218030700351580d03030140c80a810018050080d400c0900002920004000ca503c4010120f00c4200301502d0301c8c44000c58000001140c610481842a84e07000807403030745802221800b03a100c55410303445080c0740c801100c0115119441681502c4003182007411149281c0243c4202e80e901310900002e40000100c0380002c55980081d05282c0e510f06c0c440c80c81c00d08207541d0300c080103070402001404940074800c01d200e00c01e0040c4a8030824050381745059500c640c2a00c1c00c951030305241d00c0440d18003681c0b01241000c0300e0910503048000e4410074030301807040c180103c0d881d140200c080e10580e141d0f1007160303008002600703451070302009100d40d400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 651306492 1250 651305242 651305251
    0x306090e01110f210c1e07050c010f091205010b090603060408031605040302091e07050f091c050a05010c0206061e01111006060509120309061c0605100c14010b0117 72
    0x1240f80b0365a242e40b10b13154101504039100c0d0719940011699291078503840202404a00400400d01c0c58002c1a4440c1c80d40c0f41c6440400c01e040241d085000811036215602450040912003801820840d8030314060b406055005941070041000da0005549071800140e25401290080402459603c03680b00a07012030b1030443d118420300604000000c0141c94104d41c00d841251348010303c2c8050003105407490344203540034000c10304020090011104001c440000c813950018221680f649440795501c01e400d80d00c2101c3d001a11034099101000140030064200c00e030b05642c0c503400c2c0c6d00d80d80d4443c0100140743c2e96240341c04442100c0c50031030b036215502a4110030040112601111141d4090360200350030f8070082e4024400003031000ca512080340c01c0641d021012006140065810f0010071404516940500100e0601d060541d50011540741d41983c4280d0240101078400406a080040094091014500c04030b40c005103072a0303681c0d50f181c01845407140d2081c05075282c032103105500001c1e8201c24000761 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 651307742 1250 651306492 651306517
    0x90c03060f0904080c01051b1b1002120709091b030504020315090114241c05011505090a0c021902030723010207060806030a020d03030216030306090e01110f 69
    0x90403041c107503116040c0074859031003600d000d40e450082600403429110701070800050342c02008103041c003c1e51604162285401c0a080130354040c085030b1411417821400c1c081c040c000750310000f103503217190081802d40c038807441e17141e2102500565913a659074200c85a040c1300c40c400308190480704010500c640c020540241c001811181641014000742c1d00625040e10501d40c00e0390f552195048499440341e00b550301946000100040d030700d051a10703c5018510003003c920501c95100c9078424103080b50710340c1103500d4210f002000000c3e0f510181310518900c074040c0a01c40d00607200010042041070040303446021403030f130103000348850705180808612000c0e401280c0c14091248003082c03014100e080105031182e500c0801c40a05400c1001905048443d0008020441403504101440d00c00140741500b095041d9010300b09651281400c800034001c64140403e001c2408842500349903040d007120003903c0d6080b000f000560152300a1300c1c201c81c00c1d115841c0f05140144080000c8070b6204000d0101180201c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 651308992 1250 651307742 651307759
    0x31710090b0301141f0b130510020a0b010b1e1303080a050f0c070303030b03280f0605070306083f1606050a060504111207090503100b030f010b090c0306 67
    0xe201091039107004031001e0b017a034a1468002040180104000c4004110b4905d40c40c4c5414004084040010454020f0034054880d1001e0051400d2003089030b040c1450f00100343c4240f65841b178940344030580c480020304aa040074201c0d6030f110b924552088641d10035a004201d104a0320b1542c503600b854009050410500a061040081c0c0c2101c090041005e5100c10000c0c205860a52801904850b802e01c0100c0c0a80d004584540c5c0c0034490750b100100a0f2aa01c4480a003510107160101941c0c2d00801c005040500785024046d501e505078218100343d544c1e03034095502d1018241c185020705c0b88082c1201202084142c02e0034814000003500448800c0b82901483c41c1521150325000d101201c100101e80286d50751040000328034180c41008060322003280e0a01c030038460781010580c6405044101413242c100c2d000070035000c0d030240300828014200901590307410301e542410f0b44020106078240a0280c0610b80006000f00c2040c450b0500c241002070802e2020307200c10390104116000201225003020b1031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 651310242 1250 651308992 651309011
    0x61f0c150b04140a0f020f0412110a030f210e06090f04021c051005010504140a030b130606080c0105220902030f04050d030905030a0e1f0309031710090b0301 69
    0xd6001c0c0043c2d0038110520108903080002c8980111503080ca40880480d2040c001210004042d404440c2241c251a00c14a04040b031802d1441d024800c1c840c00603800401d41600004110300003c019030001c1c01000544015802401c0c0181c090020f02d521000140c1c46810300803852500ca000303801c100360701030300c41d41c0f11101d0f41b0045400c99011000001c4510701d025902c403180c04050250980c0100c21030301c5000a1850701001901030701a5008030340311503422481c1b541d09621000c0015000f16000f287c500958105210803c01780301707402800740c9400e03040000201d46040c0000b102461080103035074540c035040340a1520001010344041e041d51304001ca040004e92111280080e602465140b1202203040c20540790862524a5041000041c9030a200e06c1da0007182f00442543c000d0062424010340202c21000044c0c070a1070351102900d0b42d00d507207507100500c055040e84558810307803107034890b139800d2108032111050400048600402c03590b0890f00c244290342c0150030950030701c0c0e005030000c5243d00a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 651311492 1250 651310242 651310249
    0xc0503161a04050309121b0919150602010f0b090c03090304090507050406111506060d0902120f28080703111c0807090302090f07140a0305061f0c150b 66
    0x1000e80e41a6015400410030710310914042c1c011b20702008020005004807105408544140120920711301d120740c0c0000001001d18000000703241e06804118010050641075021601080c1030740c2c0200001507107016044900340f40d40d840380c00c0469200510202c5580da696544004d541c0c001404082e86020a03c00042c10301e007a030141d00d0148411703440d003c0e00e840c14210010803808144001c480036030301148031800307441d601070440d41d0421340c02d0783c1055455141d500018042c4c020a08000d40111080740c19403d40d40300031500b000403c1589040e0385d400b150408841981c1104082c4501d2030b001d101c003060001071150001040e005100303060448140803082c0003181007a0400c28038803a50030454600c1080c00e81d02101c802d61025441c20040409030950300403d040700b5000f4403900c506d91f02e000c0440d00c441d004103046c1c085c3d8a0010409036503041c81c440001c01505041c0c821502a09928020346801d0321840088060b00500b50784001501c4a540c686100b407140c4120b0101c02e1968035a01d8010030346 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 651312742 1250 651311492 651311543
    0x61409010605131407110c06130314010c1413050a0e1905130212210415020303040f020906120303090d110a02010905091f030b04120c050316 62
    0x250100000e1003520704030602014a039540070303a0b54904c0c03810b1003e800740c40d0301c1402c0c560080308a10b030600d090b9004a1b04030b071500022004944e880040812051030201094240c1c800fa24800c1d41605403095483d4440c0d801c0c1c490085c0c4080109034842c80d240844101640542801881c440303140749415a140c002ca440d1840a8100716003e408a608006c1c3c0d400c0002030101c50740440e40c004103e5440d0103d80144820700e0007400911400e661940480090020400e002107a541c10b400c100c81880c1c2e4a5001001e0790251207040c00c2da0f100a04040600350020050320302c130340e0704194280065680d95082001080e0010702180e840081403c1e8880d03149c2041018510640c980710040c42200081c020241558914101d80c2d903655004580c8000143d0744140c42ca4111042600d641201e502c1e0f6a407a000c00010241e52103614094603c00081840100840c41c0d00a41c056900b0381d0b06902c0340e210451b0305642c8003074007600716072040005903000c90840310340c108020302600c0364601002118402004c0d10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 651313992 1250 651312742 651312751
    0x7050d06180f0b15030c1021020301030507080109050c0904140604050d020f060412140d0e010b010e060936090d080907080d03110702131a060c03030f040614 69
    0x20b0711604a07000b00580c0c000010741040d00580c1018503e1000000240e888007402400f90207100c1e0160768142282c0a03018a04416107500c2c6c01e4881040480c1c2c0c40710013034000748000d44541c820300b6000580700006100f22048903400ca409071010709a4607060204140c40a0011120b1a01c008098003c000c003d1166031701562141c40903020a110400001345810030b110410406a0402400c1c00b00140111401c01c22241d100d04201890414034038040e2128082e11041030422400d040b41004516810b520546200c8001d8a174030500711648024010b10780101101c25410100c2885165081d20341d0401d0f04040e410442034070805000a0000c3c11010302050f943c200303c90b8030070700c0014003480e080740042d0ba00003040001080708500d4003000702d035283d86081c1940d06050350703082c40100d10000d00d4100c0d88201c3d0061321901c44104416120b41c001e0500c0c2c03002100c181c000000051161411400b04c80203880342100840c150f44070369008140044001c0c1c4220348055540c42c2d0784959080c24504588103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 651315242 1250 651313992 651314003
    0x9020f030d02150a02121b1207020c010206070f021905011509050114010c021509240a081b040b0f1e030108010b0402030408190e040515030f030c07050d0618 69
    0x101d60038083c00b50010380281265003c02c0c014000240d01005e0b84011660100e424008101c03c0b00541c5030314445403281d10001100311440000304800950001403000c0d14400a0f42190390a50b18082c086400010381e28000006030010070755801660741d504c421181c2c0c64051800011000240e90401010084a070300a444081d00c4d0001003040d40817405461702d9104080c240180301d4440c1e54002010850340c842088040000440d65900c951a4070380f040ca55255440e6904005081c42d2980101c070b50020780440c000623142c2c60028643c16500c2c030241c0c8403001044401c1d418141400b40959903a08811a030510844041c05040e50307641790782101807001d5a110359817950343c0d41800202401c2d11800d0740c00d40e0041c0d004209000c00241480200da50f00c0c110f040d407821140c5510b420454103548450710b1554024103150900c039401d0110240581b150300202c08540e45801c500c030b43c042d01c1e4024035281010b0f0350008001004203041c80c003480140d01d0311907500040d200c0032941071550b025103c868291032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 651316492 1250 651315242 651315253
    0x70b03100315090f03050d020405060d0b03160b0a110c03060703060e0a05060105090603060d0f061d0c1302090310020703050703030506060c060c090607020a031b05101209020f030d02 80
    0x1400a049280521450400c5003840f1041160322680002c0840c280000d040200000700102c03914155415a405018024030306a941e101d22018500030302100e1540a01c2800b031807560380c00101280c0c4130b0b02e0403640e03008105810000003040079181e15542c0b00c0305c200e480c0594418000c81d9502400801e111b45095200007031002e05101e400c0c04050f500810034800a807501050200c49d0b07802009807a250401200d00540d00d9030317600c0c0441c000040b58a80108409204100e06003080015080701c143d0384485104151903015404e4015079502107107416a4000f1103094180c4103200303560300100b89184001e0200c40d07111527140c86c1441240c1c042842580001c00c0420702c07604040d854003495403c02c40807180c19013021ba40655041d214280500b812003901c000180a0080d03495181c03e072400c4a40040403640701c282d41c3c0c1409440d804408400603034407840b2501c003241915103034452075034404407540d429941e000414100c00c02080d000c44103990040440c88210619901002607031403400c8a50f000e0300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 651317742 1250 651316492 651316499
    0x7050d05030a0816080115030605030607030b040b01050913021803030403030903050705010806060a030e07090e030d0b030102030408070314090a03060213080d0c024b01020705090117070b0310 84
    0x7071a640b4050b248136000001070080a58032540502c1003410768004010b480070306400402c0580041c0a2a4010b94041c050141040003030f0fa01640854107121040e1001d01030300f02c1003070044410340700b2400403c0c2d101082441000d190301c0396901501c6d52100030700c08140301500c0100080d19542046d0320031800203646e1401442046410b005580042c80203080000d014102000040d03a103002d0804103104041e920301640c010a002004050000c01401008000c1c040300c61115a4a0350312061000d0096418080024100c1c00c0501c00c03648a150071860b42d5081c81c010303580884400d00903180901c501481407001d64816522690300000552144070010b075104045000d07211a09500da11003100744d007002c0e00300b000f69a003200842c65441d50443c0d248510402c8031070350094480590401500c600b00141e00c910054080c41000d030001051152400050440315004a9a55400e40540341d04410383c04010019a4445001e28440c0220081030742c280703079112070080c803240c3c004841c003150482e10f640040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 651318992 1250 651317742 651317747
    0x501022a0a0b010302040510090c0f0201050c21070203120f1515040b090a1d10090b03210c2b080c04051c05010c05030a050c0307020706080907050d05030a 68
    0x299282040c40018010903041c0b03803180c85441c141440064011034640c40000e40b0001803048440c0545a10042013042083c50b0000074042b9055a07502c4026610305004141760480135004c2d06c1100d5465400c120201210414454120348064401c0d403d41c030051181900100c9001e620b60300c0740307041210000e4245000340e139064000c0000d2420500601c0c40702e80880d080d00014044400361455078041640d100400c0c004a200c00ca003e501046440c000b009182d15149004400746c3d0003400d02100e020b4141d030319807031000d0840780c201d060325a00d1342c41800c08500f14a20805ca900340d8504040314181003544e4031203040d080064600803160303802c480800b400e103504000c51481980311490310b40286145000c49101c103261055002d010300c620001e40315064018012040e0102c0b6550100081c40540b10001025007a60010b4510805590900d40024004042034003504d100381c2481d401480e65604d00740c810307142000040d002d11443d01070740001203026282c001031414558400c0d001036a9480c0b001100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 651320242 1250 651318992 651319057
    0x10906080c0904292d2403070b0309010608010b03070b0405190909232d030412061b0c030512060f06073f050a02100c0e01030605010801121e050102 65
    0x50354481740070090080c400b0b8000003071030303001601c1004038508a1001002900d805d00c6a40649003800c000410410320840c1908001c007102c003080000d000790210b079800c06440740014000c1031000307101030008021901e000440840c0085403a40101e05043d201c4000c0c60a552060700d059446115640741e89282c010075a100d2081b07060110003420314031500c03039480844983c0307808440218441c1e0340000410041d05204441c000e00c1841c16500303041c2c07030518121001c0c250b1403c60f260020340c40c0c00d00f9007080f0702917100f48120551550b5090b1400a46031070441c800100030785085e401442c24010805c40e5160b079001492500e00861080408a42e4a44211314000c46055014080280c40302d0040d04010745000032601412142007664480150100403441e101d0741200e201181070178806124041170300712407444c200030401e83c0c0510100341c4601c01520f23104421b01c1054050356900d4a40030101e0600411003602c18044501c44101c41465111142640c20180300100c0f600e8025901100c4850709428 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 651321492 1250 651320242 651320311
    0xf02090307062a020f030f0d0f0203070c03031b05010e0127020a12030c0c03060b100915030c0c0203033f070305040204020c15010906080c090429 64
    0x10250303094091140c0d40d00f4645245084110301100e440085401c650b03401905c0144001c024080b01c0010401d0700c0e4140d9111505641400840c5c040c1e50301e0480c00d480401110b010907003006c552039002d8a90b50b400c81e200142d6090403024901c070248201c00007403080c003406101d011180000f14040c82c500442905c2d40400141100422401034080401a21540b00030021691075072480c0303a40d644507042c155181c00303c3e140300a1a8140e80780e8084100902d56100c065085020740c3e14046040300100c064a884147d8011003a0408000410410145c4a5000b0078900750441c94904003180b15070340800d2854110294012031a0748900e500c52407000d01c030084500309462130307140d180c0843c145803418400b5240038041c0c008154841c00002c0a40d1500d40445100c12900b20884101d0540d0300780681508000b0702800201030f003070080001f04d00c030000420002030b1700000d00c285076903265540d41c542c0c45668108004410400d06040001d00c80342c000d2054403c2840c510090519010400c0003240015101c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 651322742 1250 651321492 651321497
    0x102030106030b0d05070909020d0606091a06130e090705130204080111040e0103030c0c0509130302010c0f021f06150504150507030c060b04060902041e06020705010807050a0e040f0209030706 84
    0x2c0384c080100e0310000c0c040c81101c58698000416509500208034007130394648015040a00348000020012035076031005440d04d0243c80451034240525041044c0c6126400c00e203070100442c0d01007401001140c89a56402c03620b1035080380d80c01a0781e03402240b001c2ca40485032043c4586d01082c01c014800080c0100000b600e100320742d851030641042e290261510b0180809030400a0720140c0c14100300e40705841c40c01910b8001d0056132170346005c030b41d0705034217054100341140154200340c03660380500d0050020f0f001d10344568000c2c0614031325222185400401440d04080c849444503030000d0100c40c0300c003040c4a4442656189940c0f182440d411039030360a8001c0640003000300c00c0042c4808030f540159001540d40d8051000300d10800604d001034080c10031500700343c82d481d100080000d865800741400b01e80145640ba80610990b554a000741d0300d51000d0b03c21140030841701c0c030001d00564420b0001703016503c0c0b5403d09082cac81d44204041012907820106590384264005148030705403504222420043c081407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 651323992 1250 651322742 651322759
    0x10090906272303071e110415031709040e060103170414040c020a140c1302040501020304030f0f1a07230a14070b040317010602030403020d0803270102030106030b 71
    0x15525052038144825004842c00c0070b500d481c0b14000c500b4811510711a40221200c0f55004442c03421050180301760340d041390031501c2d802a51259040c1801185829009003813008041803554691010303000c8202401641140304014080032071303a861090501825006000345107543c15450a2400313500d80e40c1900050440c00e101c104600e21800d014410449025030b00400c0010148030180d24101300000000c1280c20583d07003905c05002c001498004004048a01c0d011103141c980c100e200b24461401864011b800800088c004150f5100c54504d403288110041c41d040041512041b04000020350341090840100b4180203a90784c0c032021000c2010305450140c40100c0c441075140b1070034400e0a082000740f00342c03031006000150000341a11807840c1c00900156581c5440d2900800d800365502c0035001d048014000071540038800000e403004c0e01d602400599070101c280d1204081d94000501c141201c0620326809490703608400c55040720f01404500150b140d5040600180c161001c1e4150f180c000e1620 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 651325242 1250 651323992 651324071
    0x806040b04020409020303070f2109050306130f082803020c0a140f0615210a0602030402130e010509010b010e01200111070305071a130b10090906 64
    0x40d198a410036811100000d191042e803000c2429401401000f821235019549080d0502121304d02003030440d0405507045941c4040036a0039100d8507014000e80360154000d030006100c0744421141016402d0080c4003c000080c259994a0601c0c0e00131130741040d0101d01081040c0680504400b501e43d0f2807400e007029414060f00d90003840e034038040048054151510300300d2191080105025012000481c203041c0d52851038002d0050000e007000501050060044019001e01d0a0420b03a1b0380c02c4045180740070302081044e984130100a50009071060364004c896540ca89074800e001e1003200520403060002013158030f007210001e42140c41c0340072500e060007003640d0403084a80c5d001c2481030345500c1c000c4404000310701c09404540141a6400f02c42e42d0303c1000a005400d0542110107030441500c200e44000c0341981b20300302c00d01624801d96801651451008480000030f00701c03041264003502950408850319550b800c0e900a481204005460701c0f503640072000740b0900b04031640110034016441c03107040e00f40d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 651326492 1250 651325242 651325253
    0xe01050606030112060b06091002210c0d051806071a0a0c0504061407060608160902190c15050c070b060a0602031204110d120305060d02060d0f0f050c13080604 70
    0xb04c0c0000200219030310340d6a130710250b80d100c007519001d40703014098a070f0102d89480060341c1c0700031440c2c1080c01c000c02d480610005800042c03c44010149030005444005c08c03480080c0c4640d01f00c240c3c03e42080d10605013180a40d29900040c018280c090f11100030240001244203a4034840580540342c2c0d00e08002d040745a881d00801100d08507005c40c80d00b8040c048484c0d00c4c81f9070600802100828140c02c129000130364560020b10a101c02c10300b402681091955410400c04a108021880340f40d1403820125100c03040c002c03513800101e1405018a20309032000b00907400308440c07040b180f90100600209600342440400b01655a000750180d0740f0310b840307d0070490003a6981c05154480c4c040c0241b81c60000d0b0400852213060742500401400e0f41c442d403141403908044903845404d4420000740b50800059451828583d0320030401d4000c0c0c06a881c190380c0002003400303407000e400c526624988030600740062000c01d12880344180c07070302e0209a84a40091214490001065002c0042e91348500c090002241 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 651327742 1250 651326492 651326519
    0x5040b0d0819050903060a021216020a020f01110f01020301080c010801050303090f120d0c0629040f0e0604050f07050a061e0905120d09080a032f0a060e010506060301 73
    0x120b001c0c075840001d09004111020310401d0b1456405000f07160034048480d4654016000d400001c001201031a503071b04094130b084d402c8000d580401030744100310000143c02c0907030305c810072010306140600188062034981403030103002d40000300040e94000010012004240056110100d091034144069498100003998900859a00a118003103081c24600c0640d502456082c0b10402c0c401514144400780801a220342c0e5107080c2604e41a0a181d000700d0400541c601d01d206104013210903d4000c1070201c02e100050079603e010100a9075118035504841c58208011032080d03100b0001090840142e040751420a003060b03004501a0765112010300c1660307001004c00c0501081018103030600307004050104d954a00e550700c841d41100c54007401207640c01004ca82c089a003046a01d031354140303d964000301c5039030f42c43c20704016000400c8030b0910040c409816942c0e0400e01100e1060b1440c18802000c81420415034000483d6850782c0c074424041e9020080c0a1550b03c420221181410756141c010001000c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 651328992 1250 651327742 651327757
    0x6040b030f060303160c030308010e0408073507020312120a0b030106031502030603010e07051509042a030c0f0c0807020409140a020315060a170a05030304030905040b0d08 75
    0x52040001a4152010001d03260f014175104000c911030003440c14807240034074036400b0680c00030701c81c50000f052420024000034012f6030321070411490400d96488500c114001c0d00c0703404809040c0201c02d50a81031544008c2c4603440d9000600daa961078403881014603000081c00c03043c0402c0010b0011040e001092000c41e03078400300c2c1c180b011a404008600007030042480750030003401500c03140244100c051151780a5442100242c00800031040355845281c0c0e00d107d1441a5580700222114038099050000040c040b4440c0c0a0710228560421031400700c800b21540f00e8200e403125070004000312144d030501070603104803098146824441101c0000406d0185c20100281c0103100001d020b03021500c0303592000070364603000f40346030707012200c44541e081c0c60b5010300300d05a22911800405003054a1360880352405071100070644803d4900e403000000300c071046544440d40c0303405804d0100011aa05100a6100354801c3c3d0703c1c0107100d402d0030200030480750a001124051100c000300d480010380c2039400c03122013 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 651330242 1250 651328992 651329011
    0xf0c080720030409021b1209010c06060e0a15060e010f110c040f020d0f06050a050f0d051212160c14030c0a080406081b040504020d14042006040b03 65
    0x7010400c040301c81a07811006040361484000360000310100355901030002e40d030100609185000e01084002ea41e01e1b00b5010071006d070b00d000c002e8000d256009040324089035109400105e0340a0307031814202e810030000c0b5010106141c49030f00c410040300d100c503066030103403649081a100e16840d0700002010080d840d450b400a11417401c0503010711072010004c0c03103101135005005006140080b001c0d05c0187d08086040007400c0c0c2031a4a41d404111140200001d840c4080c0801d81aa890541004030003031100c201030384c00054400309140812014401020f86880c2246619900d4010710981c0301e49500c01020f0110521007080e004449503031050250310191740100c0182c2c201c11101101c0744c291f118480c0b2513a414420300d06400100148000548200d80346030310f8004d071641e02c514002c0c10500c003a407818640b02d202000140400d240550240550000b00702d000280030050142104450704160b4050312004141d0820380c07200a1581414614608143c9016007010b1404040f0082800040d00d9502c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 651331492 1250 651330242 651330257
    0x30406020606011b0b16030c0306060e0d0c050d0c0e01050a0320040e030c0609070603020301180c090b0c010b0922021203090303040b13050301180809150c07090f0c0807 74
    0x151506803031940100d160805c00580050502c1c44110700603991412035a80441e00f804076004040b40070707200388800c413000d6443d0034942085c90810080c440901c144112101403500c10080b4007a1aa0034100388298440c002e917070022428004013504407034050388031621807000340c0e0041c0000b5901349084010b400b4881410b44820f110540040c0141c16180c2c0d0b0b10340143f00105204441c2200000c0301c80c0a8110942628000398071090214283d210074080c0c2a1850015140c1200c911741c04e5020305012080380c41c06101d1161220700c0800b40360f109113a81c2d1300320fa44035001c0b1a184d00d040b122464000e030703c0c1c0b1307211042c100702000500100d80080f04003038403e03a410511104203c00a00468007002c8000381980d80e00c90b200c51042840303400200c044541a820300700042054241403060300300440c0315107021f200e1801c2c2582c03107511581c01800c01e5500100188140d00c0c04104070f001800100350182c003d081e1031800c200d008011982c640070307140c002030b0416010f202041e40180d1256003002c1c25290054 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 651332742 1250 651331492 651331517
    0x30206070308091c2a112e0518011d1215100806130804031502220911030408070308180d0215090f06361b0303040602060601 55
    0x1400c03d80255131085041a443c2c802208440e884080090010110000508401000050307000c40380c8900000404a4015085d9002945031503014800300320500d11210318554800e101c24064220a0021617010820114449800000311070616940c01800c1c80c0c88010814402038045211000c18682d500940c001d4124501012003403043c1d46024100713511000282c2042601c4102c0140c0c0b078400e050303407070242801240c948108208280c120b41d800c00c44ca6403c0604585074207012004c003401e030b000c03801d500f00400c040c0e035000310036150b58101485890083c11850000c02d4002c0e107202c3c5040c3d80c11183c0070420440069020342c107440440303405240035031103a40c64812444013007400804413030b01d0f4411520402811540021046035011103e441c8002d641c5400140548e6601a240c0b098001d800c5080002c1d406d140403101641840082c902028000720070001c2d00941340d00519404159810000312030101c644006010b82d00c02909500540c9401e14054000b91220f001400d031070b041100c60159007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 651333992 1250 651332742 651332761
    0x60305091b010c02030625080c0304060c03061d04060f0c050d0504030504170606041107030c0f05030f04030302030414240d1e0b03010b01080108070303140705010c080415020301030206070308 84
    0x143c2803d501804443c0c043c02d04a003414804103444210381c89140440c0125090070b8403508225001c1c1269900c0079080d61110364640c00500136a0b01141e08040d83d42500280d40c190a002e2404c4824484d601440700741440d081050540b011000f080d084941072484071581207900c5030440e6100c91031a48000340680300c40c034040324030788155030000d648524601441400b907103001c00c026005003801c403010407455402411600090140c5800034002c51a1540c2d00b101150f000220450002d21907002d407450040185504d0700250032a800c00e40060740040740c180003242000c25550320403101100d40b0050f10029030503c44000721a1941d6000d2403101107800403c107c0c0c96000101d002150b040b030522030141015503000103040181e1164408d40c2800c142003180e5014403030044c1070f1040034014220080c10740d00c007aa480e44103001b101d41c06410801001010603000e100d0040e500e6132542e1010f049040c141001000c1c0341d9040d2410404510410041005a944c8421580344943c5420400c07100d5540c800d80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 651335242 1250 651333992 651334007
    0x91206020d0f02191e0503060d03350108030702091f0518070e0915060c030f0415080108060118050402011e05040611060c0906091201060609030309060305091b01 71
    0x40d10802c90000c9501c2005409030440c001c18480300d40d9456607000303459028000e40104180c1d06001156080000c80c8060801c400b00c2c1601234024205058060801a80b9054940511051100304201c0c100700c4c0da94010350054590060200e44001c1d801c1407c1074000401520003d042c1034400022900c5007413841c40e46155034401090001c5c2105918081c4622903142c00604840040005003420300c124694a0171060913801801c03848a5100c1243e5280c0500041c2e502c9007078640b2991200f8003012900c044058010000340407009440060044032010240200a068200d0b1a43d03410820040c40302c018031169140d02050b0618002c18241c41d9800165220a039004007030640c04c00062507519080e070010001c01c12180c42d0303590b8087d03841c031510405456980c280c91a00400b0410020310081e40750aa000d400a010001c001d41514000408074608440d5070303070320101c013003483c000c0c04100b80740e005036100c0014222802c003442580b50040c0d02c90b8071421154142008054030866641083c3d116059 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 651336492 1250 651335242 651335261
    0x30d080118180c0f1701091106030c0d0603081e0f0306100903050f0601050f03010e0705101106010303021f0204210303020d020a02030d06140303160f060c1d01091206020d 75
    0x82c5202d0715460b205a80c69130441401002c40403502d64250002000307051044010440d00b020350b940f0f60420794030821880d640003400387d002068007407290182441c4e10b88a000300542c0b00e805403682d81c04d904003298a103403444a605243d494801c2c03107800d407803100c1d00045960000c41143c90b43c9500c400c08100780c40c01000380d00003922610840078485071401f030009503281a80c0048482a50344d00e1404100b50030f8408142d0b100c581038010f4502000b00d0305002a100c045a180d81c14001031491202000c03502c0d050090340254016440003941e000ea11b0070043c0001142401520290b14003400c00544404041c04040c502000310b004401035000d0512a0781501c41011030240c0a65907601c103800001d42c1c13608505c1d500b0030300314500900040d41807042d5520a4198a020b8003550602c0c0000c14130b69407040f490301041d90300440c03c00c00800010464850f06064540b1078450300291030409000c9103400c054031201c1c03418004188420300c0148003442a00709103503801100983d652556140e440f004d4880d103103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 651337742 1250 651336492 651336503
    0x10612060c230d060b0f0a081302120a060f020306090601050a0e1f0809061b070602190c060515131802030d2006071e1e0806030d08011818 61
    0x1004110b582c9080004100440e00c800060140c15160030032101a44103203001c01c88055070030030510345000e020300c1e090ba500c0200a0742c201c881e2200d80e0080707141000e99440140b050341180b00300504200d840d2040b50740c4401214800c500310b19180001c9580b40e1070142c0701ca8148080031600d0141a0f101e0b030b4800074940f0016000d481003c02e6110402d001e080300309558004180d100740024000e0400040c1144640d56540d00c103015024552503040140d84040400c3c2d0305690204440404c90301c480c00340702103143c5e0740d680790080c0705214100041100e00280c5072004c6500c00c941c500c8030070343d20008c9072202c0c00300601c0006012032005044242085032808000d416000710b840403511150080c58444030b21034502c034191810a1760b02405500c0f104119208404070304407204840c0030410503040b03074440640d50300301000c804042410384030f01030f0010440b402c0041c243d8410050641001d2102da50382c8901c906107603196505284000032480d003010200c1c0e0a180c0c1d00c2d810f01c105000000503e408035038110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 651338992 1250 651337742 651337787
    0x510030e0d032d15030803190902091512030c031801030e0c010f2a12020a1713091b030b04060b030c090301061d0411010c0f0209040c08010e0703050d02010612060c 72
    0x30302d0442c1c0c0c590003c580d410030300e90023401580039174003a0b4041c40e07401c540c2c000e089090503504c4200c14142a5036111b612500980034000c4a2807440c4100f005000c410000300056880b410507400e190100110245002c0c105402c09403002030701d02000035001e8105109003414020600400c1b03085524040030400c556007260310110b0400c2045c40040c8a00e0202c5c021109a40307030742e080d0b06042c0e0381c4454000b03000745005102d841600e84900c0f003c003d004154580307180d03205210340c0c4103000d00984455840084000484040b0106002e825100e100310008003590180302407458440c010056020040141d001d1420016281c1804d0b81c081d441040540201d1411920040143c076181541030402c030742c2228240c842c608155200e40c005d00300401465841100c2c00000d000310707030a1001204018004a8070008001000b107102c440078013030035825008181c010010546503092440ca0302070503824000c25645444010b10907926203009c0b40e41800c0d003148000c10010ba00c05802c69802c2801280f818114228 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 651340242 1250 651338992 651338999
    0x3310b090c19050f06041d0712090302300901051303060507082a07060b13181b0f210f0804090f052403070510030e0d032d15 55
    0x48844000640f01d081d54001c070000c600506000b40d40c41240a8284459038a900d0340c1216a040500d8660200c5c513407601d10b5242900c001901d00fa40d58203942240581c02801d609001c0e020460780e034407e4035254100b901e003884075281500165124610446042110005003005590b1041d076845c070046902a030100410b2509540040036001d00f522019540d021003941c00c21407241c148031918003c803803070081d80d24110859403008010000b40e454590050070031105480003001d94400c0ea070b11144c0007102e40c4d807410b504c1d00d4205068102400c01c9194441940414081c03054841d94490a44407141005c442d18008002920301000808000424081803941400100041d000140c011244040400d0044c1400440c030001540e80441308064450800040c0c400c01e9008190381101e4640c0c0901a01c0b1a42e88887c080b50010741111008008a83c441503910780c40b4104010000c071030345071031604201928017070700901c2084410b442d048802c0e00390039000492008840c1d0040c502001c2d0400100041582d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 651341492 1250 651340242 651340279
    0x40501020c06010618151211091201420f03020f010c0213050a14010902090907091a21100503331b0f03310b090c 50
    0x30280c206140902e60000940310b004400c4071032910149a1002806401c02e810411140c046030300c000c04109190110088500241c410039401244800000707a65000385c07401c0c05100e9032210802115689030010501800e01d800400d2041420300c0d02c8545694a48420601e10556240043c9030f9a0902001e0000309110f80f0b01c2c181d02120300c00d40301c0c40704640a080041d14000d081200c040d4110310002141200c5606681c04aa802102c0f2480013424201c0d150b6034010740c910036044000315550001b024191031618001e4194028554501075070018101102844290307030f034100100e8032001c081495820b410403584018140000400c40c85414038042c000d00714420068819103009000c0c41c0e0a802c040d42580204da0210305400e0642e050030f0441c1c0f0003400e40c40400804100d904081100181108070014000b480c1c075035a80c81940b91031b0700741610001080319845211203042c1c2200780d0ba182403a104802501c4906800c0314429a060359602c0801d4107042542600c1a0b000520074100d9180c9103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 651342742 1250 651341492 651341497
    0x80d0b01020d0c11010f0219030503060405060904020112050606040e07270b09010c05100c11010e01020319020a030b0a120c081b10030605041503110d08180d0b04050102 74
    0x220980c2215049001c20200303846600c000c0e40040d000a003004c1302900380f5405040102c040110074070451f44a0380168141d039012512905044000a400200340b001914080c0210f640107002207510910b0b508040d4006030043c0c0030f80c16400e803a0360300ca10025400d07541e50001d580086c03407401c01220140c540341100404845000880351110003070061032030b865046110b6100180e51a1003c401d250980d6480152010302440004030b58a1007111a00e03208201180030303c2c11001c0f11342e00c41c44800a90700303d02600b1354031410800b200350382c8148100040c1c84001c0101200c004030240c00140e032125503120840260000099441d001241140300003818146001d0140d8101e018040d19503c0c0c0d07403140c0703000351034041180707c0b91110f058207580d0344590326040c400d00031500c00a0500080140c1c2e2036002c10182d500b00010400900c2042804100f40844003034070303840e43c203011640d08010600640c0c88060600490307146404120352215080c041d51110005080781507080300514140e0300d4a464000e000c0c1d07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 651343992 1250 651342742 651342761
    0x42607060e0109031d03030f040e190c09050913060c020d031a030d030203101e030c080102090a1809050f07150801080318010c06020a09260c060304050307080d 70
    0x600c1c203041400344800c184100075031640e240e65918064582c0c010f034083c845002c002c038a585408100507001150b0030110080c0000c020104044900745480ba02441c8140000d41041240380d00740309503d168ad55205542d40103891080360394011a4403a0071032044094100d00c00186420320300007034098400e03000582d83d84401300ca50f07021320905a0350806003134155100311005030107600c80c1c4c17041700c000340c0a5005541d02044040102681581d00d000c1c2101c0800081c0f00c1e8040e8900110040c01400500612107020304200002545080c0d0003401217803694030f035842500c010031400c101001040d92923801c0308103a150004102d03400c0d040581080c5807130b4100d91140302d01629605035814481c90080140754129440300024508246ca03010a403012900000c07001c904119400180c9030018506202034000c14500d6560084100d0810310b001c1080b0900c0071492144030f0100d008005641c00000d9113004039581a2022903c1e5219407401d940b95016000700101405c1e00411031580d0150f50394042c4a40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 651345242 1250 651343992 651344003
    0x60204051008250203030a0f020c0a08090301060e13030c03050c0102071505090601060503181e1c0806030d051e12040507060305040206090904030e150405210a0b042607 74
    0x16000380e5940b60305280c3c1c40c1001200982c00130310000f82c450306982d12404441c040007402503d46042581980d04000c11900300700c0c1c0014022175400d00d10304007445290090084038403421401d00340740180306030b10103000d0801010000c015401c54101171049056401020a40c4001e5481d241c0720300d48884207c00004d50f00032028070b85070008078441000940d070741c100c507410b444051840e1516820300d42c0079411499000c2e143e1290b0700140075811094000c050619201c180941800f031494048402030100d0f208444041016083c14401c0a0b035010904080d503600e281041c56030349210354240f40e5902c01d10b20220504880c00701c0c90b0005800034012182c41207110b41d060310040e5450350010b604540d030981c0c020750800b800b88003c0420381401c00903550010300038104184980916030004c4c510000007540a4580c1101007400c0200e410240c910304518554801c51440103440c030803d01d0756882c91481c014ac11014541c0101b81400302c066078460010380c60f5080c000071104e503007038a80c030b5075444018100e91 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 651346492 1250 651345242 651345271
    0x405030111040605031f0312082a04060c0501060801060602030c060f0f04021309050f010209030f03030124200d080a1b03020918011202090105010807090b07060204051008 75
    0x1118076102003120252140d60f10390b03a0443c0c0380c07520410208001c0c1c04100d08422600a4048082a0264000c203e03500365642c8022180c900f15054040048402814407070b0160340d00c4007102103801e440300303540c1511041d1800ea0301c0303a010341c01c1140c003501899001d000c0307a5203410004103406601100404020243c2c0003140e00035110011100c01200045a03000d02c05190f8034040760041c81c00020803c10244008804a02c43d20716072070300b80c00c2c60034800150b102d80c1e6000444da800340c10103000d03010096596102660131985010303401c510412040010340c500e804034049000007d4083d250450b403a0000000d010480400280f013656039540000707a2001280d81e8000140a184642c01410700c0380504002c0c8036154508140250040c0d0071103480ca580c01101d14428441d06845100981d000b081e03503034290707038000342c0030300601122040c1a00301504002194080002c40d0345c02915407812641c00f4680c813a90f50046c1c0c00c11038000d004640143c0e90210075002c2c801c0015a00c1001203004012102070b450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 651347742 1250 651346492 651346511
    0x605060a2301140a090311060c100f180201081f0b07060903090905011d04020102101e05060f0a0303140d0903020f0d050406120b0a0f0f080d0305070e130e1204050301 73
    0x14603d0013480940c00c0091751020301400000d400c20728440701110050000c030f090228800445050a80c41c0d4903500700c495590200400308001740c05a10081c0007509403074407a00386d8940009241c000c2c0180001c0a5900e99a00d002240c1624110007005000d4540429290b84d401e01e0050090b00383d000007500000c45a80c00811064820b00c04d83e4122964024203000c120100680d20b0000000104180d065008003160340703894403607500136030298164000399507a04000c501c50710412501c0181c042d0b030242b80342e0500010717a516200c0342e41c01074175010b08207080c550307841c3c80e03501056110707000007007c0c032508081e1100304240d000600f036405003801c0401d80e21041030303111044919010310f00c20400083c5056821103420900d1394880b10340c0e5a80909032200091b1a0282c440300310308583e0011407000c8605c0c404021822042c40800c050480620f0140400d0404400080c120000d240c1c52900c2246101c0e092038020f009588010a1070310204240c1d88a5074042c44c4546140d082441054025401c1c0504034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 651348992 1250 651347742 651347777
    0x616031107060e0d17040f030c0933030f0b041119090209040609062c010b0a0e1c060605010e06032509030b0109020403060b030f0a0605060a2301 64
    0x48042d070310156201d9124400c8807081042c82c8203020b1081c3c400040c0d2005405242d8002c1006002504105044070030f00c6255207456102e0040c0c0d42d0100ca9002c1c82d02e812181040528034110805620910400f070108280e40392007655107800e0780c402801c1044c10300015007007000030201c1510450165800c1e0a120b400383c41072006020749c021100132031020b600c0051250010030360240c441040060300029100d51184031440c01c954264020031903400f0f00c5103095100740100ca000107030075844408040307600e51401441e20820301038600d480041c0042200f10002e140c54100c2c001c110003a8040d1650300207407260a042004000500450340040d01e0000d080c415030034500c0440f4082e090005030020301c0101c0103124040540850460000c0002d40030001022aa040c00102e001c0c0c1113a101c0103a42d00d103140b502c0c0080b2101103484074025003000081c00510b05010601158540d00018081650366840b40001c4400c0e055401011000f480861054003030030398422642e03918802a00c1d0a50002c0d00400c5c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 651350242 1250 651348992 651349003
    0x6090b01090902030604060c09080304031a0105061c090f06140711240402122a0103060303020322180b040b06041a1e0c06040210030c0e0d0c030206160311 68
    0x30f134155000b20082030000d6120f5200100340001e910f002004991186000c070308541c000d510988180426456820f41e004000604a00500040300c200c0e2410014400d00e0480d002000e0042001a5a0b0081c1406200d549182201c0c41a8810070811440306849a61281240d00355000c800042001240c6a54440002880101c03070000310b4a00502d10320314001d003207085200400c200c3e0880d20000544204241c00c2050203608001401500e206580ea00b0345d014144100c2207440d0704141c10300408201080c0c003c0200d4003c182000040703c2c5001e28201d45501809080d03001030000740300c04083c0d10541003203078400c02980c0c00440302481030240050030000305000d00d00410080c03080700c403007191001400c0300040c01404400d0440d5107642840604600d401d8010082c003405580040080000318036012030020070b6411981020007800381e0301300c0010070000f46003411600070342210784c0007024082c8101080c0011a030040c009503072001c00c7c1380002c3c0c2e6601840760450114080b0b086921103204080b64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 651351492 1250 651350242 651350261
    0xd0b0102030315061324020c030303060d060c030e0d020304050f1f05031803190e01090b0306040c0c02100207051e01020a060b0402090d11012d05090114030406090b0109 74
    0x89a003181290381e007001020350103404403164911450b00d001402d0b0728005041c00210200c4c6d5801e803800d011440c0041d082586e41421144650020010402c1c69030b5588081c01c80240c10a00014082c0e800700010b40c0100724100c0700c040d2520920080300300840d40080140240c600039100303081610306440a0008650780c114140f80078100c116400341503603100b80c0c00303141c0c440c0206004100781c606024a950455004088500c0070440004005800c59000100024450400c0c0b0300000c44a00d041c5400566000c0546094401c5840340d00c9881100d205011030341181c2c3d001402034418601980019542d92645e1103041e02a800000d0b401080d200c03440300803048038034180c001c0d1640c030034155103000082094120542e0f00503800d1207002c0590b190400203985052003020125038a400200025003110840c001e1503000164200b080c0b420049800103d07032000b001070078096100c0040d000166100244c2c4c41c0325020040b0007108100600809404c101041c5028580220041e40c07140031a00c02d5407100d15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 651352742 1250 651351492 651351511
    0x190305160302341403031204170c0105010306050708040b010311010905040f020d061d04030305040c0b0c0606030618070e100e070504030218091b03030f04121109130305031e0403050d0b01020303 85
    0xc0001100f01c64401807507031051027058100b8001824400000c81d640007a00340200030ba41d214018000c01131140f2420740c01c880141001005440c1641d030351003504005010042150750145400c101a03405a10b94002420008005100c07448a00c900500250850381d00441400c1c1004400a46500310100000000d590381c1c0d2000d80d16541c40d201500a8180604103e035001115072000a0300c40b880c201620b50b000459020b8401c5060443c00c05107080e40c060041c1103082c41c100520304030b4038000a80c50045850184800b05c2030303944c040820b01030705519400a21001592401c0082c5140e10400a005891007190481c40307000080083c1c1c808550122544184c5500c40202c4035141120501c40410307103000102209d2900d005c9416403101c0750001d030b1086205070701e904000010006290100c0648110950b010401845d090075480c4c00302300d40f200064140704000011070401c9280e604000306a00c8200c0c86521141003030310f4001d125074011003840e140f880c90040448074944c4040222801250707100e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 651353992 1250 651352742 651352747
    0x1505151921300e1c03270b0403020d020303090306040b100603380406080d03112b0605091302011e0801051306090c03020c19030516030234140303 64
    0x1000b050b1003080052440e036070b100c81020302c4081040702e21111045030602c25614402d0140b00629030500c59030307101481400342da40c5400c05109400500003540d049135012112a82c5070705041c0086801c501c50b407420140c1501071f40302000306206503810240c4c05194140200c104413a41c0f110103c0846240302c004076a4240d9010704d601c00d02c00c4200d00484084020b613014512049028000f808480099110111a8004160a8030f400d90584104001307840000192443e21200d030f06001c0c0029403c4071440551411001510303454184c030360000c0003800c1c000c0c1ca038410340d003096003101ba5600080d0100300d001441c0c110b200031011042c400b0300000150142c03038802c480d0b400c0a040044c448074a4040300d03100c95840800013180140790181c1c0032a09039a490050707a400e0b140c1360781c604041000440496880f0b2035610000080d42c01800c4070280d03140e40003200d8850003240b030124240b400030b142456801c1c00c443c00c4807800090b084460102114803803e030781c02540da103004184002280a91140d4950003e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 651355242 1250 651353992 651354083
    0x10e0705040911040507211104060302030c0f07030801090507020a02030a080c01091502040614070309050f0a050d200102070308120c251505151921 65
    0x794000c241554854201c4141c8840c1d85030110341102d108642c00c070000b628030300c04401010489400c0e144c0d0b10002036418000070358400d184c541c5034404e521404041507800000190f402c1c0c00c0c00c081da2008501c14035003030380c0c541941c200140410b00030b00450729227610305400b25131501d000151442081d0fa0141c041c0c10307800d0030343c1c9840130705410200c641c003199502c5a0b504800103020085d4020a589500d10040c0c4450500300002d2250710109158054040d01300601c0000c6038119002a08072001218201d03e444000c43c0420103103400344c2d008540001c01800c6400c01c000302c03d1002c0c2c000405080c140c3c01c0b0b20b014140120b80d41c0c05a032202509000c004c1021001e1451080b42d001d5201883d40310188c50a100e90140c126030b1003207514000d0511001650860400c000e45081020643c900309040c412800e2018003603031104195042079119010540c15482d03001856910000100540384200240151400d110309016500c88400c03100700d50008241c00e5041101d000a0420285985502462604 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 651356492 1250 651355242 651355249
    0x806030c1e060a1107090501030b1602071a0909060301110901180e071e030605010f030c030902130e0606030a0b040b13050616030b03061b1e0403061d010e0705 70
    0x107404003a01030031058142421944900004214031810303640e580e1900348410703000c0d9050107001d8010030a10b500700320040011808244480390848403180c00461140c00e001016890001e40e07520881a51518142268201e20300001521022030107440b840c909680c0c0c0f10806088414410346c00c0d180d9101800748080c03e512514968100a01c005800e4213a152500d002110b007030400c40321400010304c0451001c110002c1c1801d50380c15218141824807842d42030000207010b00a006074030070101542c2e0524240f03d503209400c001005600a0103044907003041180e40e8001d8403c01c01c04c148070340701d640d0104a0a00300091000005a00103052040c2501c4907031701c0500c104005002c030307491400413242e8103021507818804180203c40503442e00d002030140c024050143d6980030072203031290b0442010050f6000c180740783d00346003001c00ca04150b075460741e00e070850604400001046c950588081404400c000c150390000304090040710014070b003800d280710301d6420794412410056203a0031120040141c0d08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 651357742 1250 651356492 651356509
    0x90e0703141e0109090f0b0a0902030f1507080703200c0c15070b04240504210909020d021c0b030105010806070c021011010218150702060415050421020a060806030c 72
    0x92090201c2e10758000d030f98880070980d840c196142304246948018032003c52600704129200103c4000103407107100c4a69070340c1c1c05128001000c84091140490008041074405e5004004181030b00c481000140510000c0014a4100009040042c4101c500c0700b8040d140c81c030322a0021040c407080103460300281c0d80d5400c00f10513016004513410203040740b107400c007410400201c0c05060002e090004003807a1a090100c5410354500d408420380c4866040301043d1540020485c1c142c4000301c1c000759440783c10b000054003d1051540c000450081c0341403c14855646401c41981e0710f800328000e01191340c0f40c0f0315198450400380c5954000c0303103e18032100300500300700c0e122401d1108241800800c0240c01e042e503600366800407150100d10741400912480500d000d42e002c0d140500701a01c124105206540414076610940c0600342010200c43d04030000c2d18815030403500580b050307003280c9102081324a08100000860102244514404c2c0d202140b410722035041c0b41e12481c0c1c0100144044403110041c8510308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 651358992 1250 651357742 651357761
    0x90225080403050a050a03080f06060304020f13090c0f090501120303150b04060804170c0a08070f0c03120305010e040c150201061a0414032407090e0703141e0109 71
    0xe2030900c0004003040d418072205074402c0c0124003030420300546250090811500a080803c40c8070514213205d07440d01c030741082e02d920940c191052400414050001540032110204280e00203040c406c1c0c101c00c0040309003c0e0800c58402030b1410b100c041e220841ca0003559024080c515455034010419408648250000d80b013909060810b00c5900c1c0e2503901c0003025512540215012440060521081003034801c00360300c0c90400308091606003201080308a07111070200e40d0240800f1070204600b4140000040d55910542c0c4c008c00c520190b80c3d8030b250442d07880d003a8515201c00b00e8903107800060083d0340c03180918455688055440e01c030508090000c40d03c2101401030030110340da03505012501e5500c0c0008000d03402c00c2c00f9507164a0740d2078005c000e4203a40030004414001e0704400e030a074462101c0c52143c0d0340c001154400d1039040d40e0302c412003180c03e0401036000803418a4503205205109130140e011401c4078072407450038100c5a5600b6680e000b003000070710b00851404550401002500784e6a4400c0542 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 651360242 1250 651358992 651359003
    0xe011a061e0a032a020d05070804050406030f120306060f03020a05130321050906030105040c02250e0f0601020d0305060301111315210515060711030601090225 70
    0x290074074900d2042550400c03034460010076a129211251010034060764801c02c407601140d40d40c08140c02000a46480544400c0701c01d0000100301c8104000380716054501912010f81b0401c01d003607072420146002c1001071400d40700a400e0140d44104148240511010340704982c441c00840104104120000d500412200d02000800d000c1002124000310785c0a0056005e80d800050f214000051031401030b841d2516403041c00700070417898103d40c0b5000c0070f0b2811210704540001320761403810401d904120242c0b0104008420170103500c1504135481031590280c580e4401c48910f241e44440d900103001c2c0c400d40b105400b5a0009180c8035a40e413194000c940d001c6000380022401411881c1c441e8002e400070700d403a032400d003a1948280008840d007425130002442d90710b4110310300407a00c481d04922145542314202c81d503171540c000840e81c640c0f0621008aa003805813600d5603c2103a0b040c520510000b80c094140700b07026401c00041c10b40c1c424000d40d070303901c0980c107203800d40c4400380b0551083c00840000704640b03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 651361492 1250 651360242 651360277
    0x30605103014040b1f05040b1f08010e06010e030a14160b070b0708062b0b04110906040203070e011b14070806010605041a1b0601090c02010e011a06 65
    0x7030740503850080d6800c81942586600303182c00c00e8585610455002000d6402241e1000101c40c030140b0072243c000202c0e0401c0d900003a410203038a001c64032a185e50020780b41d15090b45803840b00044d602c100500e0480c2e0700c1e8907400101d51142001100d40c00c01240d80c40c0c0e4560300c0032900030082009204400070821010040b03440b17400b044904039a6000060b8028400d42802045c00414400d078064041e910222500d00741080346407140010310f1502d41d03100450701c2848112001c4425015030303500d040115800041c1d42103980b40514250300c01807616461640251200004140c45040600aa0380268074544507158000d80d180c004407443c00c0112000c00c1040341c0c95985202080244100c003501e02c10712000f51501500340b12383c141c50044181d0018040080412080103480d01c00160300300242004542c181d030754401812140d8444000d1000143d03140030704c100010b04900242d00c0074603941c88030340090158402c0303019040e0881351103403119050f10441d00d88040e4140b502c4402410a10808101c104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 651362742 1250 651361492 651361577
    0x5030d030f050a0605091906050d060f0c03090b13050705190302030f03030408180f0a1514070b0a0504031101090303060509090d140c0703080f0301050103060510 71
    0x9280444584525000c80d0340e8030004110306600303008043c0c0c85000000e0610100d480c0c40c006c901102c4c0e004002c458140c00169007044d480c10907030040d90003482c1c001d1800130300748540d040400081030078149956085103030503103c520782c600a02826040b2030704481002e0181e6030380d41c0301c1c0e03504800c8010b003101c850080c6440401c55a440040410001c44a00341c20306205013035105140ca0b1005d814450400b5031300500030440001d40c41c10496200c0c6149103030503009010b05002040d480385440841329444044500003048403402c23050003004041c0b05030381d0100300302400300080001c2d02c1500805881c0c0045400080d80040c0b06820079a0802d100749442c00e0007518105404d42100e01c075810071800240c0b94041040145400d20507a03800c8055000600b4810500800203070101d640003115094061001c40c00703021409040c072041c0010340e004420140d44da0b064880d03501096009005203404246000404612428403101c814803c80c8282c8680c0740b90015920020084c102c41c46001c490300300c041c071108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 651363992 1250 651362742 651362749
    0x9020301050c0d0509070308091c050d111207080405090c070215131401050a030c05040b04030602030a060b0901050f070f06020d1b050903071701110a090303020705040504170d0605 79
    0x1501c2a4030003007080783c86160220181c829101e010300701c080ca40c2e00184041c0f002c61000000c59010140444600203440c4842c980d0b0548100c2292001d052405071240c41012141c001d4051411a0341c5d420a031030844564198600040c01400c0c000b601a200c107000900036800c0081b400754101306031094241c1080b00c59800110301a004200101940c600481d00181ca00c00e21900701000c0c1c0407004104080010140008000c3e00540c68002d08042d1250200c048050040c0c0c201d0340a015000350f40f40c1d0b920b80780c0c01d141c00607510960344a2032152814030700042000c4070340152207508005079503171407a10041442c0301d80941c00c510019a098601150b000700020b43c00e00c010401003100b2200401c490707003080e0400c00c940e8440c1c0400b006000e41040310054581c0d004c10000b0540e00000c0c5440401c0d58640500fa005000710000d490300d01d84c00049144c401c07600442c02130200c9100342d085609041e1070b44184070580310140c0d1300402c0311102c003050607030044210300a00400e01c0000c40014440c1e9036913001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 651365242 1250 651363992 651364001
    0x6060e160c050102220f080102070f0602210a2f1209010f02120103200307091d033408120604090203010c0e0406050d05060601050906040e01081c03050906071209020301 74
    0x5c9045078a5003401c00007400703040d903a40020325914008505011040c0c454a00040340b000700203042c9540001c01340b1407003102e140300c88144c0031b0303170050030080346415201c0b000202000c402d00506c40703c1e01d00d000c15030b104054101010000c900c0d030841c0e081800456882d01c168101902c24021952160a800440d500c244050402a460b05002007501c0d495418864a112200420f51803c440100c0a284007920000f401c00203e6070b81d060b000400404180e0201d2010858203501407103800001684074461500d191407d031311140fa00240e4401441180b01008440911080104402c1c01846200d86244500c090b2651042c80600041581c0802c0da0002c0c1c2141c100c1d001c0c44002c00c103c407400c3d8403039040030710401c005048140e401007100c05440e02c403d0781c0c2c1e41300140024108500019119000e0b01c5a0701902d00410714541c01f00c0444d40c40344a116120607660200b15a0481d02452151070f0074803a014540c000c25070940540140c2d20762200441d60070a4080209042a40b01c400e8140161802d224 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 651366492 1250 651365242 651365287
    0x91b0e0d0b0a05150111210906030406020903010b03030a0816050c03070b070210090503030109020d020f03010306090b070c0f020f040e16030c050102152d040f06060e160c050102 78
    0xc00007501c0c504000304c0500c1c409101002410080710303000240e0b00810018180005549031a000002d081084100000c0340c8900b41a16800c964084180010030034180c01401020502300c00a224003004101816600d0060340d9100c00001e140c40049030a08882683c4400c1426507803030068644070200c00024a1580401011641c4105000400c994103030306124028003d8a0107400344000061034892070755078001030040403c11580040c0341086c1240e964102c514403408110f00340d85a41c5e49091144c001c210615003036898800071400200e4083c4141821160740c0d07880300b0b56000d000c3d019000d0040170400200d4054109598907200c00040ba010002ca19001e444c00c1c0c0e10b46006411440c10a58003001513101e039055520015a0f651204400b0310a2a8000741840807401066a030248444144030341c0442c1d41510340c5d50a09020130700c001c0c0d403520b080903030140d00144031540d07130ba0703104c1c2d51074850846440050721401ca503100c0784580700308141c400c02c43c0234a00150410900d1004d140034191821b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 651367742 1250 651366492 651366511
    0xf06061801021c0f110303061503060406031202030717120411040e011b0e0a0f0b0a090b030c120f01030302030f1b15010510020d080628061206091b0e0d0b 68
    0x24020002d5507804112441038217140c1d00510300794240340000c00d0303803400402c0c2100c0b2110b4021000446607211948070b171000707640114900d1a00d40b091400a51240d03c040f009440c0303c1582840c4c10100d8106908940f400c610000e03810540e0742d2140c450200341e4880c0c1d4000ea5120b03845202c03070800c0140901a8518021800c0b100d0000c2800c0e19101900b4004083c440500441c0030000030490400410103400844100c0c00125a461407280e00c11108040d10f80c00810b103462000c000e000306158280041e04103031102c034403188000c0c3c69055003054940024800100168801c11640c01c00070304590141443c0c0c0188814030818aa050003d1401e1050b000c00e03407207010040000404c020300d48054100032800041c0054600c0c880c02c07000080c80224024605401401d551101c0d030b4a407e0f1400d00d0401400c1043c180d1340301541c5580e0020050050f06401c0b43d1300034102400800ca403100303841502101e00030503031840002d2661b50401c0d2642c070a0040c4040c0e00803810411040862340400910303220b0f82200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 651368992 1250 651367742 651367757
    0x609030f020418060c090e0c0d05070c140106050a0503010216021009030f0812060612010b1e0c06010f08010c1211040e090c03100c05160501150306140f06061801021c 73
    0x5080040500c520340e8010300005d032011081c048c401140004454110740102c0b000b1401e41d485040c1621642d40c016402400039210040c803442c1a1010340c0700314107440d03085500710340c2c081d510b02c101403c2c1d020303c4084d5090f00c083c0020100042c0303044c040f80c840c484420304009002d2540d81c1c9820662400404003611003c00000f46102c05052031140645d01590844040d8281261041c000749414014002c88050342800103881c1c01811000c0c1030307500140300b00005150348241c010410349c0c450000303204190411f0b400b450702141109040c01a03420111181c0d80d4001d400c40c0002642c005413409240048200340304203c04030b0032091a0368454403030840e0318020500c10208809041c6004ca0207200f402d0303210729000c0c0b205049a440821100c0e0004200b211175200e8a180c1000b80c014440c9162888502402480c00400c000c5a40c01c1124100c5010500c0300d01542c821008003a486c81c100e41c4258410780030010342510340b111401403442c00308184100c07441c4c1e01008048400740f24a143c0382c01e000c034011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 651370242 1250 651368992 651369011
    0x15220207050633030c040c030c020d0201050c2b022b0c080406020702030106170a0c0b0c0718060302090a05191b051e0703030203070f090609030f02041806 68
    0x20001c0030b8011503c035000f0444180080015031409226200d983c1c841d8460301440c9007155020012021345000c024020401e91f2078080002d0010040001c00c0f0b0f0160207801034006140d40180704540c8614100901a49002841b4030038500100320308910003519018560028844401e44c80a001c402c031107485070200b89410540b20004c090100500030501a040c01c056004066011407000d130419407140000d41c54407a90320009000d418150011003a081040b04070581211000402e824598001c903088500b00b40c454480c0e00c035510424040d418117501c801010090200c1404c010302c1a103403900382c0068042d440c2d81c00241003800640740b02c001c864840040c0002c2a000b450440750b001a1810b0070064840350034804440c107515201c0070803e2000120b404001202000b215074658482155040d44d00c800925014000307400580e000c100107644d410207815503a01a028280039103c007600c400c0d06003861555102c1040100600403604030362940010381007014a001a10b07665032260364045a001c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 651371492 1250 651370242 651370253
    0xf0d05030c01063030020c0111060105090c030402030708061504060605031902030c0d0212100503060403052a0f0c120a02090a090f0b24060406020615220207 69
    0x70b004031070021480c02c40e215800707407000041d02914031980400300306103440740e200940d0100c0e10040840c0b04500360f020601d04049a0100700b01d0b034240d1f1f003600c42d41d4211400c485559580c06090161325000407a0002140c0300030042c001565015100030b08686800d902c0d80f42c1d41d82842002e030350341500342401e4000c0d501146018000e0801600d118688142035227410382c0446042c0d1048440c0ca1300165000000c80d640e02612401c030342600202620543d6122082c407090070200070700f100c00002030701c2002000b00e803901c0e0120300c503030103940c06030341307031400d21007011240d023860046210040740540c000c2c081d4003900d20b0140203801030000b22802a0658000980500aa241caa07035801d03201504400d50600059a58002a540018101034009100400c510300301305a1a00c10001603c0c0441200410050351854290f241d0060013220112168014a10610005015074002c410158000400181003031910708120303410b64200601440e030301c03608031100070b20000c05816982c2e040c03034001840106010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 651372742 1250 651371492 651371519
    0x515190f150f08041b1d01092a030603060e0a02030706210e0a0c0b0c1002040e0c090406030b3103020c12280506160503060f0d05030c0106 61
    0x341101d50100034503140c01008094990500031401804807100110f001c0c444586440d00f407590064220300ba0f0346859030015041d103101c02908101020002c00007040b0300501b80115401c60710000451210030f00308601504001d54100e9654041699610000000c900140a03110f120400c55002e081c010105006041c1030960341d81214042c0b181c0310718001c078003880d04c103401d40185103031440004282c00701d003600c2d504196604ca0064462200020041480004000102500402d48048418580760300003030200780e000720320800c1100e1280f2400681c2c191407001c01801c094200074000214140c49545d030150154042c7c03040008140380d01c088141821583c80d01110070095002903500c928247e0750001e54070340300c14071158014100c201083c040e42c441046142c00e40401d02e6001c0c00b0400c2800c2011101c0b10350b545013a9442c0c40790760040350140360103c0044d240400640d07260703440c55545009204512208111130382e004000010340c4404a00d080c005059031000710b80c0049021850b0502c050341c0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 651373992 1250 651372742 651372749
    0x30402040e0c01140906070c0b0c100c020a15090b0c03070e01030635010f0f0f0c14211305061b07230a030903030906090503030d0515190f 61
    0x50b400a6a00c1c002d070380e008401e8109444003200303440d540d165081d000c1041c0d8052000014414403040b0390114036179014601074201c402060f0101e80d81168a590070605980d4040715000150b0071000700d410214000201803013030300c85840d1011905007500d5a840342040303000c80712f0041c3c003040032080c800d5150303100d000204004001d103002d0246905101003085040c16580110305d4151001c1683c40d0807109084585a4000c2200c0c02000480e00c94844680600052803181c946140341540300c5030800024804c10043d030540c0d030b4a1404071080c05802d40011380c092402c1d0544000c0080c03150f2031080b00256464800c80048440881c102290b140c5039103401c00192015440c3c40b41d8444005900c0540e006407084950010045e1081040b80c11017040403045502824405006803c04141807580081461084a229a40c1c0002140e550801110074100601401d82d140d0410070074000c50040a41020f0340128103003200c0940803e0010002d1200c0803505143c40400071035101c10041c200c110705050006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 651375242 1250 651373992 651374021
    0x12100e0a05010501260a0207021f11070e01080613060204081e01060f0b0f0a03062409050a0515071506030b070306060509091810051504230412030e06010b03040204 72
    0x5a1700a0310035404881c400815401c0d906038040341d5003042d0b44d1050031400442e040c0d0b12000c0f0f00680a00e070004c5c00e00d10810451110340c410003c0c0000c8002c00bc4e001c02c0d0403182180301414882d103801a103140340c480352440075201690203000204210b0303418800c10b24000c41d443c040c2038182103203528240c01d55205600240c0801c800c0d0400700503984088086a081c1513098100c42d13580d040b803035400d800401542d084401420a0803000080240ca080580e01ca855a5a1070340d1a400f03035a00308101404047c2d005080d006a00a03485440c402815030160001c01c0c401c10030003090135201c07810034040710215401983e80d004420203200e0a25018810354000c0c001d646051460142c080011482005000e03002821021841c482024021300c10f100041c0b800d90b004005001c40c4c10554020041c0c20102104607105d103140c0704070100796080d0070000c400c0180b501a03c5281d1640c0306e8039600da41c0500b0008407030a01d921200900c81810090242e24080e180700030042d500da06050040c4070441f40c0300a81804d6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 651376492 1250 651375242 651375287
    0x7180611160f03020120010507050904050f04111002030d050a09020901290304150c11070f030c171c0f0818060a050a02090a09050702120a0512100e0a05010501 70
    0x4284648001d51040c3d030380a0900c51001d90701e51001e1100075072440c16101e11546044244040d0690100042805100496003032295890b01c1d10704d241150000e0b40c00a00c03152211050141504000907071412031441401505d08040c1d200c0c540b84150b0300200d420310452503950306034004510380890303030303034094056440502d1a803488801410f882289800250050000c0400042c040180e0581d44039401c116481c0280070481e080000540350014094400c1c085008110010620341111803401040325000041d0392010380c40c0c060a402ea281c0d000e05174103050b018910386140d185a03149284000b04249540d90400428a22001000700002408010607010854504000000001225900030780c1c1c0b40380000700d5443d240003180091060311300b01070704103c12080011303c60b425070380800c0c85601c0315000d644107508550b030500e202c0c1c4150310500c808110144160701192840345002a8000c08030791010425603120000c00014001c1254a1000c032074450b4014017265074030058003100806210301020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 651377742 1250 651376492 651376499
    0x3030903030c0702040204030f150c0c050613030e0a0806240105090108060303042606071115100902040312030b010908102a0903060b190501080718061116 68
    0x10389030310014108006412000c20102d00795920b0341e04640055600c00400c0340b00c000145002ca00d1046004101074006140902c03245401e03018880e80ca6105a02002915642d51081150f440740c0010140039010450340d05e00020481d240c2c69000b0010341003d0000b40002d207071a0402aa1401c440f850803450764080401500c240e0b600142640e40404090800304615502c0b000400c0c694003541d48038040803140160034005240b01c81c54460a40300b454000d031007513603554082c240c0d80c0e2035003040300b10700e40c0e404451034545804040b034249411854500f0001800c0d551061680d080c0d0700507401c2a0303400400d40701c01d1440c10707405200301141d40c4002c1c20413001032494540401d4403203110300400000c2d5906c41c1c7c2011031041254146148404008004d52082410310f8001485401c10b40000c540a82c54203008441c0e62500c00c10f15040000c0c000682d0398001c1c203290044559441c00340405c424088070000410300b2000070504200941416a40e001010001ca014030b4503141000889080ca80c0c2c80c0181807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 651378992 1250 651377742 651377761
    0x712060f1511120a0e030f060631020a0e0306070e01120c050403230d03021926010305061509010311041e0204030b0a1109220b040603050303180303 65
    0x90355501c280742041006040301450031420305000205040b000180024030210403074110f440320103504800c3d000c41380310750348603481c440d076801041c0c440d90380c00000c5981407103202e0240110182040380300c0c2d0520002445500380d21041e0f0b0800c0100c0c1c4003080700340100450508003000503d50100c0d1504d08441c4840050001801926902d11f80340b010075101c1a003d8810380c026400c942c000c50388410182200700c1c03075078101d8016200031901d01185000d4082c08598552081c001d1740c0f1901c03030300c060064010780c1d591810380300020990040d00002d000d0340c419808580c0315101960085005002410312031920540750305101d5480c031315140c8105d44a800520200e40f07134280c200f51040c0e00b65000200049820805010034080e8041881050300008020040044165615005003c2003500b0300c10f122032142c05100500070300b1649034104c1c1d61894694646121140d41038202800550002040d80354400400c06850f15504166030322351001042c070620070549400b00c4d51041098000c1e50843c100510350 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 651380242 1250 651378992 651379019
    0xf03210f050603010b0f09090705060d0c0e0108010b340c030b160c061805060118050a060e1302060f0a080103050d0203071e0503040f08011a0a0612051005090712060f 73
    0x246d80146000e4001402c00c500400090010f02001405191224008450358000d44058120080061415001c0c400d055000781d00660517554a0b10803903041400518141030000f60280c24265815544882080c3d50b0f020038100c01c5100b40070341c414010082c1581404845504060000312580d580406038580c080e50081d200344c00030741e00203400b05240d1700140c1505403034002c0c1e10300a04140a90000062490074102641d1000324240c04207002941d1001d0740c4600300c402610494207075100b1000019030301041c0840072030003d13200808460404038420b0320b1110a800040c13001010559000061041c000100001981c0b9a41840107502d401015524001e040039403001840f0200002c3c03000e102008401d00584016080300c01132034541640c0c0d029140d01070400482d003d8040e030343c0c154401e00f15043c03468520003620b489031102052000c0340344640d801804010f1500707203600c3c0c03540350105082c0d607000ba095014a07410b55402845203000c48102c01228605d62066400c18041c1008000f0522900315 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 651381492 1250 651380242 651380269
    0x90e0f031c020d0f110d05010621020307091a074b080a09061b0803010501120f091211030301051003020c0a0f08190302030f040f03210f050603010b 65
    0x81c0941c9070b9075208441030151143c440340d140380c03605092004400290302000f9050800b0407007001e2042d80d07a200401c0d00c0d640503050070001050040120301c2c60802190b0000c6411031001d140480a0f030f42d9404400d0252b50207103d0030500e400700058088144048040c00c141c04405241e11181c5d25012a4a81c1d400c0d10401c0020707064207c4c800420603011440c85003001c4805400070340d243d5541422000023800030001d8002c15000c241c2c40c40c0104142840304c5820490b160380300440601d182d007018010b4461010702001580c045480703100a10403e4208e00921240c980b00d10b4100c280c01030f5268025040340c8180c151601140d00520042040759500140503102c403c29080050b030b10031840c0400c45c14582d078908003802150102904034100007410004040600c0781c034140d2220291907140481c140c3c07005903810384441030982c0208000c0f8030381e4180700c003040e88a400c00d210551480f90070040707402c0481c800000c641d076444640f00090092030080343c1d40041c08900030043c1c010024005043c40385100c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 651382742 1250 651381492 651381547
    0x2401170f0c240c01050601030c11070303140f130e180a030c030504030812040b1303021e031207022103070c0f11120a05010c020a0206120703060f090e0f03 68
    0x42c41d4031450401000c1d059482d800e40302080350b5450410107014040c14040e90100c1c0001d03c2c3c81100c1e440c151103400e2450200a4900242014518644003103078042e040f4040c3c11082d1030100080c10100c0401401091040803e03007a00c00c400d807400c040701030025001400d480e1041e0580710401040c0b807001c10ba80c04c00c160b05082c00600c035560ba04080780e05000780e400082040c0c000140300040c540821100e54400c0b8440c001c1c4d84855520008007142c0d0b11240e290003070250344503a404c42200340341c4c0c58401215040305800c0302d0400b9410006646508810f8580e503003d40c00c042c080407854044106000b2030004880d9980e407071410007042c014002c0044078005004401e0642038103040010004000c00a41c0000f001c1240301d09410081b16112042800221119031a003e5081c1002d0300101d40784411580050440e0300f080100302d61042080d80c0180800c080607a00c000c0070030380e203050b5105080034103221000014014014800320b4502800300d144010903034003d0106c07029880c602c801d403004810380d62 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 651383992 1250 651382742 651382759
    0x90f01180b060c1b151b03070605100806070f050412030306050402030c0a080f070e0d0312050f0103051b10050a02010b1e030607110a142401170f0c 65
    0x203200d210001c00c80051800d500c60b00c0051071902040c000500900d03118641c000d085000000030080110850300000003c15500040c4095040c1400083d10f40f00c2d04040074080e40d00e0084599a040121281202e402d03101c400000e00a2100307110030840c2c03c2d404074050905282414400c1c5000c0c1003030183e803240490036003030f0920b44000c05101ea0000b6004007000740c015516400c00c1e40c450b50700d5800c0110648005011500090240002c1e010350034000e100c50b03101d1100e843d2401090156646401d02d00b6401d000848007414983d580174400c05100e201c1040d5503c035254118517141d41810040e1041d0003410f540078124040c2a5901000c0c0c00c02625035007440783e560f69544205a02502d0101480d030380c0101d038021402107440e000207a1401800d03003103040c0c0d0301d20750310000b05480d09420200000d0040c2d110140c0907000a000d000d01c048200d106104035500403881c110300c2d902c20321002844060f028050801040100004a04001c580305000007611240d0082e10270b50f5030311040c03004018031801c0d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 651385242 1250 651383992 651384029
    0x15270c05040902011707020105070e030109120c0c030b1003020906060a1d0103230627130606170d0909060311190503061311010311090904082208010506090f01 70
    0x603200405d5150f1010690740600d18003100b0180c02014100c804201150b5240031407459450184030b000500b65000c40d19180030015203600f01d808030200c0204503218501d0782c4002c00841d20100da250721841d004c0c40e5030700e60700d800d51052000b001000b61005024040c00c2c0103624149402c01202c0c2e42e5540000d440801d200a401c004801030306401d0a5500280341800c034041b80b601c169803900d40b155106982140c18201c00320315190b0081040d00b010f03058402e0310404079030708018041141c40300381d00804002c00c409403100c1c44e0400e4041000c0c0c0300d45880e400719200c10141601702401c1001060501c6c010808a455615003100410344080702910410345241e007901d00075003c00904d005404003408643d518500500d06205ca14034140c0103541c0c2c0500b00070031685540c42401a201621201e828050400003540c041c800c034404040d0041f6100740050050100e00440e030300c803110340411305003261441285080d90310740c212100030b01043e0040c4406410441c0f8540c8010348281154020340190200006e0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 651386492 1250 651385242 651385247
    0x51204061109130504050c030d0813050307080307021f0e07050f030712080301030311211b1009061505090705070c050a0306060e0a0b100507060915270c0504090201 72
    0x2c0c6400c0300c0d9010804095800840032a81d100038800c9224070100c0303060380300c850201030b43c0f02c2103201d0000000d41400009202c14454200c80381c4424401c10889080001c00e59907400c11390021130701c040042e400078003041c03400f80d10442c0401406104501c10812041610b41a41c5c8400050094034025050b108104071240c50030441c2c0d400815001410b040f00c1d0300b1500d0400d0081e8001c0c407040e000130fa07000c00c0000b400003011949800300c0046000480c0165000c800309180c5410150a060100181c22410005103400f40a80c045a281040f80054603100a213418400c988150000e44905d010400050000340c9038210703207642154103405c105450b12a545000c01c0440d200303401482d00710204100000402105070030031400c1e03c02040345406503558000205040b201c3c0d0180c003a80c081d08014403940c1c850300400081c43c0309801000d001c11150850340369074022005640c0384034040c1c0c0c0d0711303018029108035000741e200c10050540810111801291600a00340b19103018042c401c590f01da15202c116030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 651387742 1250 651386492 651386497
    0xf0507110309040b06040b03041202060a15060f051201061808030310120c150806040b010f09062109051b0a06090b030601120e0604020901051c080a021e010b040c0512040611 76
    0x2040107c81a901c0c603062034480308a800b85001c80380540300e01030200707152845034058050106081c01d00786810f107142c4841210030344203500864007801020840f0700c0a403504040f405001e0310558441103a205031074000180104415440300025070000c0c42889040080c60701410111000d520b0364021180c102d003005418040f15034449141d81461011188002e40c00c0841e1500c80ca5040b03d08002c415500001560301d40d005032480740010788a84403d018080c05800c511a911106855804440745941090000c84020080c00c0d504e551000d0511020034604400040c0030308800d03540d41100300e1030401c000d8a54a130b0b42c020382100342804000030b906644038982864820340803520500c40030000004d015160142075409074090701c00e0500100d100d0400d481203044061311890b500c80000030b5911444040e0300081c5000b0114010360b0350307425205610f40c60b82c4d002e80381c1001c000510705d1155000c001c120f4480100c40f00522000780100201440180308150740190041808500c8a0080b844c400c0b8a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 651388992 1250 651387742 651387749
    0x30609090705030703050a03030605040c02030d09210e041515031a1e0a08030c100e0a080f030106030507020a030507120c080d06030614040b0103030c03090510030f0507110309040b0604 81
    0x62243e03031390000034418006140098140640c80c20044c2d0344e114818802605c00e074150003005603108102c1c12a02c00000d91018050b507008041204800401c1d003103203d020b0b000d50139814009010404180c90034076140c4500f403008d41c980b01d0506005403504030316028442d08c2e0710001043c19510a00c0d80760a5514142c03803000c10100a02c3c08000e101b010b012001030025210300309004240789540440e41c41000402c4a1007444004020704010740c1d00e81440d4080d00086c83c03902030038024884103200041e01c4201806d158030f1400d01443d143d60401071b000f0304540e0010096004c651000000c10003003a0000103c070345031031b085021901c030341c0c041102c203444c032801d02e0754010034183c0000f54040c003086243c0e120400f601d00c201010b11141c2c4154600c0c0000709420781c5d001c0d2200b01850010000680a052855400e41c80b07801c0020030780365140001841500600c1c451400300340c4442c4400d0940419102d4107a02c9809824006c040f00400041e8554a00620142d00e02072076a4410042c1c2e6a560071003500e004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 651390242 1250 651388992 651388999
    0xa020307120903061d06010b1c110901080a0908120c12090319030b1f0c05030c03031005030a0c09110702040e010905070b180402030406020c0307030810080f03030609090705 76
    0x518001c03a0340180031091a10064844030314284001108060361800307019043d000c2c81c002e0103242d0030080ea0342403c1c0d0090300c600c2e40f0300c0001c440c840c4864032386000380d0740e0b143c01c0c0c0e403841c54540f010b80002600c03203e4000e2032000130f249058048000104041c1c140c40070000d8041d44008144d071000d0000c0708070700c82c0c1040030f00060100020011000c6001008100d42200720140b803d40c42c080c8a010740598859032030f2a42d00c07191442090403680101c1035024900c90035450a500405141d80394942142d0260701103c41c59000001003081c51501418440010141a0300501e00c84400c5e884808600e50b480c010b003c1aa519000c00d00d0442c07110106588102d90000d00400900b8400070700b050003400c07070300001c0321f490088200000f40a21054191206640030740b00d6068100820720404c03000350b0004008445059081c49618003000040014020246c0710f40c682660a051036100751031544d580d540f04036402c0d40f0095148200c05400b1003525000798041c0c403134801903103a4200e2941002c0301e0740c218513007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 651391492 1250 651390242 651390263
    0x5190306081c020f150103080903010b09010906050411120403030527010e06060607021f0210050f07020c0f010c11131e23012303160501140702150a020307 68
    0xb4010344445500848040340d000c40794003103c076030200354468030325003001d000e0040220010400b180307120b0000d24100e2401400000c0d1480b041002139417589003a000081511381e01d034410300c100d0034240f1880e80701d85e1803900ea507130411641c1016201510402400101007645400114810050203040b00b40d1007802805004130207540c2542040c002c0950010740342d40380c840c14002c40ca41e400c01030205c415035500035003002451421114844000211b491901d0704601c1922010600e0449a20846024410141c4080744038100742d440203141019498851b8800c12010900e907000c0d80c1c00220001140d0b60000c2404a00c404410004070609141e215400a60f803d200082203030000e82a00009100f40050040000142080030409011032132106c040590b802400144610b078500070158840c2040700f0b0b001001100b003000480c0c1081e6248030501e441007400032041c4103643e00800e00084c0c0748007803400700d41020a560002012107a10001000c610100001d01c41c01003407007071048401c4143c004100c1c80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 651392742 1250 651391492 651391513
    0x120f05071805011a0301121a0c0a0e010207050919110a0207360513200102070e250212120f010b0a020705130f0e010c11030403030519030608 62
    0x410501245a241c0824038110011420406402e03603080026005910076065a00300148140350101c14481500c0000759180504e42c1200141e5030540300380c00c0034180c02d40b116503280020300b4201c001d0b61501e0540d0419541400780303440301c80384e050307018099080000050040030100e2000b010301c00c000008428000400720348854000400c102214128030f220340b60822800032688a00a0840c82d1a000d011404490036904146822240c3c0105900b41156081310081c0e0742c500718007804081e1582c4041c600280b4680640e0188595002000300706004d00113450400045050704880c0206440340300c610550ba10201482082075500c40702202605070b50f40e104030100d0052a039800c4840240b083c80c803500205141507548103441c1400d0840c0c0042c0b00f01800d150820074405500891b04203401d5072441d45005500c0d183c080c01a2142d02c00000180e2907505410090280d905c250703440d0f6403584100001c00020ba0700400b225154502d6195401404c40240c40c228040e00b40790303000013a544151417125 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 651393992 1250 651392742 651392759
    0xd0b150711030a12030504020111150f010f060507060203071b05030c0c06090f090c0d09080309070b0f19030f0c0e100305130f05031306051903020403080301120f0507 73
    0xa0030520300400804040d940c1d00307410583da4140034000200308803040811007000b00e000750481e0f42c0003841410406a070340703142c4001d2890209507524441080c0403880034000c1c004020034009000d0b00f401c100e0200417906010020f4054420140c0007007803164004005002c46214a450003000400e10741d4010b1103018a04009650303070041d40003850940500c80c1d00f1126450508102d0b80c007620050201b0b202c0134069003c200c040440100f544400d29401c020b00c60f03032001d0345e102c4c2003843d41c840c400c1151242050808189004100d4116800d0b540c010003e4074003130302a1409480c1000c2060210f944d6004a003402240540800d4080300c0105041a450b81840c54110207500040321060381c80240c0100b060344120140c030b4055603503844c490704084030140845c0c4a0a030f901040ca0040c0c044a1900d1a240b0140040107020f5000b440041c80100d40b001c01828248060f407000755180c0b505509040c15902c0307446d10b52006206021018102c442c001c0100b00f02250208503094028098030002d03a683c1e07250 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 651395242 1250 651393992 651393997
    0x1027020f0a020a03020c0f010801030f05010905120d0b0d0b04140a061d06062d040b031005010503070605120601200d0815030f0d050714011503020109080f0d050d0b15 73
    0x4030017500861907090490b083c040030010543e08140d4501070b1a0b469604c900d06100c42d411400d446554035a4507180c0410410400b0400b9002d05411255031621040d41200843d20f200f1341103842001140f00c140045000b04070341e60f80283c2c0015002c01602040c500181c81c040b41d030140244403d080ca4503900e00c149607050091042e6400400742c07070702641d0b50f07802c0100d011101200c4540782244020742c410769003241e42ca80da800e40801b800008204032183c0000346000d0300c00d407a0414654984005028a007014031944005048600f407060804068032039644c8468401400a8108822141d16001002991820600c1d641c0c6280644514002d03034107008040744000c071412400e442c00444842100c2c1800180d480d01100c5181c003410b41158018000c031403583c840003066500014585407035504080038840c00c510341103691600300b526851880090101c0d4401da0011083e504000f400c12140f0001089454082c00180b170b0003a91142d8401200004041c450041d42e04205454011003201c03645800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 651396492 1250 651395242 651395263
    0x209131703240d030807020a0206040b0409060602060c2b090b061026060409020907030204090f051e07050f04230306070f050315090910051027020f0a02 67
    0x200c15050b54040c20240c1c203500ea0007241c1e16041581c00b2100000b02c1e101d070860f190041014410740340111820340016041d0b070001e0300401255100004c0c00c001703c0d007151141000070b000c43d00151185282c62065406a07009400421000826a5003098900c010880d0301c0711301c102400d8002c10070048035050480c0460003c9820358011a40003140310003090040e0740d0303019240c2d65810f035040d458083c611150000c080c041d040c2600075454121900050740c50408a510038031540d50300580342d518142c0c0c0ca2050380e040400c044201c030314141c18401c0207040500a45420440342035200140d4540200485c0c00d4031440e8240d02d0402d101240c0456803601100384c01301c010b2850059540030b000018105500d6000980f248000b01e50f616625107c0c850140300070350b5001c8034500c0c25900b10700d8044080b070b404d62021102e94000d500904400c1118041074803803190003a080308140545542020180b91100741c007024000d42e8aa40310f801d01c0100b050a03011508044044120302d615a10040000b0b50707581d440d800c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 651397742 1250 651396492 651396511
    0x110a09090609061d0703031d040e06151813020d021c021212031b0d060306060617060f0d050319020c01020d110706030b060c16050f1c0209131703 64
    0x2104001403090a0361600101350051000c0e0a1151841c3e80a44120354200501e507006070b00001140900d42d00c40c419a03003c903448001030f003218640785160700462014068058401c04480002c6802070310488465607000020f1800414800e0142c0000f0310ac811076807400951042d04044048020480f190040c2c440c14400c3d64071035008184170300425101c1c3c0310f61622900c0d02505000141071202c03164800c218800a144006107015001d80c0b40c6002d175070054005442e12a01e03450104226540840c00013180081103001e0303442410244005440d042c07000814a105503440ca0000d130074440240b040b210551184003440e1100c1a08050103901c5120100a681c051f00a403400c400c9464000d0340c074038a020b1803460180c9001400c0c079509500801c0400c090070b8102c541409606d66029040008021000b011026519098a800200800d444035290654051005004541c081d01c00310841c00d5007495045502c100680d9402c0c0c040540304589003809041d1811a6008403100080c14000754010281d45 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 651398992 1250 651397742 651397751
    0x31409030418110a0c14010501060519051201180f1a030c0a080c0d0305040315060305070b04050303030103110d080307120501050d08030a1508010f0e06061c110a0909060906 76
    0x400d10011070b001c0b0340e101c00302c1d0f05040040340c010070711680303620800d24451003022010b10305181000e421168241c000b540440d00005044080c240ce266421501c0101c52920620b441c03002c20b00d8407501c0700184078100444001c03280401c0c0c03c0c40c4581020038500010301c400c1045602c80743d465004c03060000c9046010f0b004103001d41c041420183d9042c0107542c01c400c010010b4091100c2800030300b0385001300903000c0010600002c00043c900c4030b6040151100c4040120b515402c5003006030411a042d4441c4190b500e04000401c501e07103002c001e89044982001441400600000c007142040e4201c800051513400000b04114005401c4070b00c040c0d01014110f0200400e0f070300c4805200d9012000315018000b1002400000c0712900b050300310215030441960041c40c1a40c1d01d80b40070342940e0807040220481c64a918500250400030845c1c01d038005022500c030035660b14444c1d400b402d4006182000781c85001e10b9054600030b03031100b0040c80d0003410815400c02450803281880f4008108054003161400d041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 651400242 1250 651398992 651399029
    0x1b0d06051804020904080f1b0604020a061e050702040b09010602031b0304050105040b1b0609100e011104030f0f050a0b01140306060108070c0c030203071e09051b09010314090304 78
    0x7101c1a2446903901510400c042d4542e070712600b809412109404812078410051a514485440001101d02c0648070003000242803074410000503040c26001641040500103003001c04241402d801100c18805081c2155145000e00105000e4a02e20000c0c5821084080c00002c04590003c0101410415800000070a4400500c56030310b078851845841d0004a091200b486403645050007015012218840a8520a80f54405500340b41d400c45c1c1101041d0030030010041c2d40c840710f0181d003803d45580c10003044140845441c000407402240400f40c42006045482d400b04403201c45050071098000003124a005600d152980d0075540074090b002c035075040303103a01601d58100000c0352402044161034040541d500e40e01d08844410300310b20140e0342c00b04200b03400400750b201844420044c16200046801940c2c84001d80d210724141035001900c49442c02c010800100d401c110050368809180c10b000e5541d00c141c40c0102e01074249100441c0c0140000e8061003201c2c00000010b004640d0f040440100d060030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 651401492 1250 651400242 651400279
    0x11150708032809020f010f110109060c0f05040e0f040203031b1b0319030e04060902041d13030806040c0e03010e0109061803080109020f04030813080717030d051b0d0605 74
    0x543c100250403408100b03c81720b503580a1100242a54848d250050808024207170300c85c00e66200030019076841380e44401c840c0501e50300654010240d1950b0500c18902031a000c6542d4020742c0040c0400300388004e2002103402c543d070920490f4001d4a6180f076801240308044509a21061540c0509020300c003002642d03604d03414040341c0720760102440030012128140307541f401d8807020104520070390b20554524002c00c0004091014102510740d0240502d44a404040a00401070004e4070454841c11400301c0c850009600486084c2c0c400c20546010612040e00c40c410340e9002d003a41402c85d030650800c20418900c410540c800700f80603010320403d102c099148070121000d4095002d024000890100050105003090380007894500003041d600f51810b580ea84486519800c410410b8440340382c542010003804404200c80780c064204882c100c4a01ca030040d0429543c0e1042d02c020203040b0791200c1c005007068031401d081c980240d04140c1c0e0103070b440e40480c02c0c1c032000740000d0092078031a00403145131500020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 651402742 1250 651401492 651401501
    0x9060a081504080c12091305090d030c03021905030f100b0403170904240503030f07031107080d0c030305160c031b0c090902090f04111507080328 64
    0x400410160100084460005800510003002640c62540c20007203400040d908200456400c6191710904d9280c40c0c0e00d81c108140c010041e007205141c01c0c180b20a00c00d03001000700d107000203140706040018030500d00b54402e8019004c3c041040901c404e40b01031801910b6048401180b20b503004116040595407100110043c4a145005000008030140002d000145a51090002d1b00300208861400c002503c40041c080c2d5000d480c02c440c0c4204070294000a1b50b61107030b105000b0303000c210003075400c0c40724070000002c0500482a003e000c0140c01d60a1500d4000b0902400029050100940b00302100308000984009003c0714210300003450040003c40d510180040f614421034681d03184c84040c140c41d20120380d82c20981d00401040d401040d0200002070395640e5280007801c0d095000b02c0c0600043c0100a40100010400d00d400c1a401c0104000a0300b00401290034900c12901200e258402511800d0a405094401040312400100340954000742c4282905207200b441405521210b1100700c070010358 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 651403992 1250 651402742 651402749
    0x303050415090f1404020c0601061e110a200307090b030c010e0a090908042c0f0f011e03060513050706050406050315040902060a0804021e06041809050d080609060a 72
    0x40d039030070084c0041032402044018460b0000c10140c00c2003000d4a141d42040000e90050004c2504d2940844050544410f003a00750361243c18000c000304044034502e40c40b03030f04a0b00002d160603011041d50811064840c00e00c00c09440c050106d5070313a19210b125841c01059601802d5101c4d20441102d25500e41c4070749071524a2103c040c0010190320300c0d1418040140c019008102c50302e207418000469001000c4000e140600a440c01105840d41c0916080d0002c0c2d001402c00f4801d4511102045280385030b004840c2d04440f0360803140255107203640c8011031900820b0f0401000035003001c06005081a084000814590140d020355045a0f560300e0251001d1080c0c1c0701d404086034040c400102514640c12010308030030005800403490950680c005174032940040d000d40c0100366020144000e5040032448201c404100448020043e2101000503d440c0200d00c0f40030307200c0d07007a019101c0a10b40140c0000540d540d2120071078044000d0900c0141c1012011150f2074080c800c800001072031031a140e4810801c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 651405242 1250 651403992 651404009
    0x207061b0f030e031e09010e10050418020412021201020405060403080712020c0d06050405160b0a0801140d0204020c12070804080d05030c040e071727073b01030305041509 75
    0x340ca4601641c20036410803a00b81f0705204106510411540310f41d81c840c081040076945095869060015001221140280c1c2c0c900b0b00380306020078016501e480403481c42d4260101c4050904401a00140b4064400d40d0080c0340c200c080881c001040050040c0541007080c440c01c0c445014a00081c01282d991100c80d0541e58041c1d2101d401070007042c6190f00c90707900301c0c3c00350064610100703120441c0c0d90500015030141c2e0090800141ea00f0a06030301005d814058180802d00c04010400d400000b4000c2440d450080d1145900207040c07681c450b01000303212290480781440903211426030501d903035640c01c039119541c12070244041e0060000e20420440c1d12494407008200e05250800b21115408940208088103100e44e100a1122440d0403071700c824400c90842405043c4808001c0503c41d54521403504010075601c0040103102c80c0c040c0c902016912982011a58240e62040000359241b100901a010f0108103480022061560080050060340c040034030052101ca41014202d50308152403140055 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 651406492 1250 651405242 651405277
    0x3060306060d060f290103050c03180f1209090108030405130b010e21070506071203051012060506010f0e0a05010806030c03030c010903090b0a02060a0207061b0f030e03 74
    0x6151401d01807a5406502401e00001d040740d00c1d9600008450340d104a61000382c5c8040040181c12a144008242800c0c0a107400d01144c10100581c801034000a0802d140b090000c58640e032201c0402c014050811740d82d175040324402c07003801c241c03011280c0c401184103001e19900e00c00070860000000c103c4040382c4001d00b0100031448101c416800418081c0103690401c210072401d004559a000d1002e0300350024080600703800705103140e105140002d01e03400b1a000707400511144020800340c0c14101550407040c2808911b568481c08065070300d8005812070540740f040c03080d440d000e00100381c3c8594402c91080c2c039403502070a80f03184161800500711319060341c03004641c04140304552007004565001a009800c4400300540d040000c0c0c1903400c05924104282e565881140c140b55219010f00c000f4800060210b1414001600003520b45000500041c07445400090500811034160700c62a00404024503c1462800980d00101554251192080003e090030f042d010500004404c803505844801000d40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 651407742 1250 651406492 651406501
    0x12050d020d09050f040618050901050a0b0306060609041b02060907050f031c090f03140d1412090c040c0305090d11150415050408120c0a090308070c150e030708010203060306 76
    0x181a500044c0c140c0c00c03136203d05002502d9121185105000b400e03081c0c000c00d0610b0f00811403400c41303c000b444600160308002450403544c038041261600710710f081e1145c1c2c1c2d0322074911000c100500443d050380c0c2c065074a245488901e05a000c82c1030750181075407809a4805603690800c0090a80c00c40f90b040c1e50503000182001200d62061142c12600704280c00d044800741c6d61b0b01c501c1c1540c80d90603401545c103c90300814400d034080e0107001d0007201c00352a00309621841407074504041c60307014840c9a409003020280100712481410848100c5403c4010000d0181c41e01e2080002d010340300c03d40e044603480c820089071a0185000741d05400c402554040280440b4000c81d903101c9008030301800c10b450800d0088040503c40d00c5502500384101d0207540c4140d610130744000403d885410042c88088801402d000032401d565002100fa004c036500008034640761110750070300b080d40c1c04003944103204441c0200c03280400607400120005003150110151200d560b5126000d07804c1c1e210450710980c1c10303005900008e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 651408992 1250 651407742 651407749
    0x180b271606110c060415030608030a0801032d030e10080103080a03150f0f06021b30010e0106171506060a0c06020703051e1204030807020c03010612050d020d0905 71
    0x2c0c0010a050b0048400c44000100800c43c182c1c03141d081001c5000c1c00806944407a034040c00f41000405c80c250003146000200c500c000c0181c041804010b2581c01010444600782a4016034841e103150000381e485100c810030f20b0050071003190707031001d42c1c06458100404400e0b58012440d440c100c0b0741284d80d461812104200481c01450840c90794550420055000b01c1c03240180046100642940801e4045650500801074600380c0c0c9034925030096841400c4040701901c80c420607480e020042c2c40d151602420a64a5401e05480a1030f0101e8075860949098811079054004808a64a2400c41501b0104007900c4ca078444000c1c00075003c03250000700118a203400c0c00c100520300200030340b500b40ea00030071030f40d50328041c0d81c800340040c0e0005801040c1011078000c1c0c610181c181003810103074145060500702d280c404829000f40003a04bc062040005282d081c000c1c0103000404e40000c008000c0b25484014540c030030083c011054403d0f04c52846019810b50001407421801060382c0c031551015032501040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 651410242 1250 651408992 651409007
    0x1403060c03100f031203060509070e060a120203100504050c0705030909181506040f0b0d031413230307031a04080706050f0403020d0503100603180b271606 68
    0x510b05040c46407080040c2e030b1030a01981101441c800e020503e4945141000103081d50032070341046200302e21718400e1042d06900b1100a1a00000c2503c090352909a0554180c80e031035042e800d0450500d00000404c000368500c01c403074505a0718200c6040109885001100d042c90080d040001c00c40c0d0700400c4480134500d448941030b54009001040d140c8020305008415040800c14078007030f80000f0855090042920302405106025060b0805c02c000c400182800a040c00846890140c184521150030318410300718803044594200c502c0060f20b03103090b038600c8079881d18100410340c0b190074854001ca054140c80d0100300740d01103e0b00b040b688011075070407903d030107041c0d0400b800c01c45210004110301000101503004052051000c2a007184540c42d25040c007900f440307000c2e030304e07001002020030811005202075840841900e20030b10300014032103c45004223074403071460880980f2480015081142070700301d1448500c1a402d02002d56110440c14081c0700f90340d10309000700c1d5040913080d50814004140300d10070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 651411492 1250 651410242 651410251
    0x17030412030c030314011d0c161a070503060901030b060a031b06180506030c0a02010906051815160e0402120c1e07030c020603060d020d031206290c12120a061403060c03 74
    0x52351725246406141017040600c40310202c4001070080c89031010300d002600748662006131030800601d9840c222001a4017660140001040c000d17400300031407087d84900052002665001c00d20085c0f80004c045140380280103842401d00182060700e07928001d0701030000140c2184c070090070050568403081c000f0314040c1c00c0800c202e403c5650f102c640b44042800c1d802114003801345050306483d1880d1812801d802e18510180c035180c602c4400e01409200300743c607080c000b80515285030a0b40031506000c00500a44100300c411203901544006120680b100140200083c0c1500c00349081030480c0241c07000742d24002ca11010300801c0440c202403001d420000001d65200d00028200c1b00e181c0500e500140f545003c0c4102900020340c808205002d89080d0b11905015040f0040140444003030203a10103042105008105500e88011411000445040061000c101044410309403038400c1e14049074820081100c2980c0b0b200d081c010300041e82000d440c031007180e840700a0090300f031170b5483c034050b001c19910140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 651412742 1250 651411492 651411511
    0x60c0c0f0303070c0f0320010207061b0b0115080601020a0b010303211d1b150a090b0c010504020315041a150310050a050105030606060417030412030c030314011d 71
    0x400c43c00040c20741c0e88402e0292081c142080c103040c2c1142004e080e0302c116504420f603415008181c81c84203a800045820442e0081d18020400644072803880700390010b5441e00406071040c01c40045a00805880e807203010040c0369503195065500d07d8012640c0d40c102c40409401080701d41c0c014400300e8410134241840c54403850314810401d04490061040b00c0c84000a5900f00041c7c5030006100da10a00c01c40c0040840031008070a54050b1100041d011030710007003145031a42d40016001040d5000f03d4407035008040140c02940c5030410706003604d0181030200c41c200e04c01e01480d2100c55846140c50256401a070b0401200e42d840050071aa601f22488040d040c60780210502e00c20040c240e07020840307055803000b03000000c01d0354100095200195841038210500c03e4120404020703003912101c06442c12900c0043d4150860302c0d00c02046421032003a81c01c01d1919004010081050680003100480c2091103641c2c20442d0a40c0b83e080700c104050b0a000340d42022112000c090001c45c8140b000740d82040550 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 651413992 1250 651412742 651412747
    0x1020d050f06010c320102070209061516020f04020c07031b0b030a050a15080706090504060b030714211602060f060d02031005071e020a0203061819060e0c060c0c0f0303 74
    0x600b030329410642010320707200c17103070340002d459011400d00c418250340080c3c064800718103240e86010440520300620b03e140440306000300e50041036580700740c0300032440310024108550382d0030b06c0b111075600c03a1400d01013a00e04511540502e1607003682071440b081100c82a5102d01c0c2544c13610401c010207000080d103525102d50f11007189210400020035040c0041950000030481103141c400064044429988020b1280345030a0082140300805d01c12242c0c003241610380303d44900040e461075600c42c025050507500031084400c0c20140c0b0540c00c41b2403401032a0b0551904262400101c00700da4843e0125031804401c164440030070780030300304103e12210b050b1000301030b61182507155001c5000c0303c0c42160164001540c500000028440302c0862640070342c1c0e640301804070303480342d40c01080e95240060b04d140074402c0e0032501010030001c28810940007090941e1500c90704402c3e410075401503c0d20f0761035400c46004103080071007230746000c500b25183d0714800c8001c0e1280c01202000c00c1002c240390041c60790940002c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 651415242 1250 651413992 651414053
    0xf0a0308120f0f37021b0f03090f0a120605070e1c1509060212010302011b20041107050609100902180a02120c1207050f03040f030509100201020d050f06010c 69
    0x2902c00092402c034805001038540a5a806c4000038040b04041030700700e07030001c070241940d0400100840d100d080303080d920031010880a00210321404680e6001c3c4240310403c50b905010011a0f03005107019680c0ca40d070754041c01034190100810340c03031100725800d02c541d6000045400111003150400101219213800900110141c5900081e40e0001d6100e42c180460384006004560301701d0044104950000081504110390745d41d110b54210710600403500103400c0700000c00c0740d42c0d00c5400840760b40752000704a51701c6008600d802d580d610001c0d507640005010b8001c0c4c000111703015100d51106640c004040c42450181e60510010100d0f000e004007400b143c00b040010722680c000214940210005010710743c4c0d51951030118400640081c01c04801c0050400100f88807220807030680b600705411070051480740e031040c60309903800d100b40b1652a41004040905499054040d8003500035981110402d102e02e40c1e03544080406940f084a0a502161a000880c03021404ca1102d42160a8070505444101b444 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 651416492 1250 651415242 651415321
    0x106050313140c06130e0129030c0418090b0a0b030a06020304060b0a15020d02190210020a020901060c0606080708150702010b060d050a1802100e0f0a0308120f0f 71
    0x3c503100c0345c814400101c4040207103045c02c51640340104a05a0b40e0700101128100ea40591402500040d188a0000c004103100f4841242200e00801868140070840085440c50b800548140344054642910303a200140400c034540c0141c2c507603a03400501401d401602c42c0c0e5050025040a0f206543e05075480742603440c561070311790358a170185c031b60f0807460210900c0105000b440d05650425150440d000700c45002d100104c00c042c15401c81e607048400500350b030049036080b4542114881d020354002088000040d203c0d03000001100640d000380300a01015885042440e6100c489102e000ac1c2a400030308042e41c1003151b407448039000b040d42c0c070000c00c1e003a2030400024034942044000c1c1c0340d0a03540e58144079820000748681403040034043c50313498280743c06800154075248541c0900d014840304800c1d540960352210461428264010504810a52241802c803481d42101800e280e4100d60340011403070b142c2024595911450840c810401c0c15900c5112401540c070881c010782031904941c404030814080c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 651417742 1250 651416492 651416497
    0xf0903120806030d020312040212100f0e0c1e0d020604181a010201140f15040203041b0501360503010203090a0309050a24050702120d080106050313140c06 68
    0x82541da6080941c1451001c043c180780c1510781e40c0c070565004200000c41c01c2081250700e84d02a40444001001500c0207210900b040c01112820964030b14003582140c0d0411a81d001c15640c9032003c044078032010311103042c08600404034441d51203000318036032701d154a890044030702c034070b4988068a0a824566030769420300440425401448140b81c465502d80c20340c484020358000c1e00403003403000740400504052100d041800140c00e8503001c01300c0c074002902941200c1c0c088030b00c21402800440d920b180c00d041c09200902500d2002d14480c0c406900001c1d10361088014010407010225215020a6540403901e4034555a4400d07420040715004e0004040d5001e10255104406001c0540301008143c540102508129000720703220341d00102040c05011130410640303000008144800c004003c030714800765060300035038400130350202c080320070308103841000b10302c0c18019190f6031200130711070b602c0b41404d40b0140421182c107083c4840885c41c1c1030100307103034840c06010134804100b40e800f00c00c1d035a4082645503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 651418992 1250 651417742 651417773
    0x1615020f0715021f0605180f06090601023c01050910091133041202091e0709080105010603060b0f030712061403070915060c0302070e01090b0f010c0c060f0903 70
    0x2170f50313480041005080945408000c3c00140f1108005441c10803091304c000c13040606054014010a0300207215039000b080211041e1924804c103001d06403011001450319112a0340c0d900d0b14034000380b80c0e00c0380c26805004042c0100194805003000901c2038403148000c1400c407405803002c0408000325100b6498200b007104034030f5400401c0c0104007070b0442e00714000d00c2c1a10214615103c040108000c03c0c42c103003403842109541101c0d0b2203000d849185481408130f521181c04003007545001c06008940d41c0240c8103400316101d9500038801a80c0e00c0101390103c8180e841050840441007105000c5409800011507120b200303400c242081c010340804500840c1c1003070300101d6119609081d400041d1404004903401881d110b4801c0c001c4510f201c0b40014040001e00c5040184010080300e6020103009011800103041d041d560740c04c1d50340e0b4420401c0045c0410305401c600418100640d40c40c02c0d40f0422510641030b40141d0b420801501e002c1c011135084840000e0b40081261050000c80041c06808244082 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 651420242 1250 651418992 651419053
    0x9021c12050a0903150903110601050603220b09060f0f040b0705030403170a06050316051311120405010c0816140a0207030804030602030403030510150305040201030e1615020f071502 80
    0x6c050107450003814411120400345010f5011030010002c3d580c44804072540b05865100000d01d01043c1002080317590200c1c00010715a019039010884450000207142e8810f2403000d46840c1203847c1c868118044605c142d8001d070030850f030080003036200f501860042d81c00c40e101e450170840c4114410800d91240d0002d0b030794041c9194542100304040d107010020204001018002840000d00d01070008031030500903013030010702d20744031480c0c40304108200f02940d420ba010711043c0002c0b80303020b02c0c2050080c100b00206001265104022a12036640228610000006601c0344035051041000d071140c0e80d0002501d0341d003140304d260342c04400161140b0103480114480d4901503164101880c000c5d0940d4002040c01d104485284c40030030418038071188001e21a6924180080c03240c5582c001280a02448041021140305400e1141102d260981c1c0f600100e80a0950100b040800c0710380490b00c41030300c44403001e10380c6e0208078244481070000710189554641801122541a81c0030a140c0040450307100f102c0d003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 651421492 1250 651420242 651420251
    0xf0c0307080411091f09140a0c0e10080a050f07050702120705060c0f0601080303070c0b0a060b030c1c0c121a150315061e0313140109021c12050a090315 67
    0x60814100e0305000d80a10306d01801050300003903100e205440e0040c02c03203c0711915a0b151860650141704008481e00000d00191b801c9000150007500c00307181039617291082c0f86001f000801d040c50042e50a80504001c0d0f403040c3c0307001010f408010604110f411071003107a0207420070009040da101c200819013201d821014050500c92010340e203040c4a016481820160020000c024805c6e6010400081960f44440000010346030003078014010000c0da000f07120070b0040001404100c8185c00e000e003140070031840c20401c1e02c8410511680a55180b0410035000c104080200010780507150403215051a2400119401190000005103c18800c070489549000d0000c240010412030707011308103003a00e0644800d85048030030914142c500c88240000d10000c00040003107000300395916003400c001038102403603060b40e0304107184250003080e152000724440e0801051254420000c003084000094115101c202860040e50081c0c80c164080c0e415401000345510340400022000c005021008501900004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 651422742 1250 651421492 651421531
    0x1515030601080c0a050d031e091e050f12100c0806010216060f2d0503062b11060d05010303020d1b0c05191703120f0c030708041109 58
    0x14100003040c0c004420035044030309030948079140c440400701202c5007602e41140000c81800c08031252409a03800000b524405c1c41504007065006260074180e41c0c401101844808008500c00c0c0d42c040307544503042d007281c1d480c21400340700c2c0f43c0b00d00e0040081c00306006464440310180c802100310389610752700e200401e84039010b102a55038100500403001c1d204096500e841030420300080c2110b6500c880071002c208207011422003070b02c1c1806640000c0c044840c2a42c0f01a910484040c006800c2100c0d82402040b219900410100302441d422401e40d40301c854002181e01070340c8401c0b1402841c082c3e61500000708220000100c081d61107003070b000b94001e030b000e024144481040200051881c0d40300900c0d043c241c84150300407400e9044c20740d048a80031501c0310b000f20284d24440d00c640c142c84c0d00000c1c814040e610703110007014000c002420840350210320703441c19664035502c156892074141c4070002d010105100084840d401070f51804d130003500510b440b00e47c1c2405100000c0c084041150184029280030300646c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 651423992 1250 651422742 651422749
    0x509213001050a0308090607020f030d020109110409030905040e0102070f0c030201080609090606100e060a020708162403110c0d0e0102030c0d05130902030f040c050d02010504171515 80
    0x5030702514040781c0015641d0b15645803448240280e13807000c1d2150000140d050b08551324802a43d000c00f0014058a05221003d40c01a00030199401c040c0c82402040da0032001d285070500c12546866070684400e00850700301000d00c00140964a01e4146565081051401140034000c080d0000b510038521600322604600c0014540711028118030301510a280038000c5000010030703130300d0b0b11410580d001203c418031060120b0300210703074807103840e0854400510240341c25800b02c0c490b03080d610f51908846404c239070301500c404040b4051040e02c2409010303400210340342c11001140502c4000603d804038030030704856040c103c1c07944041c3d109002680511072071200107802250340d0002031b4003400694240440c00303441d0b580710442003c200302042030005440c0c1c0512000510700020b030181030000c645902e4065140c807100750b001d88040e24128401075000a182c5000707500000350310780c1031f03558070309192503d80560340e010302c2402c0401c501e000c5c40404032070801609a1461090784026690303018486180d061 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 651425242 1250 651423992 651424087
    0x1a0a020c03060c030411031515190e070825050c060a05060616020117150a0e0712050a09320102071205130e010e0406050a050921 57
    0x100341c02500050200182c415200d0203480c1d0058000721101d4840e5031303070340c0064200306500b84002c111200305001d0042e00b980c4006451000c00c03054400e100c030000ca20042809090042c03185100000b1800c0c00562003522480003030750081080840454048a2016210708140302d0780c0c85ca000151000c1198100c6800400c102900300700c1c01500ac0145d414544045503092251010711045250a40c80345811039100303c0642d60780d50203100d02c2c081c582c1000c0c0c0c4070b040071940c6072412501c101e16000003c60228285141140241c00c551510103c2d60307140488403000c0c00c0d00030200702c0071aa903001c800b0301041017403c1000d40000300151010a8107090000300b003031080d500400488580c030511000c00043e44221460700990008d080c00b40e00e48032045c08030049840141c000d80c2c40110710b0000041d40c606203600b518082c5204603001e00542d59030b03540c03400031200c2c112403144041c1e00881d846a4050280c1c0300347c118052403189218a45071700c0ea0b500e0107031050310742c51403030800d408140140f8805446101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 651426492 1250 651425242 651425263
    0x207080307120f0804050a030302130b07060507020c12060f060d15050108060a020a080402042019031404051902011e0504050315040209040602030603010b21011515181a0a02 76
    0x100ba02860400d902c1b13242d41d030901d400c0001c050607030000f600c5000f80c00030421540103100300360969950320043e182250181c0020388008001d0702c1001d008050914117039000b0403a0480107001000e480d80d8902500800580151190750814204030a04011640001100c940b0000301c280c08105940340c0304225181450017055000c042e881801041141548040c50a800c260121004208000c444140d0300c60505040080741d4942400034405800c84076000f0075002040303658070704100d84914440c11407003440040350000d006410006030884004c0c40d01c0d007214011030062400e0309003008100341d60005c96017202c2c10b4002150300864100050316040103001c146007442d02c1c9180b0107091640c0451540d080c00740000701a42d80102c0025040d890075804800a001c0003080b4881c100554054480841d20a44404c849942003280d43c1d40c2081c0c2100c01c2108071202e00703a40c1941020010000c031842094941c507401080c120b1180014080f451300d60001000054040031552801c006101a14000510300d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 651427742 1250 651426492 651426497
    0x25020c090c0a17100815010905060103090b06040e0a0b1e01081c0f111501090b030606031902010903120e01091401020d03240611010e150604020a0207080307120f 71
    0x350880e030b9a000360321900701c0e2907140c007590540d00d900070f007800341151a40041d41c02d8860040c07007410380540a04114100c0340222010030060b12031800450540340101c10151104094030302082d558145540001e255091001c00d070b684007240c1c2d54922a14040960750100080e10318080d4510914070034004600421703074107000301058811140f00300350700300a85560748140310880340c080c2007a6000d000d00c1c0164070201c0c001c0e90b0000e1800c85d850100a40c080c0680d1440c01e2412101e0003590500107001401080000d00030a005503000e4989a038140d1b05030f208904100045000200190078219000c00c0e0075026124a114041c032000014040c1103a40e01001001003032a03c102c189907004100100065000c0c43c012404a9010003107003c0300c0e0300d8070411703c501c805400700091407540c00410203410800140c020300c07003992048030b8140d56104110703090f080b100001010070240c0c50150300600d000e058038010784618a60b1780a0345825500000781c03c0e10001208503038260003580c010111b4042000c20b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 651428992 1250 651427742 651427747
    0x1202071a061216060e0303040f0602030a09060c020a0e06130612120504030b0c030a060b0d0b01030c022a030703080301060e01120603051504170d0b03070801060e0f25020c090c 77
    0x1d01d9140e0b680c80e007504c20711050000c0300410f004c03240c03030910440d030280c106040001c480603502c2000035600e920100424000450390100407440301c1c8540c20031003209c1e40061500c0c0d501420415050395542002d00030300c2d03010704000320708048440c15004810050000110481c0060818200600760f0030340700c000d8004002c01001709100113229060100d401c11085210750b0749a81e18014254014001038000700d9049102150141078001c507900b10304d49801e002e90301400100035209040e079603100f1407070f0003000701104806103074032080c40404030880ca845c00904680c120780e07494551140302d90081c2c12a00006401c0201c014070784d604600c5c20940030315101420480c0c5851600c0d81e50300c2c0c11031110001055907588010070180041000c2c24071109070341c48490356403000580e046d0001801003081c07450007030040700d034005644941803288400719a80d503500104955582c0140a05540b80248002c580502d41c40b14201240003400240c0c460701c0094005003034400c1108104401d002c07006285a800403800c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 651430242 1250 651428992 651429013
    0x5060d050304090203060f130c12052205030405280e06010905130b1c1401020a210204030f0b060906150f130e070201021b0a0c0302011202071a0612 65
    0xc580c1240c2c3e00f4480181c607a1101e034002941940c6d8113280c3c95200c901401a4400d0781e00316400f210301003107030352100c0f603542054031036803070030b035501140c850710020310011041c007500000e10020018980b080c81924941030301d85000030301d8850491110740340d0043c0c0f2502c843e88802d0104d01c91018040740d9403618514900728000904106a0f401640c0c001c9404860b90b00c55044250801c41c65044010400311241d415480035030441842c1c1c800a4030b4000700290507004013801842190741100722a502e541c1d10745840301083c2d200c64410301407808016400c110001c0420402015008450320a0300c1151140c1884410403654070f00180c80184903450f001004114030f51880704031107241d00741808881d02c03202441c0f550580003078140d00248401c0c07054400c000c4000d0b07065006040f403010849071141400b8038228103a5694818900060284150010038009503005039420008080e9864015143c42d88650b00c4241031000c5441002c80600a5410711100d45001509201046ea0000040203800d62 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 651431492 1250 651430242 651430253
    0x4110904020a020105011e1401120e06010b0a0201230c0a090f0e0103060f1a0f04110f07050d08010e040f060f150602010f201b1b031204060804230a030804020405060d 73
    0x148d0346400d061102c950342003c5001007036040402a4034070340b401d0340d10325a035503050000c0c1c07030b401007440704010752038076604503c3d841a03029284a60b4080d041d03041016503950079062455400b8540308428001103100014881c44050205c2c4081e1012141c000d400354910325152066031015207544c40140e0600541550141030703220348900052044415100c2c19501402040081c51080300000d00203200140820010307050200802a0310f21a0085610321aa0303804103c0c1e05070800e000b0401c0300105c00c008a40456554183e048420740201000203103201c0d912070540459030503025119203140e10002c00c102c05602032040012010703801e501442408919403490450403003c1c00341005d285800324000c0396140d034540c94014159882d000b101c80600d02c80e82a170f107440b641c2407a0b140c0329100c0e00c01740c2288001807101740d504642ca95140c400c0d01c0d0322241d945054110b0307591100000d4546410300d035007c00404005100b4294003a464107580c41c2094014841925002056140158440c0c0000b000090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 651432742 1250 651431492 651431519
    0x3140f1e0d110619150b030411030f0303161e02060609071103041206020403021008010806130305070f03020a08030a020a1202031005120c04060321020a0c0504110904020a020105011e 80
    0x2204800c600303420441c0b5544c100500c00c0304a001041500180c000c41c070310f0358420003140540d001c2d03c600011483c0103c10103a0303c2c40032100b8446260024008542d8005140c00c060355070080b0390030807000a804140d440e10061240465040c01a03209505000311420300012068008240d883d200c1d030060540000d8030341d2803089100c1c15103501e04c22050070080c400f01e581034034003560340140166140305d54504024030703028080c007910750303c0d014100c08645c280c6180300003c01200d500d42c49207030824606499101803c29002d50030380c1503004480340c040c0019000801148204200c410050b15403091074802401c142506400d148094030400034031020003010034400741242c104841d070400510a02c5220340c200200d1005a54000f818440d0200c204205205881400c2e043e10384842c05c0d1501103c012030740c4145400c006000c0702d004000134001414150041240b100b88117410600e404245c01c00314080b68000c5a07030000617596640180030780350250b5040303402c80b080301d540c10a4031402c0000120700c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 651433992 1250 651432742 651432751
    0x6020d0b0414070f0908160f06020312010b0d231f05151c0515040c230c010b130903020105100312030f061e030308061903140f1e0d1106 60
    0x1304a046000740ca940c882d101c03150140244806071903841d004903c160784c0340340b070600411042a512802c00700e202480002583d120010041d0704880e41d9190201c1c000b1241e00120072020400d8813102100901c25611003d40c850070a41034101006103050304400c0c880c48444200d00c5a4030101c0c00d0f08010941d51082c48400f45a000207146685504010302145044240301c149a07a03203003000c080004034092941003490340345c410f07907040c4516040b0701c000b1a10214452282803007035460110004500c01c8502c040d0080300f00ca08000114402900001070322035114480c0d880c070080e2140c0e401001c142d428007441e500700440e031030540c0d005400c0d692001e5100c0d08850724a8200b540e20040790541c030b034031604180018254003055844040d521594850f801810740026008155000042100c40c00d03c0b683c1d43c03103424a02c2603200c2c6e580d4196a220a066441c50054100c1c0344a40d50300f10860060500c40103140009481c2c10000c00140c541c0d0460070149190400f500780440d003040c8012803000030601d503a10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 651435242 1250 651433992 651433997
    0x1b0803040b040e06010c02120307230d20030711150a05071e2916020a020f031006150207150e0108060a1a0912190b0c1606020d0b041407 60
    0x21590342c0001200e01000844010354000144000a00c03243c07800b100900d01a0300941e00c1824a014402d40014081c1c00c02f0784d007598507404140000c220911490f007940c002c0d450180703041070200303481e0403807403440d0007104003650941600000c040c45458100030031018010340700341d2103080c03000b60030001c0d00a000303180c805083e80c41c4c424820201980e010040525031540710714540c000301041500c0101d02d1840000d80160f81c44d45402054010284001c80001000141e008005040450742400800c00c030f000041509803041580305d1808034400d0007030f00050084440c1e140310382e0402030310081c9040e8059000030501c0c00a40c01a200c0c0c2e951010001c01030000a003031110850b01c881003c64404082a8000c000c0d5808004e01d2905001c43c0c080100500340003101d500c2c40c44112080010384410000b2040c021010745000c83c0b50006403101211070303012900c03d5041e070610404035100003082d080000111a030f43e60006050040142070b214402d0509002d88041180301c80c0800305000e041d20185c885400e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 651436492 1250 651435242 651435269
    0xf0b0a0e0619030515070305090105060603071202040b0301060f2309060306010c061d0d08090604111207060201060509071b021e120c0907020f0606010c1e1b0803040b04 74
    0x100c2c8103402d2030b500000e5500c10101e442c4000480d00d40b04041700c090724454002070130720020030084c0805010300750044034020019803440d01d410030f090750104514001c0d40c0307160740c0a12001401003d00b0002c8c0d402003003140c542204500781c4110080c003c40842c00c803e00044600c01101d404214064151107131400e042c0c6410345c0e0381e200d0200680f290000301e84010304039070400c100c861496034084548680c1e066240c0031106070404000069400203400c4400282c15408040040c001c01c401c0084100e0100024003d0540060150100707414034415400000250f0b4603404200850700700840c41a50080321490030301d01004003600041501340340200041c0c40740c80c0700000010f610100104d02c40340c0c440300404160b400c3c2c05854442e502c1d104480341c410f20400444000445050012600c820010304c40c001429450307689500640f90b12404050654000e0703c80c0040c400346041d66401461014001d0b0b0392883d40507500f201c0e540c030409080e002001c484d0414007080251080036803d81e419981d1042213001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 651437742 1250 651436492 651436519
    0x10211505040e0f0a030f1215030507090e060c0304030e061204050c0d02060a0309060b042d0c0507030c0c0b030a05091612030509040213030c08010b03030a0e0d02030a150f0b0a0e06 79
    0x607a4000f402081c02c6d50b55140c002360300205400e100c0b41d041124030403000d40c3d00e001d9480c0304040495101c03c000341703290b401200010b080c9141c0640111781c09072207410558003c085a00c0492059002a1f0702d40300501906000d10041c0f20082007080340008040310840311081607940415078502030000c10300245911032600a08004054000e0341408070068000c01500e29503100c01d040700e440c40d10b440910b51002041d516002181030085010b000b0854851600e04410360b9000c8919a03003c2900b900c070180304650104014988900035801500f50704c0c401300d01c5007003104000c0c1c18401e8081c011003244a05a100300f003400c56004003084459010b041941c1c4803582c800114020344682b044186c5020300e050004030400c030124400e0b9040e42c0ca070000070006900000c0625a4901c10160102d0105144165051440c5020100001410b20203400d0f6003510b0120ba80f0f20040502801c500340302c864030b81d4200c0c42000d0486c89034103100c40084400c0380106141454520b0001405090315000d10803c60111 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 651438848 1106 651437742 651437747
    0x901060801030b10030503031003030e0d05120c07080a0c0806070503060d060902180f0718030c09110705030c1e01050610211505040e0f0a030f 63
    0x640240d080d81c5420f12802e01c018030302c40f01040c00403c00700000c2c0052010714001c20ba145c00f402c00540c11807501074003c042801199010f000403003000c002160000408002030325101605030358519590340c145003403034100d4019440f544200c14a100401010b400480c0441d4491805d80e0100e03140d01c101240c06100c262241640b114111a842c00030440d664005008280300404a104c90103403c40e85265111084031a4401d01807880b040001c0c0703d410034078000306140c215040c036604504582d100301c00148580070359a41c0a41e1802e1030750b01803503140200d844c817982210840740ca4203030b10544190740301c002084c50320341c01c40108d0800380e0031316050003018007442c0e00500013110541240d0041780c070020540c07030010342005001e050240340d01c9544101c85246c040894000e004a05000a0005403040d421003030078242e1010031120080b2402084000c1e00c01e038580b400c24281e41906604 = true := by decide +kernel

theorem cover : BRFrame.Cov 651258992 651438848 := by
  have h0 := BRFrame.cov_init 651258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 651258992 ≤ n) (h2 : n < 651438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
