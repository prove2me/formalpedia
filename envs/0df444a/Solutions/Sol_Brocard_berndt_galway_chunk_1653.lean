-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1653
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:04:13.192684+00:00
-- url     : https://prove2.me/submissions/6eb79817-6ea4-4736-9692-7a2a31d65a5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 297122302 ≤ n < 297302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 297123552 1250 297122302 297122327
    0x2030d050d1416020c090c12060d050105070210061233060b090f01091a090418050a0c05010f090b0a0c0c08071806050d1101053001060201020408100c1403010303 71
    0x600c80c02c41501054103040c90320787d110f101c41c55405418617100755030400c24a50003811490381b00c01d0f80100b07240490020320501d4020103954001f4103c5003031645181c0281c1c1c00350361041d004005480601400b20b840b0030b4054000d4100461000740b001d034041841c00e524441c0185c0c100c2c40030710300100420000c0340031008004621040b82c184114014400044035000001e01515042c00e9101c0107141e42d0410b500c0140c0302080f0010404681c1c01d0f24804100960403400d0300a881c1540000400300511403000e0f02c0001520080c03800501031105170030090208141445a01c0c885100054640b040038800c40f02c00394070302c0c1c1c00403540503c50358132810165111841d002d060459080703001403980d4810940324600444501a29110703018110307442d05507000040f95050350501c8403c1008548650380e008a14100c00c2c01207007a400d4540d0404000d07406487c0c160019810741e84104800e00c80624000364001564001d02000702d0028120b0300100c4141c21342d210041072801c0044001300826400c42140c1194 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 297124802 1250 297123552 297123557
    0x13140a0507031419060c0203090904080d0507030e19061104030b100506041410090b0d02040611010911100207050607060b030105070c08040605090d0b040503042102030d050d1416 78
    0x640f1601500f5074032903000315002040304000d850b000d4002691600b204880070081c0c0140c074100403103003000c103200c42003c8400f25450b03c03000030380801c01e003d0742c407a06030403c00070f10f41000302000300c4e13080c15a104060001110381113061848002007040c00d801807088200700c801101e499035500d1a02036080f02055814200c000e40b540004a00e50800e041a90122620900417980400c075040910035400c20f050500001c0203c10803001c5000e020031002003400c0901da2a0040c1c0c0c1d146081f50042803418034201c040300c90307410480120042040c0d101010300940c13084550402c0500c95000a91a00610f03034801a041071010a0103002d201c1d495001074007840e1309800a106999448030111481152001c0c010f0641800740014010240303d54050416010090302c1034031149005d407244034241c46c0858046a05910000701030001c4061441c41030b040c24007d0000d4a0080020750000c3d0701d07091850000e1040040c0031a0345c8020090300c0d0494555111f254940c40514100181900446018003044002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 297126052 1250 297124802 297124823
    0x40b0703050901021905030417010f11040602010606030b0a030b061206130c0b09090f0604021309020316050f1c0209041811030a031b0503070812150a0e13140a050703 73
    0x128205c48002c81d80c60b042d4000c000c0e51420b03007800400202d07003050700c403c0d01c0290760759050507030111014883d01440c04401d078050350311580341060003800d40c1c6072900020201401e02d0b243c000e4036110050424152030307001d00034003016900d01001c03604440c0502200f424902c21013051040c00e03406010344030142c2e070244007543d410580780e0008a40c144190300f0510703041030300840011005440110602d420a100410142ca041105c003544180c1d0702140e0440f40300b080e4004248100d050458003244080c0b055410500d00304802248031426500802c110340145d42903c81e20746200c82c541e43c5c111407100e080203004104455104516a40d4480c039203c013190702d04070440841d241850000b400801081d45aa50312040803855003403080b03075210801048959200601c10840006d0281010302440b098444906a4911340840e000c01c450300c030f011602d8000d100c0d2800500c20340c80a5012a5484040c8504220b02c1040c680b0300040e00c50800301c2d603168180250b08015040200124805040340c0c02000c0406 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 297127302 1250 297126052 297126073
    0x12010b150d060b0a0e090a0e0a150629070303110c060403030b011d01110f030316080a0b010e04090f0516090e01020405100c030504030813090e06010e1b040b070305090102 75
    0x43c5100b011094804503804019558440c83c0c0300c01c403e039004103243c001007014424030502c20f02d45501544225188a0a80d8805031801807510400340105009460002d81012440040440c4a1032001c418a0b60320000351020505020340c0000c0111400c41000e16595040174050030344400b4107407001c40000b414903c441c071b02c5611403400c0303880d0307040583c0b0880c500540020054810002c0c1081800050281c5000c6860019003840610300c00d21040482400e0600103900007460800020b10024200d49000c0003641c0c543d80c020741c0c0e10040c1d1001d0b1800102119141000100b42c03080c41002003861003800c2d4062403080711940018100c03050518140700017020b25410034283d01660181941004000d14148091441aa9140d01d5a802402d14034545a160b450701c1849511944604924000d51803042020762240d110b680d20400758100a06900d504202014090903405096140080390000014a08a4250048500914264211960f91089494060030740d810540c1c4041c05070080c01c00c02d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 297128552 1250 297127302 297127319
    0x30f07120315140d0501091202010c170112060e030903120913060e060d1509050105060901082a040216290103150c0507050a031101051503060612010b150d06 69
    0x40301640d01a807800d15a0f024080c00384400c410032442c0503a80e540d00c0711200c07004501240040d0b440140d640c0e00120b281c400202c00601280100e44080f4180c40d04407004002c01001c90141059071540030f040800c0c0c02004242051540c060203000e6076140c011070340e00d5842e00d00b02c040209081c0c0700503580800d101135400400001c0b684284160107401c1d80850004455182c0207000615441c41190a0248001403800560440b0a0300400321130980d9200c0901c0100e107809079107207005011000040200450455441180d24402199142a03604295071690a55141d405035480030703051841d160340b1545c8a04110300569010010b245030260002c01000016a00044550582c3c4d042800103175500e081d155818001d12541031213904001e024028800003c10601107512402d00070390700c4814941c2640c40b25402c6482c060010302420310480105c5600d80c501180c032540c003010890302440c080302241d102c18090000c0d500f109502c10b0700c0a400381b035201035900141c40d044c01030340c408009031034588020f03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 297129802 1250 297128552 297128591
    0xb030d030c0f030b0f0d021c0501050613230c0c0a05010218040209010203041517070f03050f070903030c0f080412110607030903060203060a050604060f031b080117030f071203 77
    0x15040062205d0b086810304103011901900c6201801221050301010400c42e102d405c2c00c0c01c2102d05075110003e100d003520b02170b5243c001c210f034005000c100740ba8501068006c2c503001456410b113480d81000000d8074480002c07080d240d030f5220303290640b0099030081c50114002e40c42540d00e0316940807861030014141c10688203032800420184c00170b520b05400c1000980a52241588100c20441c41c0c0359551102c03041c01010b14001c00c190b444189080244c20700142c01e0b1900117086409618000381080071990b4030412040417079400d8180701341e0324030403030801914901320404050443d4200250000e94407020034031089100b806400035020401c005010044144101c4c1005030001ba103c0c030050010030641d43c002c40d000040185083e4425540d840841c9068209034007038404a194a02c01da05100d4050203031641c800300d01b00c14220a01400200078103480418040d80303000180851040d0076a0400b0021102600c2e08044030f641c44120f03a01c0d10b0401518105032a40000e400c001e81d0707410701d1071103810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 297131052 1250 297129802 297129821
    0x10e0a05071d18100f02040e1807050d05100504030f140a12051305070603050105040e0705030706140d1a15090112111e03040b0603060403020a0f02040b030d030c0f03 73
    0x42d59500c0e841d40141840803c038084048245070042c0d809440400c8120300c00e076040c01d1160301d0096111482d280445680d0000200607102031010380d04042400c02d408680350080c2c1d2421a501c207201100e908000380780484942040f0a22403401042c0002e140d00b004440344417507041c0e65442040d08a8802000e2640180448039012445074010021581c071190801603100d080014000e4684005445081c6040031030750050f00442e5442c1c0040c443c03804d0030300a003044584007000820001e4640000319580e82001c0c440d200070009102185c640340503442c412100400790a24061250103460317110f02c5407144012004510900c04402c400b00d159161205583c9030a034142c5844010562a00c40080685840d20706c40501210800c008000103085540c282c14000c295880c00c0e4a0345400d1070041000c2d84045d200305c0c82a4448401c01001a50015140d928181d008141294210142c8085009407481d43c840c00e50601131180c000d4a8035915900a04012400d907682408200400f68190215a02d981c6c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 297132302 1250 297131052 297131099
    0x9070302091309020a1e060c080c0336090a021303080c01020306040c03060305060412090f080703060e030324030c100e040f06080703060518060c040807050109260f010e0a0507 77
    0x3c4c00304251809455818921409903541c81d10b400c0f0300751001c0d4110b901221080325560300c07500b0b0090600c0ce1a0480780c44440f80c010307a020101322504005800c40e100180303003880254000818403031a04412100c43e000315484488580c540c822070301040e0207504205e80b8180a9450003e00b0460548a4004d01080340c0c1c2010241c105520b540d01c0f0111040a09110a42402001c0c01c0004400380c0c0358000400510a4001926450f415032a1803c02d848114024501d26032040c818072204000100b48550001c000f000a1144890031502190821003404070306540107070b00182080340d10b9002400501c9601c000c540401c48501d902483c0001c0b0740c01401040f07440d80c422402480001d1655116a070041c401001d52003107602c100803154908042103034a0307040c683c2d000ca000c100c1c81d0400c208100c003520090900000d401d00f4200c0751030603005410078602001d85102030040820609011424030951400000e0040c2d0015422083d41c070341424804a5942c424080002203035030890a03401c040c902d190 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 297133552 1250 297132302 297132359
    0x703030207030201090803090d08090a050705010f1214061309080a030207030504080727050f07032403140f0303090607201005010f080607020a0209070302091309020a 73
    0x15101240203410410045040d50340c4c509032400842d01c203d020310f2081905800800d5040e203805401803050b4005404c080796544180e0f04580041c4020400c082075940c20718040034040e2001c40d040302c000b086d50344602d54003850800310524254038030f0001d52040d10155448102c400c1008158000c0f140c4004028100500034001289298840c0d00141040b500a182c524107007522800090b0034441e40d64031401e000c28200f06062141850302000c8281c5501d10359081201e450103204c8070a141800514081c02c059a03040003506046280d096040311420541000d102c1d5038a03460003030099690034070130b04600e214010550300e00543c0082260310076206d01010f401262205072080d1202108015840c0c1c00f00300010444000d04401c010b2004800890200445d25515040ca02160b075929a00046410b801c0b0300100b00815400140300c0018607810b45c2c06a00950b120b040440003805580f1030039502c13002e1075617401c4207000d094100300341072741c02100c1300a089a901c1e800c1d031443d0700340a10858404000c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 297134802 1250 297133552 297133567
    0x10e030a0308100911030912070f08030c07081201091109030c0d050a080304120e181b090a171c0912050c0d1a01060e03030d021602060c071a03010308 66
    0x41c0300b403182c00c440700600550440740c40384004801d8840381c18145070103007000304c03c10090f2403041240c002c420400c240c41c2c41c40c02c0040c3e1550321074049111005007003a9000008210f00c90b80000403100c02c01d800083d0944c03a891081008000000c007880b030119250b080401c98025a03413440d041f9082280011f00828a200d0b4442c1800103000e07031000e040c0c0b40c0b0f004140c88100881c0181d00114469403194550140701d0b05c81a0000e016004000340580c041d26903014425000c00c003040301c2d96003108544200a1030703010000c4990320284511b506035604945030280c0040c26411010740300d00d840402c0c000b6107401440c5141034900000981e415400051495602002061461f1307600007074143c0904142d41340f040b030304008100ca9a90300c0310308a6a075401540d5000388400406961070140044d85048a910310444000965a000c3c19500d0340200e5400926280c102c6214140581e0306603000e07100e10740702d100440c0000c1c1c80300194071408112003185036000d076140150000b02c1c0e05072030b4401c0c22103082a45 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 297136052 1250 297134802 297134807
    0x406081506060f042c04030f050c0a020307080717012a030609150503010f09050c0402090a08120a020d020307030918020d09150605061c0b031009050615010e030a03 72
    0x1000d0000c1c0e8210a08024800d03480d8441c100600180015903841c403510445100c1e00c181040c06400e103003809440000900000941c009028040c9801030700e829501c0f0740e96120b07030608101fa440c20003580761080b05000142003d020a40d04100c42029a440108a048400070f41c20f0b0340d143c0c02405244100726415070322100800c2403145070311a403480d00244035030301d4100079401c5500ca00070100b000d8020100c2041546402d00810f03c89404211041c0034925055a0791591180101c05142c42580c02107010a02920344c0d600c03c00040001d0b20850341310381e4900c031101e1600c1d80410030b420010b010f88207040e01c1350390002003100c080c0d0740d240c2e0303483c1c4800349049a10800500100004130f42640c080007503200b140703400d00420109a000d07040c540b200c100104004400c1f2440c65014500039a403c0c000398031803021446428402c1d079410400032a039000c403100024144000c0441c00000c143c51724200000b8014001001031007007102190744020248140300660794030141014040d0705900448900e4006403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 297137302 1250 297136052 297136093
    0xd051503010b1e0108100e0c03150301020a0e0105211f050a0b0405041e050a0b09150d260d0903170906180118050c030105060d020d0b0c19031a040608 66
    0x100c2046e4051080341e107881582612842c00d4541c1da0116038044144100e48040b40316003042c10004800031840e00c1030070303031000d800500e0813145d46062000204820080044850000c4114040b0841001c058030b800c02510947c03201429a042c070b24040300c01e02090340e0801009035000d803298007551500703183c6004108009040c900b500000b616181c2c2d10700710f050103843d004e11801100c1c1148040f95003000c2d441030000c1010018443c1d40c40000d8448a08200e0304c071400c11400c1c141c2c01000c1c000401518812f440e407801044100f4106110f0002100e80010156510280c0918817a64030341203450411003152816001c00d1f1180070454000c3c0303020819898403100c520003500101e03000825041300510316a00044180502034405800410402203a0b140a104580d480760013111540800d01254010030b83782c00b00b40500038000a243e20108421105030801e03140000c4200000c905030b6014181d00a0180c601e511040484400d6258490440d15050107030400b81d40b0a00014034040c02050030400700385 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 297138552 1250 297137302 297137311
    0x7030602030a0219211b110a02060703090e06010e060d05060a030210020d1707050412030905040216050c04050c03150a1a221404110d051503010b1e0108 67
    0x856082050398a0340720310900707003c213445a5848a403070810f184403003c61a4041c2070f030000f0080386006100341c3c007200d0504c3c0d80ea03120240c80c0b51421203502a00ca08524094155034080d500180109400e4101070b0f018020b2002d0364400000746003d0748441e00151007003903074002290b42c0550240305075000055140c2c05203501c031500030200c00400750b0f40d8000c01c1441551041400040c3c1003c41d80c0740209801c0200080d992651526601140c90801401072050140c0c2c00750000c050000111481490312480170351000c0e140c0100119034858080258090010250600b100e80b8021040100841e04d4244195441012440899032556a0361070100030015500c43d082584481c1003100480c000d10100c041e20740b0940001c190300d5640e00b61602100c5281040f010555459001440610202031548010300d02d1500685022401e42c18410580d016402040c1481c10010711381000c005060760305410747c01c0324800990081055601d021300b846141d80c40182c0c40da44003038076208020030551055003001c1c1d20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 297139802 1250 297138552 297138571
    0x105070804140313141009030f021215130b090303070e100201020c01090c030605010e100b030a230105010f1d060a0c050a03020f0c060711010c1b0b0711060c0703060203 74
    0x4004d0000030400c400502d41d008070244c0400700f41140d185042c503900544030b0440d64102080748615540e200b21007440040b400900071100ea503800c2c40c070b0300347c108007102c401c1c0b505100c206058542000300c0e03102c102c03022409494403904440810202000801201d00840d50f96450a01c54800b8130240044940c9030315001e804c6650802114441b20f500b0720070526440d100d9154400664130f03506088042d14410b8010b01d05411944080c84403407109041041d04076204055095142d03501c10000f00000d0130b48010700c1060b5840039000c06c03c000d10340080641a2070098803401c5054401d40e104851102001d0961100c2005800d401c0c007040c0361860241403103841c5481c140904520540d941ea0420000a0048026a206c4100b11421350028010803c0d1128252213540c10140c40c0d46030020400b100d4034840341800300104024092051321a024480c16030a5618603000b1991140095059070200009071685114103c48a0980c0f41800c1260220740c0403000030701e111419504c81e0383c002d40c000b420003401c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 297141052 1250 297139802 297139807
    0x90603160504050d0b1503010e0a060e010605060c10050108010506030a060b0d02060c100f0203060603041b031217010503010b0f10270305060a06060807050d02040e010f060f0201050708041403 84
    0x43c103540b844602c845030f9204110b031506074241049442020031400350340910990400c0c6200010300d80c000391591000c1e400210204651078078170b040070f0040c54690040c5800050020340b901c3c40010010721040c0103000f0890402160381c0c0c480d0b00030300700c400940701c0e954550004071480000c5601034100440d0090010094400410a035000070300e40d90004901c60300d13580102641c0150703c0400d228081c0005803000c0e0551951400000107042444000c10051404007440c0160034040e1129040001a69118100b2143d2690040700604504001001b071030002228000110303031801d041c024030400800c0036207110b00c15001d1703904100d1503a083c100c001c070420180c0d400340445804002107044840c0342034203a07010381909504081381030a100600e0300700e030682440d0081141590040c1465030110f8240381c12500c07501a00d03082000f0340308583c8900d480d1440c401c000303c0c443d1869004403040381d106444101060f401c100302a400e9582c125000c0707000c10030040c000380204d4071121041c002c03402d0403c2131701d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 297142302 1250 297141052 297141059
    0xf09060a0603022101090608070f051f110a0804050a1a0403081c090b011404140a050a09060608060702150709060e0414040b070909020705060c090612010b0307090b090603160504 78
    0x100c4e881c100341e01503d225511007004102d110414080080504280c1d003011034081c0c100300200b441141007841404d54032811a070a2102280b0484150441c28000b00c03c0d01c03907008a904041002e0340042c060302c4d120348800302e0005100321054411a14074644046040e06051035511220303031a42201041070700a15000d40900703005a01da200d043e00d2144601f1468000c0d5040c500d4051082100100d030034051854410307070000080810000d02e5118403046404510740d502e04407240050400c034800200503070304208001c28901c20209002c0d20400003a0b003196500c2c1c144080420b102c1c58152510004183c0c50034041c81014803690f00c9210044015001080090070000c10b507807039030401c4070240c0313007180e20900780200306512903509402428000412350070a4040d4a6903a205d44010741b65015001001440240c29101c90050312221050346000c01019a035600c0d444040d54021100800061007514002c200c1401544c141c80d10020042c00c1c0ba42113a0702c030941c0482c03070341d8441c125400703001c801c0c003000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 297143552 1250 297142302 297142357
    0x7080c15031f0e090d0503220c1208070611161b0e04150b0a0f270507080901050a02070b040f020d08040f05011107080c0d111005090f09060a060302 65
    0x400100100c0e00c032940c1d9451300c0c485013414560050446000c109041081c0b011a208103004100d000003540950389805080746449041118a9030000c401461f800891006100503800500315403400345006008847c16954030f629180b1462601515540149003000c003c0f070704044210010304413100301d003d000350715005180c940f0101260215401181144071800e07004050064606000e020785a101416050400200300100e040c0502c00280c42400101c421200005009689181190500300003504110310000c1c0304080444040043e507080c400407034042c1000344210f65030a5000686c034030307694850fa5101d03165a6143c80d000d0f80c0c00a44e01c0c2d5288007294060004000410441ea0001c00c0c0514110014100e04e030100300442d10b94000200800c21614045000c07014450b080f6106406041c46152080300c1040003d40300d500300c156040c07900e20142d00080246070700201112900d0180403038608112103480300f114a1030300722940542c1007203054040d401178a050102c2c000c9a2034002c4c03020400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 297144802 1250 297143552 297143611
    0x60d201903020f0102070e16140c06040209011205030a08070302091e010909020c030a051308030f0403200f040e0c0405090706030509030301080a02010507060209060307030b0307080c1503 82
    0x500a2150109030400071440c10088402c5440002e00140070410f151107028aa101401081c4c0350404103080d01e00700c25640300300c3d03041040910608001c0d440f00312040c0c619650f002c0c1210300701d0203404020000b103217030180854103180c0b0325402002580740c809014001c6030b040002602030000d15400b4028070740c45a41c2c540030300c08084200600ba5444508480004081000a51040c80440d10400901040b11000b20864801a1035030038001e41d80e5404a4041da9403003170070b0384030030394500011800100051340600200202c901910490413058055140081d41c00c884040c041d61124405c0555103044c2001e8100c01c110048440035200020806030100c1d040d2a81194000000d4020681c203014082c0c01d0701c540c0c1e0b00001090015410740d0b04045600da65018204006410310402140b0042000780640440d40d01280140c503041d2a4100304070050068070741c0140003482405a484041500c18000581d095260b070010041000440034000d044090761000c0c0040602c1d00d441c1042c22180225803a2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 297146052 1250 297144802 297144829
    0x403080708090d050f011a0303160809130f06050f06070209060a0906030b270d0e04021b0c0310021c05040f121e03050606030403051b010f02070b06030105060d20 71
    0x5000070078205a076050840c0c1840c400d040301f400c801c60038041c860714000182d1700d201551040c44500320465090494143c0144a50141c1c007050340d041283c0605440d400c062464101c5510501119807540d00f00960206c1081616400100c10702504000d46069000141c100c0c501074899440f480d10740ca009419580d42d0b0f0000c4c0c40c82034559007880400400c503d0010303452201d5808054182544440254440d8902052401003110b00f9141051a41d0327698102d400100402601d40e12800c0082c4445072244800a0200d120f17006021311950800c9003402154804c0030760386051800d214403400903200918018005a613040c942400e05400a808442d46004401141d264a0400c000010811100c607420603d10301c201810311044c80826201c41c000c0d00e4100c0d9140c201b064558a43d07507035560a04000344a58101582842e000c403080001d0780c0c0c01821070364000e140d003000656480061509079507003912480e42022121350b100e030100310084c40b20b14940a00120100c1d40c2104000044d048041001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 297147302 1250 297146052 297146063
    0x8062d030d090320031c030b0307090e1e0606060c0a0206030703061a0a0f0305091005010f0801150e011202060f0a0e130506010c33050a1107080403080708090d 70
    0x420070303c140005034a03a001c0e1000308200114245400001080d1140203440c003001d81003480b508600c604a0007a042010311050140840d40410f030b0b074103000000381007411168131040c01040404c0c644140d00b8117230743e00021030800c010b00b51501c600c800c0c458158480d41e031b46070300741c065022400010394074400210300814050707802043c1207003880b00c10f5881034410b101c0b000c0c1645003040503454540c0c028101c01c1050425060007c0d20b03584120505080c040c140424682c070354904000407598440c201c011070141c4c1d550388000c000306240c0c2c0c218007291141d60f004080d60101c54000401401c0345061000c0c640910262800381450f00030101d11800d50040c0c6005c40210382074241070023041c01c0591585420020951080c00700741003080001e8941a954040a8070000c8031000800408000c1524075141c410001c5c07001c80d01c50158080303840140303001e6500713104040c10f20681c5507119801c00c09a60b842500720044030302d45441e603540c02a055200880807102410140140d6900da0b8902e1003010941340100e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 297148552 1250 297147302 297147317
    0x10212040305031b0703030e1c050303040f1b1d0901060e101508010605120c090d06020904060806040506070f0207501309021207090b0108062d030d 65
    0x28958512030303a00c4c40758040c0d295100120410110354410070030700786da80303003690714640c0000ca104402685024241000d4845e12000082c03100300301e004900020054011407180e0120380c40749481c600d0380ba50700d10603040f203030072103220f1224a0a595010310390060780f00c000005941d55903003400048110116a0a0444c01c8141c10410001451000c2095603172910b18169501d50b05120000d0400c0c081d00d04000502d10381c5000243d002c4030301d2400c565400c440201300181143e02454020085d50010142a01075401c090000501d0036000a4031801158060050819655580c0c000c070b0f2144e1860030032508510404070006544900f00c1c1d0401880c4c00040ba403020412003002d00c901d650711102007220072124808520307140803075290882941c2030100f1204010207141e510101c0001c0c101441000c0e611050164010002283c0010b10b8012601210014001d01c001c103c010b5928a101b140d40c03903088006007040d810304200d041403140702501c001c00550540c40c08800401d29041012000301d0109800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 297149802 1250 297148552 297148567
    0x5060103050c03030717070c1802091306060206010308160204110c2505010e0103090c0b09091308030604090203160603151208040302060c101506110c090105010e01021204030503 78
    0x1c0c400e103400044150002c52a00f400e56603503c1105507a4101b0505000011403e4030812400c034011030000c2c2440501081c0ba105060202802503000d4942607200b140ca0340c000c0c403101041070150b4811203041d038001e42490ba01c2c50319040034940c44400d640c10300b03160f00403001c40107a48510400000b2652821515100e03031022901500c1c10611070440110f002981e101c4c00d0300e03038100c510300e01d00341d400170b103400001c04055400503005454803c00c000c01c2004010404103803800c100c009031144180880b8149800d0b06c0c0c034040782c4c4881300182800346c40704204000103211400d29400c002c400d1440038048a01501941c09000e049010a03006a00060745556000311000138080049024250b10100110104115960007000c1e204a01c0003d0280c8000300e0390301003110041c0071100380300c00b070740800b4050300c60003041c0d0a01038059030044070082284040f0280850000191500b40008080c20a040603400d140054846141803030a540c114032512441e5071103401070201401c0118851002180c40700c41 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 297151052 1250 297149802 297149813
    0x3110a0507180b0918100f09031815050331050f0d02071505090d06020a08010f1206090206221406120103080a020c061c11190e03030d0905060103 64
    0x2d8682180d0016081a203400c00641d10280c0d020b4002d40010200c03585c040e0503546250404180100445510b40741240380e0403007000980084d1505882550f40b20520000f82d144090503404e503003d05510310b00040103c6800d54080d100868007c010003840c03041c019915481c0022144010158540003c0114000000c2241c108940d050703c030000b4020f85501900c1030b000960b00c6101c1d1049070980b4030918a40c0103100d01400c21120003150203070007841e00244900340540654802000040051081b4000240c03c1019600c103109030f9416003401410b403030941e00c0c4c0030098112224141e0f40100c00701b1111249140d00c01701e080044d018040c50203101460080204640c4022040d001d00680080100039400700390b80c1c0503e810350741d0100d41540c840c2e4056600300d02c0c15850705c2c803441c3c000400180c50075a503543c070030004403048008078050218422b1102110458094280c03001700030f0304800300c2c80351018003550f1248109072029003128104980c41d0004020364800d0031098425400210042c000d101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 297152302 1250 297151052 297151079
    0x40e150a080d1103030105030a032114070207060f050706020d150603090203152509030203070e0a05091c110102131d0c070503030112080c0709020408011808070f03110a0507 76
    0x3c2c4820061810343d8900b10210b0b4075520181401010400660055201c900c92404034440f0041d11070380c2000300388003030201c0c1449200300352800c41c050301c941080003404074418a120049418190351300d50030403415549400c041d41040300d49245054540413102804100a085c0d403008129907980810340000b14010b060412070950480d0440d19100e2080192000e40c101c1035107101b001040038928080071078401101c8034601508000c0d40345c00764080c0003c4454240c0e80041c000c4101030420407258840300c61031503803107c001c0014400100c45035000403546000c1c20248411000c82d030300152403c00a0216001d0014507504054100310240d403106a001c918008600e0340b00e8070241e80300d480c00415481e49684ea001c1407041d040015020034603101000b400c042560720444094088401c09610f4800010180d041070149c07100541c0782240c41d2a15400342d1001c41c0c10b0a0304401e440345019007946401c0080b0341030650030360034404c40f601d240e000351204211003e003450041000c0d280c0c003801e1004019464 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 297153552 1250 297152302 297152327
    0x1120f0c02061b1602090603071706060901170601150905040e030705010e06010b1c02090612250822080c030c060106140a030515130506090714040e150a080d 69
    0x360901104c1c212400a0311306030480d03501180e134281c3e07030340d51000044c0c03400030143c2240e80503440440c81050b11080c00507030240540030449903c030782c507a02c454038401401e4442502e464a41e121000403c10869074080040310404a85400c0201d40e48810104041da14a800000102e42c0b0005145040c48401c0c0700b07442142c03600e400504419450701d00000303454045e082c2601d03400c0783e0070341c100038004505a04813410000c015051685171079240010741c2d9400ca00f20707501d10f0718017200c4805081c2403140c40da25212480e00b64446c0001c0c1c0d211403400103c06020814080280b060355045080803500a0001c0c12401ca1038400070b564400e40010598100b5006a02042c00d010001084200342e40c01c94041e940d90021130300d0b0024455640d265004803030090400c5042e0440b0741240c40b800c440d040c039040f15100e2142601c5100041e00c50003c12a46824000d2982007400828002480031200d147c144581000c4200400f2069421000c002502010310358419081ca520086070540700581200078107404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 297154802 1250 297153552 297153601
    0x60e010b0418020717031506040b0d0207050a020d12030b040b010903030305130b1003031e020a0b1806010e07110f0d0c0201110604030c020306090303070e01120f0c0206 74
    0x155403400c08011454090340c0500350803080800108440b10072580e041e5004584c1010540f0314514140f51404182e0b030060703410b00b208807400ea2042419041060031101181c0d45040b43c2c0e407030202108100c00003500840011030381130083c00407560142e81c54101802d1418043c200090025850b1940070b003c8580b04800203010340d042c10a1040141e811128800450f030f018240030413260741da840340c03483c0b4030300c00038000342400f4125007071080d49803000600b002070b01e00c42d4480c40340880544241d248051800d40c007035401a405110303100d00040d1454501500100054548200d13070b6880142c003030801d50240c204444e001262001c1080180e4002c4801d07402c3c54000c0c000c0c001c14601c0309121601c2d00b68038041001031043d5040c40f9011644206da0030018000220203840030390031b251800405e030030010b4900740e100e80309e00e901140c00084040120303405a00d81da200e00005180389801561000307a40f400c0b49981ca03640d0085a00001654040c90f606180ca90380034120380c4c0341c41d07040c00341c41e861032030a541030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 297156052 1250 297154802 297154829
    0x4090e06011203230d0e0d1202040e01050d05070b0706020904060b03040203070902130302040f2f03280504050601060f02031c050903070c09020304230c131b020f0106 73
    0x2081d0003402c00c1e8162406442032a100d0130309121244414480c5030054407185240580b00030901c0804a120794400c0c07041d5036080c058a00100c80360090303000d02d0103003410340c03201c95004002500c1c1500d90049814803403400d403009150303106601c0081d03400408050b1001c9400040601e014a024802c0102415140c1c01c4182075041030303000f09a0f036040791300030001c80660004092050703203001d01d6201c00555001b0401d005c0c500c0c0286495020300140c101c3c0106c8000304030480200342d1407407103004140014010304c1c40d00715603444440c8a04d08400070892040024901002da007164030a00a942c03041d8040c41c01448254034110340100400c0820800500f1908103000b503d0f9100c803080030000c8150310001c80864a925145161801c52142d214000c6c407003400d1031000a0034210701e4000d54800e5009241e85407501301d0f8940100b001c040300540c030540036044058030100503e0030040c024180b1400034000105120b0b60f03e42000c403c1201104070002d0b0303101c0100004140003d020703d60240850f0300402c071b0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 297157302 1250 297156052 297156089
    0x918332d0501050406020d0309050f0703031107050405010b0a0507060b04062309071209082a0c0604050105071509060c0504180b150a031b050301170115230604090e0601 74
    0x7d4440c842c0040d881c04141c4c4406220040c000204040a007001451040e03442d030300c6e0351f4500a00f1394030540c02c0b0203845000e00c0a0004292606200b60740c100c07010704000600d0000f42d180c040310b0f291320024044540c1d035621a04880c940d25684160009002c0080e211078203082c0718045803015208211296224000b07080400c03100329401a4180011507562901088001003440c1003a10341c021000d41070443c1c10940700900580c83d4018941007040410015201b482402c2c1080c400c0e94815070040d5404150100809400aa004141215400e070460300c001000041c0e50307110025200003c0d1700c03900241001c03c1c00c3c003a540c0c611032900d02d6400c9a1404110a5000d0404600d003040744403409000d010300402d640e22086d000382c0260480c0c0d902110344d074102100c540405030642d0004c1c09040c2004064000c0034565070414807400709420464030400d00290314000081e40740781c00d202102c400743d5160500905c90f50302c82c08040c0c00504481c400200d2001807a40c01c0038600a0140d01020145c078203c01441d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 297158552 1250 297157302 297157307
    0x50f36060904110405040f0501061403010303020d08250809070b0412030807050c070618051008010b18091006080f07080f040f0b04030918332d0501050406 68
    0x10703030203114156804210038031042e140810900039503202c9900a170a01064424802142d40190b058550729101c4008640492445050701d02013404028051f07404407840713801c9079009694072a48218031080d648008404211078092170311410402102103200e00d000d1014810040c0030b040080e195858459007131625286490301003203024400901401700341804909454441c03c1103407050304c03039501150940f42c2e0f1807500500118194190041e2201c4003140811a482e0903284030050307140c0390f52045800c0e42080e005034020b503c6003c1d400d26014080f1815501519001e840c644038800c041c2c054403881e071a0a80161844100429103c0702008040c10881c907039402c070341c0450b048060504980c2e9103599030f14118450700240b181c050408900f800402c0105907002c0e500005441c036a0080510b2150702c140c550081c2c69864030941401d2342c0110b8224500c100340c00e120a03c185c0c80c2c2c003401440701d54031901400103206c180d09c07864041410f01d80c1c03042000c03040424078005101c286000c0b8546450310030300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 297159802 1250 297158552 297158557
    0x8160b1e150a03082839021903020f01080402030c010e010519020609062a03100308030c0c2a0f04020f19110c090c030a09020303031305010b0d0f02010807050f3606 72
    0x1401c24525032465a4554205890b40c40c014581d070203000c28640313540341e0aa040708c07020385100882c850104110010182d510030040e6034019a4090000e00c044d03501c150041d034000310241c00482c10042c007802075001030000f07120702c0c0300c981c2e0f40d81d00a803613103040079003900b8200280180740000405201407422030403560000b00c2014401c061020342d4030ae498428a18a801c2e82071b80c4007410f00b20003c0284451782400e8001448150075034400c841c00c0109e800d00300c06030394000c203003122644100441d2038103150030301514181a4480040c00146008480340040f0703e107420401d0203c400300d030b0004414100980222074650300303150010080518005000c00200c003900000c00040d140d03007001c40807071000300329508510075240e80142620346074900146000c6518076a20340954007076007070035410803d508240b603124034281d810900d40060041c06d5001903444a00140c00700040040803c022150140355501509802d28014003007003294a10503d4220348061441042c0e0103021703079990340403041c4c1c0d40608 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 297161052 1250 297159802 297159857
    0x5130e040f0b0c13060e091806010501110c03010603060605030f010501031e0203030d0903030b010909140402010f05040e0f0103200d03120908160b1e150a030828 71
    0x140d032000e0750b03a0007161001c502075003401214088242d140885c0b51600210683d00b0050241d0350203106540d581c2c0300c0a0f200e500c1d8841d038610307504075a0051146510480b41442100302032000c4038202c41811001c01d003118610780c4280c03500d0f61b46003c00c1c0668a401c0c44803000201c901c2000b408654195200d00301400d0300303074a43c3e4540480120b045800c5440501c240c1303025180550007000440103038200903000d05411100c143c000360001d035001c103030740c0301506c18040360f1020f105c0d0b224495070369a030040d114000401b1204d400d0100034000000c12004440e8602d200d405060000e50380c5515601e0075000c9004103000343c00229100309117082c0d0544070b030b4070311090158045c5448a0441c881c4004100101120303c000380c0300040c0042d1004640c84030b60204424603114417101c0b43c1c0c90742e40a6003000344180c4c0c400c410801e6941e69003c00c501003d51000030040d44070081050b4511030303481c0d56220150740002c050010034142c885e44d0715406601e06802c0c1007042d0340340c00d200501c0d040254140400310040711 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 297162302 1250 297161052 297161063
    0x702071d070e010c0219150c081e070c12031b020f0d030311180a05010e03030a030f1506030b130b0310090602090316090e0d05090f13050705130e040f 66
    0x800c0c0a042c0e0784181e5483c90007030b8001d4100702c00314400d0890311074a16000c1c01945c1ea01060702040340c1c1c48900ca0010544c1a81d00f00c0015402c0418200c600000e000c1c4880c04c7e1081008180440e101041d01c0840e480f000780025008518401c0451070040e058100030b40384100801c0c40d403c14500036889401036042121011104220182c0d000c1c0b90a500030881802c40700d003501c102166039100f0300c0c070792640c40e0544101111203092150356403004407104401807000035015001400300c541e4103402900820103e480400300402e50700402d00d03003c0b2404020358007090020791503814501950400028440b0506c0c0155020710900705090003007681d43d1550205c0806060b0340f0401c16050048640c103440f03089600909031154030a4030701c07500301b40d0038843c0a45d80c400352070300c04c8100c00c00d0070001e0751000c010b0702030712100c1c103001c0c0307520803c0000b40d21842c0d22600182c05400700a04030740c440c42440c2c07081d004d944030aa181c2000000100310700030079800c5000344001c03040a05c00840d52000001d011664803d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 297163552 1250 297162302 297162317
    0x5011d010305130b0a09140f031914160b130506060f2806020714010e10110d030e10020f030406051e2401020a0314250b0702071d07 58
    0x102450590f00c2501d5901500e41c100c40c1e001c0c0009081c0c150483d40c60039000b084000302000013200b009840c0e50701c407007a0003044d9104021090401c898240441050003a5080000702e581403940700080c107074402601c0346111600b0030f80783c0d8108144241c1c01ea80001c00f2555248807080c265642551300e60015201912450a5540c8103025584040c56010040010000a0101000307a20329a81500ca00d004103030240c000d41d00040390801d50034040b02c0c03800340165102d04030140c1d86002c1c800030390007118121003001807146242c0340c80c0e0010400751648110542d40000c5104203d480c490800801c00341d0b9609181c0104003800c143c0310384030183d07a0811f0700180001407a45a842c488503800015034a101082c1d40c44504001490401c1c281010041080a15244044400c04012612511520b0008010030348003480b03040a4010b000c0641490246141c458120782401d440034881c40344880c80840380e051107070301000442a8144040d000400380d100200f440900c0020f4440701100c2c004010004000f9030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 297164802 1250 297163552 297163561
    0x7020f060f13050304150e030a03090612140f0105010f0203040509010308210c07020301180f060507020c0402040b09030f01141303200604050d0801081b0f100801030c05011d010305 79
    0x2010402c2c2c00d99800b2003281c1d5150b60f035902040c018901d42e0343c80408030f41c01d018940c01c80e04010071b42c0044550326960741c4d414241002c0c801c0d51000d01c800c07002480e050703444c8102480111001a00c44c0140d89010310151a90b140c50f0004010010b901c46840454109010801168541d0503000d415268000034150700c80c106101c420b07030300c61032406201014580410034411561310340303030040c200d440c0203034001d105c02e10044600c1d1001e424071840c014028030190341c0d03c4001c200e050f8480d9810440b1807042d2450950601d00040503070b003141e00508401000000d41043c14901044005201c620713040c02446902003a480390aa010030082207207061610315260003003010311480e0042c0c1c13070481c1b060142001c2c5801030155640d03201c0840b4102c1e4248210a203808841d801345100c44c0c105c0790f8080c02484a03004500c81c901c92201403208030394110f00c1d03011440d085c66a6005100840e004541d9804a0961460504c0344403540c0c0c59001d2030620204071100c3d1405042807481c1040e0900a003808034031a02c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 297166052 1250 297164802 297164821
    0x20c0a020a0b070b01080d0c060e010b040e070504050a0c0e13060f0b0d0c030e0c13060e0c0a1b11042f090a08060f040b09150405011407020f060f 64
    0x80000000d600c031110440104103001d20201502c4182d004110003001680ca4002813942d0724141ca407010003141a50048a000503165081041c05400307000012902c580500b0120301591441c0d115469140c020910078029402c103845440c3d404250000c0c28003144452010140003508101552030003418112580c0020483c0c0d90801001040b100800311030040d541c2201c851705400440f03500300b0361800e0032100742070203109000e9000c903d1507140141c1000b100345420014503030701c1c0c542450302440d1030313a800080da00f8864440c00c2c8507668106210740e4582c58614018101c080300800c000810080001420124004044456440307c0c03c0c2c0d800a8807090794800382001300c01e0303000c100c40621420030f1700f0440d20710008040c00814000355030681046480e20442d50712810100c0702c916210146c2d05c0006c0c00704611a802a40140f075420640740484420000c010000204981c1a240380e91500101500509030380401640007c0c5032014011811001c0b0722640c80c6d02026000807041d06008010400b400c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 297167302 1250 297166052 297166063
    0x30f021915120c020309091812070813050a080304051012050702010603110406060c150207140601061704020607120306151206050103060810020f0d0603110f040e030409020c 76
    0x44031070000c10300e003051020041c0340c1c400101e55892160304100444814900020940b0300201c0020b00e06c11041d6500c0c15820401c5070181040700040c441c0d40c02040c00c00100800401103540920b000f0b60342c512101c850a4602006a800b003400790380c00d01d030104110301e4040306031416100225032200e14055084800c403108918414410889840c010070700c000107030158880c4007201c0c81501804e40b083ca03a082004119040d900c10003012881c0c82002800240442c40c00c8500e50030341500041c240300450301c842007642041d42240941d503002a0060001d036811100385540140b40740713042c181303a00c1c0a034003045250098a0008190649072400d010b59940030f90407900c054813485440c5502020036840c000c0030b0102816014819600d0408003081c0707940b2034000c9030195600c02000340007902c0c21880c00030003980411504140aa0140241c09681d0300760f004640c0203500855011000c0c038000c0f0204895480c0e20390307a0600c200e1a04202c58903500c0c004c420f40b0308840b0f04600c0161221318449030300d82081d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 297168552 1250 297167302 297167309
    0x100806010302091e15090d020111033108012d1407050414030c030a03050f090a03110906031b0f0616031707030e03270918100501030f0219 61
    0x30320080c1388920b504a4000620011030801c0b81d00c648440c0709a00e03848914402d80c4240b80d042041040c2000c0994010036800d03610300e060100b200d1910420b00707125460320000442c0801b40c0c43c0b60100c2003001795050410000500440d03c02004980c14080c07a64a00c40c031041041c512070251030207481d0210b000c65202180012000c2590119480c000340014200e031b000340108000c80c0302c00106100c0c50b040015a8503186407001d401001c50b40f0355610103850980181c5109066568201b1610070152a142c0040008500c2a04042c444403074030420001000e5000b001c2601941c024144012001d4038980b04c1c4035190300c169011080601c4070380203c1c82902c1070400601c0d407410307021444000c00d607101e43d55200355103103000b07522984d86514008501b0380743e00307100b911156882440340e0800d0804900002400d11080190a440c08112601042803540210703901d90000c02a0700d50300b650102c05021000020200400800096055a86002030508400c0d0040d000d2183e680d00c5801ea010ba00d044040035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 297169802 1250 297168552 297168559
    0x90406030503031603050408090108101a0d050a020325020118050a02040c1403190e1507030b1804061a1801030317041e060b060a030f0e030910080601030209 69
    0x1916400c010b50b40380d01c140c520401092002c120a90000e10034420f05005648c0030040f28a0000e08400442d00c64401405807007940701140000160a400220b50007510400a03c2d0b0035120300d00354907910100d41e001003211203d140104200118600780300380701420000c40aa1003d4161100c080032030041c03052130394900d10481d114461200b84200003946200e414800c0f10b050000e640f00131402c0302c2916000310b0410f1803400510200e0901440c40310034000d280601d40e0f000404c010540d0342c4a1a211010307034065070521034042809041681b40c02454050b03e000d07a011010600342c1c008041c4c2108000340003808890b903072400300b5008581c1818445020383c00900d99039142408101075014102d0a00c0203c000c188140140040d2110810202e4850768110001080140f2203000c5040d4800800400302d40b22540c411040301c0d20b90f40c0c407000c1c1003100c40c9a9400120103034922804000ca07848281040103641c824081800b0300e40c0c2300800f6580e40001481d100c020f545450300181e02900402441990 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 297171052 1250 297169802 297169811
    0x20a140c0301060603061a0a082208030f04050709022715040b0318010b010804020d03020708010f0b0a0f03022404030206072916050901090e070c29010311060904 71
    0x440179030641000d801d035091485e80c800030f01da800459900034443d00c04c1c0355020850001c0083d102064a81404550704d07081c007002c0120600c143c2e40c0382096030040b124480000121401d0205100080103048007602503d502145003c80d604d0000000341c0c13003803004080d00c9118988215060720b41101007404804c41c0c2900580311601c9550031489500201c41c0c1c1c0b00d1542d064140c0b01a000014000ca90340070106850300400e5459907000c0c012800d09608054003948100f038400911003500b442110340718140324000084040140041108410a80d8004003400017494024405607842c601810041c270300c0d41545100101c0c0c0101800060300599002951094000c20303204240a007070005a08250b40d01410030081c0c0c40c54402c4000d1418013034030003040301000200303100a181d0050000b00100001410140203d5a403804449800745c400c0700c15500044140c603643c010044041400280400341d101c0e02e03c90103181c60385c0c500b800b00051001030180c2e030004168203220380f034000c11180c2862028000f8003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 297172302 1250 297171052 297171059
    0x902091305160311030d03022104050309090a0c030c111b0d06020703030527070e06010522030b0601051c05060103020909072304050a030204020a02010b1f080c0406020a140c030106 79
    0x504844041040d05c1c020700a0303403048041c1134803920850700c0b50004e030b010f541b100c581084d40240fa00c003001001242d40e0321041003181c01c0fa9403184443c920590a0020201c0d5038035403810001e059a0300d40000340d09110702e0250300f00c500071011078007000300d0810b444420a20440040024040000c0180281426200091007020f041e8160001842000361404410041110100850070b40d02855880e40107500450000c2c040300d0340c0e60180300d42007101454001e00b0400c500c00381d1300d02e81404100c0c880302c000344101c0400030000e00000d940d51040d400d0070440c1c00d041c000307401e5001c0d4440c1403100c095416551400140c1d507038001d90507103074103030406403d0550303038501200b02404120101030f00d0034107170508071402c02da4100d40f6011542583c0c40580503554151842e82480080e401110340d94055540300c003030f50005900c27004405070300d0007402c4104560442c448035020780400ca0150054403001010881403180940000e6500000b0354085203048040d42c61000d002c3c2001e07151448070f6455428040c000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 297173552 1250 297172302 297172313
    0x20603061c080a09060f050d09020105040b0d09110114160f0609050318030102040513110403021816020c010903080d060905090a1a01060807120e0d080a0f09020913051603 75
    0x3c00e8039025a403180c043c13044d10303040c060310002d081030f44100011f8420001d0145881c2c1c1d136046600510b2043c100b007804c080e2201540d036056007081d42c101610360760b01c104410074090380000d40311703950a080c00c052030030b4500f00c41442c07241d20880c00f8602d0036000d94030701c100c100010080105030454000d40c040225a000346419626941310035488140054014800ca03a24a4103200300c9003110001055581410043e800800140008074000c0c08040c0b001e000000c00341c1c542000300000503c02011482d51071a25800042051845028130001c541c0800d1841d5103c4c0d07045a030200a5a40221030b507a01c032241d9040000203403204d500710074002802c0c04240004074000150008406100302c40090456001c6591065135010034412000003c0700e003c0401e000502403800560440c41303088012400c103209409061500c240107a404001520304810422408100e11901a0034001d0100520100c015900090200c29010f080070420002c00c00300801004001c0001e204801321a0707003050029035590910 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 297174802 1250 297173552 297173557
    0x250210090b1618091508120403051509060c09060714070609060c0b070f1e09030209011715090a05060f0406050c030c040b1e0315120a050604020603061c08 68
    0x1c00384031074508580a0914000c3c4102c3c801c1a07210090030462924001c1440083c00e90324500c620588600b00c00801d6418080c0400c80940c4030800e981640d50b465460040e1a19040710444d070b0460a086090090810010480c1c5400c010325800c40740d26200910001036003417007030140040000c202c110400001010104404049072042c2c2c90b18480d6640e00c841c20b4641c02ca1010004003400301000c001400c0c14058000b03038034407800500d46001d04d03000c000b0b200d03003d1212844800000c9840300b541081103281510341180580414213802814900d078418a540e0340401c039101c0c04100003103034005003841c00c04124041d007243c0c01000b2030380d20381003040441401200a40b01074a440b0b061070001019990000112400340494420951800d0702d451202d020940109101c50b05a502c0f17103035052402280b02020314080c02250701c00c0707000ca0006404000c80e035400407401303600d01d422011862010139804100d13180c1c01a015258551340e039540800164104011034690344c100c8542188080c01c0c85082c40c003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 297176052 1250 297174802 297174811
    0xa030b01140c010507030506120a0230100f0c0507260d0518030c0714030a0b070e1008060102030a0806060412031101140f010303031e18050106050603250210090b 71
    0x2c0410040e08c0304400c0c000181c80c0001c0e8401c095002c078802d000141005c20a103170030352500f101500240e4044507489003060605180d501140c0d80f080156054400300ca10942c1c0c881507001200300450f0228142c0030307000e40144d407009401e48449081c8000484444442c8041600f0a51105555000050f410000030030040d145041900403680e003252010100008607120115200020429145855070038921500f1122000d43c050040c482484005052180c0d010300503021900d61360012249032040c80f44508540e0700039010440c0031001d000311303641c0100807200d0018a62900310303001c0c0e803014042021031050343e100050100d5500c4c120828036611240249143d10410000d006186001c9100c01c1035080035100081c50181c1d40b401000020300940c081403062408440e1400c8000c03100e03124000321010603011916032006942c440080000c01c0c85884060030040300c00034110708018140d22150381200d000000c0c2c6081c1c0c1341d03103860180d008010107105610b0011042c4038802c420f04c0d00c5501c10000781d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 297177302 1250 297176052 297176057
    0xa0503040f0612090b0c0a0c12081609180c030e1b0a090b10030203090a0b010b0d0c050c0309210105010b12061e0130060807080a080a030b01140c010507 67
    0x120f5403c4a1041e006a5a142d5040034010965032103000341104903900a01400003404035400d200360005117840c18118a948039610703410a00e24014205641d14000c22285004110b0401d07001c0c888020750804540c420309500d000011b540f40c0c05001900180b091b000c24007401c1c070440e5112408100704148010420750181e451a403d0380d5202c5148003903896140240760b00c41d00507040d083d8958030a5019540c8100d075031382102e400c00030030740f1082017844081c1c0007205625400103420f85844824080e400040f0280e10f004c6240232001c07a00c854072401812101071249103030107100021030100e08026141e44c0e8214000700b0240d6950b144280c890f0b44940d102c54101e4080c0e60004d10b0500d0005048a03030520720f038548843e0144020011504007000004021800982a1034051404524003012050884108001401c1410048103e140814a50000e00b03180d10503050600007130642d4080d2500d0722403e040100ba202510340040e00c00340d080d00c00c0c50f19001c00229134640d6403481500428007925098 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 297178552 1250 297177302 297177317
    0x3040b01091506080a0203060604120501140c04030525080601090605010e09090a03030e1e100b030115060513091a131104050607170f03040c14010c03030b01020a0503040f06 76
    0x4181c042c8056901c00c12022410705800501c030700c445030300110b0340403c1c0240704030f1030700d512140700501d0392001c118203a60790383d910000841c1040034002d00721741002000503a1420940313103580366540c0e841c0c07801080001c1c034880b58007540350b85441d40b034010280004800783d4800b0341e110300300607000303041754031481c0d0002d22036014000803810040c202500420115010302510080b584054001c1c0501c526400701a03c1105890708511052a103c0e41e000e511480107002d5a041c0c3e40749031000c5d1415184050710903490808d216103146000ea80c904204e9078a42045502ea0002d91941d20212000b44d111001d00d81c140112202161144058008401400c070b40184000c4141c2c4d030528100c9660360801d4032820810802448189021800361010303511560115680940103410588a50402c103080d04c903000e07003c002c0c4004c001ca122529030103000701b160181802c1c011900001c141c4640360300d003d8149503450080640e5a4400e20041007142d4001c004c0302d0783c581d51961840303203440d074900c601400650310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 297179802 1250 297178552 297178571
    0xb10020a0b0c070c05010c0f0203011a040506060c07060f0504050915010f030e03030c07050102042d0e07020d0e18040b01080f030c07030201030b0a09050f150d030206041e0803040b0109 81
    0x90005031032501d901305004400c203508060040d00c2142211505950345e1904404c00e0006035400d028454413007502c102c00030548003100c8144000e5660140065206800074801c59007840c900244c00000c80d00a0300d0440c1112002403c10b80c0c291040707400c16078000703e181082040900011300314010501081e40caa0365150713003440c4120704603a14800c0030069a001000883ca082c020180a01041c50040300014545aa01c02100c0b1107030b0b1b00a08186d000484200089d9002c180144243d0020603504503001c007286800c2d00002d4a0f800703141c0156080c401503541d015020344072504c4140c01c03c10001c0d584051030806007080181c2240902c64620240700c3c00000e542c1030003000c010360b680401d030480101091401c42d40190f02400102c46066002401510b001828108502805014000d400501501824800982c015042404020500a01140c40c0e035074000381d400100c090784183c1056602c420700f0380b1228075a006080840020384402c2010007072005100c18580254100c400212003007100c01c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 297181052 1250 297179802 297179821
    0x20d0c03060207210c150e011401061e0e010c110409050f0f0d090e04030311070606030201090605070b0f1005060a0203030a0e061312140d14060a0b0904020d0b10020a0b 74
    0x4c0010420002600c002c12400000c1ca10800c04000010014002c141c4501d41c9400b282101c5003c8109110072040000401a003a000903040055045110710003c04405401014005281100010b4100005400d00d041400743c8800031202080780204240050b09007414541c0c0d64080d48640c02d8051301a42c1101911000b00090b0829001055265410075a02d001c4107100e8040e001070050701851b8503141064200d1000200800080d8031521340015130341e042d0f0000411840c1d1517000803090000400200c00810981d801d6550300451094000c500340e035842c0d00e5a61244c0081d44159000170021550f02450380c1c000c0061403007011445820001d11682c201c0e051f5842006580b81002e6060000c0310002040d0221640071155041e8206002c000c0a100c402590382e611040c08003681f140e54030021510b00c0c10440303041d90004421201c4090345414100c0440f00c52081120640c4100c2d400100400c0404043e0081c60060600401c000d08400184002039114411078004403070101c1e04a00091800d039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 297182302 1250 297181052 297181103
    0x203060f0907020a111f050a02070b04061b0c0503010c090515040605070206280c03020105070f0203090103020d1103010902040807060c050a03030e031b0c010e030705090a09020d0c03060207 83
    0x2e074560040201085540320519405004902141c0004001c2c842200c42645d030702070f00c1c0c0c803458140d0315142d07a402c45080090501000c1d8215000b001c008000800c65154080007404107031072002c580301c107521503078588942c0309840780d401550154280002c1000903504903126604691055407100828178042d08048902c0c8518010f00000c58020f1186001605040024048148030303000342c41204049111401c6082032455001c200095480310507a0405030b081c001d0b585c01003041e0610844088060754081e48034000c00300264101640070400754400813954000320340d140d0348066499502e5854224800c00780d403190140030300a100e0036600082d01846981442900342d002806041c000c50b182d50200c010f8641703050000c00c58807081c01040c44c610385818003040b50105800060252000cad100001d007403426201d19180c0b080e003080e40f00300700c10303100c400c5016485850031340700240c0ca8035584000346003281001000340c080341405c2408000c02c821030380141043c0d8090481c8000341d400314240c588040c0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 297183552 1250 297182302 297182311
    0xc060a050a061a0f0f1b0d03181101080a140a0c080601050f09040504020f04020a0903110303090a0902090a031a0717130609060e0109031e02030307140c0c10030203060f09 75
    0x404080013641075819030750b00030308440100d2080b902d02d040e500d03411a0324012420901c0031200c0d0420009403130350f2034040c03091704120501c0382c04c524030141c0982c40390300085d1440307900103061000140c00204001d00ea5404040402c14450884010b802c02e4a50300000f440c040c00c1c040c01168401e00800e0013503000300c003500c0c14203c95900c0581b504005c20107103c050034014104981181004407441038590791780c009844074038116503c0c0400f40e80386041c41c4801d606060b22b494040d0300200000065a111141d400e0103031500d5a4000d66203d41d4100860590321403039001030004812050b21107004501d802556004040c181e0703c41030a0100d1400820340c1c200c0540300e1a5030540d0b00320864000a20b1a006071440d2030051000191031140d138881307282500d02042c0e0171800200286c140008103c103400701c201680020380300842c11460071400281080a05204145901c1008558038480c41010000e51b01d01aa0107810305910420039503010703029420070380d191446042500302c11b0483c0d0034090344d4144038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 297184802 1250 297183552 297183599
    0x5060109050f04060f0b1309060b060921190506071d0a060804170c031c020702030601031b0305070b0c0d0e011b06090606060206010501021005010e060906060c060a050a06 75
    0xc43d00d49a40d001c00802e85003203648600e544034403008490740e40340c08281c1c082000401000c82c0a0720949000401c0307034803181a10380710f40070074014004c00740c64030b54201800b05580207821000c42d10380c0c40c1b0380c2e10b4035262803000d0302d07200c03003060303606003040b0b80410054040c40c855211090800c80110311006000701801c40e07139801c030140107170802c145441190351f1500540100d104828265901402c90096800b60000c68065400014000003100b000d07484102121080817046003004000c6e80002c3d2111010712000e020101c00c070598500314941c0400c0c0c00d0095078041d003241ca005581e241d503480305801001c0103101d14007c50400c1411140242d114640303412050355603004458070b0490483c4a09040142a51a50703a2a052500051140e10801024013015001007145600d001e0009142203240c10225042030b081070700400c200382d0240d00854010780c045942000607500c40020800a01640032102e14034400e020a00406100c1540310328002c80f0441024000c05440b1600002e0803002c28142900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 297186052 1250 297184802 297184831
    0x3111c02031e09150901021b090103080a21050a060506070309060302030c0403020a030804080706170c0708250201021c02030d050a090b0f0a050a0b210322030506010905 74
    0x104207540c007039a910341160705a602d04000910004c550b8800c00d200e24000c2c042e2000860585568040260f07180b4000c030b45520060000448010810301681880000e0804138007007031007500b403030051455031010a101c080d841903401210060030041c081c00d40e01a80c0003840c119000c500350600d001180c42d55601504c481c01c17014038004c81200254401003006036107c06c140400b0006070394104580006501542c00c0907210390a004105042c081564807420030f004041c8805504010078555403035108840c10081600d070001818148050712a03904501c0c11402d00d016110301aa504d403401744110f9000381d00701e030030700070356103001d800309403031076612000964014007040001c20700c180c0005920240001010404408940e80c100d141c480503a40d2500400344001044101c0030940f0640d40d2003804160140485510700001c60702950900850109404031084244d0171140b0030011508019050030200800f41d501303100d1118800030303d00045031a4040e08000146110f40c60017128021040c00c0301640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 297187302 1250 297186052 297186067
    0x40f0903020a1b0b0c01020315030a0f030f0e041409100e07030b090f0115060212090d0204020310170c040e01051e0702070f06030c02011805070b0d09020d03111c0203 73
    0x20155801c28140e800301d50303c2044041800ea00d81c0001e0003100040500250b01da003040c0521038000c50161800740c1c020360080302210003141c0c9008440341c015408d810301045c0b0140100c421036034060100c8046411608040c009401440c514120600c5010000b0039201021200800c260070f58540003151030640e401000d044c004511084003070382c2c00640c0c610840c1d51078460280d180742500c0e02180d0744041c01c6618002040542e07014812140c0e001100141b042ca80081176000580b90520410060700407940480080e81c460b00003a40c0c84050036081c0740d211890980103036032070b50340c0513146140c80c080d904100c4090641c190500545004090311101000d01e0034000501c2c0580e0003004081d88114800c0070340000c0d0003d8454924006840d817540d004c41c0b070b4608108080d003543d9103c0204c07511100c0200742d1001042c0c0104042d401d07501c00e4084517585181702100b0308043c014600010b50b01400240040f0101600114884054be24040c190f400e140c0c3c004100e44002400c03116418007607041006441c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 297188552 1250 297187302 297187313
    0x100302030613331406090106090303020a080c1905010e010c05040b0706200408070f0e150121020f07020f030604030806060307031b0903050f120409020a05090d030905040f0903020a 79
    0x10980c002507090503580d01c0d1242c00088080e1410041c844111280d100288107081c01c101610b1347c05020141803510340c492941e5030080d83d916203103501a00502c000315909160038002d00440d00c00030341003251001c01d003d86082c06402000c0401103124250b2811403100c61140c01041078030100d50300101e009003400ba06480b9003001d0500d000702001c014a18042c412420300c0074001500c040c08001c0000d142031410900401900f201c0c54200303041815104041025001c020300500c07a2160083c6003000001c030a5203408100184519100220a8004030300c504124003460098000075008450ba01e2230148130405154545400740c0300030703001800c180700003101400e1850003541c00814030b1a002401c0403020056482c00ea0440e0994400150241020010b21104101d001c08446140000e0940503146440a40f5184158810301d40103903004950741c100341d4018015154800405449400c14542d03515009040301c00300d000e0b00e482580b4141512100c08001d00c2404070041e819001000404160303203c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 297189802 1250 297188552 297188603
    0x509040b03010209060d0c030b0f0d02210a05030c160602100b0d02130207020f06090f1315060c12030603080307031521051005060603071412100302030613 68
    0x40c140c06640810048850f5201c02c0c00800d007040031101b00085d07654031a40008c05407204000c840c8d1281710514692800c69861002d480d000c103034101c2e1001e050900115014101d144520b44030903032401541101c02c24800c0100003010707102c00050690744a201151898240b9583d43e00500c4010f0f03014100c00351070b40b1442e903c502401c2c0c800130300768000080c8641c0029020540c8001840c0c42d10b07008500320003181000445ca410018040b00c82500b08400400420019550002032078495a110003c3c1c54440032250310441c019644220f2210300123132200d030083c1a600d00740d2403c03034a040780c1c00c1d04194640e00c04c0c440c1500ba20742c0011480d00c0c544420318100d002c3e000745800410a10b0b107180d00042c00311640ca400b40d056448000c0c402220168504145040c039034005610701080342400100005641d5107030460750701c0045420300b01408103500c0b220040070b001c4c404e000c5540c40d40c00c80611400c0ca607801c80301000c4a208404550003a40c4061243e819020804e81c01010300304864070001112540503036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 297191052 1250 297189802 297189821
    0x304030c0b030a09050106060f031a130218030a0f150203010803041202030f070806180c0616050a060e03040e01060201022a03090d080d05070f08130317091f0c050904 73
    0x8140103019882d12070840c1e01e1f036401400400c40c0803c80080964160045680c004120b28296241010702c20102c1c00c0c0405141840c038109500140f600c480190a40e51601081d0014007118000616850103242d000e00e110401c0d1100024508103a000211500031032b810707188610040d50825103401440110820b07040c4c0100da05000e00403412a180400b0403c000052941c08014142410000780f8900205011650b031007040c2c010002021250300c404048445070000c50f040e0402200031420610b0070f016100e81d004000e00d007810035444021100002500c00d45000d0050300e502641d0b5110183d00701c0c4606695a0350040b400c602d080754218615544001c40c0d416141501e180c203940b0800540e002d0180c4408403aa01c2d800701d08004032061903c1410780c400d0a42c105540e60000b0035138054440c1d2401040c116100041103802d0041620905049092103058034800740075080012110b070b152462461010413500c0d00461500c40704080307001e0254055640c1d100d940c034020404041c0b1000d0f216004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 297192302 1250 297191052 297191071
    0x20d0e031903150321090b0c03070b070c0c0b09190602060612010219030e070501050a1706060f07030806030f121b011506110f03040e0a0506120613050c030304030c0b03 74
    0x88000002c170f901c0501d5121003001d01004c00038002c21003440030703011040350b4200407040807062041d00c10091000044800185e00080030740c10a0b40c505c00221543e985086004066580c0b10030006a0750700b585001c3c121b440c1c0110740e2242c00c0c0092030758442705111a8411000182e111030b011410500300003224150360b0416100140c4ad001c0058040c280e11100802501c0000f07031390300400d00c4290780c2807080c000900002d00e0030700c1c44c10080083c002c00e04030711010300c042046a07240110345155100070480300040480c00c00b40d44c6a4056060262008600f21203082c040d01850809021950001c03802c52120f5003c941041d00f058407024902c02d888045600030007a03596592a000c0c6141035218020008100941c0c40041030503030402418140566071009040e6688180400c1c481e82c80000032031b80d44408400c80001d066a43c2d41c0c0020701501c955504c50701d01e13000d0082842200f42035449103031441e9000b03c044400000501c814140c0c1c034865440054991b01e004803003446003d0031540110382219048 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 297193552 1250 297192302 297192341
    0x1c0303180c1509090c0e01050f04030b011404050a150b0a02010f05041115131202010201290a0e01050d030c0c170d0e040c020d08060102030d050901020d0e031903 71
    0xe6603107054181c407a4101d05020402c00044070721403940101001c0c0600620a0305224034405003801900c0c0580c0082010b0501a0100d5251881420760056400072b64004440707011a50350f45c40704d12222000c00d901d1a006d00d04100010301858024080c084580720a0301c4120308161034030f10101d0340c5030003545124045548881f01603444110310b0054034041c1d801190031291000c56034080110000c01003071207407154002409820044034110400c1c1c801c94003680c01808a612172480100e00402805911403030785011b90120211440b50840490b54206050760030409242c4c950b40740c1048001c09216040d805181c081c0194000f03446403e000c0c40035032062180d11000c507215403a811042405400600266212305400c41c90903500c0f0000c580c0e0880d055801300503540e0002c800948a0310199105020b001850003c5446a4802c004071203800e401001b08000609000c1c005a01075403080c00000411400c00c12403507003440002c0f04580c2d80404070441100c0e1240070440135405400c020b4003801258000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 297194802 1250 297193552 297193601
    0xb0a02150604290f0901060801060f11250b0f070602160203031c060609030b060d0503040810021306020303010e0a05060d060c050a031416200304080f0c1c0303 70
    0xc201c14450342001d03c89072114103001100510808910542c0c03c68440c1841c400100105904107003180c1c1076034018a00700c24060844441a24400341d1440c4541c0148118507001c6800301c0d110b0950802036030718007160801e5035900c00140c41c40b40134002d07500c030380940f0402101000441c1940185880241c41c00051511a103a0300004e0868202c2d812007000620203800580c1600d03414820300020704400c5c141342d81d0007811074135201700c41c1130002c1286004528201791401400b50401c1610007c18140c404c0368100c1c0c80c4801140041d40149507080c003806080c04010401030700100503139059944140002d03041d03070b4400b8218000740502034035041d00210210a0704001c501c5c1030080c054107a1054464940e074601c2e10300028111590005140c24030b8119030140b1440e036405084081100c605890815448901004610004e100304080024180b10000c0d00090405010503030a41d4006010295008005d00d001849844030b2480050f060314440740901d800080d00030b40c049c0480d0710140c200750340010036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 297196052 1250 297194802 297194831
    0x50703060e070303030b0a060c060207050703060c02300f0a12092906060a0e0f100c0519050304060309081303081e0f0702120a0501020304060f060b0a02150604 70
    0x4400140303655030000d07107050044c0b44e01030140c8005280d0990360720542d103103040001042c030540c07140000c0c0100e80004070311084c85400c0000c0800746400000412415110100295a13000b9064894412052000c110250741e81c1c1d004010b01030242d80351400b850b2113240c0d6040800d940c042d454980c240421081816803a604c1071140c2c1c44014130a400d40d001500503400318401217825103944030580c003020410419503485000c01d80d009000f06050170420038030940c0005100c022a070484c3ca0300000746034001e803100d690181d52142c10034000c106a40c840d15140101e84418940320201030401d03882044100201c2d40f2030b0703107e501a00e000e014240c0c2420b0740e107007c0d405030035034540c015a03903a000030400c546c100190191140c0d140b9400c040e41c83c540327411206201401d0040140280c42941c200403d0081d1810074003100344c040b54007030001c5540345014039080004280a503400c0d208140b5002e00841c61401d85000c0300e82e441243d4005268070640d42c0841004180d00401043d0400d45400c041d104128 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 297197302 1250 297196052 297196061
    0x60408010f090213020a0914061b0105071707081603020408030a03090c0b090a030f0c170a06060e01051305060102030903030d0f0b040513080f07020604140117091905070306 76
    0x102803101180b10b81d00c9004011501030b1061001c5031980c130400c5011201c030b4001d001070b0f00f162612071a680010700a8800100e0501426002d41c0c8868030720344e01640180c4040d8420340c400c0b1140c0d29207036090b85d2518800380f84404211078a101043c0c030a00440d10740c2c6010403130426034803168500507240c42e40355004a801c5030403900440c0301081c0c49001c1041004a04292100580844007005017001d803100d001584c0000940300281c0112850038080c405c0c01080d05d904d002600c48103460035100d4136904c031f03226624801c2008c03d0703076801d1618502051041169100710704a5a000b4011040c1d400340040110091070064041415480108100c0700ca40d1018005071019103008113001907003e41c0f0f81c1d2b080741900c51000c02241b04620701802c00041920700d1360704c0e1131b90300d800031300040d1100a42802c030041c0340b00d1410065840480800d00141c10004520b00d56440c103001e1386c98003034441d01c4a0091712002c106441c01e0300990018003100f040b80001c46081c030a0796005100302e51000d562030300d840e01100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 297198552 1250 297197302 297197321
    0x1a070c0608061f1e020105060d06021806040f15050414010f090f060f08010906062a0206041211040b03210405040507090e13050304030215070b07020106060311120c070206040801 78
    0x10311034102d524403002002c0044c0c1c2c092105070009005a01d0031000007000321094010043c6480e81c0072801480024140d030180e03415090203055160344548030442c2040701505842241003441f55807070f070749100d43d00c224203075012a004802c12447c2550f8500c011b40c0c00700d44594109003082243c001c00200360403c44940c0004003003030707112913100c10401030008051580503000034108604085040005039484004240501c580e1000d032645d80c0c00c034641c00405c003000800040c2d4018000310b80420f002098030406508241300714101c41030601c184050000307440c80b05000503410342160f02c20000c182c1071038014020103e00141d9030b601e071580f100001002c40d50300340c0d10000013607603c550521200f10940e031841e41004074003240c2151440c05583e10382e664070403070200a0180b01040c4011071441c94000650300c8443c1e11411040042c40e054100a00038002031148600113401c100407a61080c0441048034240015000000309543c1e420030f0020496100180403a00400c00f04000580d002c028811031642 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 297199802 1250 297198552 297198557
    0xe060702040f020a020706080405060105060a020709050405030415030c0e22180b0603070b0a031806090b0f071107090203040515090f0d0f020c0409141005011a070c0608061f 76
    0x4131031803000300070701d0100260400c80900c1001010300c0081440081c800b03044400494080eaa02c1c01519001c80c14101113900c6a1565424501031000f004404409401524452003558951840040c0100c054422850360040800c03a40f005201e078600303104511101c524290317110b0b0540d12440c004030764215121540a054945182c800c003108001c40400c0f00354103d20214000e00c04941400c0c00d003a401e1140304403503070034140d680b144680011016840c2400302e0b608900100900cc80d20708108409490803104c102101c41c0c543c7c00a00528018911700300a85584001050014249003e040c020740c07001e0825204c41c4070b201184000304c4060704000d03110b100c3d000050040c0f10548038100b46070480030300c200c0c0144003002e15546806980018460443c6c24105c90101d0088500c0c1083c94848403e4840b96086006d01c004a181814080d00300302e040701c400e420526044490f12400e4162130103a40340007054554041d0040105074801c0f136440d40c000d500144005852041d0310890b084100d10440071402 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 297201052 1250 297199802 297199807
    0x9011b03092d060203030c0a05030601030b0d080c1e0a080306031608070305070905040201050a20060c0901090b090a05010c030e030607081f150f0201090c060203070507120b070e060702040f02 84
    0x150000c600c802c0005100500085081d410004101542405080380c075004001d4048001003290380301c0d4010105038640580f038048043c03001d0900d95069405880018020b10611030310350511104e0403c0841c0e940f0019028103010b83c001e0b960199503501c00341100e6030520a6506a4038a8a00201070340002e004100003003050b585503251481c2842c4455201014140c0340c00700b0080903036002411501403404078586042c100c81c2d0f02c110807070000f41003e84030720795215610801c1a4022440014521002c003626a004030700e40d120304900883c4100c0300310942100365850b0403c40d5500845050440e41d1003410041001407441000c41c1c98580e0403140c500005a00809004030060010510600780c2c0c3d407503030505042e5044c240d0602494119805a00400595a000c042031501c02c0d406061540c0d030024040c02803c0e0b50350341c025900d03001110243d8060040103000240c01c400d001e044016540d00450703480071507031540c0054031070701a01d480091704484c0412541c80140c1c0c2d10f12404105c41071003400182c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 297202302 1250 297201052 297201119
    0xa03060f09060509040803130f031814061813020a031e0203090c12030c010515100c050c01140903031309050a06050f130608060c19030209011b0309 65
    0x14602403540030700089840c040090007a0707160829032a40c46a08040c949580e910703818102d43d2550030701d040c041d2540e84001e140f0810594021a4116000c24081c45240d415403603c2c01c00d20084030301414a40e1000302040300c0c140c0000c0071403440407510001040521002c509a000d04182e81c0103048220000395540c1c000717203685441406191100340704600450079803519204481e074400e40140a1031007000342c0c8542000d904001c0085501c00d0107400e00a105a00340341c04001c803120140c82d4114880c07080482e0b40c0c20030911412068480345d8001c0001c005c002c4c402c000640e81030883c00d5909078034800421001100752420001406070301c0800c40b0040f030191820040300121000070f8040c002c0c450401d03000304090390300c0040c5070054490481e5a0100d4030700302e800c0341000305410f62011406004038000c0010a81c88072025051803088808800e40000050b03008604074840c8890080c0420841041402d881e0541d04071040f090780701e418070301c80841d100c001c01001c0610004a040c0707000720107050704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 297203552 1250 297202302 297202319
    0x161d120f0d2304060507031107090603060902090a050c1204020d0605010602060a051b0904020f04170a030e0402040608071101090b09010e0c041104170709020a0c020f0f0604150201020f0a0306 84
    0x750002c03000650020708244c1040710041c01449500c2e8043c081120074084841e0080301400408002e0101c0e01040140d40c1d52454100b01802c4070031400c0e40714406490025240c1d0740b0500517503210301440317000c0f20300d80074030f100c07800c1c0b0266009031007a030304550104541d01c00100e1a1090074040d01d019002003400385000e9149a0a55030010901c08400c580d443c65030b400110b0b1081512046042143d015855014100a440c080d0103603601c1403115002800c20324058510104209401f00d00a940d0b0141c1c41400806100c00d0b4421403090b000080c18100000b811a0b20440300071010588000001c00c19408070b07210b41c0d84080e404d4a842c0520b0350b40300917004d180d0504000f283c18580c0240ca052040701c02070380610f41180214030510242151810a000500f103007400602c01401c0b207c2011502c8420340d0300300501641107a40100d0080030400071000c070701d02c0d1500c043c0050843c010078940c502818041d075840041c1c0c1c100110000d664083c081030f00d01c0c503440d902130862000a603034005111031800c01c46 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 297204802 1250 297203552 297203597
    0x10201204080a110d031b0c03021f0f020a090e071809090503070b0709170610120c031208060a0b0c0a0201110102040e0f0708012405210a05161d120f0d 66
    0x2003001f885842a401c0700041e4002c50b44815200c0d02080321104418100524000f0b0008000e084102e01e200007183c20703c641e007122011042c1c0d03003185006569641c580b101580c81403007824048401c0900500b08004030702c856001140d586204802303490401103e50303501d501c2818240c81101c082400b8020510100381681b040c2c2c3c0da01444c06009086c0383c1404100238035580c203940982c240c40c881b00d018150500441031042c1d070056500c2003070051982e040070b09c000c00c40705d8150740c950301c501c801150000f003028522060707a01000c2080041c004891031540151602680c0074071085e4a1f540903c80040c45a210003c42c0740304000010244440c0c0c9080c080040400c4016008030040840c6130809042804440404205201c1c05080183e03890098501400c00c100e203400702c0094965544040084a40540d04a240240c9444000e022581c05420b810b5808143c0b003403419408819001a51205251904600754580f0100e0280d50403640080411802c00b072407c0000d0000c1507050742c003401803100c01c0b0507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 297206052 1250 297204802 297204851
    0x3050712081c062d09180f031205160e0d02010905040606030207020906062b020d020c0c03010f06050625050106030b101d0601050c0f10201204080a110d03 68
    0x8000c0802600481d400c0c4c248045010b0320300c0c503698529202d00410782c0c0f45030244080fa04103c0802106c00285801002c503502c2c000ca18450504100115103041c4119807603044800c01900c441d4911011402845040c4400c06000d0307042041c0a0400102c5413103521490015098990f00581e07503503e0f40c01480300c0c0200c0503081c20700400b0204500c51403500c50500e040b590080e40d161145080e031030703404084042e00449807080d585900c0010aa0380c2d600d800034015a40070300607002448010703441d42150003190700611481c0c1d0440d104018503151141d9621200c041690f80ca00a103444509940b202421070340a0b400c03c503940d21a043c148501c200c0c2c44070011f0020b0464040d100503d10807440d5121101c0405080030341806004036040c000c042c014805010801400750813a12114080c51502c006010f40d0741ca00242c400707031065030302da0014001d400c82c2c50547e840d140d003000684403580c0c0c0581640c00180c90108000b800e04840c00032036424401c40600c10010354004c81e035010f070601413036401c000785070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 297207302 1250 297206052 297206099
    0xd1d04060506210c04030f08071a1008150103030f05130807080601051212070605130611040914090c0609151309060803090102061501090b0c070f0e0103050712081c06 73
    0x17008000040301d4002c1e12116540c02010a911451145440c14042107004850003185a0304801c1005104030040e002c000c41c1c00d400c1c00c0341d064030703403102c61141050800e00010300001d40e156160758015002e40c005000324420301c10112822913985a4050410031184c003c6025a048400104410b1501c7c22101013041c2d4070202410340e400746a0480756140c4100b50b4010102d0b91510001902d100d40300614410442d04181d00740f212580094090041c0d51250003040e10081c81d19600c44a1504146c40743c070b109a81000040c02d040e2000000c00c109070300100c51a0780d00604000c000c40501242d08064135a400305061088042070a20307060909072002d94020005990091080840710303a03000401d9900b000c11301a184800341001c00c012500700c1420b400c29074180300c0002d8644a60300e07000a2103011102a003c01c1c00c40c0d41c2d180d100c010004a82840068070390351044d078050041300340441028220310b120720604c80c40c001d9844081c014a000c180b071500d6040f61b96040070044c089441c100800d81d4106007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 297208552 1250 297207302 297207307
    0x100509030c030403020d02010c020306070804060c11070314030f1b0d030e0303060405040204060b041805150907080903130303180902160b040606052206080d1d04060506210c 76
    0x103510701d65030703004620001c1e2064504100c020103590185442c01c4503190043d00360760051a00f1180909805020355003165514503000c80d10012900c42e0003056040d03110603014080c0c0d01d01d5519108e0366041c031002040040d010420003461070f401c22100401e50212107107402c4450201c524440390600221801180c03d06003480c50710007044002108480d03100c0812a40050381c0d45070b500100c0c00a180c142c1108607080000540840e0244081c0050407a250002c1c00921003039480e5400d440000c4115071440e03401c0b2008501082000e4040d016043e417000e8042c08a0341040c258203490290180150304c19404908241c480c50910941320080c0800b230a42d00e603084d403030400341d00300c0c40e40c0502041c040907046002c0403001c1000c001d540e030441801420018002e0b458814280305003481e6032695152161514034050000403c0c060220b540881c003a801d49412888410801e418518143c0e0340445642c400c1e07503204080b4150b910100580707200d40842c00d840c3ca41240c00d6854100c076080c0a812290405000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 297209802 1250 297208552 297208567
    0x1060e040c05220b04060504030c140a0b070809040903051902060c0f070c0305011d060109061d0703140a0c03110906040501030222031a0106030504030807030b0f090910050903 77
    0x4035040f11140760b0340841c540845880601c0254a54185403c11044c00c60002000a8140d91007806042a1f0340220f051000c9942d5030008400d4201000300c0341904500c0003e02000180d0411002c0c00c1010301820030145040010b000140440300c460300128042000840c0051030302e01840ca113031803d102d19000030042420712720b07440449406019003961144800146400801405550b580011548040240b0100100349441c0a507482540c03070b8103e03180b0410000141c2514280250021035807540b15507040501107001c0120040c01c010886014140c40e14240000d240c10054050b128050030640050703e000b038010000e0994800d9000da0001d01c0e01804005c109949c0c06044904031807003401d00683d81c85e4140c0d89483c0500281c208046c004401c0340d400810300413071002050008450230a00507a5a8843c0f0b001e40480c0d03400c3c0d8006e0000341d0182c0000d803c01d8025803042c1d0001d940108850b00c05002100003030103280d4219407500240d04903c0d000001c0a0b56800382641059108001d1410400d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 297211052 1250 297209802 297209807
    0x40b16170a091a040b0c01050403030b1f05031510080604060f030209160912050706090902070308040f0c080f0c030c061204150b04020d0203061e030a0303020309030d0501030b01060e040c 82
    0x1142d000f000b000c0f901440d2000410210502218003d00c01314000c60344507112224603d000300004c840c00d1713022070b0500003d100c16190440d40710780c0d107200031030030420b40c00e40c1900102d407560401401940c0e0f0040416925007a541c9011008803405041d40d00c242d201e00c0c0c5102071100341d81c42c0d58403000364240d03403060a00c016500e60320791540c881800c3e81840c966001d452000c594415107a8810005c464408483c84203015000c00c401050312569201c51101540c0c50100034202d04c5004009400213035000b01060005244c00482041c0718000c031200800941ca0b04c8038142030400c22030140d1350503807050415400500741800070f918a08800c80380a41402010b1032102e10440c00140700602564064249000703406281c2c0c400940e080003e4400c54032240001c5c840d8000f90300070354450f840f0b00301c07412101384401c02000c10705207401c6001c3d0142040c0145a0f8040d0081c1d04003502d07500c0300d4002072000d0302804a2922503a4000c6020300703c001c5440d450860060300d40701d1101e40f00c43c05107017800401d002064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 297212302 1250 297211052 297211067
    0x90203011214211b070509010b09040e01050a02040e16050318011808040e06040e030913021e0403020a0b0a0207060f110607030609180507030305090105040b16170a 72
    0x250042442c074440154044010f00702840c030a10140d80c0b004001290349000c140101030088407041500c1c0309044151610030301d54402c8513104581c0e01c1441c2c00d00501214017140c0141c4a06603010340089141c211a420390350035100304556210b442c13a404101007021409840c4059040804040841500c044040d1300900e148001440390320300652201031440100c209505c5107401032308a06038213200c0700051038001ea40d94014454564208411404680c551900f481041201c1c00d80300015803809061409002040d419410003d150380d50034030020400c1e52a0001040e01541c0031078119603250700318810803181d5207294008400144007844217210a81d00040d0080985e82c49040c05450480340d1340b01103a002c0d5080d0100c00c810f00640e010f01214640503040282621000c0c0e00502c800d002d400b0b40c0d00e42180310040301801a902034502040468040d00040082c0702062610742d144c140c4611800c2ca03107a00c82c504410900001040902c00c3c0191400315034042c80199660381e250030700050004000303a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 297213552 1250 297212302 297212339
    0x106170d14130605090126011503140103050106050a061412041121010c020a02090415150303080603100501082a030109030201060f0509010f09090615030b060a09020301 74
    0x42030000da807146401c200e000341e8603200744020409102c10b03190b4100501c0354000360401408680b01d02d404140300d1100c2a09460081e0400100300c0c800da00e070140e800603000348910514140350b600d00b583c885c0500e08042d0a4041c5000704008a0964908828020f0398850b42e400301040100c03180420b40d034005000201c0d0a030a0f0403600b0424189c07943d04040c007100c0c00e0f071185240c1c0010030781600407007061910340481c4c250b06004000c0080b8442d44105a031940c07441780c0001e42c008030540002e80014103145000b169401c4c6482c000620001e15408242002d05940003a00425030b1101004981d26080042c3e5014203240c003018425549024440c0340e507120340c003040000c070040101210300c04131021150341001d2a0000c00a04ca20b80c02402e02074000d200502409101e071b83c0c036040c0440c05040407041981202d030740309600c000345403401c004800100045282120002d4452807004030440802000d40095801f0f020081418180341c01084081031065126184090062004004a04440c014100310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 297214802 1250 297213552 297213557
    0xf1d060415020307053a150b0f0a03020c16060804061a010e09070e06040b0c010b0d0308010302010f0207080a080d0e120301060311040801050702150a090209070c210305090106170d 79
    0x21b031001e03800485c401407945942d40ca0f58420243c0c054600d00c10720742080c401030030500e4401040980311002d01800d88164000100b4206040110b021361038403c1e0700500c080072401d01a200e1807030031001500070030900d070b03440100002c014074107000a000301c0780701e61a40d420502c29440c0d00302580400117414107011044551080300c2c1d800008810710301950021816040c0208030613640d41c0c5a007013004594002c80e0280240c1d40c82c1100f41641401c0c0820804035840d0140c4440e04141c1c81c560044460340140300320b1400f107003d820340004280c1020072412031424854074206e40c5607903078889034008507056041e821115510540044161102e5941100d05582032803071301044100310230700c103400144a10352100c0d08546c81c182c100203980b036000c15005c401e104204000070003900c0724051070059810340040694000b00c40000f10700101c0c05a0500f100c041d206036070074000f60080190222180442105580220b6150400c12024280a00c20317040500070649840300b0710190802c41a6482900c19080f009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 297216052 1250 297214802 297214837
    0xa0f08041a041a25082205120c0d141911010b0316030501050c04080c1c0209090109050d02120301050f0411070c090b090603100f1d06041502030705 65
    0x207020b50070843c00e04050f0003101e0304000341004000e5030407031541e040741c213000f45904c0440d15400c1845030001c030340100d0b4040c8400342007203400341254100900f2088222114403d007400b045c00e0100031005002d06841715001b400c000080707460050f0045a60099024444008110112041c089890390898180c00c2d40340c2503603032003404280e5900501c0001c00309681032050706116001504014010f8084d80d00c140c0c001e2103291508000400075000340c1c05083d085403c0b0000040d45810100f046d0b103034000300c5400c1c500c0d4800080c0c02045084000307039000c41c6141d45900144041c030004004228050038584011b1880c1907680807414014001805803074400d010300781c500803680e6101c0d08001b05101028403540c1d03403035003107107040c4881c08414030626100030b0419a09034010700e011031003648582d0010340031300b941070140d0079a20010580d00c1800d030000782d80d5580303600900c00c86104c0704ca0003040d0074004084078140703421b01c1d610b0035034015840395450340100200011075920506684808003100400075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 297217302 1250 297216052 297216061
    0x10f020f030f06042c0706180603050903040e09010b090f100e0903092107120f02040510080105091f09020a0e09210a030e0109260415050a0f08041a 65
    0x200036014101010740515003407039458442191034118030040c1e903c5e8038212240b1595030b540c1a5584404410071540a030b40405040012900981225074000e08100a4a142640f00c0910a20502c07080d0303981e800b942c0d910411200582840c1101c0d079000009005210f03218540b001c000e400d404914001d51510320030b0903020403c1c2d500100140c0303500c0d00c8000c01b078000d4005440000940c03482400d0740240c20348142600042d00039100540c806125802c4160803522a281e83c0038840034000151881e40504000c01002030601401e01c03502d40140c55402c00f9041c0b4000348445480706950059a01c4d204078680300c28980143e80380700d02c4004480e41c00000f0b580680d180c0b460a4108440162032400c3c11a21142c403981c0c40c081070008015650039914200203c140004000d401c039402c1101c010070300410334603014641c81d11007a0610500200c01002460251110200070500081c0a8948045080442e81f0010315401c00d51710701901c40305162401c410300d015161140040c01b4007070b260740220048000324 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 297218552 1250 297217302 297217309
    0x920180307030503070b061c080301090c020a05070e0a0c08010f0527041a0702030a02100203130f06020703030e0a0305180402042d0b0a140a0903020307030b09010f020f030f06 77
    0x840007540c1000c01daa858445504129080e95007c482a0340b0070441079020102c6018817940f420314080d0450215400c41c0e08103000701e801050b401d0b45070019407041c0103000000460030800e0101414200300e001a80742000c860f0901900c032002c1c4410140244040140035103044a0105030454004032046540303c1400c0c0084a40c80a61402c2c241c540c0900030100424005404070001c00094074008260040c2d940840498890007182e02000058100511090f00d1040c1da0b00510303007245805506507262010b035030b60b800310f41c4c0203c40c04071202034000c1600000d140e0140309038240c181080002e41a080215a4014018030400114210544144040100c0c680f00d95054038080c18800c2c45250072412002d00d0003806ca100e11400042c0c00034000c0c2c000c0756502d20501904d102400c80c5c0c9400c3e003c2c100001801e812500326003014401c1283c1c10100002581e0304004070341c003d40c01550381d1009400c00503c0b8509440e42020905a2180100002480f0345846011294001c0300740c11703082d82e15103400000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 297219802 1250 297218552 297218563
    0xb0402040302091503120c0c100e030a0521090d12030b0603010305011415010c02060702040e03030709090b0105041412010b030f010b0a050a050a05010507060605060d020409201803 79
    0x80c3d0091450000c00c8144290b42199155215040342215071074107010203100490320030325201e1150703904003030248622400e019440d003644007414104028070034804000b0a20700505030801b541d040d804200c040400010701010900348a81e902c010030700c1c0001d03140100780c216001c1c0c0c600400444518941c902d250340320368003914048070000d01003503580d6501c0c20f029005e00966a00401ca16207002e0105415002c0032310907500000d011b85135141c55170856002c02c0007036000100c059802c26140c5441079068402800214440c43d1603480e030444c1d089c20b000c507003021110042c040d50b06000003000b050006a1990800300381d00b4500b00d03000c03140d0003030081c205405000e201004640521401d80f401d5038a003010b40201c400003505440200312141d40c0e40c104038051150b4801c0a411480000060015522900041031080e0150a000c201c3d503903290086501540f05c00501402158041024480e12a103400f91300404000400c2851140b4105400403450380f050954032003290030700040081e10394074180300303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 297221052 1250 297219802 297219809
    0x618081e0d060e04110103050f06130f020403050109030908151503030d0603030504060e03150f090312090303010302100e0108010501232101080304030b160306080d11010f18060b040204 81
    0xc1c000c541d0780f154240040c010685040f90100c42203030b6110095486032050b40d1042041c0801c20000d91141418098001d440d00b0324104455228014003556242600040000b0b51094000161051a900300180f05006c82e401c03043c01c50b080440b0719840c003011942525002600043c20200c0c120585000915620a02ca10301c0901410445c00100749900040500212461034a0f40600c5040ca6010103403940c410345003c0800d848003c0203c5c4101400c800426488405441140d190440415046052603011240c2c00c1403030344000300520840c24800098514041c4a0820f03200304080d280c00640748100500402d410032806a01d0703062040b1034018070490001100506960720b45110340401c00d0002c82e4851b034410b060360786000103039002d0000f0455007101d400100208994581040311a4142d00b2034060104240c0c5421010030280020301136020350200a4903255900e450b18589582520500094007408510380a10395000110040c00d05a00c4c40d440740000540e0300301640000c00a020320780 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 297222302 1250 297221052 297221077
    0x3040b131407060e061e07080403050a2006031e0601050f2d1c0905071502010212150d031218050706080f0606090603090f0f0102070618081e 62
    0x1d407400d00e60702000c6080010344a141d540c001042d02824240501449001980c045030490f03c0c050085224080002d0244c0070310030251240b400b60b8a407182460901c4d141c03415110556000030509040860700c4400c8110607094981c21708620b404104041e110400280d0000e80744580c800184090b0b10a00844015a007207044240d100c40c0c2607640c0c05d000b10080ca4446002591300d66601084550203002e6510104c41c1a0403c00c0809580420704040c1c007001100b1501849503141c040b41d483c127046a000c1c0c01c000700da40010b841d000300643c1900b040e040a080c240342088030352000e0b80c1c552070b40322580c44510b41500b880c083c80b0868841c0700c001441602c002c000440041a00903040000116001080b615240c1d076583c0c280c0c85a11900002c40ca0603250301e079028a00f004900c1032414031070061940802d0035010b489504411070510782c1881c4140600c450b00c2c2e5400074062040128a101315040864441200ca07416806551004842d118460304e0101e4407000f01c41039042a9081c0c011500c20b000340f103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 297223552 1250 297222302 297222323
    0x71202010e010606030e0709020403080910050c0109031d090106080c0a11071d010e060108160c020a090209040606030216140a14010203100e04050d030b0303040911030412050f03040b13 81
    0x1e00c0c005008050201120a06c0c0c0548100000c00b03591600a58040d40e4204c2c81c1e00e1700e4400c0c00801c1020f5403000048130741c103105090244072150202071040c20407040c001e4880d0025103c250340404021607001002c076208a0540005011b5941d110104660140590103041d6940040d0207003655041441d200108031132140010100d01c070001016103520540c03000020368206d9888000c2800c181c0d20454000d40062594000190342c0e140c0d034501040d44008030700b0501c401c1c100c29008211009456000350026076000154285c0a0505220f09001000107140840c2082001e90b0b03102d64640c2c0303581010300512000c8030f10648100e001e014074104168032062082c49000c40d07141c0c83d4080c0d00115800400809a40e00006d0011500c800f01845250300001800c814a4011420350040180c1c10040d50188801d000206031800c40f44903c891607848100e4240e2245800e2807d01070400e00c2d107084404000d030a1040c812a0070104064940040d8401d1a400d0741ea922940501900030600728090130501c4ac0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 297224802 1250 297223552 297223559
    0x20d06051306030b071b0318150201200a08040b090c0603070c060605040903080f07030e070303031a0d1e0203030910030212011703070305090d0f290c071202010e0106 73
    0xa42e0010003104d11800c2c034520740daa40c0c10700c1526000b0400081204600700120050006403007001c48199506410b01d030040304907101c1101001c562400024880543c0d50341d00c0c40c0c1107411b1000100229211941051442c0505480e0020a404000f4000a01c580e01000102c1e000980034065a80032000203004140c680c07900c000c0007000d5100c1120244e401900d8a040441d9906180c096002d800e505611030022644a00d407004040c00c0c0300910610406903103005035142d81c2001c0c00010002d5000780e4001c07990340082400e01101c1d00400da41d09224000385115000041e200d01c0d0311403107141d0000315481e1119103600100e815440360b0505a07a124500030451007980e40c0590291400e580045000b50607681c881c10070944041c1c403c0682c610a90007881981c0001c0e100d100248444100034000450507540c5948058003035048010488218000441600040d242c0d00d02044c4254201c0640581c0d0f801e00800c070b200c40348120320029000159441c4105038450003500a500040300900081045659 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 297226052 1250 297224802 297224839
    0x11a04051b270a230f122103070219050f060103060501031202120904020a030b03071d0a0c0507030503040201030b150406030e16090902010c060c0e0405090a0b0a020d0605 75
    0x4200707140640550030700e11212103c0c2841103024041e20040b0b0490070b5007000f07144040d140b0762074103900c1315401041d41d40032003299110450383c0b80200403001d000f000100100980210031403004080b164640300180100003415a000a00e0310100d0101085090802c43e00d081c1242807801e100c1c81c4280e64404c41c0000005c020031680501e0403203020b61140d401000301010308030784500041c2c1c0760707a00c0702c071043c8540c0e1010310300f650050144d60700908001844510a4000ca400d02d44a548150f4807208900341014003003e45050b010307480007001d5810017400303c0e003010141040c001d44a0181c2001008400034085900951103074100803801081c0303100c82024111000880d07481400351100103800d01401c420710b50b00009054071411810200800b249042141c480d00500204009a04000c0c0f074074209030201d400ca11410480b8515030fa43c560010340c400052106035a000b82100000364800b50064011485901551b0340107444000b0160f500d2200b098403801400741d0307402c050b90202a0440e010480714 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 297227302 1250 297226052 297226087
    0x14062407080c100c0f350103050a0b070c0309120303060503011b0e0f0f2412010f050d030f0305060a1d0402091b03150103090602210108011a04051b 65
    0x661000d00038400b00300004c035400e00b0000c8000c0c0100351b8001d43d55461400e8040501c844088815229840389a201c010100c4d030302082e03005a0b01030700035000003414484a1924550710061508042c9402e072007651f070080c80141d079803045451075003010b0f805004151007608448000c26008001f401207444002a0050a12100c5e0042c80410b02c0707181c1035009810040107034250048003c24103011003008406101d100c1c0f64101500c2241604089900b081003200c3e00600b0303021010b2000c56039151b0500003550300c1d45409401003031180045000460020b83e0060b00c42d0034520300351801103030700d84440d804581d4003282c0b1b801183c112075a00c1e14200c1021400c0010300e1040e8000c9503025100d0300c130002c4942c9a140c1561110040030306c00c100043e000c0307010020019815806140c0041c0c0104182c907501c0890300202e02d0300c2000c07550b1544c400705140c4412912030142c01000f00070460740d640018951402007500004034011910707a4000303030000301c1e01040303440700181c081501c980c0c40760391601003510007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 297228552 1250 297227302 297227323
    0x6030921051209010612021e100c0b06010813021903020a060c0b0a0509071a0d021902011b0203030601030e071502010c08070201060b0403031202091009080114062407080c 75
    0x2c6040000158400e00140a0f00040b108001010004603559400340807040a0b5210601004c0c02a148162040d03145d0481d400b00902e01076403041c600803410702c0c140d100f80e84041c1c80d9504200703c68041c09100c41c12400c803003e4155044032864404e04080c950101d110481da0310181d401080505c0004160b40c0002c04650454032589194903203035182048881219030640302c1003515848440288240001654003980030500d284101d4100151a19444c05907070001140329452110450f031000e5058090003000300b8800070068440ba01a00c0e00c0c8003e6590000803c841d04044e10792494201568050100c01d000d1703c08042040382d01941c2e0301010740a230480d13800700c6001035001000104424410b00c1103206541029449914041c81c3d030324102c0d0348008910540e01515800c210441c07443c1d840548180080480d92075207030040345400c81300350860b4178510226544203024001c0085030799a0b5404c1503243c4185c00010810000001c1c40c03c82c0b0350082000052803000d00080c250103da40005000405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 297229802 1250 297228552 297228577
    0x309060c02220c0909050405060435090906030c090c0d020d020309011506050406090303050f041e05030601410901060e0307050409120804080d060e010e1f0603092105 73
    0x4139640c925002c1c0444c0c6045074040c0c003030b402290200d400240c43c42c000d4440c071144403100c0451035142c1070403503100c990540350402c41100c00207400841410710b40340035940801c044011b014241500408248a24401800808004000141c0c8281c0300340d282c3c19a407150503400e030210b4491412806031402459801d0614245142020b0001419403043c41194140c0d48580c2e1100056440e5903010340b4150841e54814400050902020510480403050400050040318503109114501000d0504002d03043e04009101150710440711b584620526800c0d100301c40c9185d8207000071030703980152240104e22219003075025610ba07000143c1e0a038088100542e5000031402d4420030307540c0358200421030b481900003e0044900300b00640caa54051008181d201e03001d491442d02d005007200a010071101160010701c419105600107000f585158001a41d0010180201d041e5003507090f9801003441b82548545000c042e10307402a981042058105842202d4191494004040803a4800307000c82d0001c50141c0103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 297231052 1250 297229802 297229817
    0x3160c0305060f01080a0b0601030603080c01050a0e0d050a1803061d0c060315091305030c03041e030519111519080f060d05010915020a17040309060c02220c 69
    0x2d0348540603c82d541240d41c503500416510241756900015000c3c010101c60500d65a0758000001c43d00040040403400d90f44000000c103460125000000c4800c0e000007104107a00461901001d00d81000c04c5445100e4581002144911003a0300c011118030b260f0401407407581884100070300880765803046040b010380b000985803081e40210600ca900e00003101d4201c0e44020b190030106441c00e01c9124030340c101808606140f90100c141c0c0f00c0c1031540d13001c102156aa9400090108a0000001c40c0c00070203030454488038004070300c4c54469558605040700c1825004050340c40c164104020f00000e0180003501420172070114000002880107a00300c0700780c40950801440f4031111040c0301e80350452041c03110442d500e00c281c84034828060503646074039080b241036580c3d0303584c400404d10102120040300306a00700940c0c1d0b100e00c4000201486041050110100414418000000e403c1003d01007940c14074031300f00c00e201c085800021501c3c0d040d8404440004004000e9002c4603005812050032018551241c0c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 297232302 1250 297231052 297231061
    0xe2101020d1d06060d0209071e0f030e030702090a0c1115151210050712090b060f010503010312080406060e0a0b04061e030204150e18150f13030203160c030506 70
    0x50301ca643c11289198000e943c00c0c03007800140362945e06941c00a00c241707031580109510f0544880041000001c0c00042401001010a603c0d8035024240c0c034140154040c0d418442d0545c0070500406000e400e684440342c03606088101d441c4078001200046403007404441c64000c41d40c040e40c131800760131307030341c100b10311091050042250409240c0c019000c00314400a10074204c1051300d44000b004060158001c1244c002d141c001c4c0e1000c60b01800705c07128001c102280c11801c00c40c00300445903030704141281c10b000c420310041010503025100292545194140030100f035a4614141c40140003030340000003a500044107011002c905070340641702010050341c04004441d203590125969180c00d0152200c40d060a036401d00c01810560090101003191312182803d02d61100fa450b14080000c48091b819000c003021550009402000250300702c03941b807100559070f4140480c0e14018443cac01008128402c60066000c0101842001150342138607454000034031042d402d2821880401c0c2a11051340c5d54454040880d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 297233552 1250 297232302 297232361
    0x3061e05070c020d170d0203010e070804050a0b0615030c03160201021e0913050924071b020d0b07020109140309010e01110109020306070c02100e010e2101020d 70
    0x103402444a82c40b821110441e0f41e0802100b0000102c04641c5035080c100c03801072210300702d00035068007100c01d00c01503143d60601c0e010700400d0100402803400c0059000278003000c03820108480440d1a00050340b00d0895440c0000f07c5d0079640540ca4084d01c080d00081003140801d4120701460060241c813140e080c0080d80c500c404c902f03034050900c01d407010100c20f440300c50b500d04949004066080b00a811024118415051481155011a105641070304550114001c9405428080c6540c9207141f00382119402c020310014550700141d8124984075645c00d403a5815076540503000e00c0e02030350054071000b040c5001c5e04001d0103800c5400046994208030394140c2411030004c0b00707481c0072a006940c0c3d05c282c510200e0046070303214501102c901265603a0714035400503841c14800ca51090515031903100302e041991043c0140d840101002c0b20402003000146a07150381d0008480a00b81c1c0b0449030401c1c0d40248030b079246204140080c0d0344009600c002070301c800304505504440200314188031000308507503490201c3c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 297234802 1250 297233552 297233561
    0x30d0806011d0406180212010f0305060412021009050d140c1510090c17090609100b1201060e09210a0f0e0301050720010209010e0f030c03030403061e 66
    0x10340303001c5030b030003400000c1c80c1403021010b42060800a10100e50749079600d20000f848500940c0c2000d9135500020b6010310391035000d01a600600d11140d280801d0f03031a680b034030394070303028003500040003004c01103d103203e0140f081000400302d01280404001112541c138050303940349200d050702d801182c048411141769180010907552500d03080c2d000340c403c1c481385143c00644405c2c010a0b00162540788100400e102c009031145041140d0541c84e94044a95080c80d41e81200c1402030041d041580000d00b003003424400401d042c1010601a00b010070401071840c00140340d42d003000d00d11100c0b0340c40d14600103001c00149074007600400100301603031a900c641e00100c4035420944031021103400010090490300d9841100204100c030020304d001690380c2c0300040001e00352401a60094001001030b6a5040c13105520042d040041c01c00100031443d110030600007a01c1101c01c4d4400500c074a0030a294504582c8052010618440c8010305403039451743c60b4039182000b000004482d0300c0c1d2a803800d1850b0701c15882e034801c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 297236052 1250 297234802 297234811
    0x40c180c02010e0a080d0c090806010e07020727050606090d030305012103090308070203071703130510020a0b0c0403021c031101050c0f07061410090e0307020a0b030a020403080d0902030d08 83
    0x705c0300d1030b012aa10812003d4060340c441182000803503100050b0b0300780700b8000710740a80041c0180c0420350820400080c508205500107591448100c072401c10f05d03181c07041c111061146420004a140c1c3d40e0f80000074254044d43e80d0743d6410032403800c1145c0802d64141d0001d4166aa8000c401d03504c40108504102507041c200c0c0018080b4200342800d0002c2001ca40c003030300001e88004c0880d40201c2c0c84151010016406918019040e0b201081c1c560f4010200c0580c0c00c054807068511b412000d524400081d40e45110180c007501d68000305003c5221603409074201d8020755009000d204030b15001c148142c040d03480e062410380026110b03040c407031504207041c01090300545409542c1c2e0708008180e200c0102603402402c04484056a441040c0d00442803060000e12541c06000c20303d81140c40d206007001641d5036003d0694080e0010410300005070348106900c410f68040c040440e40f41d0b80d0342403e00009201d1a0009403a02202040e2009402541e4100c100b001d4800d070141c0b80305070003a000c19a040704003500c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 297237302 1250 297236052 297236063
    0x2060a0e150a02090a0e01030b06010f050412030e0a060c0c0b0301031a07031b050415080c0a050c03120c0913051608060103090803091605030a1109040c180c02010e0a 73
    0x40c0c80150049000e01400d80210b040000186402e83d40800660188141e6212181c540c40f428010021702541ca03542d00c1d4801030038241003c00100c42d0b01c00504600c5180503801d954030801580609051240402d45400d01c2c0281c20f42140948410300506441295101151401c00d603080100343e5100300380980341220b5002401c0d40494401c4110781174002002808030080654660719503950b010108407104010300c60392155a17641d810080c40306070100d0164500000d1104000902242504103011540c5400e11442e0581d1079002992070b50341544a6400010803184c07000c8280f00044a90318000d00c60381c07200f100c64010020740c44030308406071042201c1c500e02c01000441c0c01c180c6c00d802074150355807001c414900001e03404669503070b1003059002510392102640c05000c1d02100000d50f428250050941100145580c0c0483d40c0e459021a0000311702da4081c10464011804000c04070b039601010b07140c0c1e2001000c29540c1342c0a24801480c05110306030043d800d111581222400111b141e81c180c0350841d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 297238552 1250 297237302 297237313
    0x1050d03120f0e06040b010305060a06060903020f0105041502010b030d110d0e03010204090609020903010c08040506041b1a0c15130f02060c030f07050d02340801110403020102060a0e 80
    0xc01c0100010464508030700340301a19114060b5a505080c40503a22884c81803c0340e484950450620301d03d00b2000420007900c840c83c00340b0601c09180c00a02c42c00840341e0480300510314804840049030140942c0c0d0080010380e00030700d02010025019000080501c07400e40440302480c10b03000c0300301c0b00700c1903685843c1029080948010140382c071941c2a5481c0070390140c00585000d666010603800c54083c4c1d44079070380056010884141701d01d006e016100c0003046900c1c0030320050410342c035400d44408010300000d154260f8100303403003078200c0c0c0068400c4c0200307001704401500700c62074229050203500c103481200321b90083c80707500382c1d4000306030b441240695103038808450b480e030781c9070b07070361200d2001640060343d000d00c0074449401010300802c024145a0807a1b500740b512000b00b807070154a0724041011041c15500b01007100f25030396410340340e80000103007204540c01d404c1e40c050740e04068000e070716000818254280000c03403030742204840040040324404c1c2d01701d504959070764803900f01700c4100c2d000170509508031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 297239802 1250 297238552 297238577
    0x80f070e010309050109080a0e0f04110f0703031b090302120f0714030a0204050a0603150501030201051206010c020a08010203150d23100911010f030e060130050c040501050d03 77
    0x10f6482100118441c500000c0da80000341c440701c4080d000380c0c0710500014540c1c0c4840146080c100304882c00c000d010340341404028005580045240034480e0051424440844c0407000d00d84640c0000d517040504140200c01d0a4545600818810050005900595900104564030751001804003d0f60785190007410aa6051886200e00c098200b58100d81c0741c442c00f0010310140e6914420340e4002d041c03c10000a0152552500403001e02d10700c003001192034900001000580d810504031001401c8500451000c0d60300e90005031400e40361002d01a42001c445a40070440e010150300450140700c0c50a0002e40c074403250000c0040500322041c008208141c00b11068a0140000340102c40d442600000d40e004200382e4400f49080301c51b0741c90151107440c100c003920b403071550300301940c020040c641d40303010b01c510f240e40b040e0955502410f1040c10780384c580d46001d0008802c101d120038103001d9481c0b41c101c40c10140a0078919a9011542c450313a10461608000140b03d103004803203045d000340c0c185c031400300c0c0101c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 297241052 1250 297239802 297239807
    0x50c0d050c01141501030e060103030c06020306040e01090b15040905190c1e0303030c05030c180f150702040c1817031303050f06010605090a090b030309060a020a03080f070e01 77
    0x4100c003141415900e44000076404021070203d1849410075203030818081d0389840004054034405074225803144c0003000103002096100e124105401c0d00410301580d2074603090007050081500e840d11300655441e001c0340c50104403643c4103260203910242d003290311400c0d405d000c0008072041c01500600a50103140c91994515000ea24407038424001c0c4204541950f503482c078410740300303404150840d803542041424003c054140c45108480391040ca0410700f540f13020824171006106000f40180300703259a074083c504580e02d000707024a1811014104e0f003060600250541029044140124801c0781090351410000303106014044100c12035420001c4d0341442e102c800b82c032400f00408450b006000403c00701d1144035400f1806401148103c00414000000800642c1080070603000740040100810024420344c0d0743d0b0041030140c8031072440000300708214200080c0380d07126034414076030060700108820300310340e070045601c0c128240030b0345440720140c0d034800340300560000c1280c016021401ca001e14609951 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 297242302 1250 297241052 297241057
    0x11031c050c130305070608010f0f030305090a030606170f0105060907050a1e0504081b01050a030b010512150307090c08150d0b040b06010f0e031b2b060c050c0d05 71
    0x8680075451441c1010b007011845044229400a40c0d55500151003040304e1540846903a00400000404041c95070510b840e88071105000c1c8070103070802c07074085030141c0c49a4850f42038900070f6a1003401000031943d15100464122008104c40b04503004080f1150365004040c016988582402040c10030310381d840352410340d09a0064041107080001d154828003200010741600c600384021911525100c5107080e03003162400e1180801c1d115071002d500503100c4166000300035140200d64074140412080400b400483d014020000101e1080b4802020b00039840150116801d55580a6055814103521043c3c1802910510b801500c005100703100000e01541c0300c40381d40c8ac001d09000b400c030844d54001d80c8070550000c0c010355082c1e42c084112030a1164541c0c200c5105010030b0345a080c4601180c205c680000d071034900f0503014802030304200080c28a16030b20b0f003500c2d880c17408800101c0000401e048040b130717a440c2e24000d001c80f070251401820701d800c20301680039644040c40c0140140501c0a4a04041301c194 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 297243552 1250 297242302 297242311
    0xb120708090f0a03020a110f030c090703020c030711090c160602030402011106070908010b030706020a110d0c03060902040609050f0601030c0e040c110c1206011203121b11031c05 78
    0xd00410030708200600c0103200544282c0d000b41c0c011b01500aa504180400f16808011544107514020008410ba00e0100c0d2650714240200c80c80d40c0d0a40d24034009030083c1c89070701c074824414080001c0540c20000c2902901c0726038030003500d80154666840100701d4051080c40c3c46600800b40300c0c0090f40000b1250740003140c0c0144107141c5095080b01070215140f82503003c1d0f4a14000c03451f242d02c20b00c0341120034418032292843c114000c100d214600715020f51181074920001c0d05402074040c0000c11034552400c9440d02c181c0c0005040400c40d0b4908140004014030b00040384620b09141d00020101d40900403070f80034600c1103005245d50707180d820040d0002e001807448a800e00000c110a41c410741d03542d109031145100b00c1d4840128240e1806040350400c041c402c141c03881003515030b035030391a2150009005415500304100103006c6044908080c5c0703000031032412041c0c0d2203003000d5260081e043e083c800d10800c2400c5484005411317145180541d00c0340100019a03495003a030f000c00202c00300d025049540c02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 297244802 1250 297243552 297243571
    0x1d0f0c22020405060406050304020f01050405060a0507060e07080f0601060302030402010f1d0a0803040617040803041704080319030c0c02100e040b060307211808031e010f09060b120708 81
    0x82070760f5400030607000d8000394814004280b0100c02c102c158240350100383c070148024a010303440d2a00300300015007103000e040301c000c0400c41c000c00d400b010045c080c3e001140066070035045841c0b699070b40d0403a566507001d0001c08081c0b80203000c000501e0501034000d90f40600d9058555981a118a2004540a00720340c901c00b0120200004140c04e04e0325160040c0340038080d0b41d030140d1f64960800201512610140c03003246050340722175040101240c0342500341c0390400e07802014001986048401041ea501590304008085d000018010050355040928071200c40c03044c0d2001d00400f10a2031040d5900c601040000c0e400c1005541d4504c10548540040c071203c030401040002c03008480000310701e0035003040f40d03020045010418000d000c2c8051035040090300800c180240704000034001044214030207100b008160800100104a038056540c02000e0f04848120b040a5250794413440502018040d2103034900705440c114001c541e00c450361007151f80d0500c0d00c16952509841d000c0d411200280010696000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 297246052 1250 297244802 297244807
    0x803040323090f06070c0e04021809060609011e032310090209010e09070b0d3201170613020303070b1009060b07200102010b041d0f0c2202 61
    0x4802800305481411910000d0745515444000140700070700002c0000302c1d1241c01e042c4112400208505d4421041e2124106102565290341c8049165004001d0783d502a0b80b01c54010000120740c0041c9140c420001180d0410711a6600c21441140c450715004143d4004801d820600c00300d082c0d80314040440c40c1006482e0b040040c103080050400d040180c51512040d01c440b66101986020030032a0701400391454520300c1410840c0f022907994190344aa11101900401c160f001c030b101c0bc1d480100380d030002c10b0785015801a403c2000c801c6410139001c90448411200020071036010302c200803070124a02e01c004001035120140c4587c41200d032400100e0307052008100480004600d6104a4002c507101c100c080d003c0c07418100c880064401d030780c0080543c0d0400744030480208000b016040b1401404050140780982c01c2c0340101e01401d041001e81e0340103802c003c5484011180d6006840c40903134a80d0035a02c51080e031504d02c0c2e440300f5901d400d09030302c102d4441c040e0382040c030001107a0801d8419800f0051 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 297247302 1250 297246052 297246077
    0x12080a0f140a091404020415030e0102090a09050a1b0f08060a0504020406082401140904060b0c0a020405060f0102070302060a2a1b0302061c020d020d02030603150702070308030403 79
    0x241d5a41c03102101a000400b00e0400b08020000a985203003410f008a40175030915091498405442107100b461604050316080c2940740070300298100c426818026244400d415212280080908020740d95214031918128601c0c0d02d4202040d521601d00c0102d590fa07c152a064040854109002410700c3d90300000c18600092281d40b14801040200942c4e1503816562a24102d203544403040715400b0001550a2045110240e901503ca0604403048603005500c99018001240042030150482d0300800c0000810955080303000a418030000e01c00c0301c0c14080c230342e2070400b402500036214940300e0150703128100c04d00040ca0544043c0580601c1072500844c80d0942058907406c640c007400200841c0400240b04006008035403289075804008408030b070000e14550307804a03003540300e840b0107424546140000c41401d034080d90125200c100392031a082d5115565000c101c002035000b0b440183c440d01c6008180059421400c40191180046030003030280e141c91905c030003001e03a200502c11000c02c0844000c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 297248552 1250 297247302 297247337
    0x210b04020703020c03160b0d1116060203060a1a040b03130803010609030201170f160e0604090c08010806010e460c090f1203020307050a0f05060112080a0f 68
    0x109a100e00950040c800e40380030704d05140c14000348030103120300782c00b40c51014400000d1480c120381d04c0b0500340900080310254003080d100d081c01901032902041640a030b00700b0900a20b40c01450003090203d803000002551010340c0e564003810601420001b4030244000c20084940c00f015542c8881c0304441e8942160385959079402e1507200360425004a5564001441036507801000c041014850901410700c40c20301c50400d100b0010014441022440d140070103802040c81450f01d032140c0c100240a080c3c0b100c0d100e105aa01800c07042907250005411070000055004000903210304880e00f0b101030540300c2c0c607030641001c2a10031048c07000e100c0d40b403900451540100041c02e04000030041e440701451075a240a06481911070501c44001003014807038041c03010960520b4014100c900940004030403100f907150aa00754098010054998040c0071904820311008030030780030616125600740c80c001c2c0c0e20744614100100307944502514412050108600f014002d80101d41c00788100d007010000c003080003ca0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 297249802 1250 297248552 297248557
    0x1302060d0905061605090d0804051e03100b130207020607170304060e03040602120903070806010e01080c010f08150a080706020102070204050105100c080a1e0302190e01210b0402 78
    0x803032000e19941c040c0e1a0a000042c80391603000030500140d0ba50042d2529402030043c0034055030305100d0400c1e1006138007008000130840d0000c0001500f40e00a0044500d0048401c02d038002001e07002c3e00591000d410040258443c4501e400b800504140c00041d400c400c1600a4110b26006c0341c02c514104807281c0400c1200c10380840d41f100c14044035a492820789059410380c2d2134034007003030004c0d80280801d00c00550041802004800e52003a0240c454003500000f030710b44070030b41d0301152540c060301001140c2500700e4144c06042e60034400840e108609814011215003e903440c1c0c03c2c00191a0b00c0201c3e0f01002084480110085c000301002c002c1916102518241a80c075071088001d44c2d800500c40d411400d0078014903005000c04c5914400414030b540001e0416254036034000c0800d5400074003800c00c5405807141c0c10003103c10400c4d2413090307100c424029000707520206444504400d42540000207034400c09200d1581c01c41a90784509a00f0f84038003091245034030359140884981c13a0511040d07151182e102 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 297251052 1250 297249802 297249817
    0xf0a03110c1518010c0c1a07020d0c081c05030705090f03060a1505060309120a0207030506130212010b01020a02060a020f010f0b0415150c03172e03020d0b130206 71
    0x1a02c5540b00a15465120014035054030310b41407051410002c0041050405084110390081c0d410349402122011070140740d115580e802036001e84040321490a0182d41a111800e039183c03201143c5e0004001441540b50300d16001d03a44000820030000a00c01030301ca140588010340010301600b4840c1d00c148002401d00f60110303600796440c0d039a099901c820300e160030200d5000704002e507905455030030070140070340e1541800205940850400100000864400c120700402103030031000351030043c00c081e00000c003809440344080e4801e1003051820181400180b1030000b862a0580041540d05896130034410142c01c03422801084d4040d2443c1c035a4500740030300031042c11300300d03525000440b10340c2e5400308002ca030308e0300d0b01100e507001481a05220721b402482c50f425031011103042ca40013994003807404031030741040120384507056064031082c010400c040700b2803c1c40100c020310085401c4503400b81202e020384c9051002a501c01000c2d60184080f0b00090f60b021b42242042d03582c8001c01020742c000c03036450b45c003001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 297252302 1250 297251052 297251089
    0xf09050c25080d09060c030510050102070302100e1203070506180a110406150806030706030908030a09061b020c012316060b091e010902040612020d060810060806090f0a03110c 77
    0x558006000c0c7c0c10710800d54019201e400e802d880600303280000350303900135600009004600310310506403200c0c0070f0042c1c03031840b10004044000079114008299220b1300800002c40c6d1900c10303a40404d400307a0141c034400712003480c1c1d0001410021040c2d01c4400400440d601c0660f00070390b5881000c20000300d59000b00c00280c404d41c5851846062420a01d49454040d40c000300c1014a4540c2c941e0009031003604994200081407404100b808403030600074014002008981d42c500d504088a0035206e80101e0440f80c182e009880304440000c0036400c1503030340d515240a2030303240c070381c02c00c11030000c03104282c8170035000381c05034800240c40140c581c04910260000c0e140201c03001c90044c18840100540c941c61405041650410350905240c030a0190024603d542000150354011400d450076120507400f00d00100104411105581100c01201d4001d050a002d40b4803a8011400090b12644000400303c80f001c128400030084515944c40071604a0010340880b4014007415444070210354459556050380480071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 297253552 1250 297252302 297252311
    0x10612030210021206010c082101030303141006031107020d0f050f010b01120209041b110d030b060703030b030a0c06020105011508060a0302090c0708040f09050c25080d0906 76
    0x1410007030701d032406201050b00e0b814010000c0900401c07280403d250001800e08245008058610f071060030350103001c010039006400682040c0c0a031f084107203d141200e019490030042c44c40f034aa1030710746540c0c04664070303100b40c0a6000100303c41846544a8400c0000c40340110742010b103943d0004615078a001c1c005c0e90b000125200000600906205070740084403400000c1005d000041e00180410781d90740c0900c00e140d0350224500605895540080d011240740450a14428525030300c050b0420f00c032800705c0c02d01031092680741445c84d030191003403005010380140110304110841c2c2c5c0c101d0207000e40489480d0103019140d403160024543c0390b524009801d00ba0000f00791076040244147c1051100740750201003090f80b00501500c0d03240d5082100c01d50360195a032810b41e1f90364001122040c4210032000f0a074040000300003a0880068428105541480d14184040c0c2ca40d52001c080c41d02a1020704841c00901661365030700d0b2612400c41800c101d1083c2c550504101600211000300c900c540c000b51102030300c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 297254802 1250 297253552 297253589
    0x32c03070f14030303100302010e1315030c090b030601050423071d01080f04120306081e0c2b0c031a0f0105010203031b0f041e030606050616060209120106 68
    0x241118072200143d00a505516050f019243c3d45c292500c0040d040c44540100c25106071a00300e55215915106030043c4500324600c038143c003c11110344401e030782c01141880d0100303189116018400d03464900400401c100e908040810005007042d070039144800c00c014850400c40f94018548074816006174540b0b55100e001c046002414000349407406041002400802800b01c003401d0300c041e00203400c0208c880301021308460a80081c00e01c0d8102c40b52034441c0145041080325150030301c0c0c10380c07141c01040d244400407500501410344856010120035040905100704079003034200d050807210340581803800500b0303034a07125550000c07440f01086140d05404400c008460410325030b00741c010902032009510754940f0384200c54100c00300084283d024000068135800a12494003510701a0698200460003014240700705104200c492004440c8503003000c8002407940360150590b82c4c0d075500d03803007421000d480a40e2058020350000c55000e238404442405184154800d2040300054a006020700350b078141d6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 297256052 1250 297254802 297254819
    0x1e1a040305150118140c1305150901030e1c180e07030203091504030815010905120304030c0602030307300615200c010f020703150203010f05030307032c03070f 70
    0x411036924030044c0d0030402803550f048a000c21080d408400c000e0801d0b03ca511903030b120401180c040c0d00280c3e000720628a001810301d0008024100100c003620100504602d8440303440c0c0b51400110000c07011600c01041d138207885e0040b0f03103d082583c000f80c8a0341d880c2c1c0e241c41201e034141c0800d8400e000000d41c08401c12000c200308105ca0003d01d158040341e11030307a01d496035004141c148020024044200400000300d42070740182910300c09404010483c40c0501c12020038551b60b40c00034801510345102440c00081c94034004000c40c0c0c0a030199958040c001100c1e0301924220504400c1102c000b44401c1c0c0040c4154030152140001809003600c448010440c00071008205240015942405c0b6500c180040008840000c1170003c00c013083c04c280d0859115030f0f00682c1008203075400039180c183c448900090700b819550085040c3ca4111698098140c0c035901450303928000c01c00010041580a4500015041c03607036180c1c007400b03603071582080c00c031724810f0040ba0170460350741d02c07407407801480031001d015612 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 297257302 1250 297256052 297256079
    0xd081810020a030e0a020d02060d020708070605040309150e0120011a0306060118050f011119230d080a0f0903090e0601031e0c020a0b04030e0a1e1a0403051501 70
    0x5148000510b156445c640005007a100b107110028428080080c43e030b1030410086e0107540b00c82e900f1032105034440c034090901c0000340c0b078121012030002c0d85403080828a1541c7e5801d04d200520300d940c030319602c061803100644502110a070520b1400c40c42d46100d40101e40300340910200e90b40c1c42c03040d5002682d40e40303052600d80403002e0250b40c10720505180e01d0400c18089001c0c4422114200e0b0016010980e07800140e03a00046040742200700d0095440c0300400700d100c880d51011746441032034500c94003026800303c016402c4c0d100420401030342262490300002c1e4440c401d090f4110050500008400c01c59a40c0c000444054880803000b10f07410384c804102c44210180c90ba544414282424040d01e8003040301895861886100d0090003955014115040341c820000584100c1d030154002d40a070a05050103403a50800c104000d119424154000c80e00c1100d003c80f086510b90007507440ea5400742007582f541203c054030010409100e00501c00080460350801c042c07440c40c218228500038650502030488010b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 297258552 1250 297257302 297257321
    0xc05030102040605161a1e1506250c1d0703140f1005030f070632210103150f0e07090e03070c1d09010b0a1202040b0d0605060f01110d081810020a03 65
    0x42e0b500410f00d2025480740300480cac40c1d26512007105030b20101800304210060001c40b0300588101200140840c0e545d903e0070141e440d61a01118100c1c165407861000c81c20345d031280c0b21845002c900031000c203887c82100c0b0701242d04488150301c4a800320303480768003003441c00c00f0581c00c80ea030769401250b04100e4103030084003916451800340000c02807602900c2d6080b9440055102e13200050760300003080c407401c00c040c8001c105a0040100d001d00f05507503c1c18840d03851034810b0180541940340032041c0030059030610600781241e80080290400038607100f0140014040ca03245404540010009000044d104182580c017901da001c1440c1c04140341e00075501d140003030003420300c0266850945002601c0d96a071034000110341c0030407941d8084c0c00f007920114010b85080843c0a4101500d0f24508081000f603412052003100242c0305019241ba4130001140c8411801d03101c0c284603040490740d0001c42e0312400240703030320903070109070705403c580b001100524045016094025040e400b05070007021980c140a41c40a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 297259802 1250 297258552 297258571
    0x10506011b05150712050403020a0210031a0f03010b060c0304150c0f1b0b0c060603060703020702181b1b070609080303060d03021e07030c05030102040605161a1e 71
    0xc0000c0e698969903550030460074152082110f500040001e84580b00388600218041820702c01407c00e0724001e5561080614101d116020740480180300911038440c0070b02e1501d004078280010250042400b000703a94403401d0a4042d521507681340e1440c1c5500303009180c8690b035400103540d5580787c040c1d90230401d86401b40900400603804034a0340403649040800c0744480c2c010202c075010700e00b288603081d03030103050b6403007006120004103083c1d82d103503c041803440c420182641500d040d0f031345d20790040f0128460300000030341c00f00c004581c130101040b0130091aa801000c0940181a2001c84008540d8642029803000300d90601e05880001c0b80d10280f01e08001410b00741000c1d243c15051481030764407400001c050358010b00101c407003030081c1071003000640801301501a1034401d00781b0041201d40c96904901080d1920f144024000802c2e04051080f5811602c0f0f40e65032506000552510110780c4080e010300780c80074414005907140d04402e1004c0c0c0b07030280b029400b801c21042000d0791403440701c44008003071681 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 297261052 1250 297259802 297259847
    0x4080106080a150525030207050d02030a140c0111130303021005060604031e120512060303070503070b04080c07060503011707061b06110408031c0b1e130e01050601 72
    0x1488290302070021107a4504046200da64404d0418115680e04603202c485d0840308140501644d055070040014074000e905039490300b100108140d81d42d106941c8480000340400240c0072608588a001d840101b140d04004a103403003071120100040d40244848801400076200d003041019010050705001c0c640009c014081c03860030400180301e5002c0c070f12014240b0181211041240007110f078400380b810b644003040300122907039510000c1041d0040f410303c1212880d044080340040c40c001003611002035022000b10b10f0f0220740da95070311840b0000751040300c1a032814044488007400511440000c1c051550381d0725142d40c50103005480d4071781e058004200300d0300904000d0000302d80c0151685010b141000c03419a0403031592a05500404508166004d6040017090208204601000820802c040c1d0040c1c018406502e1480c0360864420407501c80e4000850030091180307061012080400d40801080001c5203402c640b010001e0301c040c81a4801c4995580c2c0405c241903030010251050103011601400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 297262302 1250 297261052 297261073
    0x20304090614130506180601030b1e1002071a09060f040e040611030402090a0509030d0905070302030f070803040510050d150303090801020f070f1e030806010201060b0a050304030e0406080a080408010608 89
    0xc2d1085c00202c0780180c2c3d06d0090001891690182c3c000f060704a00181c1a900d4000c505180c1c1e584412402c2c080f2440b444021942c02c1030329100003a61010356000b004541d444c2c20743c000b1010580ea0009100366008030b801c0c800c0e000c1250342c0f407001d00010140349140d0981c5103030078a0030300c4c11105407039040030700898280240009070f2a2070030384c0d51780111801400100350301c075103100601c1d501030003004001d070900305115001040400b1881c402203070302c20b030301310b40300380710000e1449c0d4603144140502d0b091684144402c01c1a883c00c0d044801024485052140c80c0860301801442a903425a0300c2010343c00d070702e0380e04004150344120840000c150080085080403042c40401141d0721611002924044a0303051f4074050080d42803840c000610002e100180c550070381e1801a0981d5000c031220350165207041800107860000d401200c0591410b5903c8514558540e601580d41144004502d078210f655100b012440c0f0717808000140d01c940c02034040c80e17299468900403c1c00d40c6d000c1c0c0c110500c00d03007166000d003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 297263552 1250 297262302 297262309
    0x20106061d09060418140715020d14091206061009060e01050304080903012307050301140108040302120301090207060e03040b1218010c030e010b120303070f020304090614130506 78
    0x1c079880d841c101c0e808000d83c2c840b000058041c00100c041c184410705c0d039031041000c005c0d41002e103444900d080d8095661290341c441200d040855007000e090090381005440e85281e03449889007103244000c144442d0305020f030074030200789240c2d00551441c07400e60005091001c91300d061815034400724494a03080700c0d0f860400344024030084400302c07250f0601c6404004181008100d0080e0385031144040c008100e610440210f4102e0409504c414143c0f0881c940082010300c0e1145017241c0c141c4103202e050707050190080d0011105924010400d5085000b5443e0885003568004000c40c0204400d40c0301607160446407d1201c03c0741c1d00003400c20419030040008010001c00c43d800d6400070340d59000880490741d5443e141948610b800c10b02840709500e03285000c02100d4150f80040b4140c84224001c01c07500c0b42c0343c02840b1140c04c0d0701f2400602039100b880002e00c614440c8003191405000c0d40b058a040c07035514503100c41581e540d9000344110f264880000d0101d0300348a510040c0e5445211011f101904211010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 297264802 1250 297263552 297263597
    0x1081614090d020d060c08010e0105150c1c020f0d08090c10050f0a050a0e0301020913050901022a0d0206190c05120f0604050a0902180a110301030803040302010606 72
    0x14102850302207081e06156071844002e01d20309402a0590245103079910b001700040c046601004040340030003001042080c90196080d06841004d002c0142c65040400c16034556000341800c50007d110349010340c10001410301d00006224120b400500805061001c542d0a0070324401d440320030450114100030241c4000a08038a140b04140c4011801c0142103078112440d21508440d8042080001006207540340c3c0302c402400076034859030343c01c50302d0b41c2110105802c0c0d200d00c80605a000b040f911101e04c1581880d8000c0e03800401030000145840c00d2214a2a000c0601420003a0851054020703610582800e002111154450b40f010b00943d24040c0c500406243d441c40802503030076550f005245c446030143c4200c1c2c814514502640903d842d20380d0800c40e4151080710482d016906080116040c414140945c02c40700354010b01121419200c01a0690540b800521261085031282420524110f010000b14041d40c01020010790305d240c641000b9080d83d025501c14410403604c2c5820320040e1201a81 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 297266052 1250 297264802 297264827
    0x310020a020606100507081801020706050918220507170105060a03110a0b0301170c01020f0709090c0302060319050907030206161106160201030609020a0512090106080615010816 78
    0x440e0504603111341422145401580c000600c1a6000100c1081e80c00c240b140c0702251000907401c03250940d4503407200701d41e00e010701581d642c0c014602315540508000e801405a0f840310005500110408888010b03000d040c488a4040e20150001c00090042c040000380c5102c070010792034020b002900302500412280001d910010344440e0324840001c0041c2c4c0c80c2a00c240052240b000c4c016140d58403141060b00b1440302103109011380c850072070862100e500100c0d548400d00500005410500d103819034a4018004038442150a40c0314030401000680e01c000180d40954188074100741480f204100c000304231240a130440301d0540c419201000141d50740011036002d401408030306c2c817a014151a151220f00701c03514500c0c0c3d00407000f0075102202989145182c05690003680d0500089a407040d181040384140540d0b8400a04200664001350100290700d0342c2014404000142955541c550203080c20f0090751207890084c03203440035440b1980c2c0004d08603084481000720303040c030010041380544020540f18 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 297267302 1250 297266052 297266059
    0xa0c230c0a030206070213091a18010c020d030f0915060e0f0115030c120606020f0d05040b04030f020a03150506040f0b010f0f0c0503070503030403110316080f040306090c050310020a020606 83
    0x210007c501c00c5207600b00b46201c0340e01043e0f007482c1d02025825030b4414001110706500798256460310201d2000d05010b20902d0100e15005440300c00403018084020708100c0020011054071480400001040c0f14400c0a1042e85400c000a1071414007104a4001c00050802e946c1d000740c10700144040005162021840002410f0000c1e0007044104c0c1543c0402080107004a645d260480c001003d540110304407407100400000d6424940e81c500081e1868000c6000342041e8030300600041c0700080c201a50000700500007451300d40000c0d502d0351650280410f00840d40c08041d00d450500165082c540038190848030400d8040c0440e00c8801d00007001080c0383c2d000c900c2008041da4036504814050700e4609102074101054a076204030500341a0365951085e142200000c400f081c840000300e0780032090315503422035a07010300280d04058071281e0b42a00062100c1558040c100400000110f042c0705a14ac080c1c4604d0081c90351500e06010113040403a90f08500786c2c1c4600400c802c5101c6035001c90440e0740500e085 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 297268552 1250 297267302 297267319
    0xc060a0b04090519020102010b041401051c05030301120312050403050d090c080f0f0f0f1f0f05010909020f10141617040e13170a0c230c0a0302060702 66
    0x2030094101c0502c0540b1900450104000c20a00c040f0501c2d8114000e80003408100c00c0390042c8411030700d560a0440c1003100c070400502c1940f42004603600301c4010341801807200e24040c2c0742c081c1103a00c00e03400707030a02e016012001e40030950400000d4605951070344082006107026240a0018440e030455884c2d1265900300080030401c10080c58405401d40742c040f641168800e0710500d41c2c0d140d114001c00b106100c0c40c025040328081c0020f205480c00d019401a2016104009014130600d05100d43c000f40541c40d4460900c2c1c20200c0c0c42068004e00099002003804010390052210600c82c00e9402d5004200070b0300a95003090b00b003000f44c40c10b20310070301103a0b50314005900c40303114807a44014020300740562614200c10b55915130000e401a00c2101001c681640c55142500180d02c650120042010880d4078041d0b0700344d180311014140c002000d00b80081c02c1c1400740e8604401d01c0c0c0100010b6074000f164210768040c51402c2000d481c40e074100795009a4101d0544e0001411402840c00c024801d400c903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 297269802 1250 297268552 297268571
    0x91a040b0115080c1b01020d09020109090b010e010f02070504052701290103020c01060f15020a0213020c01200c071719030903240b090f0a0b060405031e060105060c060a 74
    0x528140c1d61545c56200000c40d200e008031141080a04040c0800f64002030300800d0208132240706100720001c9040586500d280c0104020040d07075104c2e08040e051040d030041c09400905c2e6103481c010140f20384195081c6401d85500780e0348071541201d14040301000340c0c0c503242d0302c0b8440b040080350f040400c21501c407096940f0703980b000048020740700e107095040303555090a000081d050340340621402a103a00490380c40c030340c43e2952002c80c0e6500001c14040d44c400b95402007aa0b4010039503006120000070341e000400e224803504180360740e688034240812800000000c44001581c01804050050324440c03201e40d86420900042560b550041c805c3e9001c0107140340040030405000301072402c01107074095260000d41d4a408480f0202d004420f501d8020f250511100016601c1c241100621908034404c0d01075803070301c50414140040440041c1c0680128007084045003e9608000b90800c00d48080b0010884840050030700307050110684c405406160300b4840c40400751408034903076600c0003001e000050307480103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 297271052 1250 297269802 297269827
    0x503041805070234030c080f0c1801050402091c0b160e010203040b030702011814151306050901060801090b04060c0c1a0a0603020a0e0f010e0603120d091a040b0115080c 74
    0x401c5c1d100404107906010006081c1001244014013484100e090341d820002c1042402400c01d42c14000340f0f0700c20141f01c018801e5241c01c0d80907004044000d0682d40410550503002d203946803552034103942034001d000400030540c440b000d0701c490004440c9061100003c3c12030010750303240218000c804c45050701100103070011380701358806508000411030309108103010b0300741018880461010940940101c503100c41044054001c40e601540f0300240007110f06420f6201c0c1001031074040c1041c80740b5521850002000303d400d00468640500030074051505003010314000c1c0845442141c3c82d4140801d50310150b000c42c1e110f0403c0020001030a40d09038056441686041c0188020b0b040203505ca2070f07004000c05c019500301e205a200310441d60302003105903211441d1001104e401c4454641c10307801101054030346590100906000c000d16a00410010b44503604c0c0c3d0003494201c1d84c1180813000400030001840b410003050f80c01468404d18901d49050040d5000f0b040c0c0300001c1608401c10000200c804000b071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 297272302 1250 297271052 297271153
    0x6040612140f01090c0905070e0a030303020711060a1206080105060603160c0209070914030703082709010803070506010611070608070c02040603060501080708070b090405070c05030418050702 84
    0x1582d20000b01320001e80c6180c000c2d84103c5a028459505280400080c0814000d4440302210b1600800441d0b21034550350f421000395000a80440c0c2640c0361507450905074440780b02070704c0e4815440d20b0395000c1400c0000d0720b8003120340c15880396010b41c1c1041e00b8010300e42c644400f26a003000c00300c1e100f0210013070303101c1090f22604070320300009400984a00c204017103a03a1003a1030205543c03c1000e00c4c00301c94000001c00da50780301e03140806003030110100520180e08084910700120004622481505412500d0003c0c4043c00300340d0140c0007075000006c00c44204002840b5080c00761105061030800708680c2e07000940d0341d4000e0f000d09002d000350711001c58561030042c00f102c0303903239036000f40140a11510b03480d2240140101b0300c43c103c294030980d180880e1504010600100b6038040c003020070f0a04c1450300c10400a0708002c0c1c480c034180002200c42ca40450b105000500180505074204440c2001d0688070608179840280a03804641080741e03540c1001d00881441001225000d150038000d0400841c8060541c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 297273552 1250 297272302 297272323
    0x703020904141905240403080105060310050402030a150f0605160809090907061b0302030f0d150b09090a05150d03020309040c0309050d08070504060c06060e07020c04050604061214 79
    0x14015008074401c0144c00107001c8003d0240c0b0b0503000310940c0d417518001e07140390309440007004510380c42e005100b241130280207903900c0541d802e51b001000703a4440c04501282d00a840c2c40c0c09072a01c50002d4241b2030380c05a840001031110420414419180ca0380041ca2400381c60000080c402c845640c0c81e0a205103003050302d07465600100800c9060070162a03c550700d200c1841340780003050721a80544984084000c3d0510700c160180c01a52034087c0b0a9a070075075940c0a0414150443d03034440c0041c2c0b1103005c510000d0040c1030191441070359085008201300c8480d000400100400d81040c0400841c03d1841080c880c090704182c4452031a8015864180c0c103600030782c929503030001d14114400c0703241075041d0040c0c10001c2c051400c1d6085090006001c0315422000c940b140003094040004104040c8104442d0b01010b02030784000881d907480380030300b4a1012007559414016403041410301c002d03140c540300e031640180003164100715a03407408003080803800c1445400360145c070b203440480b007120304180000b1019 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 297274802 1250 297273552 297273583
    0xb01020304030204021b0705120d080423061f05010c0201080a140903040303110d05190c17040602100902030705191a03011e120803040f05120417070302090414 70
    0x25100d50b9000e2001c6e0f08030100c03442d1000e21607900c002503503042800d0040c5050070440c02405100c10038a10a5a00340d1b00500201d400445001480b585400d165115140c03c078054409002d00d42403c15103d06c0510b030408803150b8060892804008a80e000307010f40208ae40d083c2002c1032555a0001240001c20170b40300303052500b171703601d070b003040a40540130009205480c42601caa00b400380d82d80212981e21845c4640c0c0c0000720720104030350030001c0301c0c002140d02c8100c510300e048242c2c8980d9a40f448100e041001c80811070b000c1c045801d00c0391580510640c00b800c614850104118038080d00040c3c0d17910071600c00c031401407044000039441100f001c04048050494181100c500c0d01440c0f1a00b0120b600c24803d820792580031040701c600b04005c1e1150801140c01c3c0d200c50421480301d9490310b20266002500c204d60401019149400250050020f0b81807800d202d108140c031146064040c641200c41a00c096409800c0207000744016a1554040d9030070030b400810110401c070100fa981841c012a803504d2080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 297276052 1250 297274802 297274807
    0xa0c0807020601050a120812070f030e0601050604120c08102c150a02090d0f030807080c030403050904021c05040b06040603150e120c0606011d0108070305042a030b0c0f0301090b0102030403020402 86
    0x30786074214860030b1300700e0162f580402218200d84c84250302d4000030300850764420000c00c81041102c0001040c400c0c3c04c0d0180c9440c8103030740c0c0d498000c140f07440898040f250320103441b090402043e01c1c6d00050f803100d142444014090902d124800a03498140c040301c00d0305002460008600040d4030355040e901d646001503c0036408099a007000c0510590803c41240002c01030000200e06500c201d0044d4040e40502d40483e003141c480d65826601500030502480d040f45d400e00a009170305201d9a400225202e00000004840c01c050400300304005000f0100ea0280741803800410024034103400501d040011007400045194844281d181020740c20b07030302c10103000d10129001014141c00310f40c2c6406103500740c07520f14801b20510000f0020002083c03525020404d08800104030764001c0c0c03c00c681c40380c401c0c7c05100400d00c00208910640d981480c4900700c1003026102441003025401020b50040400340b030003410712041260398141d503c4140600369401e5100d20360040a64002c00590740a10341c014030554 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 297277302 1250 297276052 297276061
    0x14030703080a151d130c090506040b040b1c112107050d03080105040c03060308040b1b06010509042301050a1a010c030207061b05060a0c0807020601050a120812 70
    0x1c1902030305031507a00b000c924040880e1030030109407015030100d0303528018600030116070b01e4445025203c0100602080c1c1100f001100000b0107011310040a00b802d4280000c85060803000c0c44103d580d2078030f4403401146006621a599034420b1201c1c0000c0200c01031400494046c3c0c50103800c4816002201a000030700d9007003825100036680280d8841d03d00326022a51705a5640302000a102cbe0750441c0580480d004500503c0682083e0b00120019101400c022441c541d80c3d603140741643c0c2c410707400305e19140d8000c1001106001c44c413140320f001c034480800411442d410f00d070000301d600001a2000340030648000c4610092189603000100c82d8109e08000c01051802c0d0040700d0203090102030400c400c020344400b100c4258080c80301d0f060403030f4140e8014241541401c1041c1c2e1481c0c9011907000490720400401400a60104003542c0f180e80340407070208149041e43e802400d0580003038035040030b40d0022801409075032a003040e240101e80c1d003180ca030910184c0f1801d04000602c10001c1e000c000404a40401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 297278552 1250 297277302 297277307
    0xc1605010903270b07111c03080618041e021c050d11030705150a060b181c030206041209030f0c0513060b0d0f060f030b0f070c03050304060914030703 66
    0x2100c2400d199281031002407020303da41c10b0040203501800b51102e50a1001c0d1000c512500c00e0501450742c0541020384100030341c040c201c207060785a003048000500a004008860070482a22040e041a02d42d104c2858240390382e80312001000d1032110b0400c0b00110003104155502d50f07144010416481c007175060480e00c1400c086890b0b20f9108e03480c00200b00bc060001c66200c4002045803480b0340c00c02c0180c484040c454050340c0043c50081d01014581d0f07154003001c503d9400000040904542e000781c0e00703155540758018480c4007202c0e0b50402c104043c2c0305100e03d0100750007184140d03003c1c1e8810516920b041800e02c00307454864040c1c01c0034001e03210801c005000c2050024000c1d054400444904070311000c2c10b01c0d0b00b016991240250183da12050010415008a581100e00ea400344201e0200d00a03440e40e806002180d103d42c000d0b00c1da403400c00144407240941e064101d800851601e484000c000892720003602c00e00c4050001401e0340c0c0d48003004c4080c4050110001c002d0340000003500c0e0b0b00c04003420b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 297279802 1250 297278552 297278567
    0x1020304060c0c08030402010e03071503051006050f04030b042102010e060c0a2708060721050c0322050102030a02070b150109060c030516030302071a0106080c1605010903 75
    0x1c6650620b0181c0034400caa000315842c40080344d12400c02450765642e50f00469280424113044c5406102e1008041100529203032207000e40301450fa4001001d2808810203040c1c13131031940c801e006000302001402c0828040f4401c0f201540e42025146049880350714082c40c11500170250001081d25003050800210380c1900a2401650214121040c0f82c6940516801d01d102d90904500071400d0684505d62400d50862480c80b00c20352003444c0b80b085552254403c0c148201107603007400180c09801412966041c00200d20a8080000400c01042c907080702040c2a0788400350480700c0c0e040907508030710301021807103403020411070b0300000135901c0e810072051402c080e4000c504100c0d044180c510000e0107a064592482c41403100583d5000030381c1c0d2410303505465000d400c007015402c00000b00881ba41e140501e00001000d02e110f0303980140d84003c58100000902d2201040100000a03a80100600d03540500d001c0d130801c0b03c400e00790381d032204698400c2e900000940c030300078919400e190300501450b8200c040b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 297281052 1250 297279802 297279811
    0x50f0a091e150306180c02010212010e06100201020a0806010804021306060206060a05060306030316080d18020111010c1e1715040e0609060a02070c050306040606030c050102030c070b0703090512010203 88
    0x3202846030802e25400d906075645401407031102480c0c52406403a03809641c000500c1502ca500005150882c42e8800300306e5100e00344c100186c000b000000344085410203004050400c8440c0c4021401d1071529840104101c82c050526030400c9145000320381959901c4140202c00c60140c00e080210300c0c1e817031310041d4031040100c50081c464190b28030002414100142124841c800081c061403410b442c2c05c41d481400c1002c5001501c24682c241300600409500f4410b881c1c08000302da01c0b8028400c0244001001d0b249000080d8560b6411b2200700c07080d0540102000b032100c0c50200311b685d01e01c58801c00803104c80400c00700101000081c4c07004c1c4002142d10400c400c2c02c0d49010384c0c1c1840030022041c001a9107440a4035000c40a900407070011b4180812607000d402c483c0e114410861680340c1d2007000030f25050044d90b064503880e0b941c180c200100004c01005200401c0c1c280095400d00002c646e103140c88a00c1c0303100d20844060001303009000c00d44200c5110340500030080110310394480b05220607000b9041204c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 297282302 1250 297281052 297281069
    0x1121b031506020703020409030c050a0b24010e220c110f070b0d1107060608010506010e0319140102040902071a0c070f020f011101050c0903150403050f0a091e 70
    0xc400754031000c004140c01e0140c03501500140a904d02e10b600344070090048072400d40c00c110044011200240c818043e03010318030b0080c200c514041c02c00e21007040320242064006800e51041d5080d00840d030b40c0004507403070694401c0350304040b68240c0c0f1010540c3c3c01629014410014039000c2825200c0c2d421203212121100f11200300c44030003a1140701c0e959102c4140c0590480c611050010b070380309124030740040c04c5040d143d4030154103022080d9101019515280c001ca031140c2d4654081041a5070301088001d4003174400c8000b031030940c862100858541d504210050004007546400d061171180940440713005020f0048115a0744c00a402c1c0300786045500740300d080c0341621940100d50004a0101991201500504481440c0d5074030703820030201101d103110b1603051091042d101e40b1111001e10520f445203850500690f91a000081098208040484c020385800c4091051002207507010741515600c0c0a02548140d031503480302003e5505c0c40d200e60000440300e0314110703c4c1c11000b22030302c0d10300c0440e503500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 297283552 1250 297282302 297282311
    0x1308040f0f0b040303091a0903030319051b180f0d050c090c040e01090207020321042c0a181515051e06030613090b1e10050f01121b03 59
    0x18400c02800380f003103110150008044580601590300304a1a9a034039203140b1a12500e005140c80c00b09042d500b04079114041c1415044044582a40c903019042e80409410040c0e011060880a0350f10207010324000c07064040040ca11a44098440c0225103111660052054000782070364500140e40f4130079426481d01130740c2080c2c0810300101c3d066081c0e07400d60f5806a0a06266800e082086000303400c18001030382d03d4400e00e0009074921341198071180001540e550040d5865080000b41c02807c90231844034241c40c141f83e05006250b200040712144c0004207c100400d100e400c04107500d40b90340c010007015001c00c10509480c255089150f003c1040001803220310b5040585e95020090380386503400c1140c03d003850280756800e041c81c000c00219030009000300914032444024500c481200c1e9080c200300c4403c0f10807000d00050121740c11807050780c0311441c00081400e1900455401c000d015610a841c0961003c8d003161049a0017000540c407104403604c000c0002c180003103402d5480460001d007010200b442c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 297284802 1250 297283552 297283559
    0xd1a1f0e06030f1b06161a0417070305030a020d020909010b0909070c0209042607030e040b03030a0c17070b09010902010e0f0a1a090411040602012a03051308040f0f 72
    0x101d8130420710540903000c0030564403958213008955000d9080c00803610484440480022688001c140080031054140c014030301e094500008060501901105000c1081c000440000c0e4000300700c4e54030500c1c8003005602c880c4000500c4001e8044c52500c268420300100003c10100c00c1d51018084500c01118440c285449400b41610031106d47c03100a5000101e500000c2c010807090145200c000c8503890400c0791402800b00c1c82d601d107400c500c40460004080260030a814901402650002c0504034007440c6890041c5001401c00504054000e05020184a40040300515902034403513072074000c600d159803494000d44031802440e40e580c1c100d0114640007400801d60820144460000a000c0c01c1c51100e542000e007032f042c80b803c0b041001d052290041214425544690041400701009000302c1a155420700c075002c3e003552415648600e00702818152001807034a0b403242c1405610b0107080c0003650361078070502038010a54104015102420025002405429540048048030800440112050b45 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 297286052 1250 297284802 297284833
    0xf01021917010f060807020705030106120209090303010503060112170d0905060f0c09040b030708070b07120804030e04020702010c0c0e16020f070905220503180d1a1f0e0603 76
    0x1e02643e40c901e4480c1105008a40c0116100e582280d940d0040f00c180345e60320030000c0e0a4840e586c20042c081540c11030003c04505201314030503001020500a036085606000102e03aa481c030511405035400d02c1450b100381400078000001c00c0308104400001d603a2444198800d02601d0290001c440314400d020000da0500c0342c01c1c58181c0910201e140892800d01030404002c0903252465806915000e85200024103000400600008152048205844001e90b0800d2041021640c0003101070090580400c40040e03030101110036490801c907001615071020b800102c84161206000400b51155140080b0f0880c145a40540c440c200000455154001c01c030341c126160000d001150150354013071501805070f0500d03900080d9122404490784e202c40710800c1d580402450714054103894582001850003010341948203510140441594030164003801c654a58031603e10090819100918080100700c841c1c0340c0b02e0309552446064002225426114001203541031000d8075114441e02c205c0100841550 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 297287302 1250 297286052 297286097
    0xc0905091b09130809040204050402041503050f040b070f090513142211030a05060406020c1b0904060c0908030c010b030601090506061608130e04030f0513090902030f010219 76
    0x20f55410b036402c003262080d80c40040b10742101201d2680300341c0078803000c034140d143c5101a20042107606240360440702d100401604a61010786802c000801e007000b040082200c502079aa044251407509401c80c01007407070112860417a680006038001c8182041159004030341c6c00850b510030514403c14410b1f1207245007925000100034401f52034000341c402c01400301d4403017a00a5034100c005019a4601850b076580e6a040c103c084400704c8140350b02107880c1302600c0040111103a40c40c107a6601201c40504400000d0780300c42c00410007001243c44642d412481c1c0e01c140058801002144110384c0c840a121401c2400780824506050091040600024030f00036036003e2a07009000140441e4a017845002100540d200190030a40e44a441001941403002d10680c0440c01800e48802c00c0905003898a00100a174580042003401c00c0380c148030380c540203500100c90208503596204001000f000c0751000c80d041036090084010b4551011403c2c5080b030040010045a58240c2d64a81c00700c0400b03035241e2001c08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 297288552 1250 297287302 297287311
    0x807110a020105160807030518030106030f1e080d140f0705040612180b01060f14090f01110f010219030c0c080d0f05091b030123040c0905091b09 64
    0x30303804042a000554040d500030b080f160303041c40342c1e401c4981c100e80350344115a018031812030004400085189000d43d20034030303080e00c0c102c08800900095141d6101c04031201c024440c098041d10000c4441180c1013440007820b54501c0d03100020035184e5518000c420024046500c44032113a1303108400252540d140c029165119828a4807803070b0034182400e40480b564410000801da25681ea16614a9a030101010400095200c0d240c001c001d5818018014149803010110b50140941203000e030b15640507031000e403503560006403070080d07803110504012500003044007c00d10150081ca41410f40042d010b400500e1000c04001c12401401c1c400c06c4110112050115200c5c00144442c000300300103940400101306680d00c800c130110309080c80b8035800048803800e80d2154019401141c40c0c452400032840448294030040700200040502c61110b528001c074058480503200d1014000a005c000e81007603940090646240100003924000983c250390f42070105010401d1898a00001583d01d44100d00c0c9209 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 297289802 1250 297288552 297288587
    0xe010b0904080c07120606180216120302040909080c0d11060c1602040c030b090a060e1825060206060604080309040b01351506030f0a0605100e010807 66
    0xa9071592101c0703003190440001007207a406607080c00a54007103181e03824029035005000004695140a4804a0020088440c8503200b4018000b0007202d506c19510b001c00c0350f81114605030341d0140712030110001d104a03002400b074103250142c005d05000c00840607100294060080300c0062410b10815605401501c0d0307241c0c003540c0a0000078806442010141048039101240c8600084559002500b510040d0b80a140003941c1c9186012107481e10000c0075404c54201c820401800381803028080c1c0301107004080c3d401403d64205130050500003000302c6010545070b008529a0b100c104548003050039500c1c410390005100e540d012800700d140c807108440447d654000210f10b0410460107000181c070b80100c084d4180480c0c100418400c00541400e900081c03149066207030441e092000304a907201015004044500801038400e049445d03e070101c80e004040d480d2041f04565505003c00c0181074503801181d04840001c40100e0b00a0704280d00c4103401400341c075541000d58801c11b0032070f01040808800d164 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 297291052 1250 297289802 297289819
    0x15020105040206190216030308090115050114071e0b07030b1f0c050f1c0306090908040e0a1b05030105010f02060919140d020f0f010501050306011a070c090e010e010b 73
    0x300841c000703600c0300b80001d060040d24060800241141203c6c3c2090740140d000c580a1010400b49460070b205601c441d010b0087c00060113414100000e1203269100407800480400290540c140b00e603411104c2d20003001c00b185401404228070f0300e0402d4000548905010900300300c2000754515118071400301016a0058280c600c07421148115084080480705544030300070700c1110b0540600c24811941041c01071014191007461281004044030b00c664440144146401b40e220b00040f21101180c003106d016107044400e0340c850b0392480000381098981e44201036130044a8003085908100914103c40c400d8850940c0c00e02449030076604ea502c00c07101e404040c0c01241c3e90f40035030f58128901c100c072140144003240b102e50303588010a00d07040c10441241c0c00f603400414641403203001044500c0b041340881000348602c3d4075081c00300703503940c03018001e018184201045204840204206030344540d03030081505040d05a442003444020003e034241c25000e07508001050303040c04814001d001401501505014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 297292302 1250 297291052 297291067
    0x2040303080c031e06130e21070b04140f0304060309030906110601090e0109051e061003051506011b1b0801090c12020f09090c03011d100c030b0a0303030615020105040206 75
    0x14558002820749901c00c86c44001c000c07420095102e4095810001001011403030480d107007101c175502107141c80700074956042007041c00050000003001e400c260b204461f44414940c00b0162303800e103120485403091074440800c000600541c180c100c542d1550090302c802e14000d03124101240d4403a140c0000d40c015078006001001408802e40c4294040b90150340001a4509680c1d1210b0501000ca100190700504030507244030404001e11289400101c809884090b15107076a40311a103030542d10095403480c0d2144800139a0a90080c4004968411651005d88a1940781d2400e08000001c0d8038000700544160540440c0f80c410500c6480300081c1c0011201c445070303240004110551707400020480e040048940a03007040e407603a00d0441c2c054214113015001083c4610306060845021a0780795851140c0013901c01824036001c180302100568002005c40c0d0540c69010a401400c0120040da400141c8028000b090590550103441510000300d200f041c5007c00d05012401d0701c40a60300a9400b41003004001d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 297293552 1250 297292302 297292351
    0x308060901050d1205040506122710050411060304030f080901110915090913030e030312070e120f0a021513060c0c18021c0908091504080a0602040303080c03 69
    0x40d840e504c0f8900e456440c09071079001040d000e810280329400359014510500c1100700c1c0da900052800e03070010410034100e0208015580c1e841c0d212511000d00340b582c030b0340400e0a00c401c1d075111039020000075000c580d80e41001d180003440280c0c06d07005100060f541401162400406001c2c583d2603140e0850142e08098214041011040c484200d031004100200a50803490710303091812842009aa0458005000360782070240207200c03000b002c02e109410420440c0c2d40a02d40c0300c0c07200d4008500346000640d000070400441d40d501c2603412260b05c4d51140d20070304102c809002804440062081d9102020300561055044503401340b0300010100c400c03c08000e01c2494422140c0300e10041c050f0400320300756580d88030036221805c5d500300c100d00c0b01a0000741c1c10306003103801a4107244030b0151900800107a016501c805013280038224450344070380b07407080c2000c9e00ba410101c1694050851002030b101818905d141c410001d520503c42140425900703400a1100c050250070759203e450b0a04c0581c1d440046507024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 297294802 1250 297293552 297293573
    0x70503010b0a120c0507031205010b0f0a030e0a05070501260a02070201020a080c0a0308150904151d060109060b03070f0f030e010c030501170111180a0803070f0308060901050d 77
    0x480c01c024070003d01c05000061806101004041ca858503a0b0f61441424010000d6030360000c00d2a00c0360a280040040710000c0040302d0401c4154009584c803590051002c40c007810311a5844c5116114020000080c0a4041401d104030b481c2620746a994800812400402c0c00300b4031181403c0c80f02c00340000d50314505940040180c0c510502c1601c1e510340c107a1360b880c100341e000710708415110f500100c0c4013810160415601074120a440300c040840344803117800290207040040000708803000c41c00c036000d0040d81c59005489040c50420791b8036000600034601070340e142c2e4248561b4103490306000c4002004c12908045900418130b981d41e84000d8115550f040e01c02e00302d204813500425595901d51710800100b0b1241c1620508543d03004180b55240031202c0c030013450542a681510792400701c5801c2d901909a0490380d0310301c6480700c00298681c04a0001d0404011a400404076000002e42041001084030102d00302c00e200c4d4507440155191003060080952090041641042a07038400d4000304140070003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 297296052 1250 297294802 297294817
    0x120606090c09090703050718080d14090402040602010b040506040e0607050f0d0608030c0c0a150c0807290709030206121f0f0801200301051201060305010903080702010c0206070503010b 81
    0x8a0610b42035101c000704695000c00c80341800040d40d500c00b8004540c0c4d00c41c28180142514500340045241800031090301c1f180b81154040c00d0092181800445140d181d090f00e5040c04020821500c5a0703445401070f0107040182510b911441c90940081d460385030900c51075136140303014030007013240d6903650105441c00e03803001c0070324001080c00703228096100103503001c2e0b40301800024000d161242138400d0141d2a1812010030075202c2d069034103052103040c6d0b1600e4625900c511514055503113076101c0c1004440d500c62400b024000c146420184e0b2500c0040c402d1345074150318403990428660350746490072582c08006010003580650304001b00e04090041003162604030340c56500101d4241c000011f03440e4410183da000950030b602e8044204405082845000150030002980a0503a002c603005082c031031005005041c4a40e020010b443c1006d0700941c844c501460740400200f141820303a00f0040c016450450b840b03001503080500300c014841c4042042c9014101c292249411642002000a101c4e004500c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 297297302 1250 297296052 297296071
    0x190506190f06091407080108061f0f15080112020a0905040318030b0a1104050a03080c0708070f050906010c030212030a0b060304060f0b06030709060e041e0b0405010512060609 77
    0x40415128025500c0380b44003c0c010300400040707031031198040b4452003100814000504c000c40c00100102d000114202e03a108581c80100444000181f50500e100f01701500140d445a5020760007040b030300c540d5407104030031048681300c3e510303140e03a01c0010700307000f04041000a400480010f41007048403036580086030800c1c82814415100861071030048420074142c5e02c252020005602800852440c9100d00c0ca01d4030280310246190504100100e061045170b480b0042c002d0500180900c29404144000c3e03002d084650103580130507682d04080b121144245c00b410f0304c500324000210b2031642c000c400707215800d641074029000800a800c442841900001c0c20b012500e034480750124455603446004500c524441d10000a40d2030400078078108a80b00046154061641001401070f0baa801a46607800c481041c60b2601d1564170100115020340980c4080790035525800f8031010102113140c00c00f400c4000c05881c00c01c90790b0b9858003003003803415041e0050100340d003006d0301090607030a09a4031583e1000041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 297298552 1250 297297302 297297311
    0x821090d1e121d0108060603040204110c1b040507020c0d1e031d03010903120c02150c09040e06060d080903030f030702030c06092e0f110c19050619 65
    0x200c1140845080450895000c04400d0329003494540040c003040b40d800c41c0220603549583c04500180c44484040d0160f845414003200040855890b5084503540d036800c0100c26481d201500c0200d030342c51490218800d4505250032100c2c5040c10301d4400c0f140306e02125401030040c04001d40c141715180c0480c071780948540d201c054001c030300740411041c071442d00740c0b00b0b58400e001c2c4050405229000310080701e005100740d06017016036000c03070391000c41d0841035207020030000b55603450140180c0ca0207002501e95030301030359090300b04050580b199000d043e0300d1405980900c02c00c90442001c4c1c2d1264411602607502001440083c0042a4000007412840c50090103c07450940313550390780000f0750400c988000040c1d00001e210300034220244445a003002560000b40a40c00c1c000d407110f012451100c01c5200150160b250b0510907150035005001714036000c2c84200600f01c90255580590f51003102d004000340308a0803145010f004054001c013482d9000009400039440d0700b80703d2801081d000041cbd55405855 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 297299802 1250 297298552 297298583
    0xa030501020f040e01050d050d111009030509040f0509030307050c0c090a050412020a03020a0206031e04031e142508030a02030114010e0117130503030108070821090d 73
    0x1d100030b0290003040e010542d10b451078400c0d110007030241600043e0140041c01c29000001d4000642c0c409801014140f49110400440d41d651401c41040c40c9014414101000f000605070400014a009907066030b007486007038943e01090301541d03015100d200310307940100000750b00107201d0b4019001d20005082500c0041401e000010030381403040e00c803034402a983c0d405102c204807204c46100c50300341c00750010f08a01d0950340c0340a1349550381d03100040e009443c000000b81c82c088032080000b00e40f4405c0480c141860805040040422140d01100d150078400c1c04d04c4000210301504495900070240c0500601d002c14402154525085240d00f0000b01c10406041200003107280c80514402d031802e05006031a0341c54070001041800c001629203052119140e599405130340d01c183c0035000c00d0150207881070680c40d00c000da4183c5009140e4050141d0001100200765000081006400c58030401c0480c0c24800c0002c04040707040031846500041d03280100f0140c100f50074840340d842c010600230050050011300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 297301052 1250 297299802 297299813
    0x30b0603030f0c030c010608070e01060e0a03121e1407200a12021003050708041b081b0f0105031e09101407090e090705041113030c0f0b0708090f0a03 66
    0xb0082141d45404c00315a046030a6401d11030200140000d00082400c0352400d19a08000801030168804000079840307843d006c0d40b144d006820003598050502c000f42d0b002c2500041803042203c0b02900990100b07400d412440d40305400103e030031180c030001c0c1d03440c2052a540c0d4024102d410300c61110208190074004481d5039450400c04010b019214040100400b5481084481d0036125284c6082c589040144511a640f08044e154010f9010003540d0990484400c002c5111610303600c1080588a42412401c0114660014845054064a42e060344c61100c800640705400301b1110800352100c610b2001701c3c42582e0b85605030300510148280c501045035100c036a819a50b045402c030400c04001000e0044032a070000c0c0000040c1013949000c1c0c00380c10003c0d106030b02c1d07400b1845114030481e1105000b001c240c0040003202c10703410416a15142e0309940c6c2c40e000c1048011407040620700f4400c424006200c0e4444011550790700e50008e806842d028210040201e944002c0030710503001114038402200142 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 297302158 1106 297301052 297301057
    0xf0d170117120a030e01050c04210f05060c0403050f1216051e060906180307030309050c030109081803011407030c050d02040f031e020307030b0603030f 67
    0x11619401e0529001d5000405280484000380d0041000d402da8021010824410002d1210703940700c89402005000c1d03071003403031080e030b4010811075201c10112034804c140f940706100209000b0000d46841c2d241810841d5405c1c1c401e100003400b0f0003440303000c002c000c41a8a40c2e00c002e01c5001000380c580c0c4658010696440c1660305000307034040c03c1280c244840c4481c0091980304006891006100565544059070111702c42d008000c0070800e00c1161044044100c00848015807500700e09980c00c41c000c1c600c5401c1036403c1d001d00c24603040665000e010b10382140340145a2035844003010f82544e12800c060219584c400e070f2421303142c444020994176a00b940f065041c01e000841c0c040f0750300251500c2c801c0d900d19842c03461000130045070715145240c0820603640100c5c00d40d29404000d840c2d4058040b03101c007000c0c8d4140d008110400010f0b51a11240d0790000d00a01640c2c01c0c856140250100354 = true := by decide +kernel

theorem cover : BRFrame.Cov 297122302 297302158 := by
  have h0 := BRFrame.cov_init 297122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 297122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 297122302 ≤ n) (h2 : n < 297302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
