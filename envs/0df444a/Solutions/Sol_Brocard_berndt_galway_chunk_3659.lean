-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3659
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:18:21.77163+00:00
-- url     : https://prove2.me/submissions/5e1b5dff-f1a0-402f-a5f4-d77f71f4cbe5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 657913669 ≤ n < 658093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 657914919 1250 657913669 657913723
    0xf0f042108060a060201060605030604050402040615020d020114040228121b1a030a110f19030b06031303032a0c060b0103180308060315160206010509010803090d0302 73
    0xc2003a20030b820548480380301a540720b40c100d00702d0f00389201c0c130740c00654144082540c505e0103400071038000e400104049801a01c9541500b6070400904400c070142c0c0c006201840c01ca80c0a0081e5002201d034101d110a0760300d4550040358560501d048940c2d00c00340b060024015110203001c0ba5405401034100004424145143c40000035641080c4c4140030020b01d0030024010816540d0302036071022111407141140c481c110100007409030541c620009400070722850a001005401130304200008042c559407100300790601508075041502c80b603011700020020802031034001000841d6071036040c5800160800190811191104001810300358402e442c82c40a4115901040d10761120b4000c1d003042050781182c0005400303d54103502c070301d2b001074041d0420030086401001c074564007020241c00d40d280c0019a40f41810b0081c01141c00e040344182000f0908040c907810132103140900000e0320118003d5040040942d9240034048203148501444441d580803d0300c08d000100040000500710380750b2580740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 657916169 1250 657914919 657914927
    0x70303061e05030105091204060f0c1703010518240f060d0518190201050a0216091506080c0711030a0b101422180203030c031e030f0f0421 61
    0x540310b41c82c801d40c20140850101d0b000071440000291000005914241c50000141d481100c40440070081c0081c00c1211008102d00421481e817282407d40c200380c2e41e42c10030b0304200e2041062400302071040c1002040010300e50200840340241c1010070441242d000a5070005000c604c1c0e083c000e6504004042005e4030300e0103aa40160b8041c2c1c17219501e0860080c0740600150351050b00d030380741d040d04111441047d40035500039802440c0d10300451054880aa08282c80c803e25607030301e980034001840d41d47c40c11601c194851140303030015100d5494418001d06150824034041c0c002e0400103400310b400300310200000da0f03040181700b140c0c42e84101c9140580c0752801c0841c640031158802c2c00d42e44140a4650902c519251a2003154002d08000080c28020302d0301d40000100807495130030922a01c5016400c01607602000a0822584450025076650750061000500c44448c007044880504091050041041c01902010b42c442da03030038407030580390341c0c0ca08112140d6600c0603442c1c0c2048442d0845403110030b81c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 657917419 1250 657916169 657916229
    0x60904021204051905070b0a030f051503060c0f0f030606250c061704060b0a0b13031209211109130209060102060114090c0702041b030b0a0509040807030306 69
    0xc5013030f00c80225140080e00400c0c0d8035800c0050140d04512401d21883c803204010b00303c03410f018076001518814100b0304404580c0c095561411101961f54a0310082c9810440a640480140700071810b02c107040035540c4041c0200500004031070700200014030b050f15085d00741ca0410258640c0725506603a88141b2000e010080d140940e128081000007048541c081c1e002303210a11034201204500380e40765210031004200c2011010740c0440310388000604030030b81c18040d111b00ca03c003c035400c901314034526103c0040042c8141487c103005410808008030f0030464403805562810b101926800c485600c3c10410741c8801030440359000d840d81040c0482d50300c0e400c2c00c1e203d40c5842911070902c42e440301d900580e80c566092041c1340e401c05e102c8511810740e0800d0b100b00c9030000d09421940b820082d090b03001034159200c2c5c01c03a540390000780c12455110f2a03854082c010309a81c00740c48660364242440c022820802000b00094812a030000e1044101407083d407102d4001d00c003030250310310901c86207000e000358001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 657918669 1250 657917419 657917423
    0x30807023d0503012d08030318070f06020a0215090a0b0301080c04050f1315140f1006080a0203040305120405010b01110f2112010b04061101091a06060904021204 71
    0x1080c4010a0942c080c40440c0e06940110030600e40510380d00d038000d0200c0700741c10194144003610440c0010220400c00245009104c03427102c01d02081041c0e50110319200c02640703c1501c1186040c0300b08822500400c4190174190180c4400840317000e803140b120b40d42d101300da40c4560003400c100000180043c00070041c50681e02201d0564091484040c00c100640c2c8003901c442c1201250340000c940d510000d04619403050384209064910499641000400c54110070241e00000b83c0410401981101100d0103545c00000c2180003c5082c1c207161000309803802c000d0003072111079800800b00e0141402101a184c110844d96400c0445180c2840c03c54041d044034000d4501050119241000c248004500b4081c214060030041440030409004002c090341d0000385290547c408001c0441840056000030780a001c061078590740d102d203801e0f401040b019802c018415580d01d005034000000d01544204040b40e0b200021046094a0702c00000391544505c29402d94040e100151007115100400d020f14483c2e8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 657919919 1250 657918669 657918769
    0x23030c1501090c0e06090423010905090a032708010c0c06050a0207050309040f090c09140612100c0201180501090b090f060703181202101a0a03080702 66
    0x40d980d400c0110503501c02c0780034440861002c2d007500f95217040240180a0f075510050002c90101d80d0306500020b05100315100d10411001c0f60014081160a0f01801d41c110400f0b4004090380e9045450050051080c010f0307a40c0820040c242d141154000c4c2e0964201820802008002e50104410f020b4013442c84c080084a00ea070a001c00540200602d10a1fa01120f4000015624000d24002000001c00c42c0c0c111048820396079503401e10109031b88412403000f070080200000381010034003800320038040c40100716a00c164a800c80c41d000c80d80002c507094074142c101e80d502041c40664400e0a9000d021480c54818010501c20014002d00c201500a83e806d18040c0c04001703440d8a401e58000c0d02e42c0f0800380d1811150340880d01040a0600c60703803068400d0041c5d02c0c1c8482c0c0ad40010754512807110190b500d000300582c009031360072804211078411042020f0b01344400c03407d010302c0c00700450100c01941c4805800994003007452000d641700d4817003043c1100d241c02c81c03501c1e6070140c410340352012800050300130101c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 657921169 1250 657919919 657919921
    0x1103011e061404060e0303070b040b09060a15060e01090e0903040509010b040f03030813021c060b0f240d1b300e030c0d02010f0c0c0f23030c15 63
    0x300703018445150001d20030050b803c0ca030504080098811004e031014640d0036100c100b21213804261031009490044c0d100350500c150740e040107400540741100103002c1da0441450010500d00790111002501c0803543d040c10803000d840e600e80c005032507440c9943c4c401c40110006404121440c0740100080003650421254a4001d9807510136207031060003280a4406114180c2e082400031a006003070a0307602c44010510100b0301c0e52079501040f120410b506003804c80c55250801002041102c1c0110481d0060540e070201c011444500010394958440501a001c0050036032182035030030300e00084031302d490032a1105001113000380d040f06003806c0744400150300054042c0c000c101e8848000d1603000904008000c600c411a40f078445481c0240b5000760042c00501c010000f4040c00301c800c2c001469050581c0d000003402d02e100303249030b0341514003500010007000004441200010503510f140c01d002e907000901d40140b0581ca4035030004030505009814510310010807a141204000520300340c440d542c0e03881502c06 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 657922419 1250 657921169 657921179
    0x3030108070f050d0b06150a090501031410030b06012d0e03070b0f09060c060403020619060e0c0c03160506040c1d04020f06250209010e010305031b011103011e 70
    0x5401614043c5640c8464001c00c010302294201d182c05801c414000d0113a81e20480b400d2110059610014410002c5460104100559a0940700307420000c5000c1d0780c0408240b419420108a40441d804000c00795540a408626540d109214032218164060540c2c10300ba81401c0300701c0744406414008000191110500e46040d04021510b01c003240d403444101828900010104800fa070403110905800072001e01503901c1c0e001041001c0d40c043d0340240c0142c04942010241000042950070340d4240407801c0007410410301c101000e0f2190702c0360810f820561980103c0c03c2d04c60841c415560943d40340192551a501480008107969008500c501404481c0ca6942c1545088040b40c90500d4650915110002000b508021f410f01300644030042030140340403e201028054603079000014000f80c044141c2a44c110304041321a030340500040f400b9850113600d9561016601c1c481d191801091060711440d0f443e411809410490000d103211414584035a1120340c111100d142c4041c6284040c0858000003032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 657923669 1250 657922419 657922439
    0x140708070618031d0f0409150b0613031e12091508040b060105090310050106020109061113050112060315020306130e031b1e010605090114010909050a1d0303010807 72
    0xc0750341030315031840900c04c1803a203c41304040703801d135550460034080080c40f0350342d11407145020380383c424078104c0c0b4042c40d003003071440031281007411107402540c0c10441000114514000601200e50122000d141e241513101e450114400d020b03001412104403c1c5d03018915900265480e080c0c64500120308954a01c03010304503000c0c241600c010305000200b078041040c82d44608010800b240d4040c007245e078840f8145401100300ca209902000050355180c1b40d0301c041002c40e0042e4544240d4078944581014501065600116224814507042c0274503d00f0380750f648135440e00300400650304030380e00d4002101c004643c44080d5200302e4640b40b00303100ca6107042a840f0045c1c441c40c004003003000700640c100000c0550b001013203031b903010000000e4492103500c0b0549403588600c40b04030441034400465440e29103820711410380010b030808846076581f40d0170007006d40d9000207800d080714a4450701040c035440303e400b100000c2480d003040300c4007174002002280780c000380000258103d8800304100c0b0501a99400e10740 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 657924919 1250 657923669 657923711
    0xd08130209060d02040b0307150e03063603070c0e0105090906040b070201090212070e010e0106210b03030307030e070b070213090203010b03031315091401030c1407080706 75
    0x20360000c0548003082d00e50418441e900302c1e5a102070302c0081e00341c3c0c022000038078091385540640700c0746007542400c44009510045a4560031000c0d4024a06030400700040c40800703e540307405141070318210400b00410700b021030f0300409075441d120603070742c0e51500340c109490381c1d100c0ca000c7c55210400b45400091a402c10003915842010010007502c2285c8031541d0701d10010300c018020004664842c04510007585d80c6004a0900070403050041020a15061048080c408140e0040207010111001000083d802c4031011215444d2103422481614042287d04e000b00715040100342c06100110401030416019401a0000c14091080760310041d40c0f031b81c030601c02c0d201c1d043c40290003c0440c651140c1511154004104d814401400414251803150100c2c1c51900491520321015031005010015804002010700c60780780d440c540100e4140c1400192180d243d03009083e0390400d07039103502901c21280301d0504201d041d440c0e250315039910b07182400c010003107801105003620301d94501100002e00d031403000091 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 657926169 1250 657924919 657924923
    0x41221050916140d03050903031602031606020d08070c0b07030b120c030a030c02130507020313060c0b0105060a0e0406080a051c1e091a0315030703030210021c0e0d0813 74
    0x3d000d03820703030b4801407140141d1642002c03428407805122040242d50148050f010691040d44050500313100c9004040c9405a5403c80011122550100744140303a40810306901120103810459050707100c1ca102240c106ca200341c006001405c600040c08841945904078254486080f01c040101007000b800d125201c40e040501d5540c0760380072402200019006001003082a8002001d42a203b030308544503030180d40045a003000140c100150580500c0307511060341001e44104e103070051000381c181d80c03605050030303049c029070744550408074403a1803039131007008a000f0160b4041c10a0042e00d6807403580b039a403003800d03080c2128540610504c05c10001e02c86000791076082266540c000d0a05038242428030040c140703001660402406900110341d04448204000c4001401401990360780341001d855008494103030016446908030040402c04260300161034640d0503944200140c1c0c0303204210060001c000c01320b881d002551300305100c030400481c000c00c000300c00c16000d4441c243d039995924204502c420b156000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 657927419 1250 657926169 657926189
    0x10060507030e04050f2e0611070e0405070512060106020c0405090a210212281b151d060705030601210c030c0c030c08031306140a0608010212041221050916 68
    0x2081026501c1030014100b46695441a60451526113441d0b44ac140d034102e03420340b0b41d82e2140600304103a051032502600c1c030750150030107400c1c25414844020b464000449010348034079111004106400000c0c460140000e0340f207a002d4070900c0308014205c0a010060f0b41090150149441107481c42c000b9004070f50f010441d03040c000405c005660030714006c81c20f0f1080000d04100c1c90a01318402162502100006180100300c7c16180044101013101030701d507620000c1c4218003220403006c829032000103405030400d065040103510307039a5080040354031000b4050205d41a0074005410103075806154041c0429a2055505000040942200f80c03501e501c98400280041d0b14009600c001c1500c400265400c00086428050750302c803203843c1c5006541c25015202c0b01d080d140010302403200d0040c0f041e000100340d640029400c103030103020181807803140280060800e042403031082d00c4d032501c185903603200300462046060521b4100341d00a0000c020490300307184140f080c02201c45401400f044114116480481 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 657928669 1250 657927419 657927511
    0x2b110108070c051207060204030c0b09040b0f03060402040902060c0d030203040b1b031305030f0d1e051b0c03090411210112110d020a080a0c0e10060507030e04050f 72
    0x3e104e4159010503c2070b03c86c150b00303010120000380c403004400d0040107104065a141c01505040004507002850014821b03503042400b0640ca0700c021820b140e0140d0100c0e0002034042242c00031070310328403c40c00d10380d8190044002c100d413032035007542c0a1801a4007600326044996030390040e444842e00c0300002c24a84003001d00020703010041c25041103d00314441c2d01583d00704414002c450456401804c3d003904c189880c0c08101992004a01000d0743c50588800c09100c2c034105951455030003007401c400070f460000c000800b8814904100103c8003001d401400c1040030030160004e03c140d40e003019058010000446010040d1000d200408030705a560b8081c10501d41442d0f0303503c1112107990340c0ca4143d00501040803030405a41d401c46044001c0125802418460f00c0d1864070700c00390103180d00038800e104285400d01c403040c007a86511409036001410101c1d5070f000705003400d41c0d48503090640658450304040422170090361031036602c1e0040130802c903c80d5024880c1803440080b00b007401c10411382100c1f40f107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 657929919 1250 657928669 657928693
    0x60e100f080a0b010b34020325050103020a0203090d0c03050d0e061225050a022a0f030709050a09020901090e100c0504080609030c07120308062b110108070c05 70
    0x18020134454007440c100c05000044070251145c02c261098500d4084680b80c400e020944c1010f10291013600705504180d0b0310140c2700e5100b1104039005016150400d680400d600c80d00341d00803c120785800d2801040d000d150011443c0c102c070a80c410f40811030f11801254140b81c6404e01134020300f210100c00a10103410f065a0030204004084014400c54400703008120f2042a414041100e1880c10764683c2c8141da074816a0380040d18001c191000001e82c600301103515440d0810843c0764107d0500225002d06d01e084001d40003d00c2c00c8281e41001011500e0030301803051498180d0300032005148242c56004036607a8a900140c202c5021710200403454102040540c89000a6841003002000905015040948841c0340e240341800458010166070302c000341800c41008100318030001400002d0000c14543d4003960014405032001d007805004100a0082d041c0018101040100754208101c8052040100b403c000c0030010340210b2190208080b1008100c04c1c60bc900e4003107002c1c9070000002d04030b48030300c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 657931169 1250 657929919 657929939
    0xf06120a0506131b181802071a01080f1b010c121103071401060b090d0b060102010f090803060108180a02120c040615020c0402070c0501080604060e100f080a0b01 71
    0x2c00d075661041031058204440e400522407080140030000800680b110400c40240890f4003404ea101003122585408005c013184401d40041145d07000d940142e04c44480340b50446010025030078030391013200880000702c1d0040700043c6c140c0f4400d0201c01251a82c2840440080552000c001070b140025000f20300030011800c42e003044451041d4500c0c0c5201c1d1821401411820358015140444200c04641c0e080054280240211006888107080c5a458078410600007800c1c070781d5103080101042d00381d40015081e68000e6108150b9140440c1040c8001d24080c80e01d124264004c684060204501c01c0100e88c000a0341c00c00450b048000200500c0901b28903000c200c107881117088000d00300c3c810449508010723122402514020010403100c0c41c1110b8030740d94042d04040020009901851062280e0380c04a00e010650b0000c44200b030030301000325150b80c004600a05265000000c44144000502400800c095642021900c250f20201c1d500c94aa0800c3c549511303203024050110074483c00117020f900d0f51 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 657932419 1250 657931169 657931171
    0x120501060905101103160b0a0b06070201120915050a05090a050309041a120105040c09050403020606040e1c02210f0901081906030c090b010e031c1412060f06120a05 72
    0x8509100b104d54204051483c40e40e40402c1c0c2241c94a070a0049480410147e00c2c007050b004090318000344071448020000c01c2d814020703030401904101000284400030300300c0341c5c0000121604182074071020303640202040302a00342603400c2c6400e9450318001075164070000c030384001e410340c3c048003130f515003848402007101401070144070301d00a1b00140707084070195956041010b14a0014000812585860f09041031000015400b82500d40c0c20714003080002a40494a541c3c051001c450028203030111013102440e1600e04591403034040800c2e0001440513400040840144031200c104186a90302142040c005018812544407018028041040c0781d6005000f01c4c0ea211588005007559200c4a1f14480159041c0b580269801c6124920900c5081032902501213445804c1c00c200e903002811002207035803164101c14150040071008800f400ea607114039800904010800542ea85428070360481d015500300940e1544d2003100001c0c82d400c0181054030a980301400d903465000c90640c0d8840c601000703000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 657933669 1250 657932419 657932449
    0xc0201050d15090606081f03080f040918021207050102070e070513140906060708030a0504060b21070906030309140d0812061503060303160c0905070f120501060905 72
    0x14851014070302da00601641403008040800c400310394146400d0001c3c029540146c81501da172003092042d0700c0070106145040d022650300000300c83ea10303411200015600d0281c0d4010040c0e43d810b00305146514040300d001c405a42e4002c48010301002c2640031600d0f502c14051180034003580211404004103829590950340c0040c03d0b04007545805040d1115405408454100031030b019180d208009450030603205265010009840d4107150034804e8a8400713042c00010400700a60b51100300080400c0020b410031840300102400d139450615400d110030074100d124080c290303503074404e013400051403c11900034001240d40540f03c0d4100c941c02e10240201c150140904940c1080d141002040050380c03500003000d0084100f03c4450480c10140200300c00322080c06040c2500e00003d200340551b941e00801103a6030880c100d25014402490b85c5480c01184400d540300c511044d240200300000070f608007035010b0340e10070660303110900440005100c808490b0700780030344400138551120501140c20244c5880048803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 657934919 1250 657933669 657933671
    0x18050102030a0c1103011103040c0f06020316060203100513020703031b05071b0f0e0906090703030219020f131d0a0b0106140705010f06080705030102070503030c0304080c01141905070c0201050d 85
    0x40087e116040103602c20748048483c2000c0d16010002a8186003000014000502c065441d150801c440145800c0d18108042c108550000100e020791080c100ea0b1002484040c0c4a46490a83c90110030001e4201c91000d50200741041005180c1091049000044950a03100e65061007481e03107542c04145c081c1140007110031407a440100c0c1c0b9902c00d456010081c071910709203440d40d10f44400c03a03d0508002901c100d00302d034040310b41880020b0300401c2c0e540b4521000341200c1e10151990000841078051105129041140415000c3c0011456002841814503104d9040d41d4011011241a40c89218030001380412000c01c00600c03d0602c20070f60041019000942c2605103203080c1c071000e00f140e0700007001203000f580d545d174108480c0704180314120080204400840c20300c0c42e1a202c81740c032840020a1070b40700712030010014040104e04015038942000d0f120003000104071412820040702e5060341c01c40024142c204a940d80349116010301c80c0700300000c1e640c0c403071a0340145e4015115604109410040d01f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 657936169 1250 657934919 657934931
    0x20303130b0c120a050709120b0115022e06050108040809010c030e060c06060f030703030813031701080a0b0609070c0b06010915320a0c05010b090718050102030a0c110301 75
    0xf80c00001040c00759184100018141c148946c0140c10506d40e0303071001d00d82c1c0740c48003418008140040045411201c010256020243c2d00c00342c2241403031520400d820f0000010701080c12207403219508003442c1c0301348040400241d51220015110454221402000c94408001c1e44100754400c1d1801c04040d40700e401c04038082030601d000104650418036014645a00c8a0100038a500d0850035410002601f80d0241a91030b0842d14001c080b0310004211142170380c845100c11040610414030000103a80050307155619584484403591141ca940500b40c41ca850795001082c114508410f0450140c42c1c00e80b01c0074089005680c0745202e02e200244410305000904000094a0a80c8105040325543c03640e18070f14042c2c01d88843c1da601d15042c5400c806180d01c0c00613031401204130041210b41140b928100041c01021500c1d0950141046009141e080001281807000040e0010745240440c8403a070700340600b40c1e0700ca0004a07179034000d41c9a000005521801c03181c0101f50040840c040066001c0c2c00800c00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 657937419 1250 657936169 657936187
    0x8070c03060603061b0807020c150708040e1015090504050a06081905061006080c0d0905010f020927061302040509071e17071d10050910020303130b0c 66
    0x1160340a83c0183c60b0310b52500001c164182006600001c8030b8824140551181040f020095503131154404d218080c1d241840102000c091030000d54a80c95446030100cac0c0d495450301501024440242c030300030071428280c040851040d03004000103c20350915603500c14164501000c010241c04050150355600b80d8420700480c61103001c0c024400c6514940000006013542c618003113162440c01041400f100c8140c1e00144491a40148080e4000c40b41c28900c81c0c840140b0f0440b0760003068607403002400c1e98607000c02003005d0b45503600a0048458220350001082425003908540c160b495030141c9402128000018000d10345500000e0700c07018400d07001428141c50700e0114610350000e441c0100441c280c00c1105140a80b5103c0b800c1c0c8204132031402c01c590003104510b045c480c0038050314603000c0c44618203820401c3c6000384c4c0e11003a4400010b02c20360400302d0418015245602081c621801410380d00006a0f010740004216401101d00304514121002162940d126084010b00642d0f0030b02d07030401a10381 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 657938669 1250 657937419 657937421
    0xa0215091008013f050309010f11030a0f02190308010302090f1009020f130905010906240e0f100806010f02150c1608040308031e0601050a2003071b050111030708070c0306 75
    0x14484d4450300007156604101400501084198a100420094880071051550700080240c90005655040806c400d801110f0141d00f0240380c0070524039440701c03020f4400c0600d988806000c2c12280207650f00e0204d9113a1141c603006840c070840e140c440d0060600001c1007900c4041d40202420403800c0c8a4900703240d43c40c1c2050b200340d4029030090f2101500c030070040c04410521310400c4000d00c1610381950356003100e00c58450304422143c840009002d18420b0005c030641b100d0014004180006069030751440a980001c0d12031350081e51418005a0854500c3c02102d00000f1031810025001d22140034036035487c04030315295071240070003c0d4200d408014140005001f0710142014621440984d9245e10700048904404c03030b100405e501c0412007220601803d46d81040440d10f4099040c45c1074000c110600000c000100815070440c5500d00c80062524180800320300c1421103c2910307030280700c1b00c5c1e40d2003004603100082480c0d070034000e030000c1000c2d400041071000181041c0344100d501d1180d0710313940c3d15544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 657939919 1250 657938669 657938789
    0x10e0604091a03010e060c0d0f1b0f0503100b070c03061e1a010e010503183403020102030f0a1101110703020c0d11040b01020a021509100801 62
    0xc003059141c482c03003081c2030005940980104416070007040b1000c1d5810105580741000341801031111000150043c04801715040a40300c500c08400c1400f44031103001c59542c0000700b0004140002d952134032041010351240003183d014000010320345d01603d040c2403070410320368040e4004860200c00654000300140481c0a00c2d5148140460741c900c25039084181d410a0300e0341c8003600000e135100a003010404da0707081584044c42c3c08081c40c0a0fa2207540b410071026100000160212541c0b19210791054401140081c0b11051801c0d44200c1045054108c0041a03e8849000003405a0030500004614405180c060060703030700c00346405103031400c0780050103003100c00c91070301081e000340001111010b041e01040202d405450aa0305155840820746860895043e51152940b14588500d00340203140c1c820080d00f081540c0051046140d00d482070198100707075000c0c01d005402800440400f4900030700500000d0704035200c400c02c501e0340002c1603030034498a04d10f4441202c00410b00d203641001c0388900507440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 657941169 1250 657939919 657939929
    0x30a140705010909200703020a140102180f060702010c1b0b0406090b09090411060c10020417150411011e020115150e1302120a020d180f030e010e0604 66
    0x20300300e80e40c10306000501c01483d64010700e440c14100b203094000703500641e07072100c22464007100c4140c0301c00942c81d0881c10024101c00c050b0040b802c2c0400c121040384190300034042d42521001c408401d041071000e00c011904200102e03a842401440300300055400395000c000038600c240c02146040c07294000c11598400150402079032a03401142c01e1100b1a08901c41c840a005025a698180f4001000084104000400051101d00b009440c0e0841c0c3c0c850300c0076100d800c903202c0180c60380c2503e20300d00706009400a118a402d903800000c00811440004a4603801c0724901d4040d1a182d65610b0712003060001e0903030105810801054101030046485000c0354225116990000c50004270003c0b48040d50401900100701a00b1b080034a20040c82d00582d010503455810341d410360f42c0c440c5140c0818001d0140c105100c801c100040c0030081ca90b021580100340901c01703018100450745a0311400c0c004525441c2004128001804110002c40c0c091039146010440500d00019004841c84c0841d07002d400035404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 657942419 1250 657941169 657941173
    0x1a0601110d020c18040f11150d0e010c080105090103060e03190807080106031b140f0f0d0501081605040f0608030a0e030c0612070f120603080c1011030114030a14 71
    0x30f0359080f4034040400c800301c9140025441e0303ca003410303150413420788000c240060440d410100034184035190b078001c8002503c030483c4200e44982c46485c200d400340c08040900b071415443c004400f00300901541d8580d05076100504070324641e03820740c2d8071000203000c1d0006c000c83c544414055a5212401c44540040710415a07450780e000d41404800580248010b801c0302c0107040c10500c42c1e49400f10011180d00030b00c0c000c1e1800055139440200907102038030a00d280c0625030725002626048080400f0300034840300c440d0351801c10031681d03602d2441d41c480003d1080ca80441124803410000351401d90090340a44041080000d0820350707518600d46503600640f90310002c00e0040b94020024034043c0309069072820282ca109240060008080f80090343c0141084207100040940c401118403d1011480485100404211780c5840303040808040d00210806201445200c00300340c8050240e000307002030030712418207a504503400e00301c04103000c0c1c0c0c0c5282004d0f0984100c0b2a2032011810000a42858800d4040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 657943669 1250 657942419 657942433
    0xf1801081303140d0605090403020f1006052d181b030108061807030f0516050f0d082212060b03060f1302130507030c1b1a0601110d02 59
    0x5400c9090003020820301e012001d000001080e006102d41e00b01c810075a281c2c580d20104030348118000d1a250300301a4021042504010802d900080c4903855903001c42e0488080030f444880d40340030780d81240116500030925500540c440d0001103e6071030f0300360070400c600805150340804034004903810509051000031400c10f006210014510150442c4c1d20015903900d1507040c190541e644140c081c26104d00103c4213815180000024020b5801465212001c5112407200f4140140c1c0d81120111060240c4801500002c00b032500c00c103820142440540400c00000c1c0b180c80703880c019045444100e2180c0c4100484225101c00355058030040c2003100c0300c44c010504a4288001202c2601d100a4001c6c2d000b001031010050070300414591081c090101e0801c664010b1001c5008000c0801c982030707101d030810082c0600c0d240c05400c541082102540c1d9000303114000340105401c0024690040c1032201e06009094090100b4030580364451418101014201f1300307903195a240c2180070240d1401a00b15031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 657944919 1250 657943669 657943717
    0xc030903140a05030408030a02042111010f081f080d0306080d0e0607060b130f09121b0b0a0e1222052d0402130e010e04050606060f0f 59
    0x20310a0840c030a00c07855a50300b0306506040c09001e034800500045e02d0440040300141040b605c1d501220040c3c0349405003a512f207404080031012442c0001d1088842d05102159030206522908652a0801881d80d81000584500b030a0842d010b055025120100010090215100300100b0911f2120103850754001603080c502203503e82060f48081c285010492013003541c0d98a03a5400f01540c0d1107076042035000510300303203420005013605c102c40a20040c032420310389103203109440c0e0b911010030075004640e81b40c00780001c005c08990000c4070700302001541d80c8200d02d0700c0c00700d00000b5429501c28107140001031407850001c0c0c440c0c41e04144445035152080c00107480e80c001440240340c580e511400c0341503820740074100400210454030607040090030300e03200410301800403042031900d48000e82c0a001195140c0e851510f1000346881800358400036100c03a800024500032201050f4411034001c4054190f03625400c0400030580e100d0600c0085012040c02082140d9980d44010f010080b02130740f5041d54403100c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 657946169 1250 657944919 657944927
    0x181002010b040c18380702030114010e09070312180e0c040f0b0f040303030f022a0c030c09011401090e010b030601030e010b03070621020301140306160f0f120c030903 73
    0x4c0c0c10040c8103d80381c000c00079078003442c174504000d105009242d606952565a13500300550250300700c003941c1907007032440f8034070354400117890541a207025a1110800307650340e0a10a942d60341d0780c400108040f50580e0490f2130f81b8840c400d2a4858200e050340301034020390b00da2000d91210800c0d10710310751044001408200040f48402d10301c004021700c2e6080c6062031512000f880960189120103001e0586541d1b17004118a01e41c0d0448080845460451460548480114042070b46151480700107224014410559280008030720901b110020035508007a802c00b880c0c00340c3c6041000c20305062003003024011840c800d80c404000c1c0a050007515440e120714000000400b0b40d98600c4981e501a490441110625100030919070159180c5007007008124140400454041e00b1003041164428808000851404c24000d04003001c5041181162090b23181c45034111103c034103c00c0b401c00070803500107010451f50301332804504403069030300b804107109249a852000fa2002480c0d2032000a0343c42072541c04040e08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 657947419 1250 657946169 657946217
    0x7361d040b090a0b043210020a0908030a030b01030c020c0603040206070201020a050303041a1305060a050c0c0717010b01091d040f0807030809100c170604020c010e070e0903181002010b040c 83
    0x40340c01c10b014911b403800b11640e1582e03d002d0304032119139000105001954015451100101042c1003140d03580d807103090b4002c0c02400d000400030300090404102078452031000135141041e0b10010f1642c0c1c5035440b03590170450700750f00c51181281135008811070840428810301c051486a401094190f15a2446041d603075004c0c04010407101203a00c0d82c2c2900b801141d00000c0c03c55006400301c0d0000354503183c00c0c044521034010303040040e88601c00d0880108514207031088075810202008001c0c05400c7c1d2a000550343d0440701c0c021540030b902040d42d98080e29080d51242038015010321510b02160380251103402d45940b0400007030300404c030904207100d8000c10422480130461a80c050400c100c1204040045c003540303500c1c0701c4424441c0500c02040055507564121100403030b2400003000f15000740900651210350a206e07803001e40015200042c441500407044800c403605401c11980ca490300401000b040c001c8900b8107404542d84c41290000c00d4440e4840d8242140b010b0303e6100f487c0500149011074200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 657948669 1250 657947419 657947483
    0x1103010b030f0c040e07081f08010905060603060c1e09060712080a1406040c050405030a060b01020f010b241317010e010605030c0907361d040b090a0b04 67
    0x2004c00041120b9440300c51503e130415998a461070003900c461a00c89040001c400219113143d80000e0000780c0002c05501c01c0444510174410341e000c55507000201500e0b070100300d803a41000401040140e442c102d02010100214a1005910b42012207131800300300e40303030046030003200d80c8696202115a0320703800c2103241e45d1080008c0320512034800240c149185190740980480c0c0266160f1128980c514010020b84015190240848495804070300f0450054480c031001c150141c028006140507044043c05040c00d0702e20702518102a0f030118000104036a251040490b1560b14180504049405208129401015a15200001c2c1303840c560010342100c1c180800c02c4141d0385401010807042e2404500c0c007a5804040b102d001c0030f03941c6c017081a140f07508082c44042044034641c0194002c000c02c0c11103064044480b1259400302c6481c0c0d04000c1e0f60121040c81c244500314844000740c001150b043c003c551058041f803d6400740c1c040d5640c2c4160107101542c044400c1c070803d141490185401d9a4171000e421 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 657949919 1250 657948669 657948691
    0xb09060609011e2102031b0c1b040e030c0105070305010501050c0604020904062c07060f1205041b0e18010c050a030c02010b0d0b0403110304140d0203011103010b030f 73
    0x1c588207001070840c910030751814004450541020004902441c1c3d080e80c000c0650280b1980e0030340b090360b408001d40c800c440c0000c2c0f002c0c4603200038900240c2d107002c1d06c150981c03010003014402c054840e0840003000d4000c0c965800303912610299a8880240060301c5041c05000c008103550414000c00740a8840580100d4100081400b86034084100001c0301d6400039016140c3d8074144d180c0d8240000034148100c0900c20490403401c21220010104410103140f0f0002c0b02607030301c084d032a09001c13298001c0c561003500001d00a04e2241524644552010f50064451403500c400d46c48000c1c00030b200740005038048102a440201080510202d03285c02c00881c40c00c00c2c0c005c01038183c101d00080c00300c1c041c44d4006020035640344085403115000758407105940000034000d01c00703a0302c0f61401d10b900c0441150110700240b01800180d410010000545090302c150318001003410401c0028000d440250b440281c0c1d140d92602c0d01c554030069108025400b82201000c0c0d596680342180398404418400f070b1142c0621 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 657951169 1250 657949919 657949927
    0x1b020615090c09012a0b0103060501120218090f071403100e07030b2a0c16030323040b030f010f0f03170c0c0a06122706020c1f0b090606 60
    0x84080000301c541e00c00d024201080044441000301d41948808485c507103081d0961140c000a0101c0302d01801e0407a48100000d03c2943c0e00d44498071207100400c0ba009412590b16844804810881c0307204a83c050400e800300c419120152851074a80062584080c0301944007809034861810244450120705c41801024170994100641e121b0f5280c1951101074145041c4402003502422120300303002c1c4454122852100811040c0c2c0804800c0c0e00c00c1d80340c00d08511481c1ea0b0100e00c296400c9000080303a030180c4034812000c0450f101d4811800001611202c10402000041840868207010318014032400c0c80c0c14100350706081c64480102c050390003c1203015080300c820400610420700c080e20b600d02030003096840c2d1f6207041410b0b14002d42d80c041554000001d0502141035940600080e010550f2500c0078000301c2c210840c00b1020100a89100322406102c000090205c0c03042d400800103070030850101c030b03c94110000c40101d501521a42010b0640d200e00c1d0036011440d2401286030000c0701150120301e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 657952419 1250 657951169 657951181
    0xf01020a0507090c020f1006140f03070513021326030f0a0f050f21100b07060e0a020d0308010e160c110402040504060303030e07060302040602100b041b02061509 71
    0x1031508244142d60f01203880d1000134050b07034800e20114094070744120072500144101d0b006400a403011740508a4402c1c20000c41121501c3e050f00ba00501d00005401f80c41c103035080105002d5001c030414540001640c0030848a10710000d5403002c00c000788100f602e100a818090b003900d540e240070b4420303aa50241e0091045032600b070340e0035044810b945000c2c01c0c40b41c0841d0100d58107560b58012070b00a1401450702140c20156020000401c10044400716800000d0b5901c01d030030302810011078014082e0002050100200003a03143c0d02ca030a07046081421100e40003096070000d0745190502800310700044002004109100c1e90f14280c61704103444840341c1c1034000407828010800c0301058005030449820f091000b42d180c865a0469010703140280080c01416120304014010b00101c0c0040302051260100028000d0321910a840560b000359024000c0c0000010b081c502400c4140c2d10190701c41e90302e0041400728040600c40310031b5008150040c06040c0b44c5400d5403070201c89506a002d01419403c810020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 657953669 1250 657952419 657952423
    0x904050105220b22020310050111102415080a06060e090414030c0a022806050705010209040c0e0405060102060f1303090e0106170109020a0c11040b1302090f01020a05 73
    0x4402c9000d14006180240c1e000043c1c608084119032000300c1c0d0a50222500a1420360021486114040e4094a40355a01d100444420001210601c0c0c95005100f0a00b03540c00140c008100031032280035a004030040982444407061281da11031595100202412540c4a40085105a002d51907400801c62140303410405840c1d00f00c005080d40c420b1100c50001402c000300550001b60340c6114000712501d903176504a06135500d050b1210282d110390b40c94214400c80485105070703504100400154001c0151070004140e549810801007120155000d01c5240d065445500c503c5403e81000e90312003507400024070601c0704540011b0071160464211a08008003001c40416080d0050481182c0b091320403030b242421107806040380c01ca64100b5010b200000781c1c80d980502c000e80c54003a1078808103143d90340c44904030101e12a00b0f0f488008a01d01c00c59441c0801c10020417000001d0b23000c4c0c0045149019800003d61401d882e1201802d003035404030702000306061514820500400a000819103002982c482c59 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 657954919 1250 657953669 657953719
    0x130204121b12020f030a120f020c09190b011202070302070f0509070c03211401050a080613260d0e060114030a020409020a12060203150607080a0305071b080904050105 73
    0x3a016004c2c2c42c45600094408116096105400c003111040007090b0140050051140e0701e00c95005100f41040036034507192191206000b601140160035580f44000c0d6860044c00035808014107000207105003460328030b458002055603500c00c2d4082e06800b400c5c980c104c0c20684041c3c0183e4014201c420800c2200d60f000344082c000e8603010304000f41d50303d0f0b003100f1240c0b031041c0107414039011505050580b46c0e030804801c49141610360895100000c580c5500c02035039220760840c0e4240240d00304600020103e281820003010302400043c100c600046802c40d6640c05900c00c042c0484007130f580301e80107440f0003000d0000a02500150320040e10010b052000295144040c0c103010380f203030795070f00e0a51045580c0d0884040c028124032564034210f1134541402c07402034000b2244d510f005203e5101402c1c0c5840d00b101142d084c203500402c80750420030542c00c11401040002c0480d024401030600102c076015140d040a5426407003004610b0f0340328803035014030081c2c640680c007041c0034050002c1a81390902c0c203140c0389 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 657956169 1250 657954919 657954923
    0xa03060623032e03140607080610050c0102040902031303030c0813020621070216050406120f0309050a140411030c0f030c090405161b0203060114130204121b12 70
    0x1081d0300c0d101c2040e0b00c0c03210501c20343c142e5652000c440c0d0000100042c0005222036011110103640780c5944090301558040021250030703620120390712030451810300070740c0a88210030020000600341622042c0310012640140e400075405a40e01021200301079040c05810503200e801c0c5801015410301b64080c40680b2030f005402489600041609489088003044040c035004200041c0c5c040d030304240801944a00a0002e07120000c0601c40c4085401d040c903005007021152080203150070b02078a500c034010500043c41040f0300308011050002100d5580c2c040d9800903000c001013840090b03800d20204011038201c12030010f100c8200b4001c00140b007095105a40c603030141f0b015403503070305c0d80c3d0aa4a0308a5105012005074841e10b46030a1000c0311100340525207920340aa04d41b030040a841140b0040004d15a40d0b000f9415444000144a14200d14014000703c0d03002514070340b151901c410038041a6007044e0080c0e861007030141d490000b0f0105050b10b40f6203021101da12194400c6c2040b05004498014404c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 657957419 1250 657956169 657956191
    0x30b0934080a020f0702271b0901030c0203130f2306041214060a050f070e09041202010603080d1406010c0f080715020d1a10120e0a0203030a0306062303 67
    0x41d9800402130101d07103000da80148030421142480e0b03140251a00c5401d18030840a080400180c8561038015940c2807000d9842d0311107003007520a00c0110042d00e40c40816408600050183c60000220840b1003000392401160306488241489180e40b81040320324443da04020b4440b980e5410b03625250300b103c042d101240c001d1407194141c2d04000349644d070540b071483e0441c4502c0003001500340711075220f40e0107180305000c41c1c00300f9141c4140c00c03540108820b8803158414000e001207000580c448038801080180c0d800041446962510b0b030340219044a410700440649922810030500075007640c1e150b0021003400d1566260740e87e92140312000107003c10082c000784002030142c0c02e000c5071f448a8086084d00a106550b2001308a0510000c1d003014210004912002503d05080d490401d0346621030362855500c0900b8100c1c1f582c0171901501465000e00400d0207003407098000b41c2c80c2400203215003c51341c0c03000b180071807400314010581103d00c030b4103081c14514002c0034004190380c24102c980210311819 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 657958669 1250 657957419 657957427
    0x10e1c270314100b060f0909060a170c10030917070501022a2a09060402091008090601120c150e1221030108120703030b0934080a02 58
    0x408614440355040a800d010340301c0303201c48420400041c821900b008494044c4079600000040c42010301404034107182c00c10013071190100d203085c07441d00365034400c86c020880c4c6540341e96400d900340c101e8000303a4160107903003001c140898142070404000040f129945810480b101c169150760784440000c1c480d40300781e10000604001400025010b0301d0303161041c5042580c0c1040050f1044c0201480e102c40652580901600c12454900064054450610b81c05914481762180c40410001071401040543e00030350a018818081c0ca4801034004203041c070361a92501c1d402c05400c030074581705050340b00030356a2841d03182d4480010713005103102c011900340e80000620a402d1190503a484504003007242d0300054040d02ca0b13110a500064803641407260405010b01d901c40c80b10a20046100902400549038040f140114401c4000c0c0002c06016001e4a400039800100b04001030310f450050b40d00e082400e103d000052500000b8040c0e000d10000d00c2c850b2443c102c44200740103440c1d0b10307006207052003041c4e01003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 657959919 1250 657958669 657958727
    0x15030c0318060f09010e0f03030c070602070b0a020405031207080a0f300605011107050f130e07030b130b1503070812040e0c040f03020d0c0305010905010e1c 69
    0x41000311015400c407080e00c0b114603112a0b030302d500c00c0044600c0c8031550300b45585d0190350800403038204100b100104c09945155101100071015511440c001c9441550130841c8101150310030707030305034069203240002685d65440e000405150590104008100c02002c0204a00140e00b1004445051240342040407404291420070750b100f022004050011508000c0588003407218484a000c90440a0204001440d241c0e03004440a45185202c4403050303015400a204a01d0600081c0c0c0807800d0040a500e850000b02c980c20054444610400480ea07100712010300030000b511000907880041c0c068041400280d58442d8080090050658095408000e2070092207071400c3c4105005400082d040ba01c4d00140ca440400701741d40719208440000020b100864854960310049504803440c2007040780199045400700140043c041c07008032401c2c9103035030000000070000e000304086140194000107614021020300d40c100040a0080660080071100b20340100341c21481f00854065840d04d9103490302d54032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 657961169 1250 657959919 657959941
    0x30103060f140f06130905060c070813060e0906010e0f0d0303061e0f05061c0e1e150a06080a0605090c0301090516050402030c0d15031209050405010515030c03 70
    0x154150009040ba1407041198416408540d1030181400b41c40441011001da6900021a42ca1020062140c0c03c0100132503007070040e01020b40b00c8a40510041c078a4914102004007074400b02e03610510100f1b140d81407581040c9003030b5418540c45202801c110030307101032500024007004c2040c00c52501c40c10301d032114041854426800b184c0a00541c0004001146009020b00343c001801c0c8206684d03200c9092000c900da04240c8103907024002047d40169520707180070525005001e8420440c08548150084d845480540022a8120104190103424403440c07407000f135081500020040301580b410b00d4800c01030340d5400544002030030340004001500340c5401c000c1c1414140344c12442076044d030811416405014000c0f4000b03400006004c00303000c04540d40c03024030041e40002c40328182d00c2241071111000000050b00a2050440c43c801c14030360142d02c0b035640d5506c10039070355035050026805140500141c02d083c0300b20790260808032805c4070803060030b890820041c0701c0100721207070030341020010030380f26100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 657962419 1250 657961169 657961181
    0x160e041415010609030b060604060c020904050c0a2403150513110424030e0a03030b06120a0204050a140901120c0e07080610080609070807180b0307020f070803030103060f 75
    0x181905005a560b40c3e01c8000c2c43c440c441c0c001502d03c1007071400400c0691800c0d20807241100d01d151100c0120080c10707001c10061040082c01580e4900801c244000c003036803220550005862848048022101e603d8841150401815204828035240c021007014105080d400030301100c00c01c451000642000c0031290014000002e000c41c01080089808908000094215182150001c4440e4071410307440000b00c080d1074880d0644201904a0384211003c46e110390850588030f00080c125618006e0301140003c144181254a4403019a0100b402c3c0a9454540c0024004000d022402d01d40c0c0150f0400103684000107110f04002469030310020010400700202e0000246100c2000c05103510b00780348040e11404044841910a111003419152003a0180008034002d1502411442803941d03100d0003030702c1311400030b84a901030040d22a1140300003454400c150000c0e003848034146481c1e040c0f6900282c0307000030800316a4030035004600c1c10f0010308400415641181c0c3c200502240d07158070043c0240040c02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 657963669 1250 657962419 657962443
    0x30a020405060715050c040609030f0309051908060610051b250911030114090402040e0a0c08070b0a021005040f0b010801051915050402091c03020a0302160e0414 71
    0x500468010280b0004804e0041401e80d000c02c1170299a44080c0d9802c04c51059000380c1c000308401102c1030010445583c50007030341c240700b410401c1d482038413000061000e1240100c030440fa048540000d01401100340301480d0000c0081d01d10010720440d25002806030300445d1080340d00c01ca00080c03204085602040007804e600d03201d02e0102c18480c621186055412910300070310724001c0c00e000045074054062421a4103c500700c0f031094601028480400c00c82050143c42039902a4940740301c8c000803101803009420072841a840a4400e615140805050200e50381c8004040001880300789600c030b0300410b00b91800243d0420001d11a40c4925100c140301003080b001504503511200003007655281580324a002c3c03442d0040d5008103202008030700e0291280001608440300e5107940c10422414942c0103000f5504c00100828542450203003800b040c5c024020054005070f00c01ca4614040c10f40500c011600c00040b00d1144441a0030071441c10750b45075002d000204000b0340c542c03240441c80400d001d9034200803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 657964919 1250 657963669 657963679
    0x110a081302100f140a0c0b0403030b1302091507050c150d050403112a0f040f050a05040b070e1c05250602010f020403020307170717030d0b010c17030a020405 69
    0x30a0002030560341c1d464aa0400700c0d500044e9024641e20761003d4803502c2904c2e0346c601e00c45001a0344d0700910103c018004038285620361442c801c417a510103144c82904201c0482c010384a25030742c0100030440032100300100b92b00000700803003804aa13020400c2d0700c10400585103001c030400d603a0803650b018400d85058046d42c9140c20705200030154481c410040390150401110902881c1c0488a0030612549a882072030328252103410b0528103108a804420070002080001c110101407003604c02ea602c12500c0700300c0140c0c3c0714100010044800000394219080c2d161148941404070042211a55003442d020030b4000f035500c0c031000308039040000c2e0010345140502c0482d9008183c400c603100c00d2060141d08055403d01000003074004040c07081d0fa080340c1d001801817608610b015034000070024103006141e1203015140f0080340c0001040c0d001c0941004d88001196106160701c8160110f40d42c0d0071440303041002a0ba00e49000c9a40801c039005060300d1200c61541d2900e40c2c0504a000740304550200f43c101c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 657966169 1250 657964919 657964939
    0x26180913120512060621130204060e0103060c1e0806130207051b03030a09090209060c0f0a0218090a06050703270b0a06050901091e05010e0a0f110a081302 68
    0x1c80d80c081e002e03015000704408000180d4031030000b08130700c5010f440d218003007010340950003604000b155a03080c2d821542c428030300000d4400c0c0b9008541a0b550581100b0380013500d020040080151a1042c40415415460b1160001c80180e50030842000c100d41c0c02000c000402021400582d81d00b402528081d880c04411540c844062400c9900c903081450300362249080f00407800c2190030040708403414405a079039a0716031107007061681002908610041504000184440303040c180c0708100190321400c040d0001c1600c1303840d6104200a0350021902074a00c0a1181c052003200d580001c0e140724110b5000030045025991508102c0c0100794203440010040b07c031103550700c0007200c5500c6048410f80140c0e404d90b16582c0c7c030b1102105541c154403c85410080072801081440540e9100d4444088400c500c0742c020401c019104c2d0954200380c1109003601d20309030a0200b00c08035803042d000407904948045c00301c07001400b008120350081c2034170728040c4800840020902c0350080071030b50240368020241c03e00303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 657967419 1250 657966169 657966203
    0x90c0402030a1d010b0604030b100803040303110615010507030305072a0302150702060711010f06090209010215221401050f160804020f010f1b26180913 67
    0x150443c40321144a8010307542c210240f000c03040c01880410400502454030340741ca955a950716041d0b0003040c024802000c08030108000c40c05100a1005602039540c0041d026202d10320381e414076402a040c400388141c10009500a81d0b0010103440081d50903050008555440745401e0700e00351a0005141201c043d8600001c032032004940002d080603000780d08488490000c00034801044d542030781c200300580d0010000600b9036100e440c03008041d179600d40000c105421040c21000545000d500310004103500851001c0350740d6030402514405840100d81a00c203801c00100100c803015100d0110105440d1910341a010300065404042043d00100020083d6180c1042240e891031003d85900b00c0407024100c00400c1e042c0b28810090103140c00400044050303e1f030780010b403080342040014034217100e800d42144202d10701100328002d19900030704000a400041103410820410166091038034000305110320607418110300d034200d10454064400c543d00d41c80348040054212845d00005050213550500964 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 657968669 1250 657967419 657967421
    0xa060e121c0f03050c040e0615040909021305310c0b0306040b03030f0319061211011214040f0c0503060114090106080103050c0d060605100816050a0f08090c0402030a 73
    0x4002407269442c800c2d0200a44011010303900c3c1590651100320b400e00c024058a40000e039503640010f00100406407001e070060803010960096800085130540c0d6084150a501342041102c2210400040c20069031411070001c0076004500001c80202240c0001180c1001403090755550385145c20a000f5601e4603903801c001c010f954030444005000b07a04140d003c03000e5040000c10780b212a682901d4090a5540f80f00180f011103648100c50100c0c40d0300c0e1440080c400303010b0f1850f003600ea80034001090040f450790001405003e81c00381071401140c80c1c01c407118a02c0019544040e04558003250801d041000da007492465209160080f0340d1502030034000041081300108240c607554000d5070701120301c0ea0f949a0035107528034248805411038102c070000c881945000a00014107070b06c40c0000050890b2944081801484400159030210310003406000140c0e4402e003140d07044452a1601901d0031001110080c80c0701d80c80b08001e402d102c006c00114200010a100384150000090b00464691170040d01c0c501c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 657969919 1250 657968669 657968713
    0xf150f0204180b06030a02070828030b060a0e0f030f150405011b0912021801060c020a090902180703020f27030c061605070801051302031504020a060e12 67
    0x940c2c0200b21001c804042074481c081c25000c0107005116909640c0c4048007207010b588041c0b41201c0c1c000c01003001c42c40e201d1650060868002100b1008442c40010500203011690b003600114031400042c0440ba0031241d01800a00021100341c40341045102450007080c901900d200196450340642c1562541c5030602d0221300e449203005078000d2100940e0400410080009041e0303540018840c10340c00e00000308903625090901c1c0c8090012000b0307440103044102c90384c00c00e81141c40058548214142503190260b6507001424115400300490140c0d5070000b200d00410540880494014030000340c4624000d134182d4820005501000c1d82d17820031001c816044119012080c20b503401049103046090400040004421070060700062814075100015068034024032012101e61080780b030003050b20f040a01600e030040710f003c07820f0704501c042d503c109800c002400e41242011102c0e9802c00001da96080c03c00e9081700d090b4200b076101d004100300400e40003401d440e0018107520505140f2500021800010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 657971169 1250 657969919 657969929
    0x103021c0501060c170307020601060f110a1223120601020a06060609090f020c1b030a0206160c1502060403030b0103060305031b06060a08030403080327060105090f040f0f150f0204 79
    0x200b40d0445e04500021480c00280da064006034440001840304502901d0040c1c2480790701d0810a100c100e440c0b01071440c00d049007800301c40750203a5000290425800c45451080d4540c1c6040446030440c440d81810843c1c001c001c00c00c0030990042012130315a0f4000d00411800f1500010140181c0d0346510300940710001ca0f1242c2c41c4290300d0700d001c2c0e00c084407680c4252440d000c1d94073b0203400010242c1c0c0e650b11300600340d002c2251341402840319032401659441c2c020607016000c1c807404588183d2a0500b082884150f5002c03881c0c0c60860803801a14590208400394440e030705003400243c0c0380c6e00000490003000c0a802c02849803100003445080c00b00d00e1300100008520b400b08403801130784c82a050120031452886640b8071603105000600c00184000040c0d46e00119903d40c0031204403c02d14074200c601d40c00000c44800350003103c014800b42c00c2080c0541c2c1c0c03100404480031003508040c0c1c0d82034a881c0707200fa0060a0260400052010420f400402e40d4140400f04000d1080c204400c41000007503106100c0c5c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 657972419 1250 657971169 657971183
    0xa050303031e0a0204060e0d05013b01090302120304050a020607050a050c012109060e0111041d011d1b0c0304060305090a0503270406141305090c0103021c0501060c 72
    0x5150303074911340225019a18940c0c2c032040c1c0714403108144203007140100c1045896548502910542c921002100b50840d000c01004880e0b40c400c511008045248021040c4000e904010040000c25000100c4084640315000304a650743d5072810300d43e00380030840704000c0d0b0007440003c01e02c042c010001180804540030390192000310003100015214190003e000c13140c08114680d820912600e158003001c405801031602207803030300b105103070302d0f003103910006000c030340107802250a00c04108810f6503200e508081c003111810650500d240d424420180c1c1981c0c8031003007070400c0024150711040c40101c0410390400c14543c0c030b074210400303c651130343c101d402000002031400c4001001c4070030001d0001c0445410501451411004002e140c0c14207601c08641c1c400b0510341958885d01d42c40d58824071000f4076044120a248070000f1040181f40104401e090198a0600b024415014070100700303e1010036090900681d07130305098413607034061b5841c0441494020315010001406582100421010274031442d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 657973669 1250 657972419 657972421
    0x80712110a0311010f0e120303040c090203071e030902030a060e0d020102180103022505030403060c0c0c05010e0307091b0924140c01021b1b0108150a050303031e 71
    0x18494000d4840c40064901810b583c96181c0a5000386070905010410740340401610454002148a01910200101e61503100100300702c103000380035811902500d409002035242d41404c400003041c00f44250508000c10401c003a0500c0c1480c0254841018180d001d42554841c1c555030920100901a0060f4010540103000e41c0c1d9103800d20601c00ca0f0840c505250b1080100010f4500440003500f1014850300881c0919180c1d02e0051004150392542c98070030002141c1e00d900710b02c0c3c5a010b5800841011051103900511180010046802c510a44030300b0b1800e042943c100340002450700a00d944203072403441c03910b61598288800f0145070718480c0c0c085e49850045503071700d6240b140c1c4141b50021030203030040481046400c05115034106030450000cc0240c5042c03181952081d82281e200052140c40c034041c00310880c1000000f808400b01032071140c203004040c8624a4000303441c03004c00034000e65a5410003286a89940d40f0344a60b01c0103050060120b981740d00d03040c0b80104400401d05510300600103164 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 657974919 1250 657973669 657973703
    0x1a07110304050102120c01060e0a0207050705101209060b060d0902270103170423010206060909100e24450a081602090a0204080d05070507080712 64
    0x100701c500b2200103034001c04290004010501d6650030043e0703999059501c50b0710029910904002d1940610f968a200603074540300740c41d04a240c9906940300601a0030160060f00019403c41c24010810318455000300d00018030323251413401444c405000e00c1c1e002e41c010480c40300c16110b82e0b00c4004058800c0d503040300c28809101c000610407018041c54060101854018400035402c03d90858043d0503824003181043c1d1152510281aa0f080480c032401900403031004404e5039041140a0f0015425036820b469403c1c0181d0b410745482c1607000c000412502c03001c4d40100c2031010009200d200030042c098128006002003000705011090383c62171442c420350300c1815007400584441710710242405c1c0c5c3e9524000b0381c1c1d690340c1c9142d00170301c1d041c14154040d40b4050030200d08143c00401080c003204800c2a07000c1211701c104130001e84043c03d100c0f86544140001e0166001c000748000740d00e51070f8203001d5242c0c1c250b4681946024031070342040f291801b81c90701c0010201500c2e14102c030321500c24180031038910500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 657976169 1250 657974919 657974923
    0x18080c1201140103080c120403080903010f0603021c1a010602060708090c010203120402010e09091e0f151009091b12110603100909050c01140412020f0a031a0711 71
    0x1044007502402c2c1d4400041001945000042c0b6000794a01c1c16224444075034540850345800c11b0784251142100052501900d00d400c1c424a000125104820011542550042040920555010010507003c880784000744410100030b24018005145040401d41c5c4948000f5128501030b1841f01c0825820000304d80c2c0840f001c682482c0b0000180d00a40c1044030190f0010704e00704000c0d1059043c040e003680100c5280e201c5409035881000c90f8001416084000301000d40401403b1001503c980c02a058060820101107507401101c481d001c00c16a42d42c0300d284d40e0300b9001000c0e80c00422154640410700003044030041006030011803a60b031141c52a40d840c50340b06084402200c00511316103508180702070600e00761003d0744e088482040c0700090701da210401041114400030050b00c040e1300c03034060601c0035a80601380c0300c40074414202c0981403c2c40c108500c0c0c03050700030400080c0b14200c840494400c5841c0d0340021001141c101140000841d880ca00344070491b9000c1c0c488c44000382e01c0350101c0b01d4140340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 657977419 1250 657976169 657976181
    0x130b011a12040c12030e1207050a031205090612040302061005060d0c11010c170c070f0602092d03150106050906070c050a150909060302010504060f18080c1201 70
    0x12030040c00d1918001080c480d03004403004004039401c1030300310f60214109580e143c002410a20a80343c89680207242070400003202c80380300d4540120740c4001020702030b9031034817611041102d92100e000700201c0c510742c00946480c014107072010b8004a003c650b040100e00703c4581a4000d0b4040d400351040c0b61a0310100c20024140c0340600f40d000340d820041d000380c0030010f51040b00c0740c249a1800482100403410f6042c2980c1c1e1400c0c5010000d6580d5074100c1000c4103010100b500a0080091585081c2450382c0700e00b0300342c540707400141c051540495442d00d01d45400340c40d070050700c030b201e041c1c6004034005500c050f818010b001c40761802441003c0d241c0070350061101506041e100700344c551500302045601041015130140c1401c98000104c0e0754002815210058540098098000e00000555500720b0080107580c01c1d51200c0d070303203030708000003003001d41d0b0032004075800c2d40c000d0728203003211005122007522441c1409914030005225404000ba001d040400c034140c4001e07003220100c1302c5020a444440c07d13509 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 657978669 1250 657977419 657977459
    0x513060e031602060c011103090a030905090702190314041701051e0a15090c021c020705092e0603020915041a030403020a1e1a0708060114090306130b01 67
    0x200520302d0402500d00000900700b030b400c3d410008a41308850000000c00c0c3e4001b6a00f0b5826179000e000c2d540101a001025000540b0042e2112074107450545e2000756106503034801d54201c1105d0b50180740134144100d540411641d4106000382d41c4942e41d843d01034000508641c0300a184d440c00e00400c1302010f0480b00d1440580707204002c8030039510f80f42a0071004201684d2490b0310480b1001000031035050a00404203108001c1e009000c40004000c00c85074088800c415010454200c100c041c4050342d660b56501da002800592807002c9500e95070003203d580c90380034403080d8400000ca400055402c4c0d05400420901d038003620b4800065036840ea46ca951806030740a4042e03910b40300781d0469012101c41c030140d0790007806441140c0740c02049444060880340c1d80d07036000d4083d24150514005104101d4041c6140e00d10f034071181c54040c030b4400d2001f001e1400281c1013034100440c50021041c146034010580381800d40040a4580e0f90901548000d40704100c07803401ca84080380b070320000483d503a100c0c14407400c0c09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 657979919 1250 657978669 657978697
    0x4080a0f03090b041401090605090f1606050a05181909060b16330e06010b0408030a23042d05031b27041a0105060904020d020d0513060e03 61
    0x10f01c2e103544816178000c85121010980d0b40c0c0e04240e002007100d5010725402081c229024201c00100d4a0f0410304001050012021030b0980c1001080816800811a240c00000385440c1d5166035550402103000082d42c1000d0354040898119009120082072820049580d188403c001c0b0320750b10000800030340160000c00400051170941800407410b84d044910074407440b0300c2c0e00c1c0d00d8182d049a500c0303522134100112140780755941103140c0507528204041405480d550039000d007080c3c03800c08265500c1c414182031000704036000c8400845290410398100310383c01c0002408d600d035a2140381e0320400c001041000043c0c181071048500482e8007600310903064482c06030180c0207101c502c041900d555945101c2c1140c100114120400e00305411941e100100102c03403143e4007040c00c1c9800d100c0c0c00c14040c2c101c030078558038901c00100f115a48040460340ca6620540300903855207080c0e40b410000303014401131801342600300020821407000a00c214800796124910400458040300320709076490080440491500c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 657981169 1250 657979919 657979921
    0x8120403140705060f18030a080a031d0d02010c1b11010f05070206030c04050f030c240f040602010b030f061005041805010f021b0a05030318031204080a0f03090b 71
    0x20600040c01040000101c6048909182c0d903107001c83c54a0303101305c50341500e0f0a00401d038101c4111841c04000300016080300141840070294031090400d1099100c400f0625649603801c60101c4525400b54403445102e0003650342c00e0290070400382c00b0b8012440100001000c404409003012880c0d0788480990340c00c843c80030100c12440c0300640c1e03510f80c0d460041090000a01c510801a550072004500c80c80e0348454060310399241a0910000c1e21404501c0c0c0e102e80c0217003000e80d180d030312204800e140c01c20650003241d0010110000041030741c450410b101e154030000040200d1034640540090300701907420340c12540200b204038001502c0750001d0750341080d41c0d04d441e1002c100c1c62405401c401c01c07014031100101c0302001c40e5982c050848045400600c15036802050b000155a801035101410101240c003504c060007965803804d84030311005000d1814211880c07000603134042e041084d166042c0e14078055080030300300f81c20440307665045a01d107500040e8045036000482c234031a00a00d204980d11003050270003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 657982419 1250 657981169 657981173
    0xf14060442030f0c06090e0402180a021308070e0709030507060509010302040509130605010b040305070e150d0335060f01210209030708010e102003011d0108120403 72
    0x1210030100030990307618000e00001c80803445110105800c18412204210b5161034020040e00820b8541c2c811000031000104200141e02c40c0700c540200250000d1440100e6601c07030100000a00420160144080a8010200b81c00c4030010b445800e49103e031100b118155600c20086030944481c0c00000e040b60070401003000303002d00031409002061014100541042d4484e0b010603400c0c1e00488040404482c503126100c180066445803501408107040d03818946829a207586030345a25900c141d00202c1c21200c006002c6a4800d080d0154025009124240000c4681002171084091140807440090b0110580d40c0120340ca4009501c0e441800144180035071311001040ba0044900c0c0e0300c54103000c01a074440f207203070303807180c5d00d20030848060140141c403484480e040c10315118890f007185002d46c0c5400c52250000a00003003a03451114200c202046051f281030381d0030039840750802520344500010001040c0301c0308000c80d9091540001031150b13134a070b980c1d81c1d02c03d81d80c541140c1045005c0a0802c41440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 657983669 1250 657982419 657982511
    0x507090618050a0b01020a03082205010b040c180e0c0d181e0f030509040e010c03060819030504210203060103141b0604060c1106160c08031e0d0f140604 67
    0xe4005041c040c4031440084000d84003a80000028ac00c503038595503503030505d105241230722a1850700d41045c5454040e0350981e69802c08040c2c0d03903009902c00100138070300060b040321154040300c82c400007045050121070540d01040381d074541c80500444a1000f4050480d0420071540600290190050468511002c45480945540c0d00082e00c1c42d40107a200c0c4041042c0d440d0900824900c1c5078240c1d4005456450144528100f00d0f40840e52092003c5082204c0b01007640003081d203003915071a024000e141010038189003c0151400c03802505401110000014040311182170128188214240c5813000086050303614080c0400a0099110506110070300405101d040e140c58824843c0f079001d54909441c0c40040e0098202c09216070602245240c06400c000c0c1c3c1305203502c0209003040045d81441824480c40071807800c50910342c0304002c801f00d060003070400181c00107030442064403010003c8442d1b121079048100c50854641d402a800c0c03550209044c941c580701e2501070964418441c0d800741a5501040b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 657984919 1250 657983669 657983671
    0x140106051302190509121b12150601200607050a0e0d122715030e031318090609110a0b070b06040509010905030f1c0501031e0507090618050a0b01020a0308 68
    0x10b8000d026a000541b01d081c3c10014500451110304081d58a041d00384100600c1c107146000e048a01d4100704400080310402c03480d41c54019200742040303200065804c101030201d400b01c1c0c1280d0418070440c0140070300d03190000020040d00300f456690000d802c010a061180086149000400c80c400601c1d510141034843d40407280500c2040710325482c5010101d021800000c81604200d151586007644424841c2e0544105014003646d41d0145041c0300510b482961303880002d1180010512484404030306002280d40306000701940018100005149801c0c40c2c1300d03211b20000c00500440c161003010030a0340e2030b601580c20041c0e00c00c44041066548105010180101400c01c2c42559240c075a400f00144061002d80090030141c91026140e070a600300c080013020088500d0840e507850803005202140140390210340310150344000028001d00351800501c2d0100e142c1c00201c5540c0f0344000031515151b010300c2e2255540480300c1c107102c5922500f619504403401050104e01590081700040c0029004074401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 657986169 1250 657984919 657984937
    0x6040609060609090c05030d0309120807031514030d110a0314090303160606090c050304031805120d02010605060306011e0e030303041101172802071401060513021905 73
    0xc50a070342d4070f402000c2a80c06080c02124407402005040c881c1381020007030f0909103021440c0500100c60651242c03130f41000502100000c205070440051401c3c3c0c000e4000420340e80c100b01e400d032151075841d00c81d06006210f03801f006120740941d8562055562151a000c458260240064103103081c199500751001c07a1241a0302a200d002482412030564041c8090f2001840701201034030440b83c2032030100704556568100c030340000c0c941620340c0003c035442010782e07900513454144072966880480e4000300580c4c0c0c4d584440d84c04069491204101074020401b80028030154000f480fa003521241085500d000c01c81d10140013403941c0700d01c00c001300040c60345402900403e0a01d40349010900e40824156407044400303460f00c3e4080e03029003000d541d0220070031044080d1302301080c00340d0031b0503425140003405581c000fa0481c984000b120009076555411509540d40c1b1402c6000004103102015000c0e140394803583c1d00c184185543c00b651800103000300c8248a94103143d40c400e1035618401130351150441198 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 657987419 1250 657986169 657986171
    0x5121b210315011e0509120609030406030f0912090503011104140f060412061b0e0108061e060301030c14060a0504091a0904061512081b0a050307081903020a020604060906 75
    0x4522907205944000e4150490f950740717071503491031341c001405811659000c410a60368441002c101100c5800b10640e01900d015103400720710a01c48041041c06003418550141c0702c405440c00d0300400710780100d501400c032075095009100d0742003060f2007202d55018910071582c03610b0081214900d00c2c0382848201d80c03881001041c0504040d12080e50510510314070800700c440560b80c41c980b032410192900500c6000721b09103062503032841c46c0f00000380b4100000e08501d01440004181c08a900c04404080742c0425014200d0343c2c4940e941e040084112820348a228010752900031000050300f4488100c138003601261316030500d0170b8906003402c4000d000d02c0c80c181c10049140404203c0c00c0e610f41c09000e001e54003d80e0040381110083e4101e07691170405900100c5240c01100b0460001082903040c4c030060b010100400704180301001200e401d10034006401003880c040000d403402000144006072500b240302d85000c03041c2180d40303c07041d0124440c080358440542d00043c00500060368035003040d94128403c202c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 657988669 1250 657987419 657987437
    0xb011e080f0123091b060f070f0218060612070e220e030301050d0609051e0303070206010803070b040b06040b13060303081b031305121b21031501 64
    0x20445007040504a801071141c0d464919610011502060189452441d10782d50360f02c5040c550b02441e50303a082024110504092100005d20503541d050503641036201a04603256501080e150001d580e06200c00121311a1440c0340b6151801034426001d14490103000d09014174001c050300003500d05203402821001040001c2780301822940f6004582d00da00c11980310345000c004500ba29400540e1040e140c0d65007994000d000411903655009070801c0b41a03005400011a00c3c5142005401c00115040040509280042d605c9403110004021031044440d6426151a83d0300c0d4042c20352a0320801d42c018081034166004900071400a011860700001c008200191885010703000c5180300c17030207001c02c000c17456a030a8100203064010072820f0303016800f041e500c4460041366075030f1200340c08054910404d41d412a240d2808000301001811800861944c0c07039a100c401c400e1030900c1c85220401101128000d0512011900c80344011102c1442d0340c0b5007640e41541e4a03054080070010401c005641004078800c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 657989919 1250 657988669 657988679
    0x40305070c03021e03011a030601141311091e10031d0f070f050d081e120f04020a14030a0303110409050109060f0501050c0c010e04020c15070e0402070b011e 69
    0x4640084084c000505507951800700d8010182100c281820306d60480c0030b40d0a40400e142d5011650034192040b5011f0f040f040022180800d018850359190840d0852915400440b480480030281085045c03c03541300002c02c0c00e00340c030f454044042c030400541011000020714603c5e40690041c01b00d548101c80c42c01124030195002c6884e181d002226442c41c0d802c0410188001c0041000c00c0c4080d00003590f54040c15901035540c0f840300d03c195015600344182c070117040c424088855084440b400d9040300c8007022818060708010a44405640c2248031b45801400041c0d24000d45e540e107040244001c014081448075a10150060700f0006c240384c0e9203070400c00001c6400c0f503c510900c3d01801c00440002603450a002c401311205a2541096045c0482440070525540d07001900d4490352900b0718043c00d03445100c01c0171134003900030710410a0040c0901207640c01d58a00c000c2e201d0744164844e90714000070104400601c012842080000703800119010700501641c134442204000d0001080302519202e9690 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 657991169 1250 657989919 657989929
    0x41d0109030e0f031b271e0f07170415090302010f0b0f0325030f032f1902030a0b01030b2d060d02010c0203030a030b090a02070506040305070c0302 65
    0x14080840100303000070b54003002070401c14900d440340c40c020303002088a90f418690302c0340c40c0d000f103140716403150b0080303001c550385507400c811481580d102c3e014441d00c40782001d40b00c0c1d4a082e0103100d030b10448449000000f0302348110401071207010b07040c82c4e2580581d103451034050400c005c02c010030030b0b2249442d04109143c105014030a6810850281d400040c81502410f410802e5400300804140310f2803010007010320079075001c1a940492803580c40c401c04405440d40120718a10900c2d4009000001c00214010901d034000030f980003a0141c00800002c00c95030b480740281403296050b500ca4007070344010081400380d90f2101e0000a918001000ca80803401305588500790000c00341c00840307020020000b800440801400ca4049103103a0b01e0a11030032510115883c021118014078082c8289040c1408506690084400900017070f005800c0c2e036600c05180b04082c01800c3c600480303900803c0347c0300000e1213540c010310a0b00c90241e840801382225803030b6914102c0d440d800803041607032040c5414000200503a24 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 657992419 1250 657991169 657991181
    0x3060907110f0607091a12130f08030c041815061404030b16080a0225030e03101b2c01050d0203040605060906011115130c0b0405030c1e041d01 63
    0x4c169600000941409007000040810140d140d4400c20b081c4007030b0104070608140c459004818110850f0b031007406050070f041030410250040d025000001c01d02c980110100c0041c4103990380b0078107100c14041c05900c0300301140c8601d154081001c00012040c46814071406900c0c0080010018603401c0075100d4903102d50100d0195510300aa1003178820100d95207420001c95503110f03450341030441c146480d4441421810032500940c182d03c101c100e1000007010301490340310032665409801c131040c40f40c6180e620301c01021241908030351032401c1c50a586d01d180c4620b0621440840c03e50039001090144442d00c02500700c200a443d050000c14000c58000d50094400345101c1c0380141c101150901b4141e091000440015008604008a580040154220000307118000d1080b4911224503036686803040d1100d0080c0080013050802501070000750b0341038101c00f800c1602d00440984561700340e007100b0007000100300b40b030f0503100b00e40c868040000d900c0c20303501c5042080c010f1700c0700b0000c0030006420b0a08680c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 657993669 1250 657992419 657992431
    0xc020a091109040f0c090f0b03310b040c0503120409050601090506070803061905180403020c0613080f011e020a02071706100e011a0903030705011401060f020303060907110f06 77
    0x2d80d0700021030241b548080c03920f00074a40d0380c40c1c40d000d5500309500121240b0008242980c00035140d41d04500c0215081d08a2003006150500c0c40380000c65854242c202d00c205980a4a8000400c50b0121b640e01c0c0105a15031421b07040c1001907c0c0c1840c0c049400040c0c00010041818459000300000d079944400700200851845030080a03507030b190920803c0003611058003941046141110244003584074103c0202c90203d001c000102a45c0d101c0c034040307203400000f88055030845000b140c40010207170010468001d441042c01929541c240320b14415080701c0040390b0b401c40c02103000035040e4920342aa0700500741054030f441951006501c802c3d20345c001c3c0c803030010303604044d500200800101d41d900d119020b02401030808035030790355403520810900c140403001c40031000003000a610340b003079a0f040088603203166000340240210440c50300c2c009040ea000344220f1000c501c5602031001050b1011003203138410b0f000141600e0304e03900d40340c004884401e000c00744210b40d17218100c0901142e010030032003244241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 657994919 1250 657993669 657993671
    0x3031e060301090206030f04051c050f030a0603021216050301020f0301060f1e05091003060e06040f0204170303011e030308040b06060c0106091d0a0c0b091306090207020405070c020a091109040f 85
    0x3023814034000380740900c0c00e4030b401424003546181c080c00c168000112008114003002250300c070b485140008000300074991000750321243d80c0c00190401c010100c3c003810b44038803001c100c544030340e6114241400c0c0e110340004500034141c20401030141d03d005544061400d2031902c1c2407642040c81441c5040028210900c0310045400410358810502d0403041d2000d5590741c6103010f0058601d0202a1442102c002d407059204039103d090b001007118141c2d05513070007481c0382c0307120150101320004c840b500c0e54000e028400b950001e01a0100203080b180031202e0407298103079100c007925a20741d100d0414248000e03009607800038041041e10350501090089102500c505080011070481400b41140f00300125850001240c0040699002003001100d64070110341400300f09075601c2c4d60390383c001022141e0913a9601c1c481c529040001c500d84a06034094000540f0a0301c042003103840300c24041d1030a00c5803903402907200440010a0200b0320b6190402c220a110151445040008100020301602c0012042c51102 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 657996169 1250 657994919 657994921
    0x91507170d0509030a090603050a020715060306050c04180203180d09080c030106180504081309050f1e04110604050a030f17040b1b070902070b1803031e060301090206030f 75
    0x140c6080c0318441d040f10051005503d40b0107601009052501c03184a403600741565100022180c400d01d8044400e182c0c0e00944240708035528400301c6000309018042a1030491810b400207841c801c00d4021141036684059407140312180c081d544902a40c8000c0090441030040310404000202c10081d00e5801442a00d60800d01424122100d140a00082440c0e100e0380c10320100300b00c500101c0003946400c41016a011405583e00d09001c0510b1003205100ea009901098001400001c160b1125020744036041581e40e65458000c02c0c41c0ba8039079440031000ba410505004a80060700e9030103443c0401501030051070906035120005001c0105540c4152812400b00050404000c00008904114a0354407142c80c02d043c1800d10203070f802c0c014121582c41d0700103520700782440341d001003001074024283c8132001e6607030300c5c820f180c0510140c1c400e0b00c8801c00a0350b8041005000040030054a100300801955040c080b2500443c401c0244400b818841e095503a44486401589981c0019407241c130b5222051505 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 657997419 1250 657996169 657996187
    0x20f04080a020424030201140c161703040e0705031f0b090312071106280c031d0105090d0f021206040308070201051320220b1509150717 60
    0x255010901e41040e402c843c94050307012130b84004a0242076940a191031b61400c0c41142101aa92243d2076000d00144914400441c0c0e2008540c018020356142c603c02800c0c00d01c4002e4195500d00540c0640c0005001650020300814800e801456000d00c0c44810070b4040c1d00c0040c1c40a00b5207809422184098038001920a0542000c00c0f680b00600380001c0110b00d841960b407920008002e040d814103100d25800180300000d01000c170b502d400d490207021407075150000f00310400350924890101c100c0101d103055031031054804210021011440068607440e1410340c00804002d00015503030004c465104a20000e500544c4502c80000640380300007000300524241401c01404142c00105100b04584c103180c00c00c028400006d82c4d800e200c0e0343c8401c48030307504000110411040005002080d0b00700381604107031030414551075051420f0300030016042001c24059410700030500301001340003001810412111130301e420820ba43ca0010f10700f03024403a062041541e00c190003c90400c001a858510114100003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 657998669 1250 657997419 657997421
    0x6090a03030806280e04240c12021e2a07031a070c2003011a01080c12340804050709183819060302012001020f04080a0204 54
    0x40f03001d0840c5003032940415184c031500c3c0241e090f010303410310250303281c010a04100c51120001100188525407815900c0d0f80c0365594003d100d24524200051407000255028000d140b080712410781301c61030418030080740480400702907485000c080c07045515030b0f007801c0d94204071030340c4400c1c00c0b1040034040d100d82442d43c108011091080c00d9400e038403921f404148030010340c01c02d9136004082c0d442844210782c030440d21210400504c1c0190a0b680650a10f482c801c03031900540e090248450003600c4940350703612203030b00b040c02c18040e1581042100100708040384503164105c09180f0144a4541c9034400407000300c480d8460ba419801440021591060600c01044401e0241e030b0040c1a10300c00420507400242924006002281c00107040264952806150449040020a0040340740c04c0032104101c61881305600202d802c58690300105450f00e12418440e600d1b014030011280c059466036003102440e208420084603030060000299030800c101c0c0c1603506000050b000925015014105058150040c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 657999919 1250 657998669 657998689
    0x20a1a070f050f070b22180b0a05060406050a021005091e0304090e160519140409060203091b0f01090303050c010b27070221070204061806060912150b06090a03030806 73
    0x101b00461140814007c4081910705440418000c07040440e046061501084290270030fa04031039084000004e011420300d40080040c04490b841c0c0c0e08803040c0345503c2d81e40104854007070312611030300c0e08194580701c20213244802020080307c0ca5810383e46082d41d9089920115811601c0b0307814260042030200b01591141040e14008000654505a445202002c0c401c42185075000d010780c0054401e045110703a4840c1da100040e10f0743c1c41882150f03242418880786507100c252040341c003060041d904140f0301a040800c0102580c1c2c0d0180c41d000e600d2070860390150b900d074110850b080140d42d039a0f4501512540e9004041141214110300380e454604442c0e204501000010824010340d848500600715005c0d201d10605801d40b010204a03465103040c0c40014051700e290345c482100790701d51102900071450303654044011244541c450115403030742c400c0016044640d034840030340403603000d00c50110f08502c150041c0b451a040200202e10300b42220001403414035032a00140e001803e031000b00249824089200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 658001169 1250 657999919 657999967
    0x1d0d030e15010305030406140d11131e050609010c0b0f07030f05101404061805060306100b0708130308030709090c030902030c041a09090604020a1a070f050f070b 71
    0x248880c2e60468656076564400c40c45400d041184828820680482c08800e40d600000f000c07006100031441a8030904040c1c110342054a44e4456251b4005440758a10030a80d8881c45080c030361032120380c6000100302d01d80c1c00c4051014140180010450006503044d000c0c1c51054285aa2010260600840041c03c8402c18226031858a2070300050103000c0d210114284200c0f1501954000c000f648032010901408641d03204110301c0d0390700b9800400300303015604503a200d01c0c030607170440d580d40c0d42e03030001c81040c099a8882c610500c601004a440411401d2001701040000854201700341c950361356a2841550046801d240044e0f403651090241c1095409640c514107500d2900740320703680c030f142c000036240c4c003120290b135101e81e550f400c0c0201c0f080310400d0610010703c03005000d10742c0c41c0f4041020540300d0403300d0301240329018100c0049000018004e1b820151803d090b60b150421000c0e903034074040a45900c1099400f40310b001c500d0040340200700a0000a422240c085c5615207012101000e5250340075458 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 658002419 1250 658001169 658001203
    0x602010b010f0e0906010201060b0a0206010305010e0a0c1815060206071206180203041511040311030604030818100c050c01050c3619030b18030d1d0d030e 68
    0x800c0820b243d11107030b8002031403400c8510070401d484560050380140f2003640003141034400400d10340619500400c0c42c0c0c1c1241d0080c402400501c2c040085144c40e040e003500018207030305d0005000c2c030900300ca1402c00d0ba400307203856200040383c03500c040041680711070a501036401070740710360108480c103a40a188503402e82a11035091010350300b008510181c40310395560f084e1030954003000040032f006900343c2c0c0e40c100c0185070900700044900700040000c0c980c0140000d4400e900d0062089010f424006071080c403440c0c01d03030b9030070f03015460303034901c8610041ca40242c5180521800c000014208001d12420130410304580747d00740e40e00541d251040c00e4820003814819207140a001203078044000360100302d4584041d00ca240c54024159201c6154066280c0403107402100841c402000800c0155804084c1c0b4080c1000700b085aa4403607841c12401e5100b4181c4510b5081440040707400d0100e0f411484500007141d954000c11030482128a02c2e00080c001d234500040d880303030004282150180b210000e40098100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 658003669 1250 658002419 658002437
    0x402040f1e020a02010b042a170610050d05010906210210031808030901050403120207050703030e01051c02070b0606030903030f15030d08090705010509090a0c03240602010b01 77
    0xa080340820032032103070611035000100c1c80d402a02c01e5110500c100c000900800c00c0700410f015032001801e0030559102c0603c11003402202050042083e00421014140528001d5580c05c4c140400022240c041d90140030003401100f0f1200814010341d4043d00640d43c0000b0040c0c41c21801c8131082e59009074007588440000c00d03580268582024a0301004d0090a020484030309003460384500c0c90b04c034040504200000700600c0704251041d000300380180c1c0a41c1e141400002040241c8040f80300c1d640c0010a140d0040c0401c00000e03000c1d1940450407401410064100300540f0001d01e00d00c0b003081101d01e10185d000450004000429019607042241500d000d802d5103051800b10350f4920025009418500c81500015035002c0010740c0080f41d0103019056034074020781000082c15481041d80c0c14015405281c401107103a500c1742c0107079205054010403104031500c40301074600062800726061820161242c088040b0200b5914101c003442c2046201c0b049890f2504e44000e0840314040429410011614 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 658004919 1250 658003669 658003691
    0xe1f030b041506171b0a1409100f0305010e0c0f01120906020f04030609021c0305040306020c0304170f071401020d0e0d1a040c0905010e01090f0b0306010f080708120a2303010e0402040f 81
    0x4040c3d40c3c87c2ca041d43e50205a072100c043d02c2103920a181e01900b04c0014901006c020404190882105031007504d00301d55140141c1400c0214050815147ca40000c1c100125000c40001d950060401903010380c00043c5404803800003d540da5000d0340041d41c081d9143c400660460410844a00402403540c80e003029405507030340c1c010194403803484050515500407880740f00f1243c040c0212070083c00f5a152460003034804011564580301c1488040c6070f207000c0e00741c0000c0c4908041d03000c0c151502059000c0e040e80f00341034000f902c807480035504d42c0303400404c2c00010000003504807600e5511a44c0e00030480700039240c24905081c80d000160024082c40b4141740040200010b100c0450b41969402180130030040c8141a64500801051700c8a0798103114100001412054410642d81a02d150030162000745882d240c8032a0b480388c032000d405404140401c00c405615104440810b0307200d030081e09000141645000c1e22039203070401e8010518030030750380003404114501842040081400b1901c203005078a069 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 658006169 1250 658004919 658004939
    0x150121080d0b04060608150906010e01030e070807030c030b07020708100c021014060307051801060f050c010603080a030b191a07020a0e1f030b041506171b0a 69
    0x204000030490103020900304800081900041c1c14018007a10070031019943e4100101080c5080e102c1040307500a8104080b85424500355507440f0345c4040c3c40b803e00003d0380e000110f006107018002000a8018600c000c00c41d10010310461004500801c4030100c26801c1d414511804a4003501203425540480da00b0444500041045220008401e60000d444da02206080c0e0a01d0700c050a41c00780a89032048081c1c81c2c039052410280114010303000c07120382d991220180211210204410b8155010f210010440140f19060b2000d1468052601c581084000c051890a4501d15002158060804520401481d9241c0f00b060800901140c00c0145e90310b030700301c140d00304840901403c1c1e441c3c05040c00c40301d40e1011f190100d07000590f024026078011030361580100c0c811601659205654114401d140c81c905c00c070401c080f410740750032410700c401945666441d10002005122a003061545035a0009048003124884e82e4444210318040e1544002c48240d0540c0681d50030003407031090750501d0060001c102a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 658007419 1250 658006169 658006229
    0x6071527050d050d0605041e05090102091f090e0a2009092e0602010e010501061e1b0807050105060118080d120603020d0f152313050d021501 62
    0x503041030380c0d84d20003c000240103030603da00203682280c02c000041206103951004d103442c50206030b9007001581c461680e81d90903803055000c0154007050106010184c680c034900444c00098142c201264403c0d85c401e500d904008044824809450380c81c58480c11164640001804a40290080510300241c520015006800c0138240c491110307080800c0c5580004004008132601c03545141034000c0c1d66a07501e000740070340500c490841c030b0303542040000101507000e044555041c0e04094240d001c0148a65002c46000d1581020903025464121001d00420040401000c905028200108182c03802000140c03c4156804805401c06803058040100c5c2801080c50301000449284c004884150880020044e03c0300ba0030180d4040030362001c00042014180603e40101d20400c80300a03122141e0805404441f074000c40e1001c084c0308e141404038403014011405510407041c01010907206c0e12a101c41c0e1404030084c80420240c0e0050180e04054509074424600508080030f688038071040e0300180c0f940d84a4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 658008669 1250 658007419 658007443
    0x110c01022802220204031112031c060e0c040e180304230312040e0c07020303070f14060a02091c11010c0302101802040605010309020108150607152705 66
    0x10540004904640d94074900c100550b0031002c0481655984594120017540f2611044924030017039042c2e000c150078404000d800084825000d90308090164007115000c400e582114a15695103250202e00402424801c5010f202e9040359641c80e1810300f4503070310103083d02821948540001e01140d600c003c5001080764140e80304419a4415131070300c10303e080a02c002ca207070320503410b0061909042640c120380d00a0005c81d010b0481d0000310703440700702d030400c8a44140f09010350140c000304440804240381444407103d4621030102c803081c440b8035214846c1024000d90352381411036000246840203103000a0303030400c0c0544421511600710410350b01d0301200c40e00281003a0502c403c003228401814028425a20098010b074000d010b840d960b61a003030b8641801d02d034124030031031400f0004a0a03512a1103114081603043e102e0041d40c0e1034144407802421103100816620040400105000522010090031a40404600441c8000403a402200c884840c8a01a000345400c24400300200c0d100007401403200e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 658009919 1250 658008669 658008733
    0x30a051c2c0109050a12030501120b07030b0f06070b06030c15090f01021c0c030f0f1d0613030804050909060705030106080702010b040e03030402090a06060504090b030319110c0102 79
    0x40c07050a45030151000c03660107401070064006810601c201c69400e4044a8500c0d44e0821907685c071003050b03801c1049410406086802c9800018000500952013050084002094950100d0807030700002c9587e4000d0344c08a850860f002c00b4800641420801c0b1024004200c4a01d80c400d603a40380302001c1c070700489646a115010704002e0010710b900911040c3e81440a0a0410f00104083d0b14087d001c41e0620301e0840c0021907280803014681cac4152805601c0c0000d0b9680c2505440700e4111098807120f0112516170302c0031040001210051940410f800250300c40d8501c3ca807114a017908200041070010700e0705165810440070481011b50010031a4159041420302e0011a19401b00c224010403030380303400c2e981180c60110386075404800000a981300f18401c0b140340d10b40d0b0b640d07040d401e425a045446002d001c1442404148507403a400d4000d002d80c548050101c03801c00940c1d0150101c0b28015544130008a51202e0b000703441c0800502214034010b01c00e00007007028461040c03060082d401024100d141c14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 658011169 1250 658009919 658009991
    0x1a03010c0e0f0a0e04050d0f030207110d1515231005070c0503073506012603191205090d0804052407031d0a080a0908030a051c 56
    0xd0303484200700c3c809404401000f441038075040c60210b0751449002c01c03000200380707891140242c40f4803a000320b07920103901120044611003007805020750a28030510444201600c81d0010400b8202d501c900c00301442280c2441c1840c61030265015501c100d902200e20381b09090026091403900c50114131040704549240c0240d1b1519541488291061745402866040c0681c460010b6540b0170308014200e40d490090300c2c5000c640220402e00680505494403402a0b04584010000719008030580626141c0341c80032024049210f02c8400d09590201c6a41d0303154500c03480109030728980c05525020210f102010401076428555035042d540c06030704000c0d004201180e0002010002c041c4040c5041480329a81504000d85071030031040801001c45000002a01d00030031b41c9042100c80343e03640c80041c03440015000541c07070364641044544c004c0400b001031041000c0b0000e07c2c030380100b000348551130683c2ea589032181000c0e03e000d05c1f0101c00c1c40450010908041c400d1300104800c80b15a0b481400381c2c01d23a42d80c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 658012419 1250 658011169 658011199
    0x30b191419062703121d0901031104090f0b01060e010f05030109021312030c1104110f0c0a0b0f040620160c09020d0204082b05130f091a03010c0e 64
    0x10300f082060a03040703944404900001013080001d90300000c0135186e1140c3c041070551201c0044d0301c000154549038000d655a0042001c030302140007402002001400210384103401c0e0301d4884075010101070031115a41d46400408c4074580c07210101c0141c203001d10740007402e900856802003281c0818004c00c0080340d40000c007801014054802d90004210071030000d1030340c0541d0b043c0a41441b007a200143e90024400f6503001a61405100340c1c4c40c601d8207050894104031701c1c0602d40c892030f000380b07906141501c11450b01b0340204c0c4140030030921488406050315402d01c1c2c02e00d0544242c03841102003080203000d80c2080301a200c0144162610746c235a03402960124a503038208411808110f40c48042021f100203040107200d003c0341c00078019180400101c81d410509042d41d01070b403101e4441b4a903c018540035407003480c24424030045c50710811071070100007010f03154454125440450340c400d5114981d01c02c20f601e900b9000c0c00071104045d004800030845a4480e45010b040c0c074082c4043c083c821410292074000e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 658013669 1250 658012419 658012457
    0x806040209280e09030a032c030a0201050c040501091202120703050708010b0d0b01060507030311030c0c01180f03050d0b03070e160e0307170114041a01080303010b1207030b19141906 80
    0x42050201403000508c1c06c1540c0f80d10344951201c8603030070065081400040c04504e0250458080307075810303903c5400aa01d40308561034050305800c400c030381c4140c1080880c244c0303040812001c00954040e00190845501d0704e404542100d0010f508680121301c004001c00c0414054185c4a044a0550400c60b5981180b480d044005084c8103800c0d414420000c41804a1007075400e029040c0108140001c000000c028039520f43c03100e040e5540101003810f07a00b00403000a00c40c00252003842d807010b0001c9501100e900000b81081c0c00703508041e200742e2410080050241000300d05801040d0340d414201c9925600c1804a034940b54280100007011070000344110031690701f50f10140003141c400305140e00714101881d1000c2010250541803100c62100740011030124008000c0701c0c1221040c20f5400d180110b10b92500d581d0b02001401d441c10f055a034011422603448880150451901007626483c4840c1020f1440105085c41440b0900901d40d550304907620840184040c000d503109400c1c02e44482a100203022 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 658014919 1250 658013669 658013711
    0xc02060405010806010318050105160c1502070f060c0507060614181801110403060507050307020a02011214130204060801021804020c0f2509050411010806040209280e09030a03 77
    0x18803081404017000b814043c040d4445401103030142e0060340494080c010880321100031410281201370103040d5466414101e50051a12500c0350002918954242d115241160312031748052000c10360000b100c070100f010a20803100036110b07000f0055141e40c185e402140d8412a0300104803c0600000086034001d4000d240720480903c00e48020b11001c41c41601100d01500248412103a0310306040c0031a80103802001924407918250703008010085140c1c00450f24001841082d9041075620007800010684c0d00b01e4251240c0c1985519045d10007252042c0801c50710b007a0701194075070740305200380c0908241c4280c3c0440008405c64000d03881340114009581095551940c1421502c103803100d50840107081520303070054810200248404a980740c00c034009582003110020801e180d210005034896000d01c54581d0001c402074001810f240c410404503502e02940e1200c2c40408408880424820207112000c1c00a04080c070f0045602e414006615030741d07402103080e00801d0603129424a00020741000d004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 658016169 1250 658014919 658014941
    0x42115060906030b22120c150e2b0806040605060424030c0818070e090304030506061009030f030c020607060f1404050d11030910020f0d0c020604050108060103 70
    0x400c003865a54410000500642c0b004448103080580056a5401001000483c0c0d200328101480c002d07419940724032200c003a080001080c0b156004071f03100442c4481030000c05030000034800143c0441c003e0511403a100da011910105801e541e01c84824082202c0441c03e141001ca040141c81d0751602e00002e8064200e0760442a00141d0208000858113008540b12440c40c0f40e1401307801c100c4450607411001e43d0002050040401c1115021440c5800703050300154410ba00242914001d40d00ca01800c103001d0001d441c024600c1e80042402d00030701130305024454021201301c40200b01c2300c00306a40a0303c005c16070300c4060a0f4032071051044003410b00442400404a60041846545181a1030008018204480140f8a542c58209845e08212070214181d000e42c2d00704000700120040300c1001ca8161024580314440d07400288041503454444ac43d800c02c40c0c0340150040c00d43e003500308a4052030700c0c0c0c1c0d408840301001021580440907032112801c4400340c4100380fa24480300c0d6641c100680252400c0001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 658017419 1250 658016169 658016171
    0xd080a0e03011b0e0a0e150d1406010f090f0204180902060c030d060e07020a0201020c0405071106010b030f090a120509150c0105010e1302090105040504020d05030c030a080a02042115 80
    0x90343c07545507444080700d05280b10881354203241507101e110700c04440c901111584036940f842c01d0f44020b10b10b00b280d480104180b203440500d140b0005800c000d418040280d00518400d2400c800c01e01c0300011500515640c80460b49045080902d84840344e010f44e0074030001d99a245942d192034805640f514402c40c3c0f5821100022a81d45001c1e110010004140611600c0c0003c03021002244425201017412407407160141e005100c910026000c000003080060001e1003406001d40500d0000c000510606008003200882aa100e141101461710714100040c9494055048200104001000000d144c81405024034007a80c55208010100e110307000d100303001e25103050303000c60465000c03e8150040750684000050510603511641400d040201c00b91030001c0d032050303115005114508240d4801c0741d006000401a403881c5000d62201da01703561140d03003803640d182c100203085652541c001a006130003140000045180919040094580222060082003074410078200c02061100e60b00310078810b0f10071218 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 658018669 1250 658017419 658017461
    0xc0705100c240c0302090603070815030f0109150e030d050c130b13060302040620030f0a11060f0f04060c020f121e030f070f050c07090501030308060d080a0e0301 71
    0x1105000c4920400b8220807506242c0800682e42c4a8001d0307682c030306400361101b401c585403903001342c035500c00040c8201c03480308000c08100440c0d50108041040a5014000040c03c540d0608004411045044446603944d09003102c1030a03080c0004100e0300c00840b51f620026464450f18080d500501c035400041c0303000d0408110100701c4600704001068003009449524945551340c0c481602680101d204960215070903c2651140751903074002c806a82020a040d00d01c1c1ca18803214410094001c50b040300001b400e00240009904020010580c01c8091711480c01e0f018501850760520600d001400203203c4e58640c034840d240700f40204803003112417840c0f4050b030303015041e5007142101c0c035000507a01005000d441505005106003480403240103001d81981c01c034032940c500d4000d070f68060402e6449000c100e010010041c0c0804240060800361515081c003003503a5255060081078940042d180d58401c2145098500001d0415400c0b50315800300c0d8288044980000e800007401004112200c527241d641c000e03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 658019919 1250 658018669 658018703
    0xa15090303270b010e06010f0503090c031b1806220f0c0306080f01090807120c0b09010507020c01090f1a0409140103141b10120603060e0d021603030c0f06020c0a0b06060c0705100c 79
    0x1408a0150355042d073f41100d81c0c0300c81000e90030321a00300fa540d45403c48038045880000701040075071040799454803180450201e410341c244c002142c0c2d0100d540000640d5414051180d40c2042c00114220701d0385070000d21500845031105201880303814002810820100c40c2c5490942c000c680141065412800d020740c13a28010301c0c210b020703080440d0008014010003211003038640c0200c03040806c2e1089400480001410300101c001c161200400760700c8040000d21000030726804601900a18401c40a002061940741d403070705c0991621200c503411810b40210f600142c00c00b12a0050b446010821500300780300380d0710b10034103030351102248284107050b0f81000c001100b0703c001900645001c0003c8001c9a03004910900201c0e1504150250302d444011108010004a80f0030040000b20a0107903101408614140d81e0707010407070b1b00814034540c0300c1d08900f10030700130300c14510302e41030340700354141d500394034120314040c11986504050181d00e10890114140c949814800d1220740315465000100d2031454241d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 658021169 1250 658019919 658019953
    0x20a030c0201060f080a0f05211e040302090609042f030c010906080408030c09060c060f0105040e0312040f0203030a200a15090303270b010e06010f0503090c03 70
    0x6180c8000141d0700b00880020403115002500d803c0320710240242c08031010703a035110728508030b0140f070644441c850f21040307003042a6400c0c04405183c40310040c9580d00c45260301c2c81b001d000030107a940403407410244070400150b101c240c4d00551120080f5642c01c010354071464405040c3c856500403018007411a40038001c08800406a02142101202101d001d211010011590360a60380994000940800d0210340018400405107070480044440750341030203a60b0f00401c0d100e03000215400009c0e8844c606001c2041c0d4280000c901408003950107100c004150010169248a000148000c012026001405000c10001d1045400f503005040e81d82e50301c08803400034520f58046021000d41850414a0559018006803c1c1d00c41c43e841202a580540c4009440b0300900c0005029400d05454910990b04186184070414011960190b030350080c1403142070070140440142c000c0003e064100080c050240e801042121091050746440c59680e55600a10303402c007074a00b642e050f01031042564200c200e40d03036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 658022419 1250 658021169 658021181
    0x40216050d09080c10141b2b0207050307051e040f021201060206070c0605060d0203060109060f0803090328080f1e07032007170102030402151318060504020a03 70
    0x1001044074004001c540420505104603180c41001c24001310041b01003030060006401c1001304000c1e8030700115010a041424606140555401842141c16034607100c2c0c40704c001880312030301602c001d018683c01c00001c281c3c0c80c106402424860384040312310f810018280c8030f03240c4d1080c102500c24042101d00d02d44c02030186d08218060030358942041c00101d070251000640b01d11401c1d06075940f48001d41d5a89804004001c040c2400f03030800001c2d0b01c0c01d0027584003000b189000305150b800026280385005801c00d1320904c076800448031307030304208803102c61a500017030000a504500300c900e4100003407040107000030145c1b40744003c104240100710302c403580a02401a001c804c1c01d034240d40f4107d0300e40e80542d03c110310886200402140e00b540c2d004800100c00c10011080003007402c2210082a1103c2c654882d001d4040d0725070f0403e80d0004200300850070500041e6481c1c1a41c02d55032800c105405050f40300310000350040d1645440d40c0040e142c06031449804c410010325010707104541c0c41c0002a0000d0103880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 658023669 1250 658022419 658022429
    0x61a030319081320041b0908061b121305190611070f060b060c0f0604021c0b01090905070b070305120612030d020f040918210905040216050d09 63
    0x701001c00070301030f400410707018070301c0e20f6011400784440302e0013040343c0707510b0204011255003082e50b85803983c00740da040034400c503510b41c01d80e01c0d2282214a403a95062900c440200000d210003c26010703007440e01e1610b0159403d0710a03500b11000036a07158500c00183e604080c601402e148a8000ba201c00800c00100961281e402a802400044400000700c1d199104128001741030703440700c04460700400e101354070440030000010544d524105040704176901e007428000c9109a80e1300444144000c510782174146041031920700221180c030307030125120701108542c1445039845441e104d640c25010040b09000000160880c1c030307035580c0c030380100b0b0600401a41003c45609010000000800c030301e4680702c0301c0c42100007441d42c011490120500c44d800007039041644415070416051202040000f964001d8005402210030000d0141000d42450004108500100380d00451300c00b00000603164003654030829200291405070340c44440341340c0f600417200c0c0c1c400050074600503141a41400d0341c0c80455802140c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 658024919 1250 658023669 658023677
    0x402190e070f0309331d0601092f070210030b030c12030301120f02090403031407030203070f080603030c0706120b01030216020d1b090207150e0703061a030319 70
    0x222880c0d0b0140c0840c0c02d0324101524000d00207002c003c0d441c02e403141e8204040f00c0014680003450044c400c82c0103a500400105040d220006260f210340070080203c54010000d14200344412200c01d07000034001040d100c0001e4070128918980040140308400301ca13101c40e4050440804076040707101c0140100074020550340b29000700000c0381601c1c07074490542c90f140044000918a164604080a80d0211003070600721440303140c0101e0000503039224142984658080e440c0484c80e40d80001241030344200c010f24003000d01d44144140001164480c510b503001c006213080888668981c040003910703601981203c1800c5118202000c1402a80300361444038440d0404000d001100303031b25006605030f000b10f9001c259100c0341c5114910240c60328111051a00740a100040786a80842c600b610811105070403d454054001605c0703070070050034200802051130410010001002d0382c041180d2546068440030341031a44034908801d01d040c0300780800e0030f198001800c89035207180d0428401a5180c1c445159070102e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 658026169 1250 658024919 658024937
    0x1e050c0c0d0f1e120b030c0a030507080c01090e0a05130f060c090f060219210e01080a0603021309140a03121b0206070c030c021c0512160206030402190e07 68
    0x45010702030403c050b01c05807903c4003940325080081006003a00148180c0c103200b01c8551003100d495a072816800f42d40183c4c00740c07901d0750814800700e242c6109000c4460420404400c100400980c066200c0c0e040a0311a5000c1504d8640b00a540c40315207640c00c01822101c0c4404460f030820005522880fa0243d854135150f00c0c0b5a03440c82c04a40780a41c610416015070400c044010120b0741d141042e6280503c25a200100b50601c00d5404490b04001c02409010a240034981380c002e603045407119a101d40d41d198107020190650b40419110301090100050843d1900350b00c10130085110800894401410200c8041c0c1d0803505000307101101310100a9001440d00b400094036441c92081c420b46c2850340e400910141c8c445010441e044c0c44162016001c0180202079600160f42d001c0f01e150301750007103101d11171191500341030031800c150906000071003180007000901d104071520100488003d804407540758036550350f40007244400100858100c088812440702190f2191901d00540c0240d180d40d44504032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 658027419 1250 658026169 658026197
    0x18010201110c0304050111070e09030d0615141b0d020a020906030d08060607051002040e070e0118060309020d0f0f140d08010506071a0703060503010f1e050c0c0d0f 72
    0x714894548214440d800811061209501542074100b0140800003150031300c554070503802d00c45660545605030143c00010b081d1426115500842e4054014526000e801066148024050801402e00396803882000700d0b04c00b03a841604500414440111003d071001070814000003515605840d100702e115520203001703c1c250b41400a107885600d6001e84403408141c0300c0404001080d0081c1c00200c0c0c1510030000712003082a1700c1e001400041c03420000c0484a0704140001801004072070640d107042046201501081105041800044072050b003400071f1410411b0010800800321584007500e400504400c50040041d20300b6030b10311207401100c82c2100c1052076250070752201700c440f4404000510446c010710151900360014a5624402c03880448004040c480150301580304551440110b540c880c81086641020700a282060000c150200190b40354170115014544200010b484000e5a400c00506210030040c00c940364180e0040881c2c10142482000400e101091242c000c00101c40e0030286035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 658028669 1250 658027419 658027451
    0x110c1513020409140a0b100504200d20072901090b0f03010903020c1021021b190c0e1909110604092f070803070509040218010201 57
    0x802400c801400c8080514240c007040042d0181d21030994416811142c01e035000b0300e04100040c0c00610410742a90b05103001c202c40350501e000c0b03170700aa001e80c6c100b40b041c2c18103080c903010100c201000c850015450301c0790b002030340006060707081d542d071650041036140d0b8145850341800341045a1181480c05141c0100856050b036806100002c000e1403003143c0300601c0300c0a05c54100c2003a000c4081c1042400349040c2000a00399001075a090340540c0040001005500b803101c3e05540c8040141441102003000d0402d000f660400c02c501911440c0d070220301082c0c10094608005660b403080022a40c00180251001c107070a00d840c2c10454580ba840a030002c4c0c0c0a1010038000d114000340305008040d80400c48090001d04900c110881c1c10905003401c116031595204082d0001c0c020440d40007078881403886408100c207201056085404c0d14110801c40311074120400c64000c564001c008135120f8071044002e079818001d003d0f007245d129002143d000320843d94510604c098090981c0248000c3c0070290740c01c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 658029919 1250 658028669 658028671
    0x30e010e0304150302031f060305070f0809300c030c1506090c0c160b0a03050117070501051b0703030e030d0804032c030a0605064e01110c15 62
    0xb40040f00071940b501450790007a40650740c801c4a00d000300c440c038110325601c17585042c103d0b0496008a5a13520500111680c0302c0102c000541d01802e044009042a00b1002d82c0ca100418840201c240300714240070036a40e00340706a40c41130041d40d400a445081480901ea03c0c0d8001020240c0740d885904e0481806035101c00380513001d400061b00d4034449072078140a1440c0d940c404a00c0762298419142105144000740d003148000700079422085483e81c0c4c00100090030345e40c0c1070f4449501070f0703280d05103119a0303032010998034101c40e03003400c10541e6410400c0d402e40603088030a5820040f4061a00000241034200c803076000f01c201c084045d14519000c0000544544005541c054002211503c00d0580b0180c129103009208003c043c04130202c1c2d800c0070003e840e00d10950390841d0115102c106000203800c00783d0441500da00c0382c80040203001103040c4070200b0015100310318008039030303124095042603440554566204815400a2004c00c401034500d864641c4045403e00c1c2c50321443c1048603140a1032000c017 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 658031169 1250 658029919 658029929
    0x90627030a2318090919030801061706031203180f0a0303061d0103030f0c0602041415040b030402060a09150804050601151e1b14060f090c1212040303030e010e0304 72
    0x40840c0c00c3c00303000344500709000400d058910b105041c200d0310b21802c051500804d5034800c2d81c81d0111903040c0640180850310044801040310100b009200307480da070216079070180114009038a91241d0300e2040d02c4c0803000003000345060034095800900000e00c004a404000780b800703a2400e011042c0c0e100c0900301d150390b0240201c030003401e83c68014000648036034240840d010f4185460510140300ea21664101d0b44254848241c0e040c611510007075508009a643e00d1802e403480718103081a00d043c0107600350340b200030002482102c000601d00b0040d030241e000b90000c0c208a0000c40000b8401117005822520309030380545071072080760000903c1c0138800344c0884010303055076982403100c6821019006140342da400c1c01414041c0c010b034400c0490070540800b03d44580140840020140c038842c00a040c00304c060a01072102ca03451042204c2c0840016a048440e08152400c4411211011010f41000c0c50600b541c504140c00040c00028075074990485414101110020049100036200e8590340340304500c00c2c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 658032419 1250 658031169 658031197
    0x71109092d01020c07170a050a11030a0b0408221202012609030711030c0a0312020f01020c01060f0509010e07230703050d0b09090627030a23 62
    0x1c80d2007140034880011064000741c240009144194640d8036003660444000d8108603401388108220b0702c24450a00c0d20311b0418000070301050070301501d5042d02e41c1444c00d405081206102d07002d5903c3e48040044041a503004045a00300e030405140000560344580c5840c1403207070704410b9000c01440c80060b2901129450034044400c2403039039005540389200603150950081d40000190140d80070b12030a1440f8040c1d1001860b980c0140340b13818032031514102000c500943c0b02c6005901e10380c85100b5007030240e07034105100f81e50703981070b04904034034000c2e03e900e060015500200e4040303041e030015003101054640d18134a9456058507031052041d03003c000d22501c02d010010034040346105000d09940701e0b4000400c4422081c3c41030b901ca05030095400030b0340407030000f040000c0200700d04100b40b2440341005d00840d8281050f0500c0f14903540d4071700c030203420b00f0141d89642d550380c841e201d54035600070114903c08003900c0e1140346519004c2c0c02d1840000c07080d103110003000200004c0d4542e40080324518140c07014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 658033669 1250 658032419 658032433
    0x615190612090c21051c08010504020d200301080c15070f020109030f03080109050a020711010513030609060203071e091e050306041110050406080a020a0309080301080307110909 78
    0x86003001502c9841400e5980015500b00031401042d40f070f08803105401c1501ca60114480b0a04d4128a0541e44c03d6860b00300e000301382c0102007020f511407107250448204236000360301d071824415070100401d03200c80c5100402c1e1071650610701810840010b14101c0f549a0240d40340c000481051013a040010040d034028003000300400800903141c514034001942c0185019014180c0381d640e40f0904040d049000da0215100f20010044002140591603104084060239400c144856441c2c814481c00c4c82c00550600401050742409580f81704250f90046821007818006a24070707080510007907200b6943c910008624810b4641002c24203428118201425650340c0c500c240f0700a80c1d10405070b40c07800d000b4186440d102000449680c1006405d02550207400310040515040040000c6d00070005015070602c00280800c00c622504814803d40c0860700b5800035944200d0108102c1c0140184c240061101c040030001052528002010b000780c01d1190b2200300840c010034007003201840084500310f9250307208113 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 658034919 1250 658033669 658033697
    0x160e100507080c0c100201090605160c03230f1903020405060403081309020c01020a0e311506050d05060603040206160f0819090509010617070e0306151906 68
    0x100103080b01000f11060341c594040440004d5951500c842131440181c4d11464661300340140c40c0300d031782c0d0807000d40400d0507151204818040e200c2c660301140a018821842d040101c89240b40012081030300320b1098980d6100c0841c21010160b030006c0d4103000c4d1200c0e0307180002d260389010b4802c4500740c03a401401c4504180c0307107039078240080d8001d00e0a001e4000c2401c40003d90f480e0130b070010300041e203400310015848010a14000349001004040c2c02d10680031044521082c102e0107056950324010200c0d5100c1d11010002d1010103070076018820306811010381d20003d00560300c1701c060074498800c5c1d4400c0c0482c1c0c41b24410001540400e48000c0e40c03148081185840701c0c0b80c00400f1200d0f03144240300550032583c05848059140d042646003600c18110003030005900d80e4010f10340b0b0064071b400c50b0415100d50518000034200c601a0401070200039195011414890150040d5003d0f090003c1c00c0340c03e02d2801407135818a103c0c40e101824043c0c418640300610650b0001c0c1010141c55036a40c4084199402c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 658036169 1250 658034919 658034933
    0x403021311030c0403060f0515040c0306082409060124120614010e012a021908031206060a0c02090c221a03011512060e160e100507 58
    0x141038824038056585410000714403020001d50310400704280c02c1d0f51184d103541001c1041e14040c00209860074607090070071803202182452000107400544000900001c8400c044d40108460340000c146442801501900b0107649602d4100945d81200200c580f44c8980b419140e44103000e0045e10041600790b8400a005c60018101b0b0100441503d0310341c40c99400744030014100c8000e500f028a8540403511000c070b440d40c002110300b0305254203182c582c5110818801d22200440c038550041d19906c29045801c0941d03480ca2180d0944040003a40314000640c1c82a54a90b0395000b41114160110340034005000761030500141c9104c0800d41e161014410469420400c02e801c00800f01d410703288092000cbc600c0c081004280f0000900d11000000d0380c281484041c000d00e50004440c40e090640800050100c00350002514242035640e0400d107000d07031251034010303000d450180c000031591034101c07040021400ca0201d200c5100a01512401e4850412809103c0c451108003410703008103400700041000070b2a8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 658037419 1250 658036169 658036189
    0xf030d1b03090504180203061528030b07030501030b010b0403081902010e01020706021c060503030d02182d1e0118080303040803071704031d0f0306010b0703030509070803040302 78
    0x1c2860031a40043e141d2000608a80242c0c552900c03003036003c181c40b011400e00f005403d4100b20b9896540304e00c907012400140d4985180001d0010480750a03042030280340a01d203c2034042e40d40042d00c00380700d01e803500000300180002d100c192050503605000090b00d0f0134400840d0140c0c1d820013800351900c001c0101508040d0200700c0710208540d82d80d1520a101d00003031000d04030b030501c511800350341c43c2c0d030b580d801102d8004015002820140f403e0820001a035000003111180b0f40400c2002d0b8554542c641c1c1080d020102c1a21950000c500050b500700c44000420790403d41803495051130f024440743c0090140c081c04070551802c0018540751240c0c7d4070340c050052050280351110065240b26260b507c194110f40094504807064400403050021303050b00410355001c0748000d0300c00b070152482e06440040c51100b100004c801c00c2a5000410080c079150054007100c1618007600b12405969640c00c0100e565203c0380d0190300103890200400c002400116104080b14620001503091608607002c005130046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 658038669 1250 658037419 658037423
    0x124060c320c150d0b2b0c0e0105060a110a02130902030d11030d0b03030d15050112020717070305090316060314040b010308210705092704030e03030d14060f030d1b 72
    0x281c6141100000d010183c0760380310b4004401880a1081b01c18a4241d0320f40c0c40c250840c80b06400c000d4014009502d9080c01e84034102c000b0f1070800d2014580c09041802c150104401a41205400201e80122060742c0c0020700c40d0762090b0111044441011f50172a25640d1000740086035800400c405030144420f13400245180da130003000c2d07034a8010380c41c01c12411030b54040710600341008204004c0056682041c1021050001d4000562400c0c078107036203404d00402c0c121001c030001900410b6920605105000352406049c0140c01c464481c40d40386203079030301c0a002e8480c03180000c0c00d00c151581031480c20402c3e140035036405100305402d80d08540d910b180b250401d0484069074240000c02d45980450074035160300070401521788076691710005051084401c00700d04001420402406403203c01c0321540c001e1607005030103107801a0800c484900003801e5100346410b0150160400070501d8110540150441c00740e101200c0324100781112200785030301e48844002900205901d204c40003440049010921420f40c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 658039919 1250 658038669 658038679
    0x212070201051509092d060702060f010902030a020937050f06070314031509010f031a061302124204140f090124060c320c150d0b 57
    0x51107880740301806c000c0d0400740794000c011488440d1148005020094101d800c07803000d42000d01c0d11600c2b0a4440c2c00610480c0302413a07001001a90a4081d98150341250200030303c1d0b8445640010002401066140307517510b100c005030202c00c1000340300610903004070b80c0003510f0184181c8814040120300e411821054081c088001241e03e0b0b045031140c0254030078000c4865004605250300c09000e03019005810040d0031b004e564a0502c08107a603040406055406580c40c1c111030741d03a00011802401e92401c0d5082d92034000f2a035100c1c0c0c0c108100700107125800d824500d10301c00410412940c10418441c881c8048401d1300050720030710f1080c01c123151b1440103000d0f1010803100c039024bd0444200c03030201c441d12003103448001071080110f0203026403503840010325810015284481c400a803901507500c68a002d00c011204131700100402c2420492005401005620340c00000d050015041c8000c0a08000d42e4001c14469500616014180e10024031401d81c8550078034400e0018240185843c403000b961003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 658041169 1250 658039919 658039933
    0xa0204030f0803070801091a041a13021206180708040c030f030f0f03062607031e05070f0308030a0203190507020c0a1a0304121101060801021207020105150909 70
    0x30404074060009810312610010f0b07581e26094200603e11081a00041c1b0381500b000f4000b8014519032008444210003168000342e111020141c14200d0701d00c03900b0858210280c20441e000038483d59001c1c109090030340c1e200d414159603800c104121041c20b401f1400d44a000180880c0d4190703c21010113903c01d104503641d0028944a45070200d03483c190315000c40000b50303203e03840655558048152400031485040c207100c85424042c1c00380010711440349010204502618814440da01040203100940d004000c10720003d03002c41c035000f1404c80110b0152418400c0440006800100300e203004100d9801642c4182503488030403440002e54400762003a8060b801d000d044082808062048a008900d40d800030003000c4074203401e0000c1c98185902c982c8958a4841205000785144000c07a80d2082e80111040e6002601c42026501402651809c041a628114002c20007010541c001d200d07070b082d541c8401c416951401022400d840045810709070103c00c042200e6200d0606091031900100c00c0000d803456 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 658042419 1250 658041169 658041173
    0x304060c0908030d02041d040507140310020c0d1e080f070c0210020d030b040903020c04020c011b0e0328060c27050a05030a02010f2304150809010516080a020403 71
    0xf0356000aa07041c4111603000400300400c456461190100440143c04031050b0710700741d16269241c1c0b04a21038031051270406040000a0780e070610105208e0410f040b42107454160a0342941d41d030388000880400030502602030643c150000503003030126080c0c0e0b595101c002e56502c00c002c00880350701401503070601003140c80500041e510a40340a036110f0080d0700526480c0c50300c4800405841d040040a40103034502801800401c5d404164030001d51010303100581d40e650214009030042610701c1d4a0303645020785052903d20113034406150002d45100305c0c00c540d624040740041c0c0001c0a80d44542c2020f01120f01003c03c002800303034100c2c441200302c505011050341d0f40e40410024040101c1c00222003005101010311440c54905c001a000c2c2c5003c0d80203040c1600190f001901680f141d585000c10700c401250420040c0520341c02c2d605040380c0140d43c0d6500c45070740b488141034550001e51890041a51040001c80390201403045500c04c1e086010703264a020080882074508040c083d284100e555020000800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 658043669 1250 658042419 658042423
    0x9051803160534091808031009060303080406050f01060c0b04020a030816150204080d080a0204030206070b0411040903020c040e0316050a120905010e101106070302031803030105060304060c0908 85
    0x3039420781d44a0b4850b2981c410703003003c81080500742c000f040036514180b20b1030941060600340344da0455220300816030702d8441c001070011940141c3c1c8070f10007050030324402008059004450a028a114601c00d10058841c9030740b00921304d13000d02800300000e4034903d100c4086500181d54942050000e405818500e0716521000800c3c6d01c100d418021403d41c2c5550b0340200b169164107200e81c888000800c60400b424111510b440700c0c020184002044890000301d01a010130360304588c002c507030040c289641c0e80c020307182c0b17410720900c03c80d01600c1146441440d46004e082902a082d04190700d5405083e60b44108410840100906581c0c68a00d00c000d02c0406034001c0507010802415000e28000d0400e0700e051b2030a0401d1100d504e100404000010070b00304060790300480404d81d9050300315101c880b841c940d01d01c12030f402000044552064443d480610118940580c015402144c00c4110402c0b00040300011958a203c01e10440381c0085003000081c01040041d8403800d044c0c85645440702d01980e480b01c010b8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 658044919 1250 658043669 658043713
    0xb101202010f0e0a090e070803192d0309060615080c1c0e0703050f0d0509010e040906090c08010515061206120604030306140406080a060509070b070804090518031605 73
    0x290b04150741b00d502820400381004141c008284050040d480c0005103c10301a11000102040061001982c0f0314410311200d40f9001e05000c0041041c4505015400d500070081d041c41d00b001d540040c039040c80443c10841c00150b0084c000005c2d00d80c60f00300d841d422074a1030658040000502120401d1004601c81d40c0140a040c000003114802407121604509089040910310f61003a01c645d0703c01d1107059003a40c0c012040d24201e5001b402d10040070072403480464050000c0010042409140a03010303004c100d843e000c44000e0703503480340c020031040d6200790300124481220442650b000c00c003445112001150010490750000024104e2049280c04001c1d0b180f40010070b840440100c0e8035078006000090341840c2c0d00c05800300445060010500d008421038a403545e500c00680740030384032800507540b440108900401817500e012050368600c42414031a802c3e810030300a1300000c604110100307450405003000c03220018038200140d80b600090751615180002c0d03440c012592800351100c0c01c00c03842d8801c0341d54 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 658046169 1250 658044919 658044929
    0x3033105120c1311031501140a05180d021e0d1203020a0f0219060506040204093905030408031807090603050105090c0f101209080d0b121b130603030c0b101202010f0e0a 74
    0x2f602e0f0308000341103601e5002004c5141c3d0054615900c0381015903280301c5c000d600101c2810031211412400b034042982503070540c602034005c0502c0310b00650702c0c4c0d92540c010000b40403a80d89940b0302038503100c0c080743c0381c1150382100d18503030100950a03c0440c01551011f5027011000b0030040c50190759041ca50305640452034100803141d5820072040c5084421004040195031161940f0601d8074102d401030190700000d84080c1050a000c400103030811801c2941120842804003100c10301543c65401c0b9010302030702c1c04100e4075542000042002a480022240c1c29680010a10444a1006424010307040604840c0340e0402088100309914a071700f078071800250314081c0134010f5490180700c0f1078200b84c40031128600d019090140c003260745040c0214920044d000d50592014402c4803420001381c028141c017100070319440c40d28400008054018010310101c51080d0582c45c41c0359120092403d881c161407040b1520b0310064a07020f80198840e202509100c00c041c1441030500c00c0701800319200314000d4200c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 658047419 1250 658046169 658046177
    0xc090112020a0909200301180c170118080c070f0315050c030906190605120318060c0705040f1103041b0503033105120c1311031501140a 60
    0x1103a029800e081c20101e0280072842000c0c02000d503965108050340901c0400c0c15000b1001c1980003a0545d400c0d040800041c0c3c2c00b84100d0584011410310f181050114841d80141144409c2035004040d018010129005100600c24054203083d84800030300ba0311540b954641401030200120300c180c0c001c40701070040c60165070403100b401c00940395442241c0000c1c000104a003030030700130404000030001d0840c1d0721008500c0c42a500e00b081c12451005004540c1050344c0c0002610941b2002220010150040c82c1000712070041490300201400f009201707951031480c95803c080c00034005400c0c25040050300d0030b0520700000d4650f20b40d5880d41410740041c0c0301250400307490420401904038160400c00909812800341d890440d1803100000e120f408043c00c1c0303214000d4203052003007640d600d590743d070700a101c041c00301e10390707080001c00c46903c80c101c14a902d4469040c61500600407400c61050090b24a08040910318540f03607141542002c0c032140f0750050400482e80160a07405d010807001c4d014901d05922 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 658048669 1250 658047419 658047449
    0x10f02210d290a054207060e0c0f0d171b1f05010609030f050a17250f060e07050a063603030f0507121707090e180c0901 53
    0x2c01c0102118042d400540f18400d95100c0303038207460542041d240d02c503d10742019001c1c6115000c10a00d0410905025850303c1408075005041c000c198020104113607802054030300340030f031540c2044034005c0c5940d00c81d90080b860a041d80f000411007100d24503403c2c440443c90f410800d07040e905101c2c03141d401100945075004110011401c080f581080d01c04040b0300300051242d50305200f030003060001030b03210140015078000c81003018444140440e50040b40c2200c1d011524802070282d51540364480324a0355550000c48070200d0003102100458524540d02c1a112681042c580e25640c01518030741a00c144640600d09000038240e0311940e025009110548525003404400405002410207a15030302c605c00841194200d03000025140d0101503d9140c106404508040b0301c00b01c0700303401508070080c680b81c0d200e221b00841c5a002100ba0b00005a0f28202d050956a0f42400319001003507403244401c2111400b0100b0030845640300358805011200c3e040359002d0b95000001541c08200b071b400903945d200704c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 658049919 1250 658048669 658048751
    0x1030f0f0f061a09070e030607030b0406030812190501080604230a14010f111b030d02070503090406061e271d0c0a050304020405040204020c010515010f02210d 70
    0x220350070307038081400d081c0091b550144e18042070303c0f004010120b40405503104100d4200f517031071b644044040c6401001ca03d40b512400300400c06208000d84055103046040c3c0d00740c0c8980a030a010300c43c169803030640600b043c0c0d2119a900d4400e20b402c001c20001021140b10018030500e41082954400385c02804408405030851a22600311841a01400c01d101c1c24596028071440000e001c035a010414103844102d006100441c450a5000e00800e81c24060300018898050090010240c00d00141c01c0b103041044c1e580d500d46c2a16081d0300803040102c0c408440c805447c80b913006410610b412104a480740f4030b1000602c10020383d5403010f03004104c610702c8141c0400240814145004d520059509d0402c2c81c0440040c0060045d01000380001d220303a4841001901310b440d5a010b031007130600520300034403e034186130010390110701f4840b41040c0014045e0b84255503191001851400d0300d500702d2219003504400a0341d9460701e1b8801d1070b0b0500352545071500842040718045450021100c141e01c0e00800700358403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 658051169 1250 658049919 658049929
    0x12081b03210112020a05061b1006090c08011215020c01020a020321063304080a02150310050d11102a2a0305070b0901080603010501030f0f0f061a 64
    0x1a00b03e410324211081e00c060060b240c030b00042066800c101c6039651210442e0b142c02402c01030185121401c0c0c0921210500c103001681c100f4002e4a9400409110103107408504641c0c03010b091089205002140e440e0001141c4800c0c40c1805806945802511300600031007440d0031780c0e00001c403140059200098040288034030031540f200180c502a10380201e030500c100040e09601704034060041a0601040007a0088040c40024881e503580290349a02c49650f080c10513100c003a407480c142d005005403914000541c1501007101d100d084c1c00541c52410320b0034002800403d100c4540121036404003034001078140d586e0820362201348601a500d1030139451000300074a40391000b401d002800c20402c180e80710002051440e441728a284140e40c0313404030044441c951044000194400b030180d02441002155060041c0b0040003610000c3c0c80382000c03031b101c035418142240d40c02d2002030310303406614649074000b486517410449900d000e45407105120384a40c03564412241c03c00649620750b14001d085411030300306 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 658052419 1250 658051169 658051171
    0x23030f0408150705221203050705010c0801051e01020c0603040b011805070801030201030e0a0212031e04080a020d08040f08010b1201050702060613150b0306150412081b0321 76
    0x2d5001c0e404203070f04007a04080c0290140b900102410440661700751081d4401160b95002030401c4034401001c0045810050a281e01c0400d091303516501780f200403086140108000d0f41200c20150051070300c4075904048901084004c005036045006032030710000c01da546d41d00998019801541990380c00d51520210b001d441e0050485107200f10708080c00c0140654012030f0700b604407502804c0c04540d040741102c0d114105040340030000e61014115030101c401400c004041c01050b005d8011200d0005040358110145016603c1804c03503943c00b400301c1e68010f052203002c0680030380c410040e4a040a48940074040c1200c0c8a4101502507076540d00d81850b60700d400c0840301501103a14008011600303060100945500c80146140d0146200b450300403a107805903842580328188010b40c400d0100e0f02c801c80b00009920036a4194800c00401203468074011501701290115a4000444a020113417583c44100301c3e008036541c1401000c04540410241c0c60600040044c010410302c03080095400940b1340150b004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 658053669 1250 658052419 658052443
    0x110f0601031505060a030f061104031e020f190b0a0306051c0501060e090c01030b0f0418020909010509070e060102160815010f0807060302090301022107080c0a090323030f0408 77
    0x2d45c4020008500c8040c001e8503442d421a074007198002188000c0d441c1441a544003c3c680d5015000701010b008144100382c08030f6108481c0c0b550f54002500801203444042c0d801140c40b4a24a01c0412489007000000c004e009403500780400ca440c5c0d21070001d0384050b00d00001d10b54904417800d282c4104172080c80f0b0500038101451091401c4d04000c081166078903d8400303c070b8149135489040511540d503500a40050050041c028009441c00091044820020281c00c90240c4404404102a000107025540c414001e2000828580d0f2404241022072200901014150b0160070389088a641150130a031000d415084000c1800f4102c0c00815610303e50142d00280494107519010b111240f004105641202c0301403401503194240c50b0006030087c4100c405038011006050002c038203203206200c003103108000940320201103a0300d1004010044c400c0301112030000718404c0083c0000f4198400c503809500c40c58606001c814010380c1000d09d150710401a044d858503010604008500003000040c1c030881c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 658054919 1250 658053669 658053679
    0x12030216030c06030c1823030c0603041b0503100e0d170a020a030e0a120210050f0103030503190c051b0106030f081b010c050d0b01080708010501110f060103150506 72
    0x1865901d4201d05071000c1c0c024082007644950402144502c0740c0c1c0d070a580503410a04503541b403941d800040b49000b040400c8403110000400d40c4419074640440c84c64241c5801420705465171741c036551000800c80c150b0b0722800c0720a40403440840c040c1c4040000610700e19408600150300c4c44401111417601018030122020403c02042c60403d07140310703101c1d00303401010402e00940c41e8060a036050f0050018205191114815402480e05100c42d80c0480c00035802e6a40a540c04038071412050410303608111040c0203004400001000024410b000030b40e482400110120340000f6071440c84001d540048103420001480840d100c40d58071031001048181c091a00020000d03a0325642d01d80101015815010b0300c3c0349400316001850501c1f01d900c1b4105501000c0080107098194007024103503410080040d60030303910b4844c20011035401032180900a0545450b00c110603841e06004640d1040e00b0342030703950140100301c0c00580720745d400c1080c54082c61050f60140d441c81070045443c0c00319000180114418 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 658056169 1250 658054919 658054963
    0x20c0a1e0314010902130506091308070803151903020102160807090e0312010905040303050f06010512041e080301171c0f020c0d060f0c0302090117060d0804120302 72
    0x2618100005022a07070311a00d502c1000080c094050300400700d900001c0d4019900038450300703040c01c05602070b5101d00b0040f602d0a43d603449846100c0c0b007402240c20024440340080015501140100d0702841d484003c0340d11041d401014640801c5082d060303828030728100020220103004640e0117111030303103000705d004549500312454215220f036100401d1141083c1250f58030310000000b5024412201410181c4848850b696501d00030b030401008100ca0550000c0d140c540420000701c006003400b4002c00c0160b603007606042c40c5901d41c40011202a10454401c50340c0f080680c00c10030040c282c0d140c880d018907103c545a616101858030380c450001840c0c20340d500f000b016860003031101a182e0034036601501c1c004084903100130003a132400c02c101d0902035000c0c1c0c031442c0a004001381d90308440c0e00b0791854041484071618014007a0185e00800c41c0d03981c041200010014000503401c101c40c0d44c80140101188600d600359207840460341d001780c1002d01c0140c0e07050701074000d041c1c0401c0b103085156038401c80b0b0105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 658057419 1250 658056169 658056209
    0x6090a0905180d0f032007050d03050c12040b070315351c0c0606230f0307061d040509030c06011a0a05220803040f09023f07020c0a 58
    0x424101c40070300070905d540d8403412078168031480c0048050381182c6d411940c0d0380e000c50400300c0e5104080b012240020f428000013904901510b8241d48403050701c101d0580030b80c0c585607a5240030381d0005100300b0030903680301100c00c00912244030a00c000c000e1950099001610a04070040b441106010302c00300c01000558484207a000242506404ae94902c1c4061900f485071021103200300000405010302c5e0070400c01060395060b050343c50360703003c0d0301035029188944d60b8424001842c0c0c0c40720401d03a00d40c108880403c00d1600842303000091035054000300a68804140025040f1941030799a440164404140e84a25080820403107001d840c03118246204038510581340c108600c2140200c4040180200b194150710400c0c43c0f01882c0e840c0c0c02e410383c811041c3c54503d11035881c2c01c9481074010f6510315020000d0101424801c40e04205044010300d060f9000481640035501c01580c00c98085000502132030902040e0312154a006100703540c00b42c00d02d9900c1108104400b030040c1c1283c14061954413024207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 658058669 1250 658057419 658057427
    0x9130f180b1506190201060f060f0206060609030a0501020f030f010518220b07020606091e060d1407090b031c0e010e010905031005040c0b0c0709090206090a0905180d 73
    0x1501400400e003011000b2101d5000c59450300031600031301e040092084600c144140c040d0020b006a80b040029100d91554031042201d241c000c1c2c08406c000740e080400860301504012009010703902d009001c07500552019035840c0c2c01c903070180304480301d0207002006212400180081300c0740141422200040584600413003540305410145c060b841440044010703c544444400000d5181900815010f4140c074100c400a91a10f10441c0d015110310310b024006500103690202c020001c048402140325030355a19000e000c0078071050b02041d07071075051134a120000420100310303000240c00c3c214004603080c16054141854400d1007071a0340006203403058482443c40e40144d00c042c0505091800c0c0014101075001681c50001039040650580a0036690103080520b580201c2d008500c20101041110782e6003a00300b011b4003441c0f4a042c03030b903084079004005139080ba400803101140010702c4035290121110000d45424100d1b400f040302603440d00100440410001c0181d401140741d900548104003400314002c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 658059919 1250 658058669 658058671
    0x309062205030c0102072d0305010c08060603161b06020412050d0f120915020301080f1510060f03020f0703030f0b030105040309090c02280209072303060609130f180b 73
    0x8084247e41041c1407841012402200301d4918408106240454807400c0030b901038401c3e000c1d07090206070041c001c80c0d25400c1c4041101c0c894001c0a81650b030070404004201c45001c40c81d280465016100600c100101d01c203440240000d210f1480b070340d40c41c0c1280b40b13402810705030000c010409200210300590419034101060800c1c10520400c0007134111250320748100310006240e84412180c5c13020001140f5a640003480d00c00d140010022190300c0c401030104540c560a02b01c98825080520f000208000ca02820481000300c81e0760402500780a03200702d2034030032608114802d40019450f9154910303900e00a21800e00040010781c001d10641c42c0070f8a01415000c0288907451603250f41d036540045a52091101c4149035030040c0c2541405448c000640b813a034000181d09911442d2008040b84619028545a912240c00241c814403180003038503104042e40c00062125800000c20807807040130b80e1301c1526001c42401072610002c5c00e2170448441c081201d441c010b000100e00b046400240100c0c0c4043c0d841 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 658061169 1250 658059919 658059929
    0x7260610050d06020714010b01110a080f0304030207120c050907022d0703020a2918040c090305160e0703020c0c040e031c060305060a0506210309062205030c010207 72
    0x41d0b07800c242803600b10300034481c02101414004014045890406040d0040c99208a00760703078124102c52004917043d1949105140103004810400000342c2101654001c1c65019000c1d00560700810780d51400780712070a007540f00032601400381e0b110610080c0f074064440d581006082c070041204210030704c044c00c40c0a1603482188031661154050003050721040001d40042d50b4060107040d40e00d6610381d02070303c03519582c0c0000703c00351031070a00b100d884207028002d551151200440b580503001c0c040c0144401071500344410020000c42007000300224004001c900e44000341d032400460043c0c40c0901c0e060040c1400ba200310101f600400101d158078000140f100082d101c12100068600c1030305589615500c1010401c1e000c403903c006681079a0100f9601a20850340901c0a4502943d5001402c6040b65011214154450b107500754003039480100d1500d40c200c0c2c00d291421032303103810020000146643c01c4191800d200d09050414613455148402c0b4000003014180d000308422807400002035141c020034020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 658062419 1250 658061169 658061179
    0x9020d0f0203072f0f0703050c060313060506031009111f0203041a04090e033109020903010b04020310050301060e09060106080910020703080601200303010b07050f0726061005 77
    0x86442644442502e1503a60f054001211700c0c1a40c00304145840b207002d440705403407a000e242d44a0039103040c10b0040700d01c24010889079103454810395030b81100820b0003a15140c2c06202c1d849c2940300070b600510500170818000c03404d43ca0310b80300740c60800008100b002080031103020a60038035400c0030740020984045d900c901c194410960322100c4038024030300450b401010360501340b07a40701048100100c0180f5203140300070b120360700c015080807090b240b80030b4a0384c1c812030401c0d03002420008001e45070301402c03e10000800120b04405000c0000341a0703003050b100d1822101d40c06004116038902445500f00600508109100a10b40314040ca504d070710b014131511052100d402c0c0000c007420310a00841d920300440c64170131901d404940c18020013490044401c0c5c1d0100d403510040340d01c0e106400041802e58414003005500d907038209140c1c0b1074950003043c1c0855041c07181c40580c12280d101072101201420b10074803000341244508081c980c03d40301c01c015080507900010140401007881c2481c0e04161401038035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 658063669 1250 658062419 658062467
    0x190915050604050607082a0f0f030a050a021614030c0108130b131a01030c33020114090c0f060a09030201031805161703040b120403051309020d0f020307 67
    0x4000035184603441c3c10307414510000e0700700400001f90034403610184004400322840c01410740c2d07000381d80f18003a500c032040c1d40d8810321a41c55424441c0000f424003038818815a10019031121400c02d0409407a0000b412078018031501102d1820100958a00a1800d107004c070b1090234400ea03817a030100a001c4024080c410303644000b0b070a000e8040b01082c00c0f140c0c48071601038024107002c01a42d03201c8082c08211503440e028240021405200040c0714110b90780403086036242000001d0040400349124015025552a81c1c10b080b202148400c10f2849181510040e00614a0800800a110346041e24441c4145e00600543da4100d51110010f800d4a5081c00e002445090b0382d42d4000320141401001460b61040c0c55400d140b507800e61201d18101c2d510064035929814200c0311094490041d805031070515482845403400e8442d101842c560440d01908046192808580015289462a40101c101650000b401c00890002c070300c200200043d000c80c0031415070400100040000e078000111800c42d1141e22 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 658064919 1250 658063669 658063673
    0x150509040807050705120f01150302093103030902030f12030c0a090b0a02160e191d0102071b050607080703120f050108070f0f0b121005190915050604050607 69
    0x8410081c0a0080250070140b07444000306d50b540041c240e40401c80d508107030f00d11000f0b10b44034604c0c0060384d07802021241c403a51100d200c0c0e556043e2500c40c12805205290b03129000d9550200039000e528001e40d03000c00c3c040d406d401418507050015200400c0ea90020300c000190402c85010349401402d01038909a586188200c01c4404842070b40000c000c21100040303094182c0d40016045408100d500001248540d46e20005000104129084900385400710300c03103580081d20fa80710b401c420000100d1701e50070f42c05070729180f82245c0242c10308403a444a555004409807581c18294001000101c490901d00242540c50b0812406941001020721a403c0055160a850364200090003501c16170200034642c1c0d20000990348280790b210740801e000a42c0c03400f03c0c1e100083c2a10000703641c9070461403460601058400d40c510f903c0240003000302078039208082030325030301c01307100040b52448030402d81481030502e01600c0403114007540ea000000c0d07003800c0400103511004c05407030494008035070181c1c0f07909140c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 658066169 1250 658064919 658064923
    0xe2416060e031204060b0301050103031209050a0c06050406080f01080d030b240307231b0a05030c030319140402040b010909020d051b0717031305010e1015050904080705 74
    0x15600345140800301c3c009907164007104603507106a0241c030040c09038075011801c0c0340c01c0342c80030701010300090410922401c8202e841d0f00010078140c8070344100c9074144242d44840038014034a801900c001040024100b102640c890010742d0852031400654009500d0600450307541c0324040580000c0c584c03500070851640c0c2d039812031000207030700e00407402c28504070208106100e58070880f40e0390041421f0040d101c1d202d07150b0001103004004000d00142ca0841e550300510560704200755445981d2040701081c0700010b00501c09051281004001141c9030305001030350f14001c0b035440040c2c1154900d00b49113012907040f110265908650195000980c03182c03000300480301c440994001c061030900008009840303d00b9039211130f104003a1f04c00c02151b00b620350511100d251140c92800b5100424201724041c45103ea0001560017002041c0c1244803040140d8aa9095a0021500148940044900c508107061038001c00e0080e681104400e40110700f0000010700325400640003805020010a12100300403007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 658067419 1250 658066169 658066181
    0x12030f090e07020109020112230a0e0a050102090f060c0a1b0b070b061e030d0e0105090405040332041404140f0709140a120203100c0e241606 62
    0x140e07034007403007103180601c4007a01030440503008900040b01d4400f0b08610034051302c221310441c1000881c58111500d48101100e0203500940447d4203940c0e2030544101889041024440310f5104800243e190034980c810800b02c0c4000b0520365018807810805415a0440410240a42e681c40703441d6110102d00881101c10a44094000b0302c1400c03400a0004103108582d00d895110300c20840f0a00c25404e9440400050314441e4020540c00d075000d180702c204c001d40100521001e0b2041854a1800c10b492a80010261107081d1001e03004588100600040030b08000083c0c140801201804c621814808a07601c1c02d902c918455102c080c801d513000d25540b95166080310050020214101c0364509068034010203e40c01a10b040000c5004041e00050304c14100313440759900385c0000d0802501a25001080520000c1d0385000c9038107019040141142c0f200c280708000c41213007103544242d503240161040c404558002846030a44924000d030b21080341c0c041d803084810703091221503010f500e004a440c085010f061 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 658068669 1250 658067419 658067429
    0x5060f0c011e0f0e0a0206091c06020403240b0a09200c1c0309020a05040507030902120d0e01030203061c05071d07090506070203070303110c210d080112030f09 70
    0x51082c030060079a42190490360300c0d89007280d03041140304180c1c101c60341d840c003c1200c0250040c4050060700714a01c1c2a015040694034540d8000d011181c0c1546c8180880c0c1c041e4208980d5980717202501c10740098a028280d420300400c200400031f1f4070390240040c9280400348101540b440d110036000c03103102103c0c402400e4480c0c0105903661208034800301503031100240f101215000c2d071401590007140e80701e8098050313410340180c9011055070a00c0140405014001c0190044c1070300d8041640c0147c8078103d1441003001007034050b0143d240c200c540242140e140c1440c15040500510612082c0d60f11202d00790303005101c0301083e4465800c507292050070012654000039030315080308803101042c40d940401e00e200d5200b550310180c445440e1400c004803802640e10107501503010040510010340545544149000707800103c4180c5d9080f00000352620341110f940c845035007a070f0722503160f140208000300207070515203040481e42981806080640f190380b142c0c015041104885030504038038080c00501c3d01501c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 658069919 1250 658068669 658068701
    0x30c03030c0312130c03120302090d2a03050312071707030b030c06030106080a0906020d090302030414030a0506160c0605090619060f09090501020f1b01060b0405060f0c01 75
    0x41450307601c0d0340e240c0c3c21115000503c0c1e6005400950f9a18080c0104440a5842801800d501e4115102c00d01101010800c45051540c00c005030381099841e96603138811144120140d00c07000e000300e41e50702a01540c1911907001c20003004402e000044c0701005644440c03a41b6554a289542c030300300222055030f410701c040c16080f4543c10512030419416009440c0c0c49200354100c5940c0c0c0c00341d805000c5203120174824400000e2040303000ca0301d02c19654004800081c013411000d82480444940d20b01102c405550880141c1c0c0000380802411003030741c10502e000351044003c1c061211483c1ca826031105802025030042214000604001901440c0460101c03a0804c8040080b45000802c403070741c500c0309680090820301d9155148000c44030070300616080d00c4142120145d65032502c011503000c1d000310784045505540034400f2041e100d281c040903105140205403016000c135a000034440c00c4402d0f54201d550301850400080c0030907100d0340d0031104405042078400e82d941400c1c03912940100144517100c4400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 658071169 1250 658069919 658069927
    0x71d0607020a08070e07080403090e0618090706030b030115181b0c0b06030d020d0c030201020f03160f020f0601060806040f1103060a06030504020f0907020304080102160606060813020906030c0303 86
    0x114400229802901d0301c4060401c5c01c2e0311a0720302564101c4049070b000340064580f61003449505088110150017441c00303001c03a40c09054041c80c038a03801d90110b408000c00c0d40008410003000d94107008241000a094008010031050310121172000070b202d00444554a070070001c80407000d0203550201c001c5d40480300c0d4100304d218809d400142450303807840081e10b81581c080042103071454046404001100950000c10428942d408260344005907600260250355090003125461001040190b00c00c410601c445000c034004000058200c200784040c56086505c80c00044107190b000062040c1503404a003003803a541c0c0d0781c00000501400c106a48000c2e100c3c00d100070400d0281050b4003035030195100701c0c1da8000c29621440101d0448204860296100315005940d00440c20405260340c0c1101c5c02d03206407868180c542c0c01369420799001c48980100c07600602c484a042c0070740c0f41300e10409042545000c080e80e0403d801c0e22401c01c0080c200c042d1041c52008003003207840e60704100c1d101020801070207890316 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 658072419 1250 658071169 658071179
    0x30115020a1b0e151e030c0402043309060c1e050d080a0c0e1c0b010b0403170c030d1a04180506010e070c1203060b03010b07030306050306071d0607020a 67
    0x404403280c81540b02c0e000803c8040740084100f1400007010000203405915206660808142966440280a074040c01034801d00110381d00e8500041c030240c030001c4510410307160340500100140c04007211044403041c2001560b940c00b588030f9101c8085500c2d500c1d100c0311001d241c0c01d1142c2a007815644241000700c0150701c0a0401c800450f010300850a90f0701c919a03556074500c00d0b4016035500d00e8511b800264038003242d0101d0b16100440c600a010201360b90083d81540d990740c0302c90f00c20300ba08100e01303a65003c6020003c102e401d14515948a012158450a166944130001d69038040e280f09400510340310b0030580588100381030710b9504104c00520074000c030503a04200c02c1b01c17046110b0007911240100000840d00c00289424140201c525a6034003d1007901c0f51208140601c091030a50308041d21941c0002c1c2006c0c480015502030f00380207030565a00c0a40c0e150150496010380c0c4241c0c007d41000041002d5a600a0304501100d0210500d0884910080740017840701e200d06600254004103046012031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 658073669 1250 658072419 658072463
    0x1c050904050114040b1c03032003040c080105090a21031104060c26091c02090a020309060f0c030606130f0f170c0f2704050c03150c030115020a 63
    0x1540d0f8003910308000c00d542c1c00c018080d907580c50819200000001041c1d03840000d119501c0f4500700d204a65880c4004103111020745039642c400c6c3c40581c1c00000e418028003050a00b803189907080704280004103180802c69441e441840300508024002410300508494103e000e6003046000301c000303503402070fa00d17911000d018001a0ba0b040b01515176080141007420701e004800203000c00310f140303141200d00700300c0e0300000c101154165003030452000710021211401611003442c1079000700800c91015840340f52003142d143c60b04100a000101c1848014140900c0780c41e498100c0381c01c002c0a480d0701c0d80d28482c820a40c00d0014080e03020b0725034440001d00c00142d0000c442c3c400c81c10340344810a11603010440d2602540c0d80c1c4007072098598044075031a0001d0503860300214044585071001c1903004108d101064100380250f0464003034649421100031440c552805021a0007a01d02c503000035111400c00f031884680c02d01050082003c900c520b10410383c0e80030300800c00100d40310360210100d1005050710045117 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 658074919 1250 658073669 658073699
    0x90b040501062607050f0303071a0114060712080a0204170304062003041211030610090501060504062a080c0d0314090307060c03020918010e06040b031c0509040501 72
    0x503c0640021200a903030f000c00129903100054a82e00030000103040c80201321502d0300100050707074103100801048000070031815540d4103020a40c26080380644c034014602c00f0044070f22528030b2203000b0801017500042d02c02c290105c0d07003400c18600228141c0d038807004e8034020700c15034100300740e40f07038484940c20082c0500000410540d8070f5662250810044800000d0040c402130080d180150003d0006110413000d090381c41082c00e0003000240d00350207085002c603041101c180c03040c0e031b0b03046920041840740c002c40c4c5c000e4900411481c60010729107490f280000342201e5020400f01c030f24610900c455280e01c040522480582c0b40c01a4010740d6030310b041c8000039640c1c1c810160700c0d8046400c1c40c03409403001488001652081c83d07040095480c040c00790759604000c28450f1091000d15909004401c4107032200301503c58100143c140414031941042d0420f92422001001544105e040002d41242500c0108203400700d00140c100b040c0603620f030350300d05072224050710120310781080c9094000220f49001c501c2c08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 658076169 1250 658074919 658074929
    0xb04150b041e030209010608040501020f120412080105010c0b0406060305070b250209010e04050f030301060302070b1b0915090d0c050f0d03080c0c0a1703060306010603021c02030901090b04050106 86
    0x42c503058142100200c00a030003503c0040c1d8031100300d0b401040f00c43e0040c051036610a01c01d0b0f00040c50302c0624443c8080035000b500da0003056048040401041144070015003003220442c0c28507070042d61400c0e00080c020b450511005180d8110180450108600d47e0002c402035580322055450b01038584408500d0768001c9056142121410f56100c2c800840002024054540190400190360f08095910500074000381040380c00c0c2c4221950400045000c0c006180641800e58001d41d03a1405e6040145001502609201c03c0300303528407103101c0c00e10485040ba966500c040d107011a420200341048660f5014615a854024460003a10310400c215000006c003034404c01c03a100b0b5400c2030002c0a00803030301442400100425000c002044074484040081c0c10004940002c450701d00000b40c0d1110002403800140c140f80755004401c3c4400c1d0301d02404141c1c05802246021030401e070303090b0700703038042140704106059001e58004042004c000080d0401e081c0c49030410035006490901e850283d0080c9010b11038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 658077419 1250 658076169 658076189
    0xc2301080112020307090221070801081203060904030309021516060e01020703080a0b0301060f08211e132c16081807030f0303020901080c0a0507060b04150b04 70
    0xc070b0626000500035032000c3d0060001c00b0090306200307000001354094078030a0512141c80300202144e4456940c03080c800d01c1c9680d40c03942103515103038071240781c0920f00c08002d12420b003d2042101d60f031520240c0c0c42e441342d0140342c00b180c034881c1c9001041d0440654150100c0f1032000042c4007503080ca418107800540c030702c80c2d4810825010400c094070700304c2c000c004004001600e0344010800106680d008660a1000140001400c981d18071400040001c69800400c40b60403170030300040c854101007420b0101c01e601e00002490240500100c6200c4540304004041710030000c41c41d244440b550301c0300d00340035144112a840001c26105403241001c050342e030901d20b070107440900091014011001c410076800c0c0c45d448a421030340f110040440d8815202c0d04650103480360100000c0883c3c10343c01d51054850180e00c0069468455500041102c2d5001f0110074004404200406000e540070742119500b5800c400c0004080700400c0002c0d000d495404c0300301d251b40301c52800c0482d03c10100700c0104102c500d0f9400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 658078669 1250 658077419 658077421
    0xf070c0c081b0a0b090927061504110a0507031e030e07063207050613110105132706060201060501020105181c0521040308060306220c230108 62
    0x82004400f80c0075000341c0380c20520500c115102030400d400e62580010064400030904551444880c1005503410b2401155520880c140f00984c003008a25101005068a0038012403030304103100001407040d0001582007100009035002810311441c1440402a06c17440a4000781501603002000f900c6c01d403c929829006605000030420b02440e210140d41c000c880c402d5400c0c9038a41183c4103000a890000d42c0400400c22490700021010f008407845a43c2012035603440c0380c41e03414806019141c19100034184242000340e1a106c0d280000e41c0412282125556900b10240c00a1840c4010118810700c5039241400c00c0898459010f410000c16960280d0081100b1303561294954021003480010000341d81040c1e0818480c001c81c0d241420b24012541009407505055000094646100f9034440d1450b9030705500340010540d001640da03801c1070b400c4004007518200700e029003440305152040034112031459000c0d0410005003508100c01003111003034402c020726091407600140c43d2213881d00c60000300014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 658079919 1250 658078669 658078723
    0x210b01061e090510050c0312070c0b010801200d090215031f180e070315050f01060507051506030703080304050105060a170a1e0203010f0f0e070305060f070c0c08 71
    0x716003c50300001c09002c018203007040103a80c241d01007104100280420812908084680c10405004d001156078030403403004d00741420f16401c8010b801298660341022020392a480301803045050701690065110350340c0d100700c02c2450041c40103941c020741040510784224034540c1011301031407140b00990382e40c5682e0007031050100301103180e0b030040c110304203800c100d480c021002d55031058075040a81000c46406549030344030110501c50316100c20303648503180e03410030500c1005160380d80e00400c00d0b810524104891903a81d03036201d00400240d9440181035200148a65808001034001950002d0740246e07070b41070505000d4003030031003101ca960003406015030010700100c04502c850500c00002c00138000103009541c0b40d0704604040290410b0164500d90a880540e9003841403001c10400072900050500c06011007100b998401030070740c92213401c54a01000860408520260f003c040b48070700c0031655690140503211100c005101414a0303002e00c070080380000001642e4022aa07a0480e0700c24000303024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 658081169 1250 658079919 658079927
    0x3043b07030f0605041e021b070b0702180105010e0d1119051203120106080a090215070302060a02030606310314102c0f011506030e0106050307210b01061e 68
    0x103412420308046c00305000300721442495001d020b04003c0e0a00c544070721032800740c0072031800c0060b4110b00300c07070980015001d0443c82d0001c5907c010001c1d03040136585640c50940040e004209862001d4011104100024100031400f0900300c0e2501d0300606242840200e96100c081500203405003501032654a6100010301d10000309480581010411507840c50382060b0044404c40c00c0684072003407190311070f080c90b001a0343c0c008162181a1200440c90740303a00541c1002403a2000c042c00361043c46104005004440d2210400c0728005400700c10401c49480359803c000800c602c0d001c3c8100c01c902440100481080700c035581d4071000c82501d40803641b00901c4001d0032800c440d004d400300030521051304100c1602c09100c03882003100703031a40b4003951007013400d082c400307400e59800c0e1880b0031820a00f180d05125254040c1b26002d00f00305031000030483c550815021030f40d00c3e10300c2e010301d01d0b29021496507a84408100d59034505425031005c1fa04940e965104805040007031200e050f4584010110590000070740f00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 658082419 1250 658081169 658081181
    0xd150801061421240703050123061b0309011e0504090c050c011d010c02160504270609030813050a0803180712060e03043b07030f060504 60
    0xe8110b0b80507005281100300401050030003402d803c000007070854088010b60500c4080401c98109092100e641000d072940305448000800080601d450000148803818641e0001017005052444000e002d040d5000001c6490254a6116000c801c080e00100170340782c8040050300b183c440c2078988c2d904615828000e99415501d0000c83c00000e1010f100c1045100000e801070340200000382002440c0c04a034022407401d4520796007220515080031260490200401d114810814ac0c5c544007401c0703030300c08210f004002d0b021540b1400344219100c0400141401054101c8501d00341e8401e40c582c0201400d141c480054030090b1000c1d004243c2000010305e80320f031440c802c580380d20b80c80300c068100021191390302d0540740c0000e00ba130001c0324501c814500000500f040240b001c0d00502000301c07201c1d502881d015081e00c64224610a80360030070302c8101700502948031608540e0450b10400313405140d096040010355144030b40c0300c9498990510034004036640651103070f01e40000c500414041e550701c4005020a40e55 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 658083669 1250 658082419 658082429
    0x12050706020f06041509020402090603090105150a18050901020f07050705010e0103050103050a021003020c030c01150f0305030415020a06050411120c010516110306040302240c0723030d15080106 85
    0x401a10034400c0003080e6030001c819241f0003040141400380d4080444c0a070b801c200c2d8100007581d900c005010380c18034001c0c0c1210201d20100d88580d6a5400c02380c0c01d00313480d55060304555000d81c54001240c560030007074043d141413503010684182c40e030380e03070703007401c5a50344400c0c03242c82e02040030040341820300c1d4460300405051300d40202c0207284502c60fa80c207100010032210450010180d090100c1c001030b81040c001000e00211200c0082404000081d0200001040d50b00c4001040100d105c20000a40d020040e01c084600f07502c12030300d0b85010000280d0820484034001042c1502e00801c2004012030340340701c00d1200006442d00070034402503007003855452000c0b144141c0030910501034a1101070401406120603486000b9150105000c00007184c50b104090320202c0141e084010078001e400c0c115901004101506d42c17000c6901c3c00c0002c0c0c21607151150180c003801d800ba1120040400d008203c03030031140721107680201e0760b80d07100e1000444020805940300d0800c0d87e9845900051000c0c05000d40c2c000c1d12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 658084919 1250 658083669 658083683
    0x605010e0606161704080c040e013b01060e15031b15090607050c03060f060d0b091c0f1b11040e0f100213121101051312050706020f0604 60
    0x3c1905540410010090700301142c2614442242e92081c10b10b60740640005d0110300000c21170a4980001c01040e5400001e010303c160f850280903800d07100101d0021598403003038101100c1140f2010110b0b900707108400d5241040d83d0b08000d00082c41c2a9010103140c0f0403500c04424a000741d1862040580325511070310746013a4981901480c4240e440e104081940184446060f03510300301c41000030408941140310305903145e41096011603041d00303040c8072503a031020700414940d10b07a240a200084810390020005481c00d8260000a004040d0810803512590068500d02c551002c00000c01800540b2000d015400540c0d24850004034282403030611000d035900419040261141605110083c60725a03008500c1d840341600304258803d05010400b40e81c0b100c0400580d445000c900c9500511714140e02460556044002c514003194519004100e0a502460600c0da40c04410782d941c100c100d4543c00801501c10004540c10801c10002482c10803079505030240c4802c1816504260b442d420200c0d00a0420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 658086169 1250 658084919 658084927
    0x213150c0f0b42010c060612020109050a0e010b0d2306030706210e030906190305150105071709181f0501050403060b1311070218131b05090c04030605010e0606 70
    0x1503c0c0050050091250605d81000909035a8444000390b40180d0720100201c0100c0862401795680203d514010342001c3d24040c2082c0c1c64000e108042c81014420346412000208030b0b40720091058100f680c2030314088018181c810322a0741c8048100c102038840030f12038410352500280ca24090744003103403200004510607540b81094a0b040b0f000d410b0899454006000130043c0103402e030307200c00203031080b00100d680502c02d803804d03801d001c0e04607817010700f05114041100180c010540c1e4400c044601c11039008015070a07044800c6c010b040725025120240e40c1c031500c4024002024140040d10910910032400e44203940f01e408ac0341c00000782c0c1c0700d0080c1030029808100034000700b45103030080c0491300c0c0c000d0304001081e0500c0521404544882700c505030b41d48400118101545006841da4809400b441000c8003e4103246009955821403042c0003400101082020400c8403102000c900040c5009061100c0ea460045080c9480358040d000484d24245444004a2045031208801d4480d050190040f458 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 658087419 1250 658086169 658086271
    0x906010809150402030309041103011e0e061e0901080a0b0c0c070e0718060306030201110106181d12130f060818100905100f0213150c0f0b 61
    0x4420b0000708140c2c3c062000308031101c507544440c41000b400650380c0a219490754100b104c514140c1008541d41a08039031707488000d20a0b07169200400d0340000c011115240d0041a6114030410118140c03401903011b0a41000002d183d1004aa2000c2c8284603454030001940d60301d00c0c090090054151020ba10f03841030300c06100900407840d800c0e0308016117060818040c950100080c2804009810044c00030b91034410410855800c8500480d4000a040c0213020303190a00e540108009000080034580b16181c0720014420915a048001d040001d0006e0300c8501d0540090304040d540409800b11501d1145140000c0c500840b10440c01941cac0c05540e0282d040e15540d004081c6450f001422807260b0243c1036490b01b100c0210310a070241e062240d405400c4000305038000c8800c8a5801c5100d0881c140104800350044409540b400251504030003410351040514030308503503603408144003d140c0c1c7c440b00b0b000030900c42846025445040100f800c1c4081e81d880360900c030702c0380c0c030580701c50042c0702400030000c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 658088669 1250 658087419 658087453
    0x9090204150e130c02010b090a200d02160614090303040809010302032511010c090605090d170a03140c0a02060610030e150a0b030613120207050a080303060906010809 73
    0x4100b040003012510000102142c00f011640e0440c481340150f0b550705080c80c82c0d410840310841d40088180b00030010680c0c4411040000d00340c1c4445c084202c440000e0941c1c0003038003507055604000381c9000c0d0443c1d4013054a41040100b00c8549001680e924420003d10707039070b50020031a07100d42e43c01744d401ca0500e40d8503c0150017940001d801e580b82c4040c0a915800d01c0c503004082884448500c4da80c0303500d16008525918211054140c0d0f075020441c00310001d120b2583c014040b035600c80c07800c0e605400381c0e0020b414005440703184212000081d61000034403400590385030b0480c048540c2c002403034240540313456024080310301c60641078070050b81207980095a42d2070b00d501d2800740c456107030402213014903a14480b1400d14000d0706044500080c070b61b027031102c04460b62040d0092420103600905030360502d80c409090400342510002d0044450800e00440c0c68420301140004002c085c040c0007900340c4418820b40c40e030b0001c58401d4000c090040c00120950f00c40d429150048542c28094a041028603036151 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 658089919 1250 658088669 658088687
    0x6080f03040b2505211e07020a0b030c1c02070b0117070b031315110f0c0c04020301230d031d010c080c030c0d0f0815010c1b060909020415 61
    0x600070840c3e8404000d0281c041d214600d0f0814400d60252104180341c402c001161030754046580644c0d502400088482c40010340b440c0e40c080f07000d680064035101680b00007502a041f07a0044c01e60024040180b003409104840901904640707005602c2080d00615820000c0340500131029049182400c01001048078514610b480c8110032010303500010380b10f800c450785583c0207a54002220010000f0740050083c242c0b5680c0300c594223a2801d0011031001d540301156070150703c0501d0030700d03030700068514000f507020403900c107500c07c000e0019901c0f5a9540c0c110007042c1e180c0c1054000d516281c115062070b030324220141080c00d41c1e141c1c07510341e038158107040840002180b800681d410302080c0413010700810340c0030010b0a0440442001966103000c1140c3c0b0320700f4281100c2c5035100303000e00c21004030950786d04030201d00d40c01401440c0c05503c0503000001240c0300107401d80040d00c0062210500003090350003400c0c0000f560103e48599140917964070581c42244200d1180c0060000300c840d41400c005d21a503102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 658091169 1250 658089919 658089937
    0x170702010e040606090938010504030b100e0c0903062202060f0414010507030e0103051003080d05150102190f0302010603150b09070503160806131406030106080f03040b 74
    0x800d600c0c041e000003140031607680b50020710103d0801407040150000c03901880708440300ba03840e807041725403803940e26021861001d02404a003a403628080340d060703440741054030002d54100c42c403a10321b0304140881e1210b09190380207030122900f1082c005070030104e42500300c40d0700000240041c1003550341d04001480340405260f112a0340040080c0c02400340e91150080c04698551314240e5a44521b080e280302c02c401c5001c145241404070902200c8086a001114004104006c0c200403807035075924503e0061402483d00010401c0b10b0102d46801c80c021203600c500d01c40c1c2040350518a008800c0401aa45c420020300303042d4000c500000050000381c0c8250105c5030741c0f0721900010030b50b03d8070380c1e5030b003810103c0d10342d0b5100080c0e07035500b0000070030302e402e0303600c06c2e0480604d04155146040421a06240041e50f80b0040b060091850101d030150720303030742c01c200c0e01c0d80d205440400c02d5503c2c030401030041c2501550010f04c2582041c001048014020540624541e0240c00031441e251034440304001d103410940070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 658092419 1250 658091169 658091177
    0x51005010c1205041a180405100603090203070e01090c02060105030705104407050310030b04030207180e06060603100312120204150219051e010f02040303020c011b17070201 76
    0x100203640c84200d00171007860415105201c1d2075400805030503d101c0003000b0780503c40c900780010700480c0c3c41000181810f44042d0b18011a20203a1800400d1500d11641e02c400201c00143e400000c051500e03600a101c1c442c501c0e0f00391203032030340c3c1d40c42059540c0d445802040c6c3d019081030f88880307031140109250f0f04100302c0e0001c01036148000d56020400f1142a0480601c400340c004913603050840d403400300e20b6001d411401c1c51030071810940c0c1c0d079040b0003a103408000e05034210ba03404602458000c01c1854002c000034000802ea0303012100050000d000100c082c05081d109003030118500b03283c200700780c80c840c84110001d04800f03071a548440228119801202d03043c005100d40f000b80d1442180000d102a10b1512200d40980482c0070001b45416045e035000c000c10060b19075660001000482d1003008840a81c20110402c0342541c541401400c0c103161445460b80700050000c00c00d5004100c060a22409894a00d81030242c0300444002c8004040001d01002da5403800c07040d0ba007045070250861a0043c90 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 658093525 1106 658092419 658092427
    0x8040f0b030c19180605090a050901050f04091a04050d09050409050d1413080d090b03040b070c03120e100e0f07090902120d05030a051005010c1205 65
    0x407005036800c040e080f203240282e101e9814529000040700b0200c0c1e990b03580300c8002c4c005038031030030003980506800303000001d080c581045158120b400103004802013940140410004200c041400c8800c4401c2400c002a1210095406446148a0302c001c140d90240da010281001c5c9456102c14440c2c8e04200307500d0009440803842041c07011035030a002d90030301c0a044c244100d6000e80f1040e81d03001c41580d900080d40307180006040104400c0340e1210004162200c0321226540700c1124090894100a000f04080921800141c500203003e46400291003882180d0102136424413404400654000581140c500701c035403048400380c0b551000103010740035100440f00d4035540b1138850b05440c039550310b100318295154910a001d030301c4032030810380748030412000000d031860704280c44000b1003512340b00c0020181407011040c00140c2c0d9058581c003117104159501e5450001e204840707403041001c140 = true := by decide +kernel

theorem cover : BRFrame.Cov 657913669 658093525 := by
  have h0 := BRFrame.cov_init 657913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 657913669 ≤ n) (h2 : n < 658093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
