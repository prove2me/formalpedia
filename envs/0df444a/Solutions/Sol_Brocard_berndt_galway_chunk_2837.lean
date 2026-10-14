-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2837
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:12.564915+00:00
-- url     : https://prove2.me/submissions/2d6c3b10-a3ad-4ea6-87b4-8f4e0642f1d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 510071942 ≤ n < 510251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 510073192 1250 510071942 510071959
    0xf1b0d03061406030c0703030522030c1a101509121b0503150c0d110319050106030207031d010c0b15031504050a022806080a0e0d0f031a120c 62
    0x810403401d40400c840811003417404106200004e84a58000c90744002c00500100d1005251124402c5680c54503400b1030100e4080d08110041c44030034103201000303203003081c00c20901380307480d098162443c0014803607001580003900341001411300070381e0b071b920203001f04104c519680b800500703000d05c8800741ca040000114001c4178001c00c5904020491202c120902010072005449010407002d0744e921401c9020b12a0ba0b603016000e03d41070800c00154003c2142c1c061f000d03600415000030342c04036401a401181414410000b0710001382c0c0104c1107414070071910046481400140300182e91454640e10001d104c0d6410404105104401c13090365062450181c0844803100202031b0f08200350301d41614081e01c940e00402c0301800500c0c0c82600301c2200840e04e000040510200c5409488807d070369004180807030448400c01407050741c2d52048405141c041c20083c0030001c41c902d005440300c00d0700c4600800701a00c5507079a2002c0e081c2d04001050302d40e0040d03c41c10000e42e0f41c01001d03032519003800e041885107108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 510074442 1250 510073192 510073229
    0x18090c05040504050303070507051005010e0f011e050118170307060e030a050f0d0605031006091107030504061808030a0801090b010815040902030f03030f10080609030f1b0d0306 78
    0x41c8150b9100759813000081d4503685030102c0075112500480d40c100d890f440340003140700d407424a90149600038402c1c6005131249040215402120f640c05802400011003119082c27807900b03001a0301c61040b64000e0a006068981244804410703d01c00e40088640c8064000b41a00d40c504c0080104079450185800708101402c05800686a12601c644d8800050091201e10381000300280148440c2070745003400180c02ea03551001c6400c2480d01c098099407030350b9401c41005802454026680388410318200a03182c65042e40d4007800c2c900550250100300006c401d031102c881c041021501000d42411401c680e201c59080c40300401e585402d0081f240c40e241000f10b14041c95014a1400c0c0c00b4061008818130854007000902005140010040c0c0c4d152107902d105c00342000040c0015030065504480f408450300d4120701e54400d040c450707804200254045d100700700107a80c000c000c1d103402c0443d55003101d9847c846080e602d0b1207000500c900820744d00840542055052f0140d01c500115150041c2541c0c141c000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 510075692 1250 510074442 510074449
    0x1120203070602030405010e040b06070b01030b0612010516180f08010603140a030207060509030a141c0807080109090206070204050f070f0c2411070f05190f0f0c18090c05 75
    0x79032046d80e000c101458400c05403454640c00c85640381001030651810a044c940f076801090000380d1080e03c0c03401880050000605114821440d8203001d40c00130b0116082144000312100322004d40c550400002003614040f11240100b80b60040c20011109020181c4481c0e0b0240200010311089030181c11a03602d005803107801040100169415070003428680749030080650b042d60104041581c14000c1c4001800000c40340380740131542c0c851941c006d0202181841c1d82c4900c50b0f02140081c800d10425204121080c1c2d4041c650905491b0070103c04030309881107202080f5a40a007000c025401428481000f42d01740d01041c0d50307445494540c1e0b410511149540060b1484902154060180007001000c8074540307800011000e2031030000303070340040e051a12102220568100200450340840302d050500c042c86410000201410440c00307071075905c0c00c81583c0c2c03040e19600c0b0348001401c22460500754030034003070850a600c5c0200000880d880e1885180c00f4184014052260202d40c0521820004522070a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 510076942 1250 510075692 510075697
    0x130e07090f050904120201020d020a02030d0c0302072003030d0c18050f0a090b0d05010e07030b15130b01182c040302070b0f0f04092309030d0e0309090112020307060203 74
    0x40000d00f074002c040e200e6844180091050889607403d56408004488801c01640300034401c059007035001e036454555402644c0243ea00a55050080500601840c00494203c42c024071000785002c1c21211014031000109003180550b407990f082441c9006940000d49030407094000c0f145942c0b0101460042d183c04c100080c0c030300d010721896041a6101814003100d5016440840841c8009017100000c440070b0341c8060070350300a441c0107000360700300007406c104000103200c80c6900b10308110014101c441c00000403803000808041c01041c0507444281d030241507400f4200e0071300c7c2915007030124010780340c4a01041c4000d030004040408040f024001140803c2c05412440340030310380c164064100d062501c03040c40d01541083c1c198100c0a4010002100355240c40401440208000305c004074580c4259541d820282001c1d05440d40307600e0030f0310304203c52804040f04441c507038021220b00141044030f9412041c0340d4056640c0e11500000140004201c09503c4c00303100c0d9a40d482141100c6001e525003208903140e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 510078192 1250 510076942 510076949
    0x10516300206010608070e012003040f0608090c060901030213150f0201023901020a030f1a030c090c0c0303190e070e060108070c0602030f19060515070503130e07090f 73
    0x60100008900306034400c00d0f14800720a01450412600c150340304030279070942030045485081c1d9000281c00c01c10600d00344c0323400c0000d0526040a01e01490003441c6230b0780300e0203000e407014444c1a00240798029030703001e070341036440b070a400c4103442e03101c0394032204407404450b0b40445100201f030071100185201c1e4070500890b4000d02002c9015000c5202d03840185201c520300140318104446040005802c41c2c0b030074805072404506554002c9214190401c10034200c40d1101814514903030142410110340e02c0005010340c0d208026203a5000941e55000c100c0e1042c0201000002a0301000040c456000c0c030110007903a40e001e0b40801000b4905038050103035500d0100e440b40303c180d000d860000030100e600078104a5032040550030400381e80006a541c1a04a03841104d0310300186035039000344894005a6040354a402c000e0781d904001850034000002c80b81e483c070141164031460700060404c01c022003070059621403011040064070351500c41c102440e403450200e6480000039000600080c51141491000045 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 510079442 1250 510078192 510078197
    0x1020c1c02040506030c06030a0203250f20030a0c050105060d020901120221010c0e030609071208120f0f0a05042301090209010f0321020c0105163002060106 69
    0x2020740d0a101c081c15009141c140d1501440121112945a0030300440c0f28a000480c0181e49140444074032070200061101c518405d400342c0464100d0903046000001045401c2c1403005162041c003a0540c50350344641c5200c030117030101180d1004541c1d0081d1481840c203206030000d00c99541c91400380080240081c1e40a94494101d100410202c8800034136a101e20740050311016603400110400d0841d0310b42c40c0c0c00d039820340c0c1d5980342440c98154070145071454407400314080c0840c1e0030014940b81c3c0d40c22850041d02080071442402204218940044800241004102e04e6062524040341c00c0310000c1110f40d14041e9020000148099a00313209551045611a6402c1c2a0000c4800e42109802c0950440c070744a40d6610389801c0541d803074448450007407203110301c2c8058aa040d0710f40060540d00403941011000d04c81c0000b10265074000c074009e0b1101a003844c00030740740e000324501e405105001d4500035000d44010005201e018001c0c0c502c408400b81071540000d03a812802e081281c1c1c1d80340c03d2148100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 510080692 1250 510079442 510079489
    0x1a0c0a1410050c0a0c02060f07020411090f010e060409110c070e07080108030406050313022101053102060a1e0903021f020d030203090c091312020d0816110a1101020c 73
    0x1031400a01230402c6e40030b000c1b1040e0411010381d01060440d21340751041c03020b00c400401e15541c0c524000c03260322803401003032805140100c10040840ca1a014034000c3c0c0d5100d03925244504c544a5440d0300b569000e104100885248a507589900100c4540070394440b00010a254004110740000004450844481d6a230312031550341d0f502203070b00440042010403680300036418110004c80000014036080c290180b800000c007802c00c044084a0500704000302c0302c4003412040c4040f02d00080c08200b0344c0300c6805a0f800d03075640240d220101d404c10030980b15091b83d141e444002c0c00b0425070020340b51065a10030b0702c07170507080c4125102078240c44030110740c440c0046c0d0180100099252098005d580c20a81807801c44446a075000005424414200c034140031001e2800c0650301031000d042d15140b10030481e40050201c0d280549001840303c000100300a031100801480c0841c91449a00600a0340441700706407503450b103080c68200400c4c0d81c110103450042c030030b80c04000309910b045082d070105070010680d8001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 510081942 1250 510080692 510080717
    0x801051003170a11010f1a010c05060414010e100501030c0509010b03070e0a09020d2004080312060a1203120c0e0609041d0a030c1505011a0c0a1410050c0a 68
    0x1103681c0702c068414100100301d84c0c29411910240aa0000b480d98000c010800200842c103070003008000541060402110f5005400464000f1070090f8100750850035008114414080c503030301504000340100303138602c120711008140b146164043c6069038031070740340209441d03030350310403c42d14240070300812400300c600b0008030700b0312070080a10701d07104a4090254209a40d440d01070001300d82100840214043d1520024400a400419000621020320240d42d040078145007086550303000b82103154046c0c68003280460304542d40d40000344010400c1303004044046003030740341c010701c0c18803036170407c03050b66040880c0c00d1100da0044103403042809000d080709040801d00f6007000090034501003040c106501605200031645c4043c052040d020b802911180941a424500f07000e00b0448207080c41e045900d04001800440f2210681100d050842ca07143c68842c5031000c60300781015a80000180218032004118a07104ca000c5035050100b000c1d81020070042d600c1a002c84040d06c10754030600c000601104250 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 510083192 1250 510081942 510081983
    0x9060108120306010905041a1f11010603050a030c030315031208090c1012020c120903100203010b09060c010e010c020c1c1208041b03050309040e03070c0b090420040801051003 77
    0x11480c85585404442505a0b505c011801c4141d02c034024881880300c9c1100081a290020380510f1408400030080240620703517180e803900d50711120303801410440e401c010380050600c40d403c0420403410b1040e0758a1026524900b040850081400c0c92011481c000b000508102d004212004204000b50207201e02c01d040d03600448503006180d0000b0781d450707801e201e07400100f041004400c05a45099040301c4d5904000d5080600d4801d900724041d521500400c018481e8004c9202500c860900c10740708143c56102688a42e809031076080300c07074402986440704007011194000f40ca1422100155406168034010604500c01c901424074050441d068002000c2c400034891000e180d80280a01001240b420900ea00c2a106c0b1209070700c00e55169201040c800e00d1441c052262405030368685000714600001a42c40411800c4e00d07110f00844018081804805a10781e07400241c1e0400841d41e101c09050804502015031390428050030391150700e80310001e400c01c8d02c14501c010907240c200320041120808910714 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 510084442 1250 510083192 510083201
    0x3140a0c0507060203100819200103180c09050c09090619170d1701050d020118050301140103120203280c02090112030e0603010605120c0906030906010812030601090504 74
    0x80040010030480da0b4007080d141d101940c00307103000e082c01c1c602840c942140c040ca8404c00002500b0300754400c210000002e07441002450344511001c128a0020308003a0042e00101904c908140034410380c1e000300ba0801c146040d000003070ba5401c3c40100504d40310700c2c1504000d402034121881d0407140c040040750b2103240042c5142503620b991488559802c1d11403030851300119900c2083c40c6981c2c404075240310310603003102003507a1404c04081d4094803589400e00248143c0c5560502a0501400056041c500a41c0c48003150143ca0f024009001c142d00008416100560034401601c110001c40301070300c4030303074070201c1102c252800c11002150304500c9001e04c1c2c0324400c3c1c0c01d0220001e00c04056581e50060700c548213610f008007034070180491941514103010340446040a42c0502c15401000103010450708113041e10001503001000901503508ca100400c044e2051884d0f160f44007001000b0400c18803000540723341030756410010f564824508a0031112a40015694076000c14045101488142842d911 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 510085692 1250 510084442 510084461
    0x311071b0b0f0c0624060d0e0d1d040506060909181225051f020f030114100305060108041509060c0e03010b06040503060a110408100603030f03140a 65
    0x208599015540c0542100a90140c51080050751010800300f10040043c482c483e403101c00700c21141101004943c5100280380c05401d118441d140209031081200030b5a40144490444001101e24005080c840503200c821021043e4203100c01e81803000d42141800c0c018640140400741c48142415800d00c03c0144c800001841040b501d0b2039461040214a020440d84080305006104181d55401c440d0302c5c41003140c0c02c002d44000e031035020b40c0310740b002810004000b0300000c2d5481035046000d8001da1f60700081c0c800d416100d0a11240880041954000320f03020074201141151004076a0034400c90940682d00100c441381d0108800500007004a0102c607100b14441c0071312080000d400c07641c1c2d5681e00032104183c00d4140003512021802d01142001d200c0c1103036083d01140c48a0500e807501c4000b035900e40000b40603001050f12036004103090107043c0c0542e005807184409a61581c101104034030002c029510090300094001e01043c1041d900a114110400050a1900c11169258118540544407054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 510086942 1250 510085692 510085733
    0x1061707180c14070b040b01050f010c03080702190c0906060207080a0201140408030d0605031603051f0b060304050105041502041409040c050d050601050a0506160b070909050a0507020d031107 84
    0x5010351072424440021306003c0d1050341800c149060908120310116816044540030710031200315200a0380c0c1140111180f01c0c1d052a01c0141d40e0b80d1030100704d0421206c500c0da0070b00b600100c000001004800000181a6440300701c003004900d0780c0e0032040342e84503418410a10190420444180954400c07440b4084900c05521a140f07816a6445200d10395072000481d504802e607103880c24410f62400b071150320031050140c03d0803c1c001c0d0070341c0c6590b03855002810800039850744414894181d00e00c030b90042240e100c401040261213107014201301d40603002c101d0341242e580301003542c03a4403014132500c29601610403551120030a08880700a102800c0005001910f800700110400206940d500c1203002200e8400c50151085514250a01c911001340b1303084503201d10014860703090f00d0201d40d4401c05e07805030403154a64054840e40d1068501e04040d81090100c1341c102020020705003881e800080c09003002e6800c40310200300f80c2c807044045840300401c08000040c20040c620116a194080301020030801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 510088192 1250 510086942 510086957
    0x5011b1b08120a0b030706050a09230603070225120f05010b04180303150e06060708190f02060603161401050c0102071103061003020d03050d0f0e01061707180c 70
    0x300c02d148184800701c0d1003021860f110082d02c9070a00b818003000000b400d090420f1402d00303d4601010308048100e00a12050481c0d070202d0320700746503e80070302c00100d08029040b60780c0c904001c20000c1d140c1ea075010b40c461080080c20010b40b500f1605194800445a20b40c945c03112501c0d19a071114004403525000b95915034a0b00c0c01480d20344d8691146505804100d4021140034400d0326000e02902c4078501640d113449000c4904202907507070b541515911030012250360380d40344620701d41185d80303004403400302e0004070340801e0401c1c2150304401d03034000c1d07042c0c16002c58026944c1d0104050750b40000c10b81c01514407000447c1002080c81ea45885201310034141400c074203080f551414142203800003c0280c81c072070701c0300038561414103051101036000304c2200c4500c10144c0c2550046004104010700041c1089000501601000016840703284000b000784800e02031500d043c00198040c12090107071085030900100000700603040015031408032050311000300f0302001c40992a030010402c890300319041c40f12a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 510089442 1250 510088192 510088207
    0x5010c05030c16080d020c060304081e07080721020a0212070e04121112120406020714010e0c0d0c050d0c0509040812071b110111011805011b1b08 64
    0x1d000781407000350f1610007400264a0700450318030f49020020181d041d9000030295100076203441702140d0b4440d030003500840e03642c00304d401940605402c1d01002035528030041912400c0115003802030103108e00a8002d09101400c9180e02e8100313100106242c000369001c21494801410041c0e1044244070704601603445070340e80c5020000318a0b502b01c0c0c044849441c0c403881d4135a01a00710803008880c0142030000c06000042d400340c0703105d6200c1d6195154070f1640c0e600000d401c00c0001c1e0104c40f01e140d444400e400d1460044102c560182c80c0e500c1c1c4014241c00350031a83c11003814180300c105003d5030401e6000400314501403e1000c00f40451501791008058482d010035592103600986000340c0c4030750640e1340c0d900d2404044410180c40a010401040910f140c940c0d07001d4004200042d8403500304400080404c1c4400041e82e000405502020065081444600d503e01c1d44100007888280100020701040b240c1398580040f4200703480c88403021500c2e42d803811200d007041c0140019807600c90000645030260 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 510090692 1250 510089442 510089467
    0x70e09210703090506043c03030c02040e161a0f1c050105030c0d020d1e080a0305070f050a121508160f0317031b042c010b0906090a1d070809030a020705010c0503 71
    0x111b681049d404120310314004811030030700c0c1c4030307040325402c0c03c1c00500041d00d10f840c0c140d40301645511480041614002442000158243c21100410018800700d65180b895407501c00d04d02d16000072500320a0320b0080002020704000c0ba21100141c001461690010269800c00c072500b83c40d4942641d008450030b90103101c04600c032800703501a5001d841c0f440c0c3c07240800c1000405840006080070104451503625011440e04002619501c0c01d203800c200342642d420358920401020800424a010022140000f030203040120781070441000c01005010381503203c0b100794640d1403161100800805400a4420700203507084040c6810001285182240781003a10162016804c50307003180700060004c1d540d40721400c1105003075414003440d1a803014071030362400031154614051258590b000c3c420000300340301240e8504080001400c1c3c0c0260015040c0300701e00c564582401d080380c0c01d0000c11003400121328a02c44c00004e45005018541c0101001c5042400440703041c1d08001007183c00b48024001e4100000d03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 510091942 1250 510090692 510090809
    0x82d0c071502120f0108010b132403060c0320090108100911030a0c1e0807090504060b0a080603120405040209061207020109030e04090203070e0921070309050604 71
    0x50103c0e0800c09420807549107030500e0410790100f01e641e03241c000045030a0b2911280c810001601845c00203030840002c51008400d01c107290310368800f0030005408020040da0b03030b0114500e4901581d042000d05410450300c210300c02016034102c2403000c148201415076100e8001319510580303a182081c2c1c00c650f10030081d000c1e0f40d0200281603104d1404010814886014491510100501d1501c030401c07a49003041907031940e0840d0b490504202070b100004041c0e50180d00000020036000d04108542582c4220140c42c81c0c200d002d03018006030141010940603c0d0002e04684c241c410888082d1515182004210080d80030313841d8681c1103c801d100e0744060307041030b084540c8100426000803410000e54a0000e00452802c2c400314030076031504c4200000750b2400940002500c100d0054021a03840c3ca2100310714200807045400b03100c5070a203005043c08181c41000d8030382c030b601c40c2d16045043e07600d4404001e0b42d40250b014a110b0700c14050038a054001c00030480d02c0415506801000110100c2d0302600c0806 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 510093192 1250 510091942 510091957
    0x7030201060501030b0d0b0402091015090918050615040f1b090b130521010c091707060807050a14032806080316060b040c082d0c071502 60
    0x10303559074200304000d50f010701030344211003000c4401411448899450070504030029101034001c00300c000015001c0440c143d021030140100c03041c0780c2c44808250100806c100f449002e601703102400c04580c982c00d15010380142c2101540a000307011666075201e04d001a4170440703105030307038410345a41000c80700101902c1000380308008000c40580c40c2405c40006031074802076610020728901c040003007403158650f11f800c003003d86008503107403448039034072480140310b606a10317900814951034080c07001c0b00d031904140702c407085400da208900d80c640b403504225a1141c04070300c03a800108100784d000841c10340c0319000a003c2c400c107a0411501c50f0341d00308007040031f07a04100c40300704940e06400c003c800300c82070301d55052a061407101000d0100d1820900445d48900a85462280b0301a645207a002082a2500050000e07880a030042240341f600d50380045c013a0381c0c16183d00c0ea0101a0142d140d5400090704601002c01000160914103034a031a500b101c07141d40035200580350005019086007c803245400200500d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 510094442 1250 510093192 510093197
    0x15051548240103060c0207230105070c09021905030c0316050c0601090e0106050d050a0201200d080f0a0b0109051908060108060405070b030f0c030c120a0c031a060f1b030703 76
    0x760340c190300e455421034290403044e105540c011002004095101010040c8c032084080000a0010a401c0140c985024400e030050414004e68004200000b141d805000961180c0b0020194003842940640f2240301c240c2c1c24581e101c00400000d40d008001d0034520721070702190f160042c40c1c02c03203071118076040c04404c0e00248080b40d00c03990040c500890900590001d05011140d002e0f801c00c00355141e581d030f4800c4d000024107112080c411450002e10720111226051042d00c2036a81404848500400564086960811001e200c00108101d0740b52881800040201a102c070108030f8188020000021074030001d940c4a0704940302d01095041c810310299000303003c00401001c81d4141441c0045c10100e49405c1840e07001070500c100401c401000412903088003003100ca0035079944031a01c60040c0c604c5040c001400e4182d20340144070b05030030304e0384c48903401c0041030354200103a0304444c0d80801c1c0f001003081c00a41c4100705122590b061003050f03005044000707005003030600031942d034000e030b40c00c0d600a0107040d0302 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 510095692 1250 510094442 510094513
    0x2108041d0106030c0e1e011b06020307080112020616060e0a0501090507150206010b0d14010602100e06060d060e0102210a0e010b0d0615051548 63
    0x38a030f41501034400d80c5000d90518151009418003c03400e4540d80c0760001c1d101d10000341034400240d0151850004c1284007000e400d00d04112410042c2c0690b1042e1000c60004406100000c3c0500c040c1c0c1a0128159004010307510700488085140340001640c01c040d2038580d560812503003004801c11420b030301544220004034500c01182000d40c1082c6545c0d0228000c0034440845558a80e03000c541c00d819145120581c5441d4030518950030020440303800041c081a80100c00415226000200700c2d803042c2c41b141d0140241d11620081c503481d42d806803950b40e0030680900d1100005103050f0030041c44030f050750f4001800d001c82c00ca904c280d0884103070742d00c60350a803140f0140700a800c1304d40101710780482150001d0008182c100e010171101003a8081c05040290754024045010410320b06000080100418492144040d0809202d1582c000001c1e80e8425988010308440e080c0706182e0220407070004040c403002c0710110f28411500f03440783c0303004803070501488075070346150342040413071704140c2c54516100e44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 510096942 1250 510095692 510095699
    0x5041b0f03050c0d0b010e100503010207030314060d0312020a050d05070c0b07180e090a1b06021e030403111801081b01081b0d020c0105042a2108041d01 67
    0x9042c40031071241ca0b409420012080300c0403c05c26894079045a1030314003413803040c0d62540144002451640c0220780c3c9940000750900516500da0440d035510b000c00701101d0a02e450310781c1007141840f16202d00030080342c452002a80d101000e0b50241c00e0010307242c01e00714601b0a16840b00c008440b0200c03120700100d40c60b0707248201071000e085581c5510840c41e0034030602e45000c0c0071043d14451034501c0f4426401c0c0316100042c40000701032090380d8141e64005441000e50035003c1a01c4041d64041c003d0000610900084c041c0420800708407422440c2158040e41c41c0c141940c4408244011892806801410500c62071154103001c1a20700d008201c1c03040900f00071860030020b0b50301d01c0744d482c2e200e5042100c4c000a00600000c0b4800c4107500704408e003180c41d1341723182851403400a402000240c02c400d52902c0d003040706011500783e02d5034940b0f04910101207060f5141c238040c011025030340a409603a04189014151803080f800d400c2c400280a10707002424242c0c2c0308504051104410407950f88411101c0042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 510098192 1250 510096942 510096953
    0xf01120b2404081e030304170702030307031e180b090406080a030f08060603220203011506110f0f030a0c0302011401120606050a05011d041b022401050a0905041b0f03 73
    0x291201104070030000400c13002c0c40401070340c9002c0540301500404400ea0880816070500c2d040701e101d01d6010302a25100e0300b0f64103028003400c0810300d981c240e072040310328400d205912581602404100000611a4960515540c6c8000c0d41144030307550b0b0000c1d40e608010030740e01c40401035124802d04c6030341c0341010442c8940e4014030301d0304040d08040c01000c046c410320511805420200b4018543d95a4428100f4940e0001038050070003401580e10307031044268086030f40343d40f00510740300b0046180700b120140c968480e4247c1c3e0b5411a02410802600144401e14095100e00002c40001d8060303c0041404843e50888031251142a0701c8008c00c0c0c3d1004040200300030042c003c0c200140800c50f030303641c00381b480d120019041c105c00d0702903110112124205849e071a43c42c1c0e03000383c150204000054100c00c0e50315101030764410341c840300c0d028100e4419403060b0302070b4a00207065041e01c00103001340600710710301404c440c081c0c0006403003160040c0013440051112110148036000800f0300740402003240b4a1800d11 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 510099442 1250 510098192 510098203
    0x8030a15060c06230c09120c0f0d05070308030106030903020f0105101811030103050303040c080115090515030d051305010905210709050901020909060f01120b240408 73
    0x120322400050303800401106820000400060b40c001201041e410802500f400c90344000032103643c446501c2005110002d200700000e00011201541e0354007043c41c850040c5907859100300c006581c07001d044100202c1c5070500781c1c0092a100c6c0728004584100f5140d544521240d0826017009001995462040d0705042d81000140a0303a140c683c001c01082c18091803404900382180a1100c201c01b21074424141c101060b804041c4002c400403006480f540c40385002034407640706a6090f240b80080e0b540100c0d1203c0184140d000d611000c0480d420824541541c3c2c002900740100040c081104999049402da00c081c040c44881c900c46940b0640e46a00e03408800c010f5201b1038204c141009203003103090001d611030341d103889901041c0000e00540038030006070040c9012240d40215203998100420b00440342d805401a10302204101c400c0940365a078031042c8a04410b00c51140c1d4002390184441e007890310703102e41c0842140c49001c0d1a010507010b5003801010800c070440110303101814001020007455105200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 510100692 1250 510099442 510099461
    0x405040f081b102a02060705030c0903060114190e0106083303060c0a0206060f280905061537051b0705010c06020a050d2c0c10110f070308030a 63
    0x92100404e05840c4000759544030086c40f6a003840340020104007000201c00a4a840c2900202141d11039030f12282840281c45001001d00c1c003c07100f00300b10401480c68981143d0a5600e40080a00c1036842c08000f04d441180c040d1400d1014600715520030f20f10809100702010241070000b0000c5407a0548080c54035040300200300c4001c0c2182030011280d210341c0402c000b03402050441d91000c200ca09400010100050842e24019017100d4910030b0740035030800604502150ba440f001003001d51340e450700b8410f150071002c0f12405082010494080329280c40f111007103080245d0704480810110401400d004041110300c02408200040f030520520f14a0100c0148540040c070080c007070762450540040e00030102c43c45c00401e800d03004100c00d0a0303036108030305031100c1c0c41c0c0800041c0642150048040e0045619080c1045001c000d907070614011800007035245220640a000c030300024071903034406c507402c480340c07201d41c00039001e0300303c0c81e40c010b450401042018500526440f5034a090650460084403070a04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 510101942 1250 510100692 510100751
    0xa060602060c0d02040b0d0b0f010806030a032001051006020c06090109050112110a020325111003020d0f0926030a09050c120705010f0e0603070305131703150405040f081b10 76
    0x402c00190b0303180071803002c01803980350a1407a00311078901c8050d002c030f002807440b0380a551b107013400b08190038510500d4401250555020742c0e0000a0410034401148619076010340030a907800000c005552203074030303441c80d02c01c1035400000340014504c41c2c03034010381d01142e034410050b44086413403883d0680c0c5801d0305010301c0d443c16003110102c1d55559100e50030020309508a114440b024050005280240c04803510450358000401039110701c0b5074002c0083c00f0101c000e40341c1485000044907800342c0c0d00ca0240300c0c684458003590440e43e44207107000c05804825401c65080c055031009130b8082d00c442c0c5003108042c2c0000045d00220741804001411050851000010080c0781101851aa112502100e80005a611300401d0b5a03903000440201c0f0407481200810022032001c5180c02e007030150010354050ba00c1416022006502e040c02c000a4400507a40a48842c05990600d8006404000200200b42e420200070303030b8044540b4110341c140788000c1c0d2518502030301d5040d0f6040d8001080c4c4503061500000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 510103192 1250 510101942 510101957
    0x50106170c03070302010302030903070b07050d06060302030910180204050c1e070f0f061407020114090703110f15041502010612030f08270f060a060602060c0d02040b0d0b0f01 77
    0x100009076983c00510020741450b60000206035104801c1c41141c12142e001005000c1030b05150038002c0559201c40d0303014024910384100420920321074000c13a80940710410080854023450024a0028624405c1044101c40303210b24034030050b21a400361610445030700346a5501c0301c90405180b2a03905140900c04914034040060340009204d00d01100d00c2141c01040c1c41110383c0302443c2c18001403100c00301840d141d030608004c01242a905403c4410303150210740081007182c46407641076a941c969400001e20a00c400700c01c000060602e1420000600c1d0300816506050700c0200d2009896442500001c5905110040000070341e0b8090003040010107425803c003d00c4001510010080d401424030b810030064007c1c0440c041400c400e07142d5404448a02e205e00e03480c410301346400ea480540d1400500700d4000d500001c1c032665040e10aa200b125280c1d000b0b800c1580e01c0b455643c50300d9100c4100b138210103a080c0070100d00d01c4940000f80c001c100c00110700144102d6428104400a103009889504000c140e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 510104442 1250 510103192 510103213
    0x204090c03051b0c12070c0506030a1a09060a03020402071a010b0706060b031302040507140a09050306010f06020717070909060b041503020f220912081006080612030c0a05010617 78
    0xf900c02907510181400c5c903100d031441c2c40c01c011054001e42c41158031280c08030503c61000c55982c01440c040842424000300c419102052203010b403402c4403d560b116003258000c10141c01d2507001004c40601c204808440d086041e003030410380138020307081000c0c0d580c4081344510800000e0301c12240600741800525040d0b01d03004210110580072800300074080da49800c00300d03000d11701541044541c030341400050360300d905445031700a090031300c58810315110340f1801e00001000709070000481c095901030360160803002e00344070034581015200210440580719408000412454a100c3c860f52188a010049241c2c030050f01007200381c6a1000f0312241c10703401200e0400050742c96031285c42200d01c0586605801040c9844016010902020065a028104000a0100030543c07054658460054807035202c0d903282d50a1210482c000d500803080440d04240114116150150780c500061848c40112490300c81111415800d20403041c50494803a91103450074060891400c04034a00903410030000c081c4010b9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 510105692 1250 510104442 510104467
    0x901060e090a0605090c0702010c0b01030602031e06090a0209010c12091406090d120314090a030f050711010c151d06060301020903060a020708040f0e072a150204090c03051b 76
    0x1405030100c40186d5001442d0021a40503080b892440e0782c01c071085040702d40e50b90038004065401100d4000581801c0c9851900f40059800664080d080240c88c0051954a40310132600030b5002c069050b0511043e80c25100000b50000c602103501d091036514908410320b0032440c0e8031201e4440300141c0c4940340a001981c0281c0303509544e0381c1c1540c2c004180c501043c044410136001411402c0c00040d056000d40c0812001e404005000d841c40e070300c203645140780f81c0440c040481d118002c00000800f103c0305003c50010562040e03400540c1d0a004035100200e8850704544d000c100c40400d4114520071503061355110091005000755640808150001d614141c443e90000e5120300c00140b50b1040c80b5800314240092205000a4401800000d48503050f965160f0844141c01c1e0780c110f61140028030b9980d400c01851200d15000480704011010071100164203656044181c1a61941c0c050119800d000014a4000c1c40c0a403034110a00c64800054509005040e0040268003440301c24a082e0100904002c905 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 510106942 1250 510105692 510105709
    0xf0c1206040201030c140c031315080412020c13050f060a0b07030305100f080708101811010c21090504270c050901060503180106050f150403020901060e090a0605 71
    0x3642442c1c009205d03e00504103481950301140c240380003e401003940e801c56080003004220030b090681e82158130594030381980512144000c43d203000514003602080018100016981c03400c0d0103801940c03a102c070b1a8001c20703103480e20420386c240f0542d124000d100591032069107858101c9015100c51001c241495506801489000d034002c0403da03881001032411800d8089039000740c1401000c0d90302e510340e036000e819a1015203000708001070065031442e60900902c1c0c42104002c1c00140d521108907007082e11260282c2040d03020709130500c06203010300e1001651041515501c44d01420a144022083d007900801c040c2c0941c01030b900417072a01c03495943c0c0b461008100c500c10448444980e140e80e02da4940030300c8d002c1c0140e0116412030010070000c42c1c0c0a4114000d10300c5811400d2444000301910409503090701ea0a1040381d402c42c034110b081c84071314140003400d15100802c0440355481e09070340703a0100381460801d80c020000035540d10b0b80f50023240741c007500407900605018020310610f402c01c0000741041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 510108192 1250 510106942 510106951
    0x5072a14040e120c0c091f0b07030c060504020f0a0902041703210603030f07080a0e0303270a050a03080309060708011530050405190f0605060406050a03050f0c1206 72
    0x300c010540d00b44158080107aa0300d14940580005031300e08045d1751f00000f80900c02108001c041035142c01041e01011642991151505961441503010f0306440380d50040c9001740c03090342c101c1c080c004e11070300903195205241c000308650301d00182e4441ca0b055038903032004040010105180c10801110008a42c01481d07118058480603007040075440b40b00001e0300d10320603c0b04001802c0400300b090030910100310041c118030810b03034a40c48102100a420540c8a2046585210204e241082040b44203200c5811600c40c006001e810b1401e500d485000050b41d04001c2c2d401221a60f10000400660300428000c16421681500b0311520550500c6001030590000b03551880c104484d1460b085e545d0026142d211788007165902508401084816044c0045d14040703400303840a214103011201d002e04807280a008840d000100c81d07540148555442018120240c0110792003074807408042110b684200c04840150311800080842c403545000c414240454005080e1090403040407200941c200402c0312680b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 510109442 1250 510108192 510108223
    0x1c0201061e0b0c07030f0506071d1809070803070b01031203021306051606060e04050d050c030d0b03210a110318040b030709150612150605072a14040e 66
    0x90f06541182c0344d28100c0305900140c41c4050b00400301c1c00703001000c6456805003a186e590241008018010185000c411200090700700107107903c2000f04084442c05260481c4401c3e00352180c0580c0d401c20145550070003d0300f41c84c0c1508400040080250300e160720b203820b10150070150700f003000161094418002a1042304c4c140500000e0008011310b803659050450340d40880100b040070b07202c00348030242250071101202c9500c101044803814034042d0080d143c480c2c003010011842c004414000001501c2c003000c0094040c0f1a000184442d621b0f04200405020105039803a42c032030141d09070090401d8034803a02c02d0b007180c1003000060082c517102d101034440148196808202c040d0054007191a000069000070802880e01111103112600c0501c1d80c400c6543c65039038408954030384098242281c0344041002414000b03a40100656030250028040f15801958038402e14019400c5203044841c3d1180d96400006600070b082c0306d00055400440c0b1846426102004408807840c00b2641d580d46541d1500c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 510110692 1250 510109442 510109447
    0x1c0c0509120c0d0f050607170601030c05040f06110601060f080c220e09150f0f0612010510090e010b21011e050402012307020405181c0201061e0b 64
    0x1d803a904101c07080808001612100350000241400da40420601104803554011903020401142c818a0300750390001c12810300c202c4640320b00005400808000e01001c091020600000130b400100e0840d400080c00b8540721150045001884517060210503046034090024212640c402e8a921070a056406442d200509503103004a4020208200c3d6040351b102840b00c01003030201d0200020b040c0349010704121400c0341e8141401d541181071103841114242035035040300c40042c0e4210b0001d510030f500620041c0c0320b80f00d9180700780101d50030b40c1c1c0100c030745952040c0ca600c030402c0400c01d58880c001e034120300a00204200c001e004009442e0388130008202d41e420701c25140c0030f110200294814508040d654095002c51074405000402400302110180d0204108940858400b0050b05650a8101600c59180d2800140f45c0c204001454050030702a1840c201c022280700040c8104060b0b0707550080340c0c5418207ca080000c0c002c2c00c0d00c0903500114500305016a12203010800c40c10a441a122003115864 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 510111942 1250 510110692 510110719
    0xc0c070303030b011e0c051b1305040201030e071508060d03020d111903030b04060519060f12060e0603060c2a011b09030506060402040b0327060901021c0c0509 70
    0xc503018000c80c0785c15910782d0004000340382d040c3c00c4140034034628820402c0d030b080110424103a0250100c040c501503007140700751500d1000c0390882c0e40140c0d8000d105040001d404007031482c01303130f103050000e070061102c10300000d07400a111504076544a40c07101c802c5510000c500080e54000b0f480d02c080c45004020310038041d0302241c680c10180080304110307a9030b0180032003045007800d008001d444d074141744902861a00c040401e0a04054000170341c61010622201c82c002d19009045805603004482601041400082000d030102c082c01124000e00e1182074900490400c50201410500d0140290303502c20390400c841803419114440c10f00c01d84110b00307801c000e14460328200e5409410182d42a5020308684041d5203110307a0060800d2050f24000c00881c0c800d50f983c1001d0008030310440c0102d0500745001e00001d0080c60507107007494240c1e00c92101656004040c0135032249001c80c269000303889a500400c6503c000b44240413081c4469402c4502405500f1580d00040d00511900322041d0041201d8039150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 510113192 1250 510111942 510111947
    0xc0509130b0402150a031509020a050a050304140a0b1e042a0f0e2502070302060f0705010f1b021203040b040317040620130b09180a140c0c070303030b01 67
    0x621300700c640100200d50ba48040d0700014010070107041020341128201d2000329601049109581d68030704241c40c1c103440d01c12040d41c1500c071504020001c4500f619454802c00f50018280407060b074040c460b11864510b400c20000750220480040c000035424140f0004200101d0382c44505100c440c001180609032051b0300b800da81c9610504c43e00301d05d8031030110040008013a905509554403e81487c01503210842040030000880703d0480495001680407510a1002d8a4034200429000c1c01d04020203140c048641d0b05c0600f07507a5110040910540d540c0b0006d002c1e609001c00320500c200142c0b000e41035410302d1300d85920050201420181a0031000d00001701014003408000c85200003402d0004142d143c00c0c605400a0101c4441c41c0304e421840340c0c03403080080b0001c400e58544c0c20b000058400d01d1810b00141c0d0300710b13410800029a2192080346240c0341c41d620307000c00e64000c003005500403410a61032900b40898a0024200760080c81c03003000341c0d510b04000400c0d504c0550b540b504d0301103081c80105004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 510114442 1250 510113192 510113209
    0x140408090d0506100303110a03270e19050903040305031b01021204140706030605030a1203060b040608091b1503090c0901170105010b160813090204080303040c0509130b0402 76
    0x2c0c100d210b4035044c05640705504100404403486640d480e90071b00c207031440700381e120751100000501084081460600200c0d980c40d8000140d24948d0080381d400c0e5650727451004070380b820f44445e00d2004107804000e0b080c1c2900d004041d8400b00c4038005624151850b03232003a6991141b1b440d0300710380705000300c1d400440da202034044403001406041c01110354201420201c0202d00300603180060b52180c0c0d00d0000c0d4803070081c01100c1c100c400050281c11075112a4a4424000c000e0740d0b00c0c00b0070941e8070305022400103070010260000c4c0000d5680e0700490300e80b4960561524101e00852800048181000d076040c1c0e071404442602e0810201115451f901d0314a610740c6460140300180f54840c810000100d52414668105805003104400902c100c0c0d0380c0d400401701c140f060941d144140f0188490900200350300100600041038640d504514031030b038641c10301040f03070400d800c4101103800c00400c3c00284603003000110061311045400d0700b40350a180010351034886014600070004182040050159500c0c40038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 510115692 1250 510114442 510114469
    0xb0f030c1201030c090b0102011b050702010314130c0909020a051c0203030409020307020d0305040309050d0507090f140f15100e1305101d0a0e0f070e0109060914040809 74
    0x410204030b585900c0d1408074111180501c03840d007480c0c5102456150f00c140a0500d00342c841800c241d102da11824000c844981c8103550503814141ca030041e07540310601080d10b051003100000d66100b03100e4280d2130440c3c0c2c545055445410342c1c9007071804400144e0703100780007401120b900315200540111440e115141851039424040d40c9800301181c0002c400507950000c51040015a09880785408880029011a01c050700e0150025580b024140982d040c6502404040c900400449a08550300c1c524001950483e405180e08191600701e040040c211610450350058190144200107140c11100301c0d1a11101c0c50300d071840b8404040d45500348900074040080380c402c4c0130301001c0d226183c540c00400a01419a200304900b07400d1007001842c0c441c0014508900302141d10302510ba0346404100350090000918454458080c012a00b0101c00c002c000f50001441c42c000031240b07642c540100e0004595003680180d00140c100201c0c614200945480ba650003a0301c400c5107511182d801001c034542100515 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 510116942 1250 510115692 510115717
    0xf1d010c1e050a02120102070506010b0d0612050c040c0914130b0414040c0512030d150e040b010f1203120903031e0501080607031401140607020d0b1803040b0f030c 72
    0x101d140c400e00c0303000303d0300722940b5000b074550300381c40e945500d481803c07441101c002628a0304140014810121040003c0c160728009240c041a17180e140c0040c0c2103510700405040301d050b4801c84507400e981c01c082c05100b00c194001d081c032104a515002002003080101c800c4a8865181c00465400b20744007548a8103030440c0251080003c0d900d81100031036450000c3d60255090114403100083e1850003420030341c0d1494942e8091420031845980e540007500200352144641080048c5c00324525822030301c184d00c02c502400c540c5034594544440341c01096559000108034050345c909420100350031420b07151110900050001d12034000c1c2c103049009000761900140c2400d40900d86030700402568000c18180c0d01c1c0a816145a42ca4640041d000c954029004004d1403202c00d0040103c0100d480f00070b18000c40288c8041c0c03514046500064203500b120304200d4071344010000380034850308143c068003124026040114a814141804042c443c0500c0c885000001c2000000a0031a1201d109036080c180240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 510118192 1250 510116942 510116993
    0x3020904142e060503062208070506040308150d0305040303050309070e07030c030b0d33050a02030103050c180c0a0e0307060305041208011215090b07020d0f1d010c 72
    0x21040140e11020b4001c4804a035418200301080d1890003207021400303a2024501156801c1040c4850020001e155405031290303d028001c10300410070600441d881640300ba998a0440d2504d07000078a00302041c02843d9004000d141540c0001030740150403038056942606040c1d4903035130b40c5a0b500d8a04086c0e41c000340907601c004070a0104c001d800d50465420b0780c04070b4509102c2c1c92249401c0c4003690310030324400341c0264000070008090100b082d50181981039842c40003507078880210015410385409892001c9041ea00200400610001b4003210b89464000c95080d9036200b00300408a2590001a0801e40040310018001803114000e400d0b190002074081c05640145a49a1001d0000c080c210340a6940720200c0c440000d80500c0346020380e058503149407802c05801010389481c0c0720710380c10307622414400b03036a40c0c3e2950104030b1043d1068170440482d401080d01c2c4071031010081240242855030803d1220001500410040c0708004010740c550a103400c00200c40141420101a08010040803016000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 510119442 1250 510118192 510118243
    0x4020c0d0509121606030b0a120f020a15020604080c070e0a0e07240305070507060f091202010e0307060e030909090f0105011d0f060f040c0c1a010302090414 69
    0x101d405000360309001c030ba0007103016104121654480140e0303050980301c102c0351380b030030b00080e4040e0348608a460b0000e4540340d81035444a05160b03407a9503050064482d1101000c01408501e05001408040c009807000e8400300da00720603000e9a64070340500f00400f01c600100d60540710303100401c00380b0000c050400100842c0c2c180101280000d2400710074909060144c28400b00701d06103a8401d40840c40c40741e42250f9940c0340f10b120110300a1802078000001c00500308060380c041559402440c1c1401a58500050b0180c951315012600b003070740200000a59050603c9510034260100640c1c2e07503a80c0244001c642c0c004030101e5123085224118085500811020502041140010b0b004c05080c0a0034001c00690b62035810340c080c0e1140068001c07501c41c404000241d40c800700b0003a602d42260f00500382001a09113100018140d5581c007076400c0c0015202da2030003060081e001810aa0b1081c07841c1c8034203080d41190046402100c008001514401701c5202035a15a201048016544202030200400c40f00d803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 510120692 1250 510119442 510119447
    0x20d060f020d020414030709050402150a02070e0103200102062e120c030309050603012d0f0b090a0b120f0c070203100c0807090b030a15080102121902040303020d03090204020c0d 78
    0xb11241c440c000c1c0301c0c00e40c003c2401423080c81090b028980041035030805a44402203800c2d03603440062440c046001d503000c001581107024503003a02075031040303941040500801660440340281002000d04542c4580280002d02c00710b45600c00c03100980f24088000100b60a00482414400d503001c814a01022080c0506002c0303030b00310369403d6138440c4e641d41102d42d81d50801c10174580402e00581c3d8200030120010803c402091340a41540080010086200c640d94a01d201c440e0803d40e11000703e40d10001441c111350315058401e0005014120206820100440c0c4549404c0030000c003401018044103011681c9000404280d41c0b00d694000d04a614640d101c1c40c5000c0601002000038010992a4020035411401a54000f0682d21034a041c642559200c0761005d01a00511003108041049000302103201c90080c0000c00c2070b14403076540301085042000a641d910031025908880c0c0c148103000500000b40d0101c0e10400100c0c072442c0104040c601800018003d205881c0f006800e0702c0b0303d0340022103054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 510121942 1250 510120692 510120719
    0x509071401050a050c06271f02031f081c090312081e090106060e0303030f060915120601061412060105092e021009030e120304030b0106050d0b0409020d060f020d0204 73
    0x110b50101061213400003900c440d40c8d2020010a540c0001100b100c1d5a1900c802d076000e558040104581c40d6503c2000c100c2d080c40c03110440c4c0003801079800400303802882039500003040010074114070746250801e10315120304201074801c2e2155410000da070700129503140c80464a00181c3e0343c005170305903031794100401c015008000f9441000e020034460300300c030301c01d40c0b502006480c85070b2407840c1000301c01d50341c0401700450b1480040c0510f4220075040e13001032098941025020a800d50000101030319410448003070482c0c2c006004040c10444200070011240c0320446038550011000e0800d00d440e00c1118001400403080c0d40101890000050f51303112030400d00c5486242046c50035000c0d90100c807009207000c02a07a504403000b5011401c400c003a03910900300208a0713498134140340c0942e8102500c903903840480d00801c0e8058070014002181d070b1100c020903480f42100c1c11208980421020400364082035070325800c043d02030600f40d5692210890300c40719804131407070315000380030440d642c90310b41511700181e8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 510123192 1250 510121942 510121981
    0x60f0f040e090a20060306090c22030c0e0118110d0f090b060406080a140321090c061201050f0f0301021903140114060a1b150509071401050a050c06 65
    0x30301c1c04559a9210004c90b011030005001e002d0601e1613072880e082c808001d5001d0455582d0308401c0140c1c01c8481c0d150045007521030010540c91603d60701e0f5091072081c1c18101c2d0480c070310840300100100070405600884001700120100042511007511821066602030b01d0080303015203041980c4d407143c45c51554842e80640d4864040302079240c0f00c20045c041156101e0041401f143d0100c2140c10110348070042d0a103d9030100f6040f281350820b031103014603001c0500709200640d40041014041e04140a00180c00d94103425510a810960a210080980c0f0810721645024401d11542c0c2030144d207820540d00c060210280096641e491001c480307209120800403c940003a01e8034410000d04188844454100d4496011f207841c00030010b010807d46922036040d050501c103644500b80b08000041040352486400350101d0340040e1054116402a2080100b051f4165000a40140000000101c150b0031649080c6016901e5004a0005503424400c3c0700e03034444284141e4040090003501d0004200d680d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 510124442 1250 510123192 510123203
    0x130302120a0309051c05180303220501080f0f070e18010806191103040803060109081006061d18100803030c0705010e0d020309010309081b2505060f0f040e090a 70
    0x680c01c17460784100c500d01c00e00240c940050810000c1600701c1c04080c0c03d00600140040030b580c07a00c242c02e031948034075624072101c1d402d1404030b24100b08007561b000061554498110a080e24140c03810310b40a0151120091000003805030744107194452b0b85600d568824004250074800c0c1041d61142d055658401c4116000c21114010350746491030114140181201030380142004c904603192a610560682c0000b0b0101e030420980000c00076882000308800764400c034100d90002001070401c8002440581c4213042c0c50b000310703504a002c0e000d50b210048114442d40310341258008c00d481d03030900c0c0d03044103100d0351040540d807001000b03204183d070200c001400c503280f0900082046da0010002251541c86903c0201c0143c3c000f40112134a0f940a030b003150310700034400c4d11510715104c0c003a681c9444d040d03840884100c8a504c900b001c002e44800303500014903040b0901c0f0740300300050b14040c0042c1e40e62080400407840141c005c181c0c0c400e2011030707030283c50140c04249084d032941c0c94984c07141070761826081c406446 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 510125692 1250 510124442 510124453
    0x305010c020712060507030209100f030b090103080306011d03010218100f1202070f1a0703050612030708070f0611030f1605041e090f0e0f0114130302120a030905 71
    0x2040e4000a804822104000950704801c0c00c40e440b000c004080003013002060603020486c004466454101c4052001e0f8241c80f40c031840c604a01009007116002c26a56009000c403000520100d52014240da078801c0c1d0900e464511602001c1d00d9082542d4001c0b0030302d42560000c20807c40360622141c0c00600b84009588185903843d0f01c2c101100c02840080380300c00404c0960910410707002e06a00107002450241b5000f10f201911a81c1b02450702c083c18500e84852207004050041d8217916000d0342e81c002108861001c3c00c4d48180700e503d070302c92250740700080501000041302c100300400004082c000c40c0d007065080000380b004070b9080b440c40e8011034410120a81000010700c40b4010890800c032207629995815040c18241900b0302c9040f80011415030f06030310107650020b5180c150307009003a40500c0b1100042040503111301c15a10b40010381903000c00c580d0505c40500555002203200c3ca60280300d1004001c940030382400d0581c1411025040300b4088403000038201009a016003004245504c92000c680 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 510126942 1250 510125692 510125711
    0x906150f210c050d050c0303210601090e0a0c09180203040b0c0c0703030e0d1203020c2b0305040215040603051905070842090106090b120705040e10030501 68
    0xe4920100310009002d220360301e2003840b0b182014200718608620400407a48030440c03100019241d90004010440c8041101040000400c03080402680203070702800e1100700c03582407078151b80040c82d0082c0000202d5607604501207800703125080c0100180130b22400d071281d2a041c4440100a58011079099a81d080ba48000c20b5420490500311240c101c03031302007d46050b0b4110f42c1e046901c0c907000764900303a00091006031900030035170301039000e24072003925100160381d5070746800360382c1c2003405589031200704a14903010b40d884c1b80511904005100c600d858001400c0d5214800110840584080c0008880c0d000c1b4002c54030a402d540901c1c0a050218840c100c2005240855815035004840410000b00c81070081481d080703800052501c5100408180070704001220100510780c600f401c204180d015001da140107840c106118940c0c0500f5040c940206400c0c2040d1204900380300301f00900003103c2c009800941d040340304100f50f6010f00750824142250b81030031400010844c0c460b000940e4207521304407100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 510128192 1250 510126942 510126989
    0xb0102100f0203010618080c060702040b04020d060503190c05040c031e020901090e060f121e0c0901140306150604090f023705030405010b030a030f0207050409030e040906150f 77
    0x38012542c440000301a1001c400042c840c25411001083303810640b60300213002c09640d240060000354403e45000203030241f0b00310400d0b14061280c40150860078a800c00701011615007110101070b500d054a01150b4500c0c0c03040d007240141282c4d8001428624080013285a07900c6a40040c610003109907503542e125500c400110300030b0401500c01a40c00510b031a500210747c20f050002e001c1031000d04050b60500100c280350317103000040ba207540b072010307400400c0c4801c02403414111050142142e004415045007403400030958484000e0f102c1035400d605010005000d980340400c40d0701803e18428140007110003004190065000080d4208815a0100e81140511080d0368003484092900c00304440308110345000343c406a00240c030136540c039500c80c0030007003054404110030300f1030910a54a0b07242c0c00b070983c04000d03704a99900404d00c91400d11072507d000c6540b1910b00c21201000316000208480c1c140b0f000c0000703040c0020b00c10790521516074009000fa019040500c104d034030010b04c088911061403001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 510129442 1250 510128192 510128237
    0xf060905010212070f21090816050a030f15110a0e180601030209040216030f090603060e0f07020c030a2a0315020c03070605190c020c0a090b0102100f02030106 70
    0xa0b10300d101d0080c0500343c00704015080c500c000c46d001e803814030003010b103400c041d814454170821508045021640104500081000440182581030503006446030070040043c07800021444045c100114000d17440b801e002c105104071000d94000c0c84100302c1c807112242900825000007880b1804240d02e42c21040e064200f01c0c0c45840342e50384d886c506c4800382e0f0302c460040d0002d4018441c015081707036080c030800c2e4010b50a0b0540d000d8450290721070760781079203003524001c107560000c3c0c02c04010542004010451034584000c404d8020415288400b1140d0781c0600403442d2108030300420340d00d881221000410302450319420380c1c091600768030305558090600360508500031148002401c8041c09001d41c3c0b42080707554050000c159800c426070386004456261882510002e4406c00900740c0406030010200384284030700c181050043c00074181d2070340240300041080045200d5080c40303c0d11030341480d00320b80c428040c8007030003102014100720190810354610000c1d0002d0280368082001c900b40a0000300e090b890 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 510130692 1250 510129442 510129463
    0x30b0f090607030e03070209041a01120b0c0a03090219170111070f0807080703050c07050414070e040b0d0317060415090c051213021011070e040c0302040203010f0609050102 76
    0x1d080603190300a0490003040300c40d0a1300d48501042c010000145c0e20322140c603000382d002e5070b82498108280803030a800f190060348861048207506100d80000b81c6c02c2414541e22407403030101c43d901d4881c00034060b40a4002110001c0d4024a610b0080340490251300d03158064650124080c5241704603090903508a55520a11038071598051091400081a155a036803440340b092240c2d45c00c0203566501e40801d0f41040604034040743c1c000c03903103034050442001b0308001094101c2d0705000e06816580c0002c1d20751000740001c1308000500003104240c1c1c8480d0000c03060100c0161001318001c102d41801880c5244000044080d1442c110128982c0d107403c1c0074102091407000051a091807801410100a007103500e121014080c0c140b00d081e8401044c180110f12480141460440356549841009803000c6484408010b11180c07190342200c842001a000c03090303075002682c012150f1100c0c104041015102d034030080d442400000046006a03c900484045505984400c0415a168401680c9561400fa0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 510131942 1250 510130692 510130711
    0x705011a1e061605071214160302090a0605120a020f0a06050f0307021615020f010501030b13020102011413030f09050d0816020409110a050103060f3b01030b0f 70
    0xc048014914000740145483d40561611001d0802c2c960b03a1541029400d41c8060245e54103d021107062201c02400700482400c14005010000380b0b41800c106012141d0001030300400354100051000f060365030006019100041c0100061100784500703503501c4900c0c00080780560340f00c042d10b0f425418402072100607200c40da158241052412080000d06810013401c110441c458078440ca132030150491120f4000c1d0189805001034500780c48070180c80c01d030351000d00303540680c03500c001000071400440940750071246100c03414000c00c8031400100c2c054000d0a070a040002d1243c0f0a20003e040c0c4800c45000e000d20036158160724881c1d948058940c14490320449820118101c01c0c44005014100102108265940300c0841c0030b5194000ca0100d402c4403600b1140003d01e09130580961800031402c8000f02001d00c3c05216850030720b44070320500f2006200c0c4034200c0b0b03402c054401d5154118031000100c089000c41400054000000c2850440820b2000b0f40d001000d42c8086414624443e1002d4404c1ca000c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 510133192 1250 510131942 510131989
    0xb070905120709021303061a040501140d0311070b030f0603010c080103150f091401050106020712020d080a090519030c21110609100306050306060f130b040f020705011a 74
    0x480c43c00a540640c1c0302a580403001c801c080009461840350540701c0d40c8441c0254410940d5138280b10840781d040e007040301c45603000c1c01440550354807442242070701640361030516090040610305503d01003154011030701c80000841084880d08641c1d29192040200328000d1210580840058400030404e0002170109042d24119522074581600309004a00040d20b000858141944484065130400e002d00409651242d004003c11641000090090403040d000e4006101c0070760b00103168041c4040d001030180002180c40081d00e40241c000400401c0082c001844600c82d8071400d00702c030310b16400121405841140003060702c140d04240180410392103195050f10650301c0d2145600160a0800769500c504200416800740e29030b9560203180202a0b24003181e05424201010b04100d03008103480e005440f5403a47c810140c1c0c6941a41110302159040003403003c1003840810040c0c003a51014900190000820300104001507102019140c0003000e6544048140c1080000031684400307400c90308501d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 510134442 1250 510133192 510133199
    0xc02060409051e090c040b120c0d05030405150a11060709051e031e060610090e0c040b07150513050c0103020904021204210525050a02030a0b0709051207 67
    0x1198011500008003442c2160b8800024050a608010841d640380081e01712803550680b600381806400031099045985400401d44c003090707070b80e5910b0b00440351482500350402d11801d020041c030494000d00f8020700740b40740408142d8403030001035007c0f002280c00a0300c1c200c0000c0b2103a1010030114040e00759580c405915600c0d00e4104003c1803401e440c460526411100300c508103640403c10500004903c4d03640302e12100c009817000c2e003004030040034280036201442582880980c0620200c00b0755030320b8a0504034a4850009810090049401413090300c0ea000401805100c0c1d04200c01010561845c0117002075a6107440c0019139291b00400100158003c20000c485580290040d100c03d400107040141821501511207030441000c0c0c0307096480341058042c0c10014800f0b4441c951031007109040403490074201e006448121030f448a9020124104d100d4020108841400b1020032140c005044450858990074484c3e0640400d40f40318005c1410880b0003d2141410340f20410544055000b6100302443e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 510135692 1250 510134442 510134459
    0x61003021314041b080f0c100c0c3f02060a12020301030c0f0b071a0c0c2d0106050108061c02030a080d0b04091e0c0f14040605010c020604 61
    0x140d00044894907078548807581c071800c203120302442c4103034003032120312504c071140742d84559292480f43c10200072a000f50b60003002441c0c00007000c0c289080d09449070021054070040480d1107124000008054001120000905058516814581482441c00940c0313200ca0400300c0c550440500c140404180554040c860240c40c000025000c0c41c40d107410031040c40944221400102da001341c000b150600d14404007845010200030000000d04406400149080c54079240c0011000d05410704c48042d94440c000200021174640541d2192940e001c2160780d0545400c0807030030341c03400c881250752410703000d52002550442c050241000311081a101d016044d2104020b024294503e40c0d00c0c0c003041c01070384248600680b0200300c910703a424000c80c000b5072074103000b42d8018295070562400501c1642031a0102001c61813225050b1800c03503020240669420613807512502e060165403081c1da6416600000007001c42c14019100e0301c04404850401c545a243c20055038000000400a5000101840240906c69 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 510136942 1250 510135692 510135709
    0x60e0106081303050c031303050714090114220b0f03061006120204120807112704030c050d0c05070e07140f1306200d050a0f1709060105030f06100302 66
    0x1802440c21902d41401e00800f240f640d48880007a08a11521007000c00c107210040c00044007920907c0800d002cbc4071040d4000610b883c2060149551007866143c11060540d1921310320400c1c1f125102d03034030a5011008440ca0001c0240ca52014003079050005124003d140201e4a2442601110b007850942418607030f08a815030300750545200117640c2000040345042640445064440c45031201540c0c1c0c0a4500c0c0060f202c81a01035140c0c000d2200782403c10405851395504010926803083c0a02c82d99105e040844039000003010252190003554407050344268002104c0202c80c0c0107000300d50386550780b030840e188401411a500d1000500061060350800746c0480284905d010300c03000c05003420020602c44880100c01c1d4014004240d05e0786089912815400301c0c1804821781c1805450410703d10a0082c003144510140b11040064090350041e105001e82c50802b07290410702048801450800710490b6582428010284a4410300c501029584800150a4481d80003900700040192843d403e004400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 510138192 1250 510136942 510136981
    0xe030d0b1c05030a231e071709120a08090121050f06010f1803020f0607080d0204090510080a0308071403130204150b030105090402040b0907030f060e010608 69
    0x101e500c0d1502500025075019680c061406040070b140e581c3c80d14031003e000c02c1c82c00714090700f2031845904a05254410f04042c0c3d03080c4c00c8071300c1e40b0490000483d820056584a8070f94014010080e14408030741a044141c09000020400d840b40381d60607000800310350343c44a41c2d1000800c0154100f0200e081c951290f041e42e011070031014000480565200178400540700110340301c000c2e060341002001043e69014000300d050f299641010140010080c00340102c42c1e8aa00001c1d0244070a101103000c2c0d070f22a80121803150f40c01000b00c90712a411010302c034001c1d6004e840b4400c00d080c104070200d20325407110b41810040710450303070007402c000105a800380e500e05001080d0310284141101c004a000c0d800f2030080d4459444055140190919441080200d401d40b080403201d0f43c104510500424a41c1d4044906403a0200c900c102103989900c0000c7c06010b105100d1a0050709500901ca480303071b09500040e203192200501030090b19181c0d5403103040c1410034410303540000d00c2c540101c1c0704c080d401800728142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 510139442 1250 510138192 510138199
    0x5010f0e0604090515070806040b09160e0609060a08090d0504081b060f0307021501060f0512061216030606090b09010b03130b0712060b03090c1306030b13060506040e030d0b 76
    0x104505c14510740403001c003114090085003d03d42080000c0c9443c1c070030110304400c1120890602e0411980708008084121a10341c00d00185502c0e500c40c0f50303070f0034090750384000d801060142c6c1c44450b2540207000c030f4000d56120145205400d08038030348038000d00540701130384c00c0d500003800008511412014140c0e03a8a910700d0b0049000c11003120110541401144904040d0f001440002e400114004040c50f05922003c01c1015103c01d503480c01ea0f01000b2101008040082d5202c01d484d0040056076200e0110f02804a61003440300004104000321a074400300c9000d11000c00c2202d640b502d100c0c007521140c0f10b07050b0b4081aa400180070488480001d550000c1d40450301c000d03841255a40e000800c0c000b600c4000c042404043d0310b40705239045010303002c00f40c0086100355066040c0210213541c1d90b0b80c11801d082c03080580d08841001c0c030f0226030100c0011900251064010704040300c10744449212404180d8101e41410001505030416004401070821540c0043d450050b0b42082200145008210f2951 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 510140692 1250 510139442 510139453
    0x307180b0f0d15030f0b130813082e0b030723090106030b030a061107050a060203090f0102040f0506070516060504060f080f0705030c090310050f1b0307032d0f05010f0e06040905 78
    0x2203072902014040100085d881d9554007403e24030300702d140104072fa007041c0c100c60144500701031003042c0c1d0001030040b500c800e038007103540d0301c9500001e0300300800f94100340310104200e00c0c02c20401c00c1d04842c1c0900c0da030055601d01c81903620f902e0201d06031044940c40c550140d01000244c2c000800c04e601042140d140000007604020890340d40390b003842d40c248804e03101e00e6004000d2080c284014052040c0d088078860003140780c42c2c03400c0c01e04400c104080c401c2611850004c500300040c130105121181c0281e441528450354940c03115030203412a0881d000c0c81c0c0000302c1c40c0c022411080e0180005500a00302c440c611031040d940c18900b10f0300355000a0010044000920003400c140d2810080700502d451103644c040752030700d400c400c01116071130300402c14400300103004072a00450b15070004580d00080d0f645070101c0da018206040c203c000c07020b4944584103a0000300101214046580320003640c0c40f61410501169a0344c00ca100c414003068080e40f0390301c2c01c441c004030b001843d2645c080f4600c0340c41101503d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 510141942 1250 510140692 510140731
    0xa090602181212032a0a0315091e0b0103020c0d0306034d0406080601170718050a2a031401080d1107030501021b01050c0f0307180b0f0d15030f0b 64
    0x1740d00908403071408648c03560f100080c1c6080c1b01e1040405000744102c2000710b880034100e400b44021407141a01c040340d581740280302c09640319804440c0c6000c0c0c90401c4032540a01040024002c3c600f610007603d4840000c0305040320407050089803200f00030030341902404200304c24080c60040740c000054111110715040c031880c103529079000d00d500512258010300920362501c074118617450000380c02c52280303030042e64041c40601d01e000514001540c411100240700e5032660791120092003203030300003600c007140c400c40752604240d205c420201e000c4060f40d05024084030070220b081c200301c00f0b006d8070758250000c0210003030305841118580f01c840f210100700c038000f035544d8894908a034040c50b28050b10040030307a03800c0035091090040940102c50606082d1603c030440d14007684900024144108010311500c1000180c60074040280160420396003c40c0c2d40e601c05502c640b62a481111f50b03002071800e1005044039001a01020800c03203400c02900884070100d991455803480c0300074490100084003840d180c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 510143192 1250 510141942 510142021
    0x60306040b031606020114010503010207260705060c0705010b040c02071a070b090115080706050d022107080702070905100522020c030d06050d0f0b0a09060218121203 73
    0x60f0001c25003900001403450350701d080700c1001380b0160400c43c040ea004204003c00200b49450006a41180000300c0008504d1050082003504c1017a901600e00c0c170880d0140401910f50034000c0040c10310400080203812108070a110030f845200d0300c10f00c09038002c2c0c0410407030702e1107a100418039288820040d6190035a0380c1e0f14103d108100f6101c0b081540e544002030f8100c105030001001c06081140028018249000c4008100348103441584d003030036401050114080142c142c018000e20104450b1900610304410014441c0b070307003140c40f5401840341e0a40040c14044500c100b5000d508081c250701034050400b8180108059442d547c0304c807007021034500b402490154030241c80202c20000c0a03541d50600c1c05021000d8883c03640040c0d08c40c00b110444030000401e51400c4030306096000d403c0d03610950f01c2e041010018040b529000e04581d00000b40700c01c0440c607040c0302d00c038561000c42c3c9200744c040c4402c0255a03682d002d111251288941000400c0b1807031504046d00090013600303840700c980883c001010303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 510144442 1250 510143192 510143233
    0x80c09040218010806010207030b0112030e06160c050f091506042705160e0f04020c010c030203160801060507060b041112070806102a02040501030b09060114060306040b03 75
    0x30021000350307008000d82030f5a07000c0903076604540e00748024007240741507480b0300c8085101880f80c40c1030224030713a001c4010540640c2071b12091a00041600e602c40c071903a0920006007401000072903100300181c2020895140c842149400b19a028200d1245c0e6070b101d080d030105c00943c41031700a07401030051000003400c5d0010222550a10004418410800201c4940c501901d0000d050b600485c5003a201019005500411034414040100c9076803490a8440700450000d00c2a900030440950800030048031881e0140c005601800030801012101d50612800301d4000070b00b070040310000340c0200aa900440e165070040d0100c0e07640100f0000304444110058a0703583c0c0880500342d00700c0311910030002150b8112100c59849081aa922201414040350044c03200e00207182d6008100c1c0c002e041e10172342044001e40c240202d9809042003103e07507101e050020404c40c088139110001d2007004008654500c00c5258003245e0003014003418110346400042201030050074104581522a1945060359804100074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 510145692 1250 510144442 510144457
    0x7020a06200606010f0c020120010e07120f0215160f1b06210b041d1c0c120201200307030c050f04140a0b130e15030d080c090402 57
    0x480041d4081d0400c035101120103409141030203904100d04001007030760890601c549046103407425180c20360380c502c0162407501640040c1c1d2201d41860711000c07000c1704154018503030100d9842c101c918043d81d41040f10317005a50204010030f0403942c0207440e4010309281461454000710300001c9400d18002c00d00c07101450b004014181e404080121480d41030002031042828812101c5c40100e070124146140a00450184205803003480b9058880c0c0110406035031011101c80401402400721042c100c5459001007800c81d0550141e0183d016101d14032400c4803101c150f090140d444e01510b5000710789504a4030300440c0e2203070055540320200702226080e5080c46011000e0300300c11041e1a400c05000040c221600f0344611802d104040201064004030f038001e8404030b60b00d01c000b42c2401c20711b03080491028922540540034543c00441c16850008428104a05586d841103542205907107070345c00007000b080107000c280d4268001d0f84d01d4140440c89850f245601180c3c900300c031407614000b1b002080403070780501d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 510146942 1250 510145692 510145697
    0x8100902030f0f010f0605101707020f01090c06110f120708040e040b19060506090910030803012d14040b0103060f080703052415010e060a12060b0a020a1707020a06 72
    0x1805d00070001c080c0305a001401c400d4400d80200741c50004080d000b44409030607946402041000203414910070000002c4d003401b03800003402500a030b85010fa14403040d602802c40860280c0c80e4412606100041c1e81b016040390600a18040e02c4095810b00075900c8840191089002004007080c0a40d038408424083c600c600382d1034a07945806840555607105401042d42c500b41400d500708615902c03c01507642802c8100e91204d029250407416078440320203940002d0180d5004800003c282c04409645207040c4801184d07401100d010721a2109450060f01654960170306c011403048050030b159024459580e018100040c215071108002480b40980342c0c008074042c0d006500074010070a003440f003034006007942c808200381104082145016150010500740c0d00c07080741504280560b2007010081031200000d44050b94038140300d400101079100040303025207298185900010800100b4045810040a41d40902064186039070388440440300b044004480d6582440000003680d81c100000340105450b4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 510148192 1250 510146942 510146951
    0x2031216080a12060b0412021905090f07020d020a0206030403032004091e050f0f07050f0712020f0a02032a041a0312090a140301140f060f030708100902030f0f01 71
    0x43e5031460580320f16801c1075200c11070910041200c000c0e40340c80381202070740c100c9039400c0100801410820f080341552102d80d0001d0345009003e101903031003260901491041e0b007034640254150b1010703a42d841143c2030081d0003040c20400a00030078800c4c2d100f9482002c0c000c0f43c40f001c4944001240400d038026402005c00247e4980141045910415607101200320182042c4490702c1c0070a08000b04000003030001000140d200b0026031014407600c122400b0f2106000055104d54031f505000220301380750520340d0007502c40d1003050818035400117074a10702c40394010700a240584000e0540010160010074058900d080100c07414035503035403400f40c1103448040c01011030300035040004141c500b05030717450011507076241049040e070b150700d0341c00c001e03c00e0760a0405018041881000481d00406289090b03c50701a186014405039641c446681d5003d10012583c00104204040c02c2544a03000303445a01407503400542401c0c00c014481d00302c03804284c001803e030340c6800d1400f40440d040101641810a590b50348 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 510149442 1250 510148192 510148217
    0x302010c030e3c0306060d08040e071806030e0a080a030e030309030a0806090c160f080c0d0917070536160e03061b0d0204030b06090c0702031216080a 66
    0x10308440201400c105003c2241e201072012a40307520014101c103000d132070b61840e01d4041c403155200f190010422500c3c019a54649800010200325158284108100b8a0b50340001c6141c40b82c065003060200d5000079052200c0d4590300c80c00c0343c0d070101c040c100c181500c0c1e8109050808060000d94810340041d4040c554944c6400310040009074000d080501c5440000140b24250044c03100752501075040301540040401213040c007084140c0040c000410b540b200154103980f6120205402040324026143e00080c00c0d21038442141079109116507030480c2d4407840007041a0b03e003100ca4582540003400c10080c5a40317050341c212003010b905c5d4040c01000d82402043c050f00c0209802c10303541801141c5440c116201c0c0d044000390f101c1c50040c103002840600f148130300649801c40000c407408044541c00441d030321a03a80c98900c400d070a049444a00c141da80e500007808442c011000ca4998541c0100a0018003445106000c00c64008d44800914180c120b915180061950801040110001c0c0c0320303100074182 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 510150692 1250 510149442 510149509
    0x10060803030414060415020c0c0d030f0e0a2706090c1710061d19090603030201150806060112020906030403091509081e0a08040f180504030503010302010c030e 70
    0x42c07280301e43c5611903010800400c004180904e0041b060800140e62018440225450542440707901640000c04c520320100301074009140c04035000340c5860b440701901842d000c02050b0704e130301e00c00c10013221074070550800314a01c045009020341c00140b500180e201d0315030704200d0403510600315450100c1d0300c0340c40701c0c0030500c0200c47c110352140b0a01035403901d190030010020152200c0c2c045501303074044051001c0c0e50a60707807040301d100c03414031104005080b140e071941400040c110510094000d94684504026802181412801a82e1051004100d191140307401192800c001204a59a030f84c0e081c000c0250380e969610045001d14005d039a00c000c454205050281251070b400142070038014042c40c10004030001142c450790314183c1d405041d2880c04010320250518405190080c6103030000140031904021420320f160a1312185000c2c200740c5c0035030b0185d2100300d401c141c0e4040c010030307000d000401c0158843d40b81c195185200b4038255001c8054035011030b01e518020f1a100040111041c9000b90920 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 510151942 1250 510150692 510150713
    0x60b0409060f0e070509010e28091503050c1005040e09030405040605030f1b030f0109060c030506010f120b0409020907091815050d1704230103051501030e100608030304 74
    0x141040d450f81a9080990000d0018800c8619250600501035982241550389544035460000c441c07200b84104840c403607414002440318003072104018904132682c505900010078000549034000024a4030380140010000c45002c3c0c58030300c508125080001180f00d0100c0901640200d0107070380115103a80c1000100026224a600014026401410710940d60302d80012018032010b0300e074001e01a008681e401103424840c48260600d40c940c00c0880903010485c1d00d510443d040340c0c455604102a44403980119280c0b044201c000001413004c1ca00c4121220881c0d03c60005000002c0001903000d4503503020a514810440d641c40100309031310340030041100030280c040c1c28841e46550400c1441d0791b4403403c0d22006014010340d4040d0b2500d0b0186c00400c02d4000d030542920740b01070340c00c3c0e44550390782500b4100c440908030914407c5c86100a50311065009000d00c50284214174050210b41580000450040c030b000f088a0181f885004040e44410302d980c401e150103450b00c0f0b0040c1d5601d01d0141006400c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 510153192 1250 510151942 510151949
    0x509030f0711010f1d0d03090506070f0611160305030c0d0914120301050a172d15010e01050f010306052d0a1a0a05040f06200606060a05070303060b0409060f 69
    0xc500c5d0b10a0014074282d2101541c075094044904458030410350400f121590f02d00d41005070040b200040074010320014600e001ca80070721415090008240ca500200140e002e01c01d21060348840d030a41c200c0000780103030040c55005034108001c0b41842010861030041d583c0c0c880c010b6403001100e4040c0c1d1500401448544280e04002010707903d594544000f04034240c0072441111401003240e042c1c40100361701403022502000c20005020185003502403080e444010071440d0134850721401c02800440c80641020a0403201742081e84103c1c0da2a00040c02910140001d0090400d540c818010505903507403101070b003108142000d510000846600401d03102d0020401c89031080c07401e00070400c10b10350803108284c03810807210600c0761582d1070382c8411344190045070082c50700c0410410010424651000b03240e12075002c0b030509007607051200303001282c44213016110641c0200c0c0400ca20891140180000c0150394400e26000982136650040c2c02026005600000074258071541c0822125928000ca400034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 510154442 1250 510153192 510153197
    0x607200610090b030f210f1b0d080421020c130606121802060f07140a021003051608060d0b0114030d110a1e080703110d0f09090509030f0711010f 64
    0x18201500740396075410107507080d0106c01e9a8201a85001c010310281c403585401d00760419280c100802840e404058548041c83d554480c100500e4000c03807103041001d0096800103243c2c8984041c030311042880c105000c1481056120340c0014446988890f01800e0502820342d100044041c14407000800d03040c954a50b0160a80c10b0000c130701e40020209800100040e411500160b4441c21048804018061560302130301b0a20481d013a0407039501302203101700c0940d20072103070030085035000c9005408441041c0d5101885c40f0310a4102080c0d280902c2076980c000000905040007586642d607000c015203000d13084019050f211144c00409800c00f04415102d00314103003030080d031141c0c40f80807050b07903608550405040d48017409544840905912031048140360020b4000e5a00d600303a080c00b038840b61100c009003103180300c0c0f641d49a01141c4640340b503071600861a5100302c0128548512171380074007006400510180403c00c41084e0142240d4020003000e4070800c100d2007210400800501920030b2000507105 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 510155692 1250 510154442 510154453
    0x12050a0c06050c060a0203221a0615090f1f1808010603120309060902151308010506100806060c010606020d030516050412030309051009020f030d020607200610090b03 73
    0xc2c50240840d01d0750380076a02c80001a00c9644023001c022000030806d80d440d03000313520f0100710028001103000c814200810104110081d03200e5001b4080405280384000c2c00511003885a100d492414290040310080c00800e02002060f4150b0705941e01c0141d4a1400d0200701c0c8546044c070320340380503c1c00c3c0c070050002400810580d03145440c0d080d2592401c1d01090308141c0d640a480003003110390786c04840c0942d006072071003e03c501000c44468031640090b1825454800c0d201c00080d12100c14007403648108005002c0103415400d42c0810340c0c2203100900341c40c2e4498018011440d05040912680303006010300d40c02401c07510310340740c80502112000b4010780351004540d0780c0a86900e0308001101c0c1114004c4190024400c16400c04500070700c8140030041403401108000d107403588a64001c00749550080302c8001e00c10081340308040d43c4000b100c0104c0c0140e002800002d840e40d00801e68202c07003580c401c881a640c045410340250030100110f03012080b054034280c047c482034000340708807502c8070010303002086e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 510156942 1250 510155692 510155707
    0x6230907090506060f0307270b0c0f0706120209060702031b100302030403020a020112021c02030105031005060a0303110a06050c070606120c1806051e0f0d0305031f12050a0c0605 78
    0x881c5c03484020529414804003803e80f0400d00581828010340300000b8081c0c20781c00e602c9440b65080c031f078003000d2017250b07034032a4070f0132070b40401b43c049040c40844095482d804843e417000051800690851000c5c1079005009101150268406100900c0c3c0043d41906c00e00c610902081000f98100d10068039000700b61051040000094000958422550702420400004000c49444034040d101c2d10000030307803840340c418080315001d943d5005181640c0007241901c0d01103203000c4488040307940440703020350f12401a0b10b04001207030241d5071913039a01c0950fa0580b800c40e00c0c070707413134030001d440c400d4030a00c450300d070b00141240034402103224010140c10341d5240049203105640b111211800341d801410610340b4000081e10031404194001d400174940074240005540c80a13038140c808240c150355140c001ea080614501551070a00100c404007a4140c4030603055480d018070032503038011006000d4415250108012a02c501865010b44c00c49110b00d004000b45035903840e110041e0000b95110a06002c030521004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 510158192 1250 510156942 510156967
    0x40519110108040f0210031e11120a0e03070507030b2d061306060206310602092b1b1d040f0f1227030623090709050606 53
    0x402085030920342030740340d502e442c2080b00ca030070071981009500c000c1d031031401c3e06401e406800c0b240c400440366545c0c801036583c00003c6010340365614039044508004004512407075646501c1203402c000c6010002a40c40c4444c2016803550f40446003d036166441041c1c10000c000d11514402c0d4020301810300c10320a140c41c045103100780e40d000c3c5c4c5400d80d402450b0000803169100e00c04404010812040c0c1400220394800c000b0b5250a01a14902c0c0050031004120545420413954000d00300740c0c410340c0740b03025089611410000d40002da2446e6003c00300c010960344030205150030f81660041111410480c43c0c0030300d40f4070203031a0341c1c0110804000c92050204000c00b690b0004014282d002c20855075a1364a81c9003075000c1a1100c0c80c000e120520b00d84402060045804a031580707400b1a03217030803400400d610901d203990301c00151a010840380c142802e000094958120341e101c0c1c0600c400d04011051092140a80c0200454130301400b54410082080007540074003400390408010741c2d04a19018840c03042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 510159442 1250 510158192 510158213
    0x8010c020a0210050703031401060e121902060706090b011410020c01090515040306110c15130204110c10020a0f0302030c03040b0405030c030a053a050c04031505040519 74
    0x43c801e0210203c1c5400901d806034001445944400400620540c0c42c1d560280c400d9020680c56802008880590010700030b000804019008115030a945980d0380c660030082694004001144d000e178450403900005183c1f01c0c4010301810b5100700c1c1c441041a6142801002c040c0846200210340c80450b5402280c1d0b041542c280a070b48056a8212024075400040f0310f15100d070368401885c25203400c4040400540c11000fa2049808010540d5203050b811000924082e40c1501c11032900149081108018605603200741561001d040600b03040c5041d280c2045d0401c800b950302c82282d01c0d00003038031070389441e40040c000c8501d100c1405c00b1821401c2c111101002c0c2d0100400041c18901504048dc05010b0704005840308645c0040442e9900c24070140002c0c510f80001040710001c0d000207403c46484003200c00d1143e01c5d02c3d0381682c048102d8071030700d802001030500030f000244044001c02c800300114131040b41c2d4505c00e544807000440c503400c003842c03d01e2034005017000140481481400a40c00182205403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 510160692 1250 510159442 510159469
    0x2070509070810090f0b0a030c060306080307032f1e0d020706020303150a0b03070908150402030a0201030c031e0e0601060201021e0304111806040c02012717030c0408010c020a02 78
    0x80014108440d002445d0040100c0441c1c1e5512650550b40001001940028039095940d0f507a81070108a41c3c40e80a16628000c0e058010045205546d81001010940861181c2201c1074018205c884540301c2e800c0342803a201641240c8070400300d4811202d032000404c041c20b4002c001748010070030f65151550007520f174040504003480300d240300c805209140d56072207841e2000d42200c1079595600e081c1882c0250034202544140301c0c80d8024440d000c0b4016001240c242c0c46260040c02500700504198011001041c035000c400d030a055803880d580407152001386134401032881c001130000d5045a04210039107007000503800b05d8110381c010000b0030044034000a038a1a4208445125030301d0780c50384d2030018003112800303200fa038221081644000c801074026086038000c02c400d5504111000b2959012800c1e6131107121655444604100e2581c240c00604070240c18645c05600240d0107054056080310155009840f403003050710000c281800280c10a214a6aa40318540014003802c0015401700d18054403480 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 510161942 1250 510160692 510160709
    0xc01110310210c0e10080d090506090d05010501060c030e09010803070305130803131d1b0c0a150b011103030f010902030711010c0306080d0306031e031101060602070509070810 77
    0x20b90082c2400440c020082d081d0b00c0700156000720745074905865040c3c411103c07500415680d00c8000350000b03001c260710142c00310310354461500303d0610091020582c0003070400780c7c0000f12249100089070302071003100d020b0b202d955120301c00349146040051902490303505003481001d0650040020741d500008440344641e160800a07203c01010b00e142c2c401d066540d04c140f446000019078150142071614008044c3d428041c5180e0765a000c0c020b1120b00034004882c0c107520640a011290012001c40001d030541c2411007045440d400602d6030340c8040a50500c1c50000081d464001040c1c0c07940c0c020712902100380105005500310700c3c280018104602041c410300d8080782c1d000012070f54207445000c0d2102503c100390000e1106c40450701004009220034450900b00f40100c40c1074002c0c0ba8801c0c0610400c8031f400c42d290f10480300c0c02d09079882010003002002c07414400345000403041141c00f8028013008141c00e80107071404600e400180300001800900c00030802039100308001c039020342d612142c0181c80c03c1c1c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 510163192 1250 510161942 510161969
    0x4140a0902060d090b072c01120b0d08040e06091e0417031009060602031614070f09050405060f1303080601110f100c0e0d080a1209080c01110310 64
    0x41c000b00c1d08900c64a100319114604001c949414400c10030110350041599645180034181e44d00404e80510001c90384900750a1040030072211503610401c44201c07440c99901c000121080140001180b032008100304444404021404114050007510543d134004419103d204180c41c002d881031b81c5200542d140441c940700f5113004201400b10034400380240050307100301144c1d01e0a1900d0b1010070700fa290b20800c0c00842c00c107080441c4403403011064400d810f120280a03001800d2a50720000c009491100c20320032445200000201807400c003160100512010100143c2404c06090a03820058003c00b00d4403076910a00a01480e03042c490b281c04601501417070100712039140c0c0e00040760003c84007011880e0074801d50320260100180032032910708843c80301d0020400c50400c080160744d6100d80c00070080c2d01052159107040030806c15001001c1065041c034000300342d51011101d80701121400c1d4000c2d9800c0c2c0011940101c0d0000911841c002c04510342103280c107510b041800b40b143c218050003a00d8084103903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 510164442 1250 510163192 510163211
    0xc0f01031b03020c03043204060614070503160c06091508011e0b0a030605031507171302041409060a0b06180303070203010e0f0d180e0402130903050307030b04140a 72
    0x117105442c043c1039541c0750551103205d00f0364000150038011244040343d80c480744218080c0e19113480341d074080ba0100c0e06c4400108100100040058220700015101e40c08200306c2c2655040c8000d20001c1c2c0a840354804048031410038000a004002e960880d4060321284001220215000f42007d170444049103100c0c1d00940510200480c0e00007550b112801b03220700440e04008d1103806400603400e984082d421a4140311a05001107100d81080e1488000303d4050032040582e841c581406680c060000000d040325801c40740d020400300c45402200e95038180c03110052004000c400d02c41c40d40c0041001380306021902403000018814420712030411015102044100320320785081c03042d03030442074004000304000b15505640c26200c03985030020301041d0180d240366030400c50040c01480b82291681840d08400c50074240603800b02580940243c0e4814030715542015407005901821035290722a5071000d40340c3c01c01c218064142c422501e98288544e04206404c9101d00e804580c1d241e212401101c08507003000c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 510165692 1250 510164442 510164467
    0xf06011a0c1906060503240705030709080601060309110f1305060d0204140106090b0c0d0c020f040218010201180209040b0615040b070b0a0b090609090106170c0f01031b0302 76
    0xd2a24030b000c0c000000801c41803040c0d6500a90495005505503914011603810562a00d186c46680f021030f041c07444045407415220f1405558040414140803140c20b46540010b07250620980c40040080d46071401d0310300300541c00c200c0195086042d182015452484c600044600c129068040c14459541d40040d11580c7e5100e01c032071500b40c02034401c100d0300e04107450986400900340140303004140600c000045007032643c0112031303c5241c00c0d0041c04a40250100031101c24524000590f84202a40d844030429540c03071000308891204202c00400100a0100290075105400003500b100d881d9040444056101d0302c2200ba4080e606c00500b100c269070750000a031075406550741c410345104010602044070700124004281c241e01810080c4c0300b0390f6414081c0d01c01c1c1c0d5000084540c100e05500042007041c1000c800d20b03038008051400110704551030303200c084002c00d907040c482d5800d9405000515010704202c81d1148983c0001e00c1c080c4000011b155a0712880b80c13408018000b0075070700144585000c0c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 510166942 1250 510165692 510165703
    0x300f030c1709160801020d0e060103020604140d12081b13180905030c0d1202040b0703080402010e030313031109090303061509060412060509070e0601140d0c09080f06011a0c 76
    0x15041648110310f0798030b840d2828001c0d004a021182c4445c0303803420300158650002a0b0a040740e0f8000c0c00b8078038141c182100303044400708500201e078008501c0c0da62000011444858040444916691100e1624000d000802e07078001e14402c4c10b148041c108000300c030f8091581298400e8a5070000400740c030b00c2c00708044074018101114082c281d80000700f0400605c480200b1a0320a40a240e602d40c00544a1084000f00724801e900c65900c04c61070400140000034000c1e000d8560090050500b5000380d0b1089000c642158001ea50620401c07141140c1403080101e02403a2055480e000c2c0c03040e18540c606207060300c0d5a444054902031090a44110140880ca112070072550300301c101924981d21542d881c9148074081c40c0755407081707520504082c0095800303e00001d2810803142400d10442507074441900550788118200390000000c4001c0008000c41101c0340030301401c012441e501c1101c2540b4011005042182c400a44152500018010002d2004442e1032008560381ca50302241c0e22040030307500900c1c11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 510168192 1250 510166942 510166963
    0x30905120c0607080c130306240e0702012004031e0c0603020d06080c0306070305070c06021201080c0109080d05131706152704300f030c1709 62
    0x390000445030041c281c042070b081d0089402ea11400003e8482460051040c02016613514840c030b46581c00b007022079040d400091241e90003042002072903c0300d07c00000c0c2d0420641180803591046010302a107035609204a0342070006540543c2c500b50792446503050f40b44914070001e00300e5111201108090041c1c800318110b0242c0c040c0800d40050340d18000940a50031151a04036060702c1d014001501000103d8520300b4450010040c18040d0ba502c94150010701010341030f042000507405030b03000040e89500c014817207640d18000d1709200d90f141144041c41d045030744070a541085a84101000301c4a000a60302500b40114105140c40f284403003401e586a0311240d101c02c014408011020703070100c00201b1510f001d410901446103c070032030031092141165000076495141900e200012421a40f602d882e25042480360415100c0b903500010204610003000c000c10108450010401d00e0583d0030641d84900c6841130305092101810780c0e0030150003101d40c8070380c498406000800251030f511003400001c203c5d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 510169442 1250 510168192 510168223
    0xc150e03030f0106020601052211130b07050111160605061f0c0201090501141206040e01022b05060f19081e06100509011701090b0f040b25030905 64
    0x1070340b408941d442c0c02400d0a00c5002c000d809000004030304c43c10030040c820f20402c24840b60148c0c5500d001420760081a4808036804c3d91b0206000172641c11100c0c10141e0003c0c164524040d0302e401c901e04100b4211140058044494a410440b0103036071010f207a10414210781003003000400e0341c0c900d4042030300c40325140903030000000c0350f09410764690703042855024454002c0c0d842e00442c135103903401528980c144015001c3c03035083c01d10080c2c41038595102d080fa0710010140002c04e544000c2c1000500faa004442c0c0d911610011183d4036084190380d803240c1c56121045030050081c2e04003200400c1005003d007440c60b0003400f503d886840120304c507050f100e000b0001041102c10340309900c50700200e0b02504049030001c43c080c006c04a241c0401e03000c0540c2c1134903c0146100c84991030700307a00a009410654048805548803815080418548900c00d880f440461195465074a13081c41c158640700c1c0003c252442d0a0404010034681002d802804024800f15040c001249030090504514050711680788056 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 510170692 1250 510169442 510169447
    0x3141207080409050a050903220b0424090e13060b0a080619090519170f130b03150603060a0b0d09110d05030f1b0f0d02060c0a0c150e03 60
    0x401000d41c00520031030b42089000c20103919005030300340581e1310a4880c200d2580c01400b4403080e580c44c60546c0030b4011100421501e900b65130350b02c0150315402039482070303c0401c5075aa894001c0606481c444550524600d000d01f062802c140d900107880101800606000e0a4a1031b240c003000101d82c01480c80c0c1714001d0806142c1d0b591010f005507200300448150000c072140110b9280070003002c0c099081e00f254054060402030b540b8032850141074556460a0351200f0349015407041d000c0140380101011012030310003940e511858282d510000c22030fa400f80081704810001c00034942e1950a551500030021250540d807500c5000c00a1040d840d00e4018061440c0005410801c4441661054030710301d20420b8090100750a201c05c0081004c00c03400301a006400400110f03000d0840701004044a50489000181d03a001d281031441c40c040c03040c01c5401456100c24000811180c042002070383c0b101240311091319241003a20700410020081c40d004242c0c29401140308130f00801904014091408441141d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 510171942 1250 510170692 510170707
    0x6010303050a032c01060504140406090305090a0f0e0f04120305090c310207020105030a0b030304030c060f120615051c022a0a0305070809030a08040f080c19031412 72
    0x8003244c2c0407104002c1d55880c00030001041d061500444060422143e050001039442d81c8403000a03011140003181003200c2001007041c155142210000900304142a2226603800c0466441d40b00c40d01400811102c880300c0c0c00c0200282c2d0381034403609000490315000c00c054544100091901a0303104030f66602c15030a0f400c0100c0c104805242107020b801c9004e80d620f800410307040c01012032180c00c0020b40001d8040000078450300d40c1ea0032100e4640b0016048030724140daa1385810714007a001d42c1098001a0a11a081d900340d540012166005620000100300d103d103803060701c1004002f40d01c004010300001084150343e82120200740603140202d60f409556403078540b14505814a134030b03a440b1441000d844411100e28000140580c605549600c03081d1514009450b080089e41207403440b641c1c140300300b04a29000540120151000340180a1011079207401d100315070b410400c02c025607a008040c0c00c02c3c101c0c04204901940400c907500029080c881d02c4943c5442030405004841e0448141c0c400541030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 510173192 1250 510171942 510172001
    0x5060703020d110a0e0d0c08060f0601030c030e0c0f01110303070c021201140a0207051f0507021506030c0d05070e1303030635030d0504060c11030a0206010303050a03 73
    0x5050000d802c4904000444042049000c107000390341c1d030700c0c000850200c607801c2c0c0303814030048803000c07079005102401200350307120703891842c010040729000303035a49101c020f200311540c05019000048409003028068500200440d5a8440600c03043c54860380c1e0400078010141d000f0304203100e40405010a0ba07540c1c3c5006a00540b80c440c1c02142203025242d440b02c642304085041c81514070001c110305040c0c0707194840001201c0030b500400b0055541e030242100d906141c900d84024103441003240c1c080880d1910302004003904086c010103500c13040c05541400c0005030398011a0b5101a0581200c00007400a298107240b0302e012850780102035800500d4060000648282c820510b0b29842960248503481d200d03803a50612100101c804c020900b503081289800710b000c003030034200d0f50704e40c50100d0b814080001040010f03250b0558090b2003487e52008000852540030b0070130303e10402035600461600d40441c1009640d0320b0148409400c000001c218140f220f40b090700300700f184560550300c8080d21000681ca2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 510174442 1250 510173192 510173197
    0x705030706051b180d080409020a030f050123190312020f01060b0a0c0f170403060203090c03060106021c1b1406060307080a080705011103010e0a060605070f140a0506070302 76
    0x10f601c010703110701e03200341c4144103c030080ba000040715001c04820f07402c8840c1402041505080d080701c00c224140000b1890344c80c84e00c0a04120b1a0315038002c80c480c846141361900319601a006488218446c200600074410710768117460000806440c0440000039034041d990880400360002031059407404c1d40c03c11101c0e40064011810207100000308685a694500036040e03102c1d4800d0100070640c60000980411042a00c02c00a903014151030000918000e59a1102d81c4c007075041207807030356400700c01d10000c4081003006588809081d03005144079418118040e69861170504881c60542c4c003a020086c24520601d804a0820504081410b8500141c83d15283c803810103210f10341c42d44154030008030b807864005500d200300c40e000000f13800e1407807050b22a070100340c0c003814050f9165900e440c1400350b81710148000398020261601645564189010070a0588005620203030400c84140107240200f401c40c01f58a28080c0c1c44081c0c1103070003104103035490400c0034030341018090f8000d580410004c0f0390103400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 510175692 1250 510174442 510174451
    0x40b07050312070c020a0e0a200c1b0105030f040602160b09060603010903050405041d07030c06020f01060e0a2304030e0114040b041505070f122c010311070503070605 73
    0x140d000303180d450030f000b100e4030f40d11408007a5004c1130b4074408021403100380b14240c2d040002c1c1da2021540c00c01c00c01d03400082180c2188aa003011200040d0201111028442400403101400031031300c0e100c2159000030064000608201e0031880007502007420000c90368100c983d0000101c4140a40f00f155041c007090b203050456840100d8003c03140040e005280612541a40d10f916803691030404e81010f0a200040c80d4130300c0b41648194818040e400400c0c0c04104003001544640d0000c03010504000e4000e003095030103042107140d41e041100500c031500300100010361280f50013000240c0e503482125881d405400c4003a10441680784941808103140e404000816002030a80b10040114100e0b802c00415110310321400030000030921040c090400840c0140d06210414a0031750b0030101036885080315140c03050b6046404a180c0c20844200c55042650581040346190f0100082200c000074a120800000c80c4641050741c0c401e60a151140c5880a80d08055040005c9903103070246440d06c540104415036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 510176942 1250 510175692 510175717
    0x110c0a2327150910090209010c0605090303090f16031205160605060909190b0603010b03030f040f06030509100e03040b07060506182208040b0a03050a0c020c01050a1202040b070503 79
    0x12040e01c076424080c94860180c80d0652014134042e05e0150214025003140f180d003410080c59200040210f81d89008240c00b85814002460741c901b8081c002500d440340c0300c520303811940c103d0480000c2c441d01310303003102d030440360419440c04005500305021901c40c841e070081008400000c54a0500b0301c03103a5440940704480c00e99a09800d03441d0454080e540b04155090380c505d42104d83c4481c0700191211220316001440130f00085245240c0b98000f9080d074010284000c0755030400300f0104100d8103034150600050059003000c10250909a850300c1d1116846001d0740940340c1c450928502c211020801c4030003e04201c14050f0b2903940501e44400070301320680f00244503c1014110121115590069a00a191f0082542100d8401d842c54100d0885039140070382ea048004c0c000003d00000800080000106641e0005860300e803026109013190030800c0c110302158031104040c05242d812500b1140b03450680c2c10a488641c03c5111064040d03c035940009000f4580400d00b5000c00c44000041c2c0303000d64004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 510178192 1250 510176942 510176971
    0x1140c0c0a0618020307091b180504050f1f1409100503010c0201021b010b0105070b1003021c1202070b0d0f0209040e0708070b0306030601050603040f020a0303110c0a2327 75
    0x2503480c0c1c0306556070a0034a9144103088114070030054010076910038061427a284410017517a07200001000c0382e00464a40d4035200f400002c001104245a00740540e1400b0755151030301603420090000e0950203410700300c1c0e01583d01040450906c4100c00000801071400400034807140c0390030000203000c1e41000102d1041001c510122403031041040c041d9560442060750360500b00081c50300c0c0c0d92410000540304064800c071040c40031000d40c4428011485011a080090380e88061074680181c540001444540443d0442441441004a40403c9400264800902003061049140c1c0e400c02882035041c1150703c64a000c00c3d00d1052040441d20704121050042991001c99850b414220244412103015a0640003000140140c0c90705002854006015541501203013801e0341c0810341d82445c0d0703002a00401c0800c0c170075001c5544200982c810f11403082c0e40281d44649845450881c00340306030b0121600c1d09522003050700a48801c001c0c20440741001011080c2651001910000c458041d00d00e000c0b1038125 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 510179442 1250 510178192 510178199
    0x18051b04060f080c0105280e1e0108190b0d060608060603120a0c0807150624090e04020f130606030b1507022b050f010e01140c0c0a0618020307 63
    0x10b040541007180c0100000c2c011600400d40112130a502c5030f400a0307074001400c01804660300400b00c000404800c1a11090803a903404410459624600d02c00c034801c0e10541e00040c16513903404002d598003d440c815104101d03209985006010f8200c1115294221500904d0300c2d00f406801e4011004480d0480290f4540e51284030606480c1d004582c400752507403d04000066080c0d100d00e0f8107800050181a0990405881d030b61045c1c07829012003c50125240c40e0101809140d0b00010109031282c4078540b8240c09000151000e0012140c0b4481c04090700000c200082c03c1d5190742042014010000304003103c802c200e40b0000e001003000d40103900002c2c0c5400406c00c0681050060550031980341d0340900d007818030070b500f00005041f010408144040c508c42c0e281c000c3c0311030b03106540c1c840d07481440500003401c0303803040413821207600c10381c264450b80c1000c40d00c1c10b02041001c90b154012542c00e180d2070380e80542890883ca01000008010201071401600d1000c0a02142034600300e5882103054890b11b5a8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 510180692 1250 510179442 510179459
    0xf070c0603050705030f0907090204032906011d04020c031201030b100e010e06031f0204060210050402090105130e2416090b130807080a14010c0f0318051b0406 70
    0x103c40100100b4410000305940e214401c2032242d0149414040703070b40d40764403890303168180d800c580e0049a90303218010270025500c00036070017480080400302e0b000140c0d181c07040000300b44000303201c511071102852a102c0b2079540c42d603404951503500564126035540c821000d1128000b01d0034130082d1202c44901c03000c1801c1c072659451880407105980b2091a00e81d00300200401e83c00006080f007a07151251420390b51010242240d81e080f6942c501d02c0050f140d52410b00043d040640c0d855002040505d403900300001030f03840c50b0b400e60640c1d00949991550020003408071004060225020055204541480d02e10711500500b107010401070b0600c08040303480e04c40c82245207503c00006003022552080d001e0144000e035602130940381c1a0140040a10340d0784155450505603150012122900841900424854441081c000e0b5003140d00c020042a10140c0c001000c1041c4c55003000b08140d2980c48078801d100c0c4008203591066040b805a0300520141c07100c5959400100e0982c500441c02d0510014503100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 510181942 1250 510180692 510180701
    0x90c0312030207050a0311010e06010e100e06030a0308100306140402041109010801060305060f040207080415020a03021f0f020a020105070e0406060c02090618070e030712030e1210020f070c0603 85
    0x40c0c4c060002c001e039680994040c0c66a901c0c03000c5c0c41c200396503a090300f4100c058041103518000e2208100003030540c01d000d08907000c201c4090f000858900500c0e001d202d400d4a0024407160703100d405241030900350300c070742c1d0000841403503507440509060f040c1051284084179140216004510840302040720b41c02c1c044030104140039039080a800301c0e4a1000420501d4026003115070710400044c510800b000881c00014126005580c041c0d9031903001050030702145900010300300c1e006009000900c2140113076035009540d5500104c14032094030403030586884c209440d41003050722040c081390a64a518001400900038001180c0c03001c0080c4940300441034504280c4200d9090b80c10a695280d144061602406a4904042c1c5025000b0124080111030066000040f0b030140c000e990702c800506403407004044c0f6269150b0040315001c00b58502c8213000070307000380a02c0c0b60751000b600d0140700c9144002e41d0504180c2c0600610b0115400085c02008002d152002015040d105810701d89425481e00422400c68 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 510183192 1250 510181942 510181957
    0x1b030c0907120c050c01091a0108160902250602070308060a0f03030e030a0b040f030e0901060f0807020a170405011404082e0617060702150a02070c09090c03120302 72
    0xc81c0c82c104004510b94542007440b11846508215140c24441d10205084070740c000c90a030364806104200303200b48087d00003124010714100b4000c256040149800c001180c10a1003694800c07a40014003142d8044644504c0c1b6442c0086c05e480d90207026181081406584950b804030005080030340020414030380f00b00601c081d5101e4190b0a04001d0071560b05480203110000c1c200d6052107100f004800182d001e81d42c00c2e109902c01e9403c0555a49240b9028000240315108540f00f195014014046280e004890183c0c50180d4944030001d07482c0c83c1d0003641000c4484001400c44c0d003a8818114038013103180c5c01001214003c1c0d8420400c0c2c0003855102009020300d00840009400c5071180c1c440c10020114240c520600c030250811300307100684606411204a41c0c40411815910701000c2074550b001d0007110b0b40810305001400d100c1041041b4005104802480f40100715400302e0b448061002400600019010040003086480c14500b0507843c049030503c01250080303201100701d00340d00c0c468025980074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 510184442 1250 510183192 510183197
    0x1410050103110d051525030504020102032709010b18030a260c0304080109031403130b07051209012f0d050402040906091101020d0e0108010b1b1b030c0907 68
    0xc281c45004201400101030015035442c032a90742200c0d00c204001703d00d140541c501039400c000310f0b08200040d03082c105171541200140f500d040104030150360007004403480e0802074010050081001480f28000c00311014946800030b60520000c1480b003d41801020040000d010f41c1034a0615001055511454150000c02545005172113a41004114401e0441c0010151446081c40085400f141c80c40c6c00ca0b03400b407561691039500320410b0541040c042c203041001034070b64900c1c500e42440015410104030b0380c0100091603034000990305134466010f69501248003003001d9140c2c14682c0105010b04104d00c0c80c007003102800c0254108007802070300d01015030083c45001e58203000443d03c0d000000c00c3c006000b680c1050310f0b50714400005000748249040e651056650305c0b50130040301c000a103000c100d804400700b4081c1c00c0020992aa8100030f41e2411240c0a116042d40c504040d0079040c00c0b100345001220a610400700100700141803038000c1c1060990030b074129011a804101003110001094991034003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 510185692 1250 510184442 510184463
    0x9080c03070303051c09080a020604060c03020438040909142d03040512011e11040e1009110309061006081503010608030418110702091f030f1410050103 67
    0x200b0100501e443d078442c100c0e2030170004203065180c071801010f50003000c000c00140c1001c03081008220441c829282c0000c2c05150460829080a102d00070b241002000c414503000d02144c110001d261841000300b40070141c1c1c0011b07480e1503a03402014080c00c00c0d02411180050000301c03242c0004000182c3c019903800e0780c11294004408000c5424800d08160354880060104100106468a81c172002418040d1031000000b080c4400c000304000410680303408016207800c015003008008a8101a14182c82c0f84100c08001e60301c9000d08107030001015030150000b641050511050074100e00050351082200900f9950b0603507441c402048903440700c1c040c0b100411085030104458403a01d003440605000b01a0002852607100c1c642036146821030740c0080303c49002940e0b1a04007074454003a04140309030320b0008504015050303001612b112001003503000c400e20f05800780c00440400d0410540210340204800601c46002e08002a104c4284201c6500500ca04000103955110921030700d41207c1c0c01003070103a03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 510186942 1250 510185692 510185707
    0x80f0102090907080c09030a1101020c01020109080d1802180609090a170d021b010b01091d04020d0206130602060402011d010c03080a061809020a050a0b030f130f0309080c0307030305 80
    0x11078606000c2c4c030b917100340305092100080380d0700c00700401e0040320b01484078816403c0c103517000280f07844880480bc0f411a410108102c00055240f070a40304014407611010030f14503642c07801194401c010b81e01c0a580300b40d124605400c06500703100041e000b00402d461403025a034502c2c0b1680c0c2d54510a0704000d01200c000d80c02c100105036854003a1030040b000200c090310780200d948a000c1c03c23084803210183d0076596441c22010320b40c0c001c1444001886178960301d0612058101c4100c455220041019010394561019403086540724400c80d0400c04801080021503519464020b5544800721422404148012803040044211141051040c00160344620010b2510341e02250110340180c0300c510700e9a11030102090415139070943d5400300030b48020009628007640104240350b4007a900030390042c14401c1c0c3c00d1000620312811250300440c01c4d10902c100e500d986c1d00c0d10070429801c40c00a041c0d0f6010200c0f040070564000c0581048590365421034241d4601d41c81050b03103c246906c03004020500c100040d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 510188192 1250 510186942 510186947
    0xd0e0d06060e04121701350601051c0b1611060c03150402070f030c030521100905071e0203040302090109090506090106050303120a0b1002100e0a020f01030203040501060f0f080f0102090907 83
    0x40744e421010074400b640c0f28000000c1c1c147c0071604010000560000c10042c441410844495503004840c40840d00407402ca0382c40310300b00b65401134074086481c500c4904108855000c0c0a10380e0b400305800c8100e17103051030b203100c41e040a07030000d4903690080c2c02c4400c2c6440b0940303401e0099501c3c81e5040703118450304445507a0300b03941210b025030080b000e00c201408885041418500503400c007107554400c0a0140c50451100000d03400c080e003046082910b80010b00c4491607003d00100055040c0c104020402000104c0070391640c011030340001c2d844030b4042e0000c5200805070300b10013110740c80b80e411511503443e055075080c04e0f0381c158041c154041e4814000d0907901d6861540c001e4001d102d18000060075800b1030046200040760301500c07005a4410402c030b40703e41c0011710482c08407065003806000b2025190b400152402c0c9840321040c100f54021000c1000e2260a41c05030004011001c06065a9a9608010b003111280303441500070070300038034500d03641451042c021103c107108001c007182100d582d5000306 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 510189442 1250 510188192 510188219
    0x1b0f0c020a0905101703070c05120709110a02100b030c0f1f08190c051204051e1006120206030a020f040305100203060901080f0d0e0d06060e04121701 66
    0x1a40e00207960032002820402c14407405004560304400c01034114202401d82e919011101078100c2180d00c03c02041001c1002d894041302a100c00300c401066001540032454540600d80d000340792107628003a0142d10381115440100f00041180d020f9640b81011a0b92010031984003544094140e005158a42c4880c075004051403156080100020149800d40030a405400e000b000c0b0701c00450210380a0151440d2071800e4205101d820100074480e80860390300003031081c0100140b2858242101010804024007882860442d050404505c2c0c4aa40c1c42c81c103075907546011644907040c0c0e500d4220040f03140078004c5200801741d40c001e4201441d540b10101030720300940c4410f41000100c0000c0c403011002820a1008181c0768039103102c050b0b107900f030020400c95005010303801800703194003e0010360b0702c00802042c1c04100700c4a0f800c1078031a600c4100d02050300100000340c010b0032640b410700089400c180181d04140580c0c06035400144080c841c07003054450591198014243d41100e030010841e03486000038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 510190692 1250 510189442 510189467
    0x8100608060111060c0406030b03070812030a1d06010f1403070b0f041e0905150d060f180c15020a051f1401080f010b06090f040b0303071b091b0f 64
    0x10543c1034118401156424044d0558203001e802d00b0015042150302d41c18000c007003603018224043e14981c3c0c0340020a03581d0310410501ea058014001c0005480d6401d65408502a00d02e050b10302803088801480554840f0305c24080c070700906015440c0441c060403158000b40070208042c0081450505060a000c01d540045c0c41e000b484e01403c1001103462030288040780c403124290b030480b800740e50925807a0340956200074040500702e403e8210340b00140d512003040c94802500280b00044145059861b480508000e54007010740341440043d4004012002c25000210b80130303045103100025001404030388484900e500a4060390011040304101005031001d013a1a80640100103030300f0f41d40c401c0100c528170342684a0742054200c0c102c000495403081c014109a0b00c0300311103680c81c001b02200014a6913035002619406644e541d084982c46840c10030480e9006038002d2880000b81f40480e841813034a100038051441e500d1304040480c2a101000b40420b81045c009444008000d80031030340898543d940c0b1003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 510191942 1250 510190692 510190697
    0xf05060d0e01180507050105071703152116081c03020c1e100902130e0304090509030a18031205090105070204060e07090f0e0411031c02011506081006080601 69
    0xa2070345092001c00d104032036101c1c102440400b61002c26003451800c0c4810342d442541401010001c400c000340008440a283c010010100e5840fa1190100303200400720003e00e541d0012030522040032410526190b000d0b0f95121075003180e81c2403510b01180540340300d4a1080110750384c05807035003c950081c107000070303d40113060340380c01810b15807501209460030403503203004403010f6041242034106840c00e00c03020f0b4404001082c1400491011342c003054481c450412414103045e501d10884d50a00020f10850b0024040c0341010300c02d9080031454079841c0d0b80920080030214005440410616180240328004c917500100928003e0346042001d441950091b40e6980c1048800c1007140c0c010b83e124490300014100b0b04800140900d403020020304660301030342008a044c0440c81c001c00504c1000940180d20a80c0025100422100f2401103480d1980304084490420601610050600c0c0d0561004104020028820390950b9860106644007407003980c0003521100c03590001c1c08201c0c000d90001d82c1094061 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 510193192 1250 510191942 510191951
    0x7030f060b2d040f0c02060103022106040c0503060f0c0304060906090b09070e070903020d0204020f041205030903100e0a0201080c0408070e090c0a050603070e0112090b090f070f05060d 81
    0x1400c450705034004070300308000707403075410b03002c902e40703081030310030003041800b1450104420703101c3c3c65003e941e404052000034442c005010b07191555591102c2a17103600d480721808c50300c19041c5403034041c2c01c07a001360003500c0c004d201c1c180018048207000d01c200c5001d0341a0046a9246031559102c0002418070203c0030b85006880b440e01070006184c4d030034007038403803404640544100350a1800d2552119800740c140d40400140c2081400903903034442452980c0c0383c0c1181c0050380e4244180081150340180e602080c0818400bd664038248600440100a003000890130ba81c541c00340c14031108101c0b00340149e4a00d0304d1344030500c10390065004400700d03900b00ba5000c500b9800c256032010410320f454055000440c03462114400e00c148441c00308910324120108640b02000136003043c01081d40c0307000c000c014200f0491207466002080c0d00030940c6ea90382200190091050100da03040500c4002e01c1940d400149200d14146018800c40118100081c0c5001c0105041401d2410042084d5500144002c1070860b980f03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 510194442 1250 510193192 510193219
    0x2040302061912111b0f030a050a02010609110d0f09140a0201031824060308040f14040b030705121603032a11010f03180308011707030f060b 62
    0x503940a41120140e51034140080a02054020882902d900f401ca07602070611043c0c04000d0f04400c26911110f109000c0d40c0007074900404100c0c0703820840440811280000980c6000b00d640c8036000b03100c00070744d94000f48071aa0b65000100211501c4000c41011440300780140712540d4040d820000c1001c441041c0800d1040d00c84c0c0710300421460560000c13410703a110307800070030465815000c1d03214014480b80c06804214910746402c04613038400d40301c24a81e2076141c441030a030a8441d0340144003864008400585407030311200038090031207490044070107502400608a16a1a00d800750b00c040c103002401801002d0f16000a00040b0b07491038250114900418090055040e85802070000450096030f45450249540c490031021280569100b8160503941c85001c001c9210241400141c0c4004e180c080c1100e241f0308012401000301503410300c0648107080c460300c24140e01044c030505964048041904d11100150000c0d940c901c0c03884020102d00b208d03986200415055404020000b0000d003215019082 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 510195692 1250 510194442 510194449
    0x209062119020702031207030c05030d021806070312020d0f090501020910181a0702180f10080a15060f1d0f01030506150625170301030201080403030f02040302 70
    0x52610082000c4140d400030401580035a29800903050144581140390207060307004aa15140c0b07401d03800e1500740000819208040c8640f00b55442c180e04035058070313252004401c0b604042d40c0f00b401801000d10b02c1700d0340d24965142180489800c02e41c103888035903d946444464201035046408031241566990f50345240d01c11960080c10f040740c0c41900010381d82c00380c1d9020014100c3c0c0c0f080c4400c041007454a40160540d8440001c2001c1d24110100103441415a04200c0503c0c452064029001081804204613421911042c01d00403500141d803000c140d51449444101d4003860b104100b9a0351203446248045400340c001910254141607001c240390392905900d20841c7c0c090740c056410b040d4810840710b901000c0060042d00120004020301d181e500d543c948950b506405007441d0742d001043d62504106070b07114000c4031141d5500b505004681c8600215013a000800e650059414000c01312100106840d4071089038141d0f40d050710341031516182c589085005200b0702c0c11b001c40d400d500b000f0100c0540d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 510196942 1250 510195692 510195727
    0x5011b060b032509020a0903110310020c0d03060510020a3908060c1603050306030c09010609052419021002030a1a090423011d030304020307060f08040303020906 71
    0x1010901c010707100f0340d8100c000e00300c18a0b640c401106940706004190051b40d01990540459400c1006d40517003900300000207040c414040785031100641700080c0b00700c80700004556802c010004e034408200c601d80d10300c2885200183c04400d44016007020100f0b4001800a401c240490103854035003182170465541041d140491201c014074005d44460130800c0138100412043d58480050b0303d1136800d0543d151010080400030701001000c1c0003000c00041d140d41c404101c42092a44003d140a0f802d5039100c1015042d041103000d040c1c02080501610700d1940d0401030740020f2203a1107892980b400362150244403210f65000580400c6009003024022014440d001643c01000f503000300092060608001c908010129540035010b40350100400010519a0398a001449900303131310200c1d0054103544880c01882102e03200e203800300f4005598000c013074001001d50311891095040f1803200740c41c0c2805950452142c00a90001014074000900280c820740241070700400140241d824400c44003072008022 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 510198192 1250 510196942 510196963
    0x2070f0605040320060901030f092a1703070f030c08030a0609050a0b03070e0630010b03280305070b070c05010606111b210a031805011b060b03 63
    0x5001040a005000d002d400354880f04013a40764030102c10540300d010441a014081e22541856a9116461224000c40d0000c050381a80880c4900300710801140e801070a001341040c03070809280c005000b2031804051001c2d01d40c400603e00c021828003420ba502e01e00543c00440f401c408228400a0200024610a000e58082d08014501240c15030130074031154100e50004000300540c500380031040565480104400040d40da42c59030780c41059590201007184c2591200311841190ba90403035050f030405a807900c0b261208a00380092001408003010140d0300c05042101071000d91079840180c0d0603211190045d5446480380c1000343c00d090458850300540c41044070100d0100c0e1005a60208001c001c0c8070b014050100785c240801d030801e1741c0d60b0a640d01d18101c0401e00007500c00e02401030f500e50740d000c400120031145456220050003a88156502c649001004401144801c4c440551038440c0d01105070a071141a551007001080c40c010070f84074611001002c3c2c41841c1d44406500750b9850601c00e0f4200d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 510199442 1250 510198192 510198197
    0x108160302091203030a0b061207080c1e030f010617070804020d020405010e0702060721020d090501050103230109081c0e1204263d140609010b0d0c02070f06 69
    0x17a40341061200090f01d007403200c5a0321034201004480724103c1c0300084076400850520b0302145a548000c52582544070b0f0702d050200115100c600450911081c42c02144600800c09408403182d0340d4000030303a0310701da02010405401b03800d040058036103403040c01490b91107400108006040c14a54010608580b82a0800562400c80904120145030100680c80e0000c00324503180c103a44400050340440c084c25481c10200349a0002a41a9502080e03005203d1040c2c220000b0400c55a5a1030001c603074003561403404041c0140b503182c0810703800381131148080b041e4020b003000f482c00e2082c81052400c030301e800380c000607040e40c2c602c0f52800c40c400030000300039500340901c40c1c160f030b80703040c01c00d01040ca5483d54400502001c01d03090b080f10503074001c90204400d11400c03813030260b00c42c00d0f101c0c1c2090440400352058408038041d54200c643c842e59401c00703001c0800d07407140e129098444400f4841c2e400e40074003034201c90300401c000541800c0c070700d0b61206031109094810f80f15040e46440940740301d051250b001200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 510200692 1250 510199442 510199447
    0xe090120040518060901170c060a03021308010603031d01111005150306040c06050702030a1a01050f06031303050d0209120f06070c03090303030f180c0608150108160302091203 77
    0x510700306410f60b100b41050f0780c008660107282040c0000d0060205002d512620030603034a18a030400303800c100742c02c18000c00815050f110b5100a4008001f50420203210140c840d0012000411900602c20070055941550300c0e00b009103000d1100d04081030310f0103107242c10809584038410f003030401031110340f400310340346440800c1d0f81c2058401c41c0b84140210f815640302c0d0b04524103120019982d4540d000c09c071031950070840e40fa84060b00029040955018010700299012a10048500140b4032000d05807a0211840c155400c51041030000d240400c907608400580101c1040000c0b901941c050611180300c85c1c4050319008034500400c08040c3da1099520140d440045925180602804025448100b920b061811340ca1030740c0303009190000900c4060140356445241c241c246800f034001031072484101108a540c03108502d043c100c160f06c90300c0307003c00042000380810100c0018011400c22048160754505c4079440d84002002c0320001c1154000925900b0411401c603134403005019810400d42030301458 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 510201942 1250 510200692 510200699
    0x40b10021b0a1d060906060c06130501020c0f01140109020a0e1509130b18060310020304060f0e030705071413020d0b1c120203090d030c05010608030310030507090e03040e09012004 79
    0x2006006001b5521400c1c013807141031040440010700700c1c2e1021014910a18844541c2465070080c40b900c01c5020380f41c010b44000f001031036015084010580c92140f009100b41c0e0307a6000c040228000c8890b21400900d0b0b01d00595164504804103548601104044911b020b08801c0080c0d0381011080300e603080740d9113a17209000246407020a0240c800c11784891000c9524001e80082c2d2503904c00b80b020b91a1603030120101703060040507400f407084c58080c90170821000e4150b1907166074a40204000300d07428400c0240c00724840c1202c008582100c00c0183c0690360911041c107403940a0742062000b16100d0356912000f044030303a148408010542d11061940742102402d00b0080d00c4540411000ba09641c02044074003400d4580201304416103416292140c2c4500043c50154090003159109a440d40320200601030840c0040c040300c000ca81c41402100d1742c840d6556a00020394140d19840000341d0003c1c00b0030000c1e0340501014581c0040d05000010b00c20000740c00480740d0b045144944400342502140c00e2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 510203192 1250 510201942 510201949
    0x140a15080d020c1906050a12090c240f081317130611030403080315040f0c020616030908040b03041e060c0908060f06040f060504110306040b10021b0a1d06 68
    0x141c0070120701002915141000c4000c0d000d4401c03503c40c44c0c100b24100c4245684688036a202c884410340c00310101d00002d5564400ba001003481c0251441c2c18103a5014120bd0940030311048001b0460b03030345840b6566076680c580400daa04503c801614058150205885c10f507450304010050380241c0d001101140d4280701c0c00410780000324282031001e40c42000240040bc20403030130740740d02801c06981d54009081203404107010382005c18000326040d06200e0381c0044140c02244191050701c508039030140e210f016840450030740f204400040c0404d00c0811091100c00284001035900c240520f0450241da5142d00247202d038001c07036100c16980f007948c2c0c0400321042a8442148070050451500030141070034a400c0301c41d1100809000148656528800015005503a411100007407000510410141424a204011541c011104a4492464442a00c0c03c51502180b0441c1d4034441c2c0d40200842074080e56028080c0c004010582da1003104404001800e8044203840798509281e0ac400203018140340090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 510204442 1250 510203192 510203209
    0xc0624031509070e0709090b0f06030a14060d03090b0306030c100c02090c120a091103010c0908070e070807030c17010306020a1404140d112d04140a15080d020c 70
    0x10701c00304c1c4260001d10520710350084000c002e4070309003240003500c03c58407c001501c503807031103080c550069404010014000aa984555000400c86400004540c0d0b04410405030008052000f004070321040c8061010b401d41c07201a5905c500c0190445502c0d04081e40010380c1804031481100001d0366030040042181813101d440b5422503003948240d424000624122040400000e1050780c90940d115030303100034031a0203d440401084060000c1028000b495030042c082c1c04140240e000c0c074031030346400080c1b88a4101401b4412150740d6070340b288545030040d044010388000c0805404105c2d0301c0c90800204501d541459000318400d080040e0740f11424030000c1c0002c2e480c02e4640c40e41500906c81041884591205203944035401c8561035400f10341450b0185185032090300d22500003000515000600c400c414032003010a101e10800c10481c290740041100742c40030100c0006029081201165a0313030301613001000c11440f0302c0c184023200c40e21000403034542001c84500d000140e1183d0008045070a01019 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 510205692 1250 510204442 510204449
    0x151d1c05011b0f2102030114040e120702150405060409020c0c0d05190501020412050d02150613090204180c05281716030b0601140c062403150907 64
    0x8202c98903101c0020050f11500e02c0158480901103500d002c40b80080d40c5807032004404222010454032941c450720040c540300061200345005a00c0c0c543c055085000008000301400e24004d4030074a0141d9960a00800280e100300d400400c11081c480800e4542e84d4001400140a0100c40180c450000c402001c0c44c0c60110740e0503500845454002ca00411b60200d4021810042c48050195984040c64503900a10075503008026817a20301420201300503012601240c042c2e056030031034548241342d10f00c00307070000020740e40e4a501840410f083c11303004006401c00042280000c00014040301c1141d0059800400c5500499400020201c28402ca2500c10280b43e0060800c02203800e580030840d03909041e0070f41901410742c04148119114694401c2048010030256660440c10502903891801002d07a01055981c103010550307500d500c1e0f00480c400d00948602d00132140080134030b9100c082d100300307a1810340121910b020b15804810b0510352010401c4140d186000400c0c1065480e1101645003170013010380 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 510206942 1250 510205692 510205721
    0x2070b0a140f2221060b03190f0c0f0602030304060b060706050f1b07020108190612030302040806070302180d062d051501170c0702042a0306151d1c0501 67
    0x201d40c250350b41315192405001c0e6884140000c0ca0038600d000079250100050402c19580e43c0040a00104604c50451710003003441403a07403490407034032000e0f4508409098083c120050344117000040103d00d55800c2185850009007015113811032945030030094a508a400d4488038a0180034401e500072040727001148843c1ca01d05480c100480d5500090490300080c1030031159a1201000c0403118035035a008030014007404203111444050380c0b5005e03003e50040e1240d64118081c280004010030301a000300c1c4c6400e4002144421000440400c1100314800c0c03240c1590300350758a000d02040400e103501849014040c4400e81a0190300c03a01806058640c010700540700384140e1140c1486503600441032030501c40405041090545d10070390790039001d000c0c0c9440a9405801c0c03110780d00181d8503424007e0120002a0324003003c848290708141d00340c0c1d0f84c3c2d00c45c540c40c803588072240c0d00d0703820310602807400340314003003038041000c0b043c93f0300010811101c22408141448407465030030304004092003a082c1044140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 510208192 1250 510206942 510206969
    0x100e0a0c020705120a080f0405040612050c03070f030201180e0a0209040b03031312031419170c1801020f0307110a09111b030702040c0e010f02070b0a140f22 69
    0x90340c0c5445e21030000008041c0400403c1c2e40709058401c0080ea400790101400401c55a541c03140003c1201c100f09400f5a103074003c83c06044003909000c01c005d001c0d158800540c5505618582c011900b4102c00b4480a00d000664500840d0301401014424040c0d04000800350311290035104000840302154a0648254000c01c2a11342484909400700c2c101c404000801c4000640c0c0e080aa51030f0f59551140407403440e0001d02d140352240215590024051302d80d5a80520590b401e00c1440590300039550413504140c14058541c4800c00c0da2498035281d9018815100b95940d21400ca0740b664001900842d0400b1008100745468201540c8010081c40440000c0c442c841540c0346861301440f50b0350004030017410346001e60142c0c590400440c0e0100e9409841048140301130440104403660010000340017902c818002400030380b0005a200070b65010392180c5242c4102503c00391104000d0000042544400b4001c500032203803d84007801486100c00076199445030102100c2807025a140c0141c01d050301d60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 510209442 1250 510208192 510208219
    0xd03020301080607030c1107030b1005061c02130302090c042d05010302070c0b16120302120f06120f07050103060f0e060f040609060602032a0d08100e0a0c020705 71
    0x80c040e40103403042c1000100b50502c410700321400011784694021f24818044000104007007407403041c0c4a422807840c10010030751a1810020540b10b00c840c0b4907800804d43c0200a04844245d000b084203c1550381e90841003a500d901041403035004440780020b504c00440c041145039807030501d2101841c081215841c221005042840c190b00160040b0342c10141d000c42d402c0c081000c840ca03d04054080101225192408905120102040d070103040f030740c01c03070351030702e08100b05000340240c42007e56925100c032065230300c0e219000f0001e04c0040c40507610844d13a232411b841104050120100c5550340001801070181444000b505452107913000504103007151804100300f41c5941c0c14190030010889002100494801c00900030340002d4201e0320b10a17241c0040007416540010007007030441c11800140614040e0340315009060710014100340e20b550020900030701c0709481109103c0c4d102c81071b260035201407911203464421500c000c80c8c0c030300c9946654203514121117070104083c02c0200f07002c079043c1064040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 510210692 1250 510209442 510209459
    0xf22020c010e070819170409020702010e06040f0b03091c200c090f09070503030f04051305090604080c0111030f2e0506070201030f0906021b06070c121e09080d03020301 74
    0x100099076494500803000000800c006d00659240c0803a4143d80243c03619100ca423660001d40c0b0008049010922400301038a0901700b500c140c40850740c40c02d00c498400352506001c0b00c1c5e507038001400305da514002c40c003241090901035441604062103030307941c10000e50130318083c8a4107020b05103d0b0700c1c859070100080004540c0c581c8003441d40200a081041d0440c3c40c1d11080915040141d00000d1f4103010208801c0c12500710765002d00107c81040303c072501d80070080b581c10001c852064400011541180000502107080d441c01010101e2003440000307004100140c900300741c0c0d041503864040c40700c00e9409202100f8440090851a042030142c46960b002c8804040034800045100e458003c8401080360029a80a948280034110141700d0a000c41441c6241a01c029400410b50382d803040e00c2c20300541c0d48900300181311441a8040d032621001840c098585080010b0802c07400d0301006500740020104c080021190340b000305141c1c841401103402c0a1b512420000e030758007404105841840100240d46 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 510211942 1250 510210692 510210703
    0xb04050303072a08100b01050c0705090712020708030403080702030c1507050906040e090f07031e080702180402280506070221030712030c0e0f22020c010e0708 70
    0x9a102405201125401c0c9040550b0007840e40c100b90f001c10355400000311500d011481c10a06204500308005514013000107549500601845d0346c4c469000d64000d1049080600646d5040401410301e00a01080c40d101a0182c0c6c3c03007100308071a528008010301040540202e1184e0b0445d12900180d802c04070a0514145d0791880750610020400c800d0b4040360205005204a444d0000050f00b51682c03203032140842a44c8000940d4201420b100c1c112020803064008208070095039444800808904214411081301d0440c4500685094104000940050b5141c1d4205400005034840104d00c030302c0c09004011400d140c1c0c400d0700701e0b1440c1410140700300918640a01d000d64408070b450903190499800401c41e10702c0c02d418007818a2590162100c40c4d0f500000151201c64410074203080c000030468000c4058910001ca404003141d42d8500f1507040d0f00d40050004107030040075249109078000030700b2109846042420081240303600040e960504003086c0510100780f82140c6c01844581d2600d0b0800f9a00c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 510213192 1250 510211942 510211957
    0x60114070209060a0b2a060603061906050607050a03080a06050f04020c0313030c0f0504140a0e12040f06030e0309010207050d0606053105010e071d03010c050705070b04050303 77
    0x10040400003d406607200c0030310101401c2c500c460191100d024540b000d540c04180b410350040c00d804030b000c6400884e40052020303c01c0d24060302800c0d85454001c0f1404030340c0084061501e896880d00004106501c03940083c000440c0584002c01000c42d081c140a80000d00190610513002d051480921080d103a5209404030f2020075500141c1d20a6100320250640c044e04090001c9007040d03032800414002e5020300c000999840d40c1c00d40c80704940e500204000c40d0728803070303240c684580040002410404268000b24004070100141d82c01d5804800c01c9164950080d00500c1215824810601c82c0030740c548210204081c0240c001c500d08420701002070350301e0a541c850640314140f02d4030890304002864000500604019006501d04c401160390203000040d6400760b00c000c4051150200500241400340c0f90480389284078600d00c0d51202034080380c0002c2c45052085a0b0309940105007100d4400348905003011000350340700340e190044c600d481410030000d0760010701d444400748000d00907a5404411140e54 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 510214442 1250 510213192 510213199
    0x110105041e0804030b0114090c090a030b040809040c180f0518070507060c05040627150c05060a020d0c09031a0a060b1207080702150c0705071206140601140702 70
    0x804181d8a04203219119030b80005001c01850400050304070a1a4134100f1800c0303040300d501220340d8418110520a028400c0000e40c040c0c0715440400c046030000f1a07075a041801a044140b030551010041800d54090307c10380400150000f0f1158010a400c540082c040c00d5605010603d0700c0c07411000419110f001004000c2c1018260b0214580502450480700c0c1c2c558000c030144100d1440603006001034100d40325440104031000110305020b01c04401404800c002c0c0007400903250b0901c258a10340703090800c401400e212403154410041401003102a1045c41c1070f1102503900da0180442c182500d028a6600b0148100002c00b480026100d110100650503848440c861940e580003005020300002c0c3d110400150002130105404044001c0c40b034410001a11204007a403504e0004980e149039400032042c00d401c3c04000f203103c850200005056032401807041740c00b02521000b00c40c254021441041311202c1c2d40700d21651042c0c81c040040c6038032203800d0030840d0b00310ba17402ca03840600e4411690000c0c030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 510215692 1250 510214442 510214493
    0x1051e0412051b07050907091508150a0801060305070b07120305130c03060b040b0a0f060804060e01050f091c0807031d01020406030603021806010507030c0302010b0d03080711010504 80
    0x191046090b540051040c03001c0244286034400d030a0380740c20142c000d0038001d40d40e007030000300307088d0103101d00314111080c60500d0f0b1145602c052007203d42540181424407600490202c482c00d641d0b44c89441c00180c04210000a08a4a58035080d403400601d588018507240044c41500d000c03454075821070b4901700703060078081031550b100c40f855840d100309a0070041c00f40d0202c4401000340407682c3c0c0701010048080e039080100c42140320800c24a00703241c1c4a00d44007020400f00a00c80e00c5e1155040a401901c14880404c0002d10b481c052802c2d207104907054107510301c00318100401c81004001c94007032a01030300080700e41e89d500303401c0c0201803600041c5940300345507c80480e0384c031a9004020f000c4c0c00d5110031000b10744039501d030180100605410b2005070301c5403482064a00c9906c843c104481c5c003920b0141c455503d800016a0282c071076030700d109000d900395540c54404c13602507120701900d1042203100741c0d207005241c6013030702c40036110781c0e46055400c40b01e82c584001c020001e1841100c091416294010000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 510216942 1250 510215692 510215723
    0x20708010b0d12021f020d0506010c05060c09060706060b03061903170a110f0c150412140a15090c080105070903080c030405040e031809070c240c0207050301051e04 72
    0x3e203440001c8401c0c400000c0d1044000841503d194083d0107c1c1e440c040082c0300d26140d0300f0044030003120f042ca024007243c00450125600c01d403140c3c010a4402009000f040c00d02c032241d11100308540d003c0d406298071100000812040d807a00f0800c1081030311211240c2a81c2d207041d03480c1c0c4074480401c0740008a41c0480069140040ca008a0300001c226600b03c0403101c0300180c548000703032291003281e40300380110424001e00c1420304403c03041e107080c0c81c84031000c11001c00054336003108001501d004c040c0b40e4001c0381c40303e0300030841038020b921a800d02c0607004a0b10035502c0c41e00c206038080710351104005034034080a1018596010095004072600020b049403103600103d446420341c03099910a40c0d0092400350380c10b90740400030029002e00ba00700550256448800300501402200403900d60f4005610b031403040c000035072800240010414a03000704071605401c200300c44c044070741d680108409039009100c108060300d001d00a6030b80c8101021100007610030102d521002031311001d00010084041c03444600b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 510218192 1250 510216942 510216947
    0x40b06100e030d0f0807110309040c0c120507030e120c0f190e0402090709050d12050d0227040b031f0e06010b03100f0302060412030306170c01020708010b0d12 70
    0x28030078403001815a000312814010103424100b02c00007040109030744900049000340078030310ba4149131410704051071510241604000041c1000b640010a000c41040c9610110713859191101c180702c080c0c0c07641c60740d5141909001d003000705000711080c0314014002c2459041c0c000801d0000000e0030036140c140c66030300c1c2e080010307481e0703015403507011560001e40c0d00c00140d40460340a418055402515000745c15141c0004c110340c0303e0b60f42d01070140c010120200000c000380c8428209010219289011400c00c1c585040d4442030ba4490701d5504521210310810b08030905041c81c502c46545411a020486030000101094550b6085404600805c0e01c0c0c1d0f1a641001d003a94100b684c4c3e5031024402e80d00e43d5a103070706020310203400583d68003181d02c0e6900c4011516444610b6a041a280c0060003241031500c1e0011141c40d49803e080200c040640759000040d400050030506000b031800c020103807100c0c58044000902e460030b254010007840c0e040c0350000d800d40d201c02c81995401c0b5003108900c1d080c0e40e6a99000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 510219442 1250 510218192 510218207
    0x1b020d080c0106050f04020424050c100f0b03010c0801170114010806040c08010b0112020c19111002011a0d0314070606060e03031201090f090c0305060a0b0603040b0610 74
    0x191424800260414903080c041d44203c040d6801280d6606144511405100490007640070318100e8106400c5d000b0900c1c030641083c032503051981c0c5002450b054030641d05c2820000c050440c641d031140c5035031b001c0709405594090580c81d41c200f580208914501d00130020040380041c130035481c0c01e00440408100c07c841c01e4100702d00c0b400304050040c0ca156921080c40c2d81c0c0b0041240c095411031121000070400c0801801040c0724048140d47c0c1000c1074244a1b0494000e5228584039183c0e0322070040800440c0540ca2903d9099a0103a003d8440c03040c010001c1c40b0803408401c51407801c5900d4001c03c58001c00440728070b0005a00242c0307103446504214074041c0c40107042c14108818000d00400d100041281a8100c04181d5482c0d5540702d070a0b00c1c140c001d040d030301d0080343e80042c08500c4a03401030000d10b80d140d010441c201c1c1c9658000c5216800f030744030100c0c0c03144550819611900140d00f000310016085c003480d00b4101007038030390901d12315181e03e400c82c21040c054040c0d0310801c1c030382c6c0c06d406456114088 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 510220692 1250 510219442 510219469
    0x50411130204170312090303040b040210031b12150819020d051902030c010302040503030a081f0611060c0a02030d020a020c0a1e05010e06180d1209241b02 68
    0x1081c281c01003c02c00b1190b582d04203180c1440181c0502d000240014804000c2d2401990f00c1030b034160b00b0392a1582080810740307082e5212000c1540d5901c042105139883c0748448003070480e90f1601680400903094207801d0720003c40c4e404d26a150040001c0001c0080020035114100e02c4a002e0b508600c0c0d0f40c40090141d03801500040d01500c110111807a42450400741040c1c114401c5080b030f41d443c02104015801e80c010ba100b5141d1542051140460250040e01c12a0f40450499444c1030203c01c3301e1244070b18041c0b076400050002c0c511400d04855a2001c001694100400542c09818815560343c000d580341305050342c1e4900c8075008100580c03030a00800c60402403c0300204000c0c0c143d40c0320580042c42c00381014942c0d604144030710340060254050400f001246802410301da1400650952144d604c8031410300075a08000e070003040c040450381041c11300c04442c0a599400c0c01c0540307040e980600c2500e00401c0b0f5007121404442c00304005402c0104c0030054005240c2c03a0b14811460700004516040850 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 510221942 1250 510220692 510220709
    0x1260a020f0a120e01060605030609091e160f030c0b0a0e031c030f060302010801090e07030b07020312010803090603010306050c0c12030727091806091a0109050411130204 75
    0x45514141e60000380c0420f0031091590200003003000190300380c0c02c0e40c1d4980315a0780415030800c0032a109003024030307869501601c00d100f25401c00020644002207490f6441c000005904005090503658421030488030042200e0300b00c00c02d00030300b035817584640502c0c94403402c030312245c0000305084514003034080c9203a481c1c0e0013419138580900b009204a2914496503124002030314080a8916921981c801c010980740c060f512001560308090010f8003c040f003c07a402d01c00d00c207441d8000006000200c6840c416202035001c0d40e00c4000417018032b00c0603c03040c0c208034004c0d003040c00030107200e444040580781101d03000031022a041d210380508100a21841480070303881d0154044215810100c08004c40c02001140e9680d601d07941c24100c0340c003003201c2040040c02600d02040007000110120703007200000c124090061f00c50540d05540c1d94040f034410b50021181511307450554034407020402d44c10b0f401440f0549080c4907502e05541c41c40443c10309030000030310a03405c0c01d002da176086020b5410f541c003500c1800d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 510223192 1250 510221942 510221947
    0x809010509210604210c1104061a0702030c010207081911030a030c0b01080724020c1c1a06062215110607020109080a030209012609060601260a020f 65
    0x2110280c83c0c500843d02541e102402e210300c000441054400d80756600c0481c2d0302c44840c8410741d911096034500c5000e1060b401034451a01149e40b0141e1103076003c459082040c3c01d84e80d40414410306003424500010309066411140c5d04010300080450083c58a4035891401d941c40400c44c44d240702080740080d0030581500c14204035404064005601030030650103816090202daa1716201541c0c0c402d954016641c7d20800e48030450403008103411003520703003203541c015100e01c842c81c580402d486081400300b00c642108011000000c0c0101c0903000400c00d9009c1200031580e06c0d1490104200d84540d91900c0e110208110350212583c18078a4800007508146274100e820380c00c1d480c4001c014128072190101a40118800301c6c2c803090051260310601c0c0d500c0744001c0d091032107548040d0003d401c4100e80718107008121004001d400c007c00e4686000c06000e00c01003465041031480d02d464000d0003440036042c4a20200900c919400041d507800c9419081d401c66100769480c00d45803006805460300b0007a950790003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 510224442 1250 510223192 510223249
    0x120611070b0604050f07020a02010302070c0812040f0605030601090e04030c0213140c132603340b0c0d020d0903020f0f0106060509010809030909010b0301050f0a030809010509 77
    0x1650090300900c0b04030b805011507121072020f003090107420344031400503920030b02d90080154029000391010b82e0190800100f00342da1130140c14140208040e5012180c2800581404800303414030001c0e011b05024540241140360030400641309a0460040309804100b120004007098032910115080303a84c00b50258240c4a00300f4040405040c0f0300f4001182000c00c240001d018036041400c1c3d5000c500244694011203103001044204905016900d071032100c007825800000b02d030100b00030045403498441565407000101170005400a6260854105c00d065580360800f0a181c151140d401c082051901580c640342d54504d070000344112501c101c815800c2c00006800c3c190042030302208581060107940006910300c0da42c40c200d51140c024107000c51000c2c4003000095101d0141d19a00c8030b62501242e240c00310410005200c035209902103825013000000601a07030500502d12080e083c0143d40000440e419075844101c0b6000c0c0080c07c504012011425544036900d00941d080e400840c0704846000c0d248 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 510225692 1250 510224442 510224453
    0x3030c0a0b090c03061e071812060b030d0905010f02031c050403170f01030605150d050706030e0325021c03020609160501080708180f0303011401030e060112061107 72
    0x44400440360f01035045186824140820024481c082c000d000a0304201ca003062007444800203042103080103a40c17002070390005400003040300908100702d00009401c90500d081c1c1d043e1040c580e02540240c0018001880103a0002050f00541e002401d01c10f43c01d007800c1008900e1401400034070048003840c80c6905082c0d00480d4840f5001d0303030080d56180040c07034054901c60030b5502c00b9100e0743e1850920300300400108900e64071841d081102d01251640c4030400c8400661501d02084060f21290000d403400c014054043c400e006044038030300302840c10680c0c91281c9020aa10180050204895844461045503609240d268403202520101c1c440c5014a050003580d45c941101c0b214800e10911017980a40707010703041c4c03090450388140d5842c0c900c0c2d5591741049400e0300018180d089011150845009918018040724a40206c1400156104e43c5410070b42c0e901c0a4224600606051034100082a40040420340c14151a001c01e0b00c01444421450505d0003422100007080b0a2200401e60350304211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 510226942 1250 510225692 510225713
    0x1020c0a061d030313110402091f020c0a081e21071208060901091d03030a0c0806190b16050304120b15010e040c020a0614070206160e0f03030c0a 64
    0x4241070500c2c001200491065501c0c4400e0700c0303001038113204030700c06800251458840e0030134080162001d070420381c625022441d41440c20080c41c1900950b00c1b4000122a410484800c031404200e98003401d451034890015110072412080702d00140f05240302c0080d420040001d0840c0c08c9400350b43c00c1c0d1604405510b280e250300301040440310b0071080440511840e11448405000e42002008580a0307440c0211080003424600c0030304907400710f007200b103003a0382c00240301651040040e0100403682414604009045110040c28103115408000a0383c11000440300c140e001e48002c2c05c9026565040095107641c140150440188544000540401e41ea504242807864449c4144210308450300e40a0100c0054036040300c00d1400a80394444400d154a0250010000004140140c422198043c0c607000d06444140c1c60141021041c041405407003581001019072040840310081d203040190103004201308004007029209900b1085640c210395824011902c0242c461000c071641d024182c0340035815403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 510228192 1250 510226942 510226961
    0x612181505100e060a0b0703020a020a0308130b0705030a0e13090302100c05190503100b04090b15120103330e0f0d0e04090f0b04081c090b0402040e01020c0a06 70
    0x1a0310400504080c60240280c01400004c2c04148414105171540c6d5498124000950451141c04c9148015031940e003401c00280d4000d2006640e103c4d07510401b0226040300d80d026000042c0104a0b250100d5008000c1d0307240f1501900d00080c481500e0000258220008955000d120340340c882410101900020107240c080d0056006000d48503c1d5502580c9034050601140b1520004800c3e06c01d10f28440e0002710762007440d0741070b50808142c44110040054001d074000e44040c40d40c03040840f0907880d145040b1280d011030100c0c1241b601c03183c0c008182c0c0e48181884028416181d01a44290003001d0a000801240002010300403912070740702102c000e8135074030008911038001c00c1940300800801040c40050a5456110420781a03c2181404000d10b640c0d40240d81c0441c0040580000440f07040902d80641d005100c1d890700daa4400e00020076a41030703110402d1100c1d160010610002d003001142c1c2d07901070380482e000585e420300401d007075001e8807620030040030b68024020044c0030812942d0064020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 510229442 1250 510228192 510228211
    0x9150b0f01050a05221d010317040503070608091203090a110a1d040c08030a0c0b011e03022707020a032601051912030503011e0612181505 61
    0x40403000c8015100c612403400b40c20009101041072105217202150105001042109080704107030703503004503003003e203c1c0d02084150b88002c3c0e070040040c01042c0d1110600d2109a00d5501e03d060b1412001a40d68015417103100d003031000d81c3d000100600d40920013407112051682e0403659074a41a01084c0d103403105580b04603000c80c504050750603a800c5c01c2d01010151a0001100280034280d501070242c48000180b080b1540b10f94140007140c03059040c006030402522544401054501a03e0600c542d51030503044a00d070700101303a01244014441c50070850403a501a210495009103000290b00d035010159540740041c20201c0c1840052a0f0000b800c0703042030f021751749886564202e071051520207035a90008a07000d03030348200180701600d80302030381c090402800c1e0403551b003a03640c904141c0e051101c0d070358041e004501c02000402558900c50a801110600300a40580f4241080400380c60381c442c20052a0400d40c4d01c01001e012a071000c0603c02165802910140300c1c10759030780e05900509000c0710002e10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 510230692 1250 510229442 510229459
    0x91101030c0c0b0a09050c130b0901080d08040227010f061713030e0109031e060f050f04170d05090c0109080f0a0b1e04110a05150702040c0309150b 65
    0x182442104180c08007a40700d03404910340e0703c2c0c4d104448040d060180003a9807a0180c02c0c8014020366a4207080b42411030040000f00f44400d000b4100070340000140d00c1403856030012035002d80c030f80e43d2000416034803560446030305880503a40810f050b01d0b134003891030048001448000108190b6034415045003203039100d03980c0303121b0700402c46048840d030401520014515500d036440b42000178000c18030004400c0046c500703040020384d00d0f242c0146051400b94044582480e0050002c1031084600440407101d2950f030342131140c2d007090b821182c1500c41c0100f026001030751891b0000d0790a80640b007241c180e40d840100a0005081071030b0965140c43e0300c0c0c0d410314007054507c81b0006060002150803501506190080c00c510300709600d60701085400102580251401c5180720b010f10450000e500f40100d0142548050010080b824800352406a81005102e014130007021101241c2c140c007284d09255041c2c90201c1c107100600c0c026000b401e038501e8001e000102c40e6038400d40d0061507038001240600210b07000b40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 510231942 1250 510230692 510230711
    0x3071d0d0c1412030702040c0215070819051608060103021c0b09100b0a0e030304030605180106080f03040b13080a080d0b1509040515100c050c060c0316060f09110103 73
    0xc2441000b040c8141a0420b01c0008003500e4981d110f182c400f1152700503034000c2100300a6410080308200c80400c0420308640c140444403c032106601c0c1446501e0f10104101e0910f01400300c1301903da010307641c08000350600007800c0782c0d2098060358000355042d142d03210380514111100000d09050750240f4040c031140380c0002d1031145100c0c1e12104072018a00340618145442e00f0480300b680c8448101e0707806100400000000503914441d15224010840e0903622a1070f58417030300303800c0d0381250307204804640c40107040d00d41d01c80700401128102c890b154001c41d40d8601020701e1440350026039100d0940307400b80701c5010307041c003100d2001440340d010450f60401c0b00141200400c4140c0c80d1010f500c1110301c109004031001c4d800c09611050f00000c10300f44840e61403450b00000380400d8103071891600043d01c0042c0c17440401c50304100c04d0243c030004590960804603104401590b07401628040e042c0d00c100c00d50441c0074018030740d101d46c12546455000344070040c0d590800c0346040000c480c01500187c50640c024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 510233192 1250 510231942 510231949
    0x5041202010c1209092304031404030f1112010606090b07150203070801051813020d050307051c09092f0f07120e0d0b0402060c030d09060f0b010203040b03071d0d0c14 73
    0x6e0100c1c200321000c1e4443c0f0f40300c0d51000c603090380407800f50b201145c1c000c0001001117100f03580021500c6210750000c8035080750702c006000c6419514100d090481e03060482c144007140d000a00c42c410360b03a01c00b10301c80e00c510450801c0700c0d45410124014050a10000520440e640e00c44451810f07194260340580c0d82c03604d120188040d440c011a02d0a103111040c1e4040f40051414040c1480c159020f541281d0030019292101800d29840e00200c0000030b2140000401c8160404c881500402401d4810441480b0741150703a44940c182211417040d511030b242043d400010329000fa80d0008913100d82440c1c4803030701403800c0528083c440d0041c00209102004242c6c1d01d19110034040c1441c3e510409c03d000c192200c0d401d00202d600003030b0602115020500081401d601203101d203a20740c6004510204100c1d81d20341141301162103440140341190010001070246d0100142140d8000001e807038030b00c80e40d80c60643c0201c0030f00754240312560f00000108180c400d11003001c4450080d2000c0c0b8074416004480c40d0100b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 510234442 1250 510233192 510233231
    0x901051509090d08040606030506090d030501090209030a060c17010b07061406010e121f060e01060302040308071b1716050303190e0d0204320705041202010c120909 72
    0x420003c0e404151010026807081c05100d82191040b00085109030300c035a00c290401d0f50444948201d07501040715020345540c14041c49004111100086152502c0400800c0c2c6955003e0b6015003510b48031544141a24818000d4a03503806181c0b0559400f5611621141e42940c09040c0a403034442c01c090480786050313460b503142d501403c0c050b101c4c0d4000c0302912043c400c0000d030110b00d00c2c1c10707406250b82883d105d43d442800d4440315044030710b0010b40b447c10101010302480b8181c01850405205000600c001440d42080302c003030b00c0d00000ea004450080300503c80c10840103400c5440c11123084500b00709501c10000d80d0010301454888204803041e06d82041c50b54070f0040c8280d40e0b00310b10210540104050249000300c24024018205040c503c0384c2d40c0102d03040d00c3c107240043c5404840c1a240e400a1990581c00b008404011109100790341480f6400034154001e0b400741c4284402401522011680603528840d89158010603003000c0444051000d0851111417107414034080c100940c2ca46500c880004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 510235692 1250 510234442 510234451
    0x20a15020d030b09100509060414070923101206180209120f0c130e0a08130605040b0706050702010b040f0b0a0b031e060a0902040801020d24031104090b0901051509 72
    0xc2e41c507885181c06c04202c0a40750242905030415581d00382e03c0b0b40e0b51140324100d4402d00168407415402e616101d6100081040c41ca000b000a8440c0c9034005d140e655414030829204405140165140000070140c0c4018a020781c041480d240c05c41c0f002440011454010349060501142d01d80350041c000314985868031801c07598001b064000c00342130101e03480c010200d044204400500050100040c0d480340d4a842c2c901001524401030100d841850301c5071540c1140003038660382c0346c028217062424242c81e05034025400c00515040d02d880004045074400d40c00b1041180d8010001d0207442002c2c0c0c1d0b010001e1000c901518003903040c1307000108a018080003102d00540320380e080c03002180448202880f401d80042c00660b44000030748000201947c0c6400a080034207121400180d03100d100e040e00c00212a80d540000e40b2041d00389042c140303003044256148003204c0d0800325449141c41900300050007040303005d200408940d080e03002d0000b407141c1540540d116400803068034030342020b45410401601c01c1101c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 510236942 1250 510235692 510235711
    0xf03090b191d12060603121303121209030e040606020d0e0f0f1002100605010e1003050c16081e030f1f0b0a080910020f16020a15020d030b09 62
    0x140422003446901c5400d05802d00401080320500440005000c03004100c1c2c4403040390f8054402c0c007015140030700c9950310044614003500e140000000705107802510b0391001070400c007070107007112155030b000f9592034116418a51f0b041103c209945805802400142e410701d00540c50711501140c1140005481030070a0070946992001d01401d0040221103c1c118400c10f421003040800850a6241c0c0c0001c00c01007840c0c0d80203454181c1d034860f1080211a444d5001c0e80c10824850612007154480d00c0030f440c3c0c0a60989004241076461036815101482055071440198007600100ba0030301034505e01408010b1134a51b000709154002c030141c41840d02066640040741035224000c90b03a401d582c840083d150510303030b07a007081d0f410b96103c00c010840d40217005503902152500e0108144484103200c1c030070742440340000c11414444041000300541c0a0b00786c5030707100c2845500500055641d448044801042c0d80b2540d418039003500400251908680001c80707020904140640441d490055520f5102d0030581 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 510238192 1250 510236942 510236977
    0x2040503101d03040b030a1503020112020d060f0f03020406080102041a16060f09060b0123090a030c0f030b10080a030309021f021e03030108060609041b030f03090b 72
    0x3918030000b0044060920109040c10002090501c800e0000d00300400d50300c12001e489103400040c88040c1c0b80501c96080c0d2003001c1c10740c00e02c0140e800508032204030500c0a030041c0c644145070800341c0142103e4101301d0060030804000500040b441e810602601e200ba5001e1202075501d400c2c4030700f80d00860040c0c1981c00b0a138440f58000d40080e01c007414001a2504e44082c03041d00e99158842180c03201c041003c9559110804001441414084d600c0450800e02c0e04800c6644e40c0415518400c0304240241c051490009490416941d0300d000100038640001d903010115688000700c590309820340c8000c0b43c50380382c0c03a000260302552030000c0c44102c8585901030051240d0030340e001c9008091201d07041fa88031071100c0712000034010001d00cac80511030058000b03000600101c00c035103540722891180c0c060254010001445081d00c00300700a600706206440c0301c8129140c515008803081c444203c4021340701011a00001480303114000f80c4512400f80c0c4903440219111501640c05105015900318484c101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 510239442 1250 510238192 510238213
    0x50103150e0c070804091103160c110f03010621050d0f0e19090e0604110f0d0611070209041a06060406020a0210120911120d0c290702030706060902040503 68
    0x42e0091506912549643d89481d8660780120100d40900e203030681c6015010003004940101108001811211402d04000912440d039036a81e035110007500d443d0180c2045103294800c1c0c4c40c25000000903101d440b2144100c43d49000c012500031600400c10b60307081c450000d900c1882400f6980c54150401c45070703a01602c200d4020b09001c5080e60000800003440c0020788000f0350304032540b0551800c0c4011801419943c01c09050107400340069040703207403099100780c1022003603692f02d03910044442c0d0700c40800f04051007010080210750080c2080603410040758405c10041040e5590300c00e0031204201030202407070300d810323050040d03e020300c1c0203100160b4001020980949452101132010003003918241c418bd901c408481400c1e0707500c9060803140221901c8084c1c8581c0340405040340368507a928000c040381e450300c1c83c000b00000001240a001c02492500152070185610520481989514001c1303041c0e0400390002075a95000304025074801c1d1801c0c5012640c80454000c40e011244020024405200d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 510240692 1250 510239442 510239461
    0x60d02030a1b150e030c0102010c201212011d072a020a17011d07060c1a100e100602120d0b0d030f17101503020c1501050103150e 57
    0x5030280e000241030b425000581c07120700c032400400081c150ba41c0c0801c0b600c0040e007418a0034102c0b0215030f05590611400000c0c1c50362008049c0180801d40600702801413150722024240400e50b280709401110005841c204140b0348104030f070484510441030500788100300700e03000882c48280c07804d10000b2580354032858075500626807501e03c5c1030401d44110740b5008980c000b40c0d8480f40c0394042820800300f40c008038aa000288a80c49401c503000c01c045442e80d03170320751215490703040300d00803042404070722070404040c44444000105203080f000c95484441c20a0901c401c4c1c0c10f441c40c8640400c1d038251400080d00c0e1010b110700300c0120741440d0001c09960081c0e42c8055031a812800b00e0700d00590381c1c0d070111070f01c644d81c4c016030b10103d0307000303444004460b10300388402072071515441d00401048181500740030308004200e8584045401c9940e950540d03541000c01180039100310007000c0000e110300c00c154405e030911188140c0c101c6c1e0302602c04100c60602c5e511401c2401c90300d88901021800031800265680e0b6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 510241942 1250 510240692 510240713
    0x1208090102151611191217090303040c09090c05091504021306140a0c0303020304020406080303240f030c060c0307080c012f0a0c14030c0c09060d02030a 67
    0x4a050042d40c5001c01c04014580c0700038011505030f401c4510100b0708460460f00102c0c001800312050b40074101c0d142c6008400030702241e0b2884d0041103040e070307081e0340c2c0c08151181c004140036000002100001e4140400e00582c0c1e40c1042c3c0d02030f19221510607001132030ae2100e11621075000e5010740b49440b91440c05041110314103004102d0010350711807041c01a416541d41c801442e112039103001c8809583e003804002003040d4105010301001030402c02082501c0e1760009004220641d261402590301d40e105c0c40841c010b48503942c4055010b11000c000d1200e14081d11917a01e5400301d001002c00711070388001080120003a824030800385c064004010314002400c1c01002000268504c0c400c0300d1514020b03a459000f00d9108104480c80740e55600e5a400c1c0c02d80c407521005403155404902840c83c1070a104800119126681d008018030858646005c100300d4980500001c20b4405015661151041d1911948480540100e54890040d0000159580c9000080c14211503009001095404070660f01e660499 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 510243192 1250 510241942 510241957
    0x90b072301020904110304050d0c0305040e0c1b011b32070b04140d05120601030b130608070303090e1b03040303060e0408040801232206050f01080d0201061208 70
    0x40d50200042185500c40d40182c1c1102c8060301e540642d21311f401d00341242040c0340031403050200078400324402c0c04298007409842c15108d40d00001d40a94403249054006031181007a45015811100c0c004040d000040d071100c0c1390280f20948004c40341c03403c01c3d0300720b50f0010a5148291340d03000780c0303d00d81100707644041a0b043c102e44a0102916100483c2c40d6201c0c018022901290000140b5601031495041400140d600c0906410720750305007030061136030075078607040101764904041d51189201c0c0d66554014400b6403c24189804001d81d1341c60300c00c2151540341900040d008a0160000019905825400144160030f0200301015804680200a041d0b40c00980258201501c0310000710312030250310a41030080c2d10500c881580c0710314000c50300d8252000c40840365070301005d407100d01d90740718a010300b05540b09000746507804206540746000602d00e101a0b5014004510704410450101d19868101c1c1c141d619942c2105c2c04064651012420303100302c0c1c041d603400c4606507007142000031441710203003084 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 510244442 1250 510243192 510243263
    0x715020304030602070c150c0213050411040504120e0303090603040f031106010e070806060306030a1202070e010b03251d0604080f0a0303060f0305330109020406090b07 74
    0x301942d03612020140d8000e01702c107489000c0002c00401400b00406d001e510740440d1414034040b0b281044e000204500809400b14040e10740301e400007000c0149044c8511901c9500030801c101600f05410072402d00c40240c908040862960201180d56250001c05e4480f0454014101441c6503100d590325540700700e031290110244002020556580041807040310b021304040e142e80130369841c0c00c5d04002c040400c0500443e026070310400500c81e203601d011a88656098110030401086070140700c04030310300031150780000f002e0100c20001141600b0941c00440c0a1f000074804002d10840001c900840300b40320041c06000708907196207403d944020700d00390051032400201030605180e903d00c2c500b030500740040b19100054201d4480c5604051300b610030080030742140c92616500360b04664030185d9955079140018040c006800501015115041d5005054403440d0080b0300d8950390ba108500c0a500540104004140c16900100d040f800003001c2d111010740010010507001c102d08020700015004042c80c140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 510245692 1250 510244442 510244447
    0x1314060403050f1c050301030f03081902070f050f03030f010e0a090c0608100b09010e011101020706181221020c0a2004061409040201110f1f0510050307150203 70
    0x440c0040c084202c0f086803040c0502140400b8105203c1441c40603070b400014410140014008a1420030396110080e526050030a5542c41c2d0b03055909024034407240d401d200f00d000281c0c10041040194003012610320031800c03100520822a81c1580b40e000c103c1d00d008100c0c00704001000070500840d001a00904182c90025030f0f01c0682d22019040c01c40d0b030b042503000c20310490078848661503c584c03c0004110425510303041001050009102c03107980c2058504015858030b1041c89000c0a5048400240e44140c08100405110412020700e101c528003e0b03403840608000c124490b4000d01100d01e420401c908146414071680c44814001c2d08258421003203841142c0d5960001050760b900741c0300d11a40e01c45007244c1c40b41c2040800041e220700c0d0300807114011403d0310607009504d8486849402030350901f4040c80009505680b14580034041a40b840a031041c065550f4100404541140e411092a4010311069440142030000d00483e1321a06826034094082002104101c034841c1820300c01501c140c92 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 510246942 1250 510245692 510245699
    0x8071103030109020909090c0f01030228091a030112021216091a060903030702060313080d02130504090b1603140108030a0f0f1b03030f180b01050613140604 69
    0x91441e00241c01641d1030036400a008991480e05c80c90f6590f1005101c0e00900724a286c41c0081469401c2414603241496000308a20114000180c0d912590324101500f1a010b00204100241503a0862069840c4d0388510200302c02c08201040449050303510b12004e00c1c038030f1180ca45c28003040210814251000d802640c40c41a8030b4400d42c5c2c0b160700140008400030030b085014071100502c01142c4040316104100420910342c20340c07404400d039010700743c0444640b92070781e8506031450351003403820750001d015100010341244280c602e0b6010708910407110b040e80000c00e458105000890b00103c501800488012000a0123038102500151407050f15250114000741184499040c0309070030703088020a6040400e0005080c0d6212194020240007454002d217082c10800019003151002081c1e04c01d200c0644d001c08080c0750090f0008a07940d912900100204506201000d54500010302c080b203a440020380001190302d022420f1701d10514800e01410211454000d603245101414024243c00c00c90512001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 510248192 1250 510246942 510246977
    0xc020301020d05010303080106020f060f06030309060c030304060f0509030702130b030a0c0e0c03070c080a031103180106090b2211041503061e0501030207030207180207031d100807 79
    0x10410801c03000c8021403d9415840d01500b00c0805821000455000c140d004054240c0001d640d5000581640b08203255103c50000ca41540f09001009401101c0003400b00c0c08201b000000314403450080d8010000c0c000c1030030644042c0c80059409900030f502c140170500c0545012070450104200b83e41d000912048a280030074106080b40307c1c08d455503240c44004000404d80400d50300e07400401c0001d490310314a0250300c080c0030720f8450754003e00f80007804104003122038025801204000c00d158400f0f5100d1a04407415042c1c00180e180c0c2549550902d100021402010700a29104c1d0708002c056010220402036610000326046894002071600c400001c0403c0389000b0081020300f200c0244404001e215040240940d0000c0e807250091460440a00104151450701d1500b80c0303009103800341e511242402d00b20328104842e040402e500082030300c0032503100c400354020300d51075119481e4000040c03000d03548014840c400d6407c51390008147c2c501c540d0302600c82d180c8150b0004090a01150794a54040070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 510249442 1250 510248192 510248197
    0x10030b010906031b050a0b070606080102030a02030109140105032e06030302030304051b010905061c05090f0c0409021507030504030f0b04020a0b1c0c02010905030d02040e010e16050a0c02030102 85
    0x2150030640d01e0b1002d2051090740c00c03000c201c151400b00c5150a907460400072031060515031080c1e5803802c401040120422919030009001026000001d5482c4d00f041c04540d80258404c1c8a85d0140314038081440304c40c1c0c0e412000382030494400801900100405030410304482c1601c1c4c9881040c800302d1045a2041821446903001541c000d5000f55120719080c5000307860701102d400d03240c8400704481c01c0420b02d41e900502c0790046d241c0c290340f8a6220011806591006005811034440480c106410454450400107200380351507001d0085401c8025800148000c650340040065084002405200f8440300504001c00c200d82c820304c2c14514080e85e07a100c0e820f11000400d411940340b19848240019880c080c0f4041e80034021400906281c1403500400290000300b500e04802c3c000d45640e50816458000e40c40410b0883d0404240e139516625660000c000754400e0140100e10130168001041e583c8541c01554403440703103003482d80c0340020fa60100343c80640046500208000d00a05c4a00c0180c41c02c0c0003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 510250692 1250 510249442 510249449
    0x141f2c0913110a0e0109090f120f081501080126120702040f050f0412020f0d020303090d020606010c201e120f0706140c01050f1501020106030c03060510030b01 70
    0x100304101c141646000501c502a07200501e00c0b0388000c2100b80702c0c0070b1080034040d046400341c4100240002c4185030000e0240980c16018100c10120203c0b480039942006544528040c00c0da038007038030769aa041040c00f01400e003190315400200a08014005505203913740c140705a00242400c425142003245a031804520b102440c1707503600040354003011820140141595410034020500c82440c084982d4280c40c14001c01c01760000c004841042c030a2402070292855140009095a01d154010300c13019550b0fa0003582c2250044c4a04501d0241a034800709c0c00c540100301c1650761203071035000741e02c0e1200c1c2c1300c09240c40b880e2264211490003d41d80c0d0740b90840c0c10036103002090686140840001c004207201e10b6004520321b9040f90070442090352000c180719098030303d00e0070320b60600301c3c2090311444103004a0300010820b6280c0f00502c0180e1b4105099a4416509417081000708403040e001282a103000d4407009007480e40551080c400941d29401156102c840f842030610030300c2d03694464010800302a0b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 510251798 1106 510250692 510250711
    0x31101021e0702150a02151501480203010f050402150711030a0c030c150f3b030c0402131a0c030301141f2c09 49
    0x410344c1d000008407991961110f1070070f04040c0d0b0b1781d401c9114a051452140340002c460060380e000881074600180d41d4080f010302102c0c038884000c030a0350810380300020410a0b48001e0051181191040c000c031198051003030205005140c2107410b2640310031a02400d003400c110240e120301060f0844803c0c4400a80c0d51010b0a05065282402aa2031140d01d80100d030100c0061181149000060700c2c020381c401424155035480c0f00c0301c5211003018240c0410b400c54050340726030b40680b15031902613030018140210202c400c601d0740600c400d071800381200c1c00100302001034a801c040083c2800c40e1415182189010514850444449860f01c180d424201c02c103188640e507107903040c09460002c05804100c0340ca95860b1a80b070303001c140c69501c01601030884c1c00496003200c8010304401c100c101e2540c07240c0da102c126012000c80c140754410f141100303044501440161989544c24490321604031070 = true := by decide +kernel

theorem cover : BRFrame.Cov 510071942 510251798 := by
  have h0 := BRFrame.cov_init 510071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 510071942 ≤ n) (h2 : n < 510251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
