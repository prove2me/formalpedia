-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2737
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:35:22.569966+00:00
-- url     : https://prove2.me/submissions/0d14d076-3bbf-4dc8-9752-919dddd8b082

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 492086330 ≤ n < 492266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 492087580 1250 492086330 492086359
    0x503070204290312070b040c0e0907180213030b19091a010602030f0423030d030f05070203070201050711040605060f12160e01080907090e0303061008010e04030815 72
    0x202c98400c540506144034591402e8400c81c10300003010900a40300034400c624007020364503015540c00300204210b0740958403107000309500b2600c446103070086041d440103000c02820700d031180c0a03414642c4075440301e50f4814803c501d4a00a00009e100c21070ba00001001e85648501104048420f44040d00e03005c401e082c50100b4080094000b6424440c60040d003080d80580d0b2180d904a03241d22441e070f01d0705d409900501090020742101820060705150341503907007025032035600c082801d0504040003800400c2d030b03510385181c82400398021254043c0e11132000d9854183e695001901354090300e28080c2c06d00d0403500d00103890752501e0388503501400780103080c1500c900354114120000c3d8080607000c1d20001032180803a03000e0002404070012824280c483d8030880203400011500408010092900780c8180c079000100540c1c01d20135204441c0301c4101656403454844140031b40380c2d40521540d010003c0074401005007400c0403842d5030b0800d40c5840d01d201140c4800c00d1011900445071201030344400c242e00700c1a0f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 492088830 1250 492087580 492087611
    0xf050f0a050f0d030c05041503060e0406051812040b09120708031909030c050d021504080c011e05030610030b190e06090106140d060f0f03170301120305070503070204 73
    0x224610300c841c044074807103800e0031012029a14917881060209609000611040801a030a070750302c446549000204181e540000c08031043e400d403819581c040d5074206008007415030741c5540341d0103034418005000e072201d005a20420b6125520900700c1189010a000c00303a50348a8034121030902d800400c40c0c400030344400d1926102d607c4854400c0e01484052071072880180542009402c581d0000f1030780f8101c51400050040d0f20440c0722040342d10030090b2212010505c41c49001c1c0001d4180ca03c000c2c011021801d00150100510b42c1070141714081d200071394a07910368004203c075889503058501040400e060f09094001d8500850580d5000684003112099032440562220840d441403603d21001d4450106205080e4001e0240743c0009442d03003048180745000c80010b14840760041000540380d0781c0d90f40c031200900b41503000005d43e00c3e1351003001c1050210359080c210b001045101e40a28552500e00e402620364074101005090203400310300b00703051140070701c01e0340d25864001c3d1007405804810302c18038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 492090080 1250 492088830 492088843
    0x92b080408070f0f0e040219030804051e090a0c020f03070317161707090f0b030105010e060406090501180e0a0507030e150a0225030e10080c070f050f0a05 68
    0x5100e00c0c4101c1800103035140110484008071070804e5400c20310b103400c0c001d045001c1c401c01030059070800015021180742500c1c09030781800460054410320f8640c0d06000400c00011001c1c034810741c9102a180e00c4030100c0e40d48aa2280d00300b4005071001507036451494082c0d05001c1c0c103030141105400041088000e240d00403401c1c80b40210045090380040eaa00ea04c40c1901c25a210200f00006641d501a500c9038030303040050036003000441c00c00b004103c3e5140d480c24030744010f6802c1040e450360040010082541c000650100c2c03003e040341c03150300b05414214024024142881128100500c5031807185c4040901c50268016001020000581c0c4c0390400382d10000d00825215040002d242c5400002e030690081401c10b00d214020442500544882d04042d003e50046145015524004d0300b8032020224460380c0485168030030746481101c1103020040115101d2042d4200050000d0b0750104200a40e50314112a0007035480b4091100d4604a410154646400e4050500741c5104604131882807180c005001e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 492091330 1250 492090080 492090089
    0x20607060b010e06040608070f090506130306062408130609050109020112021e07050c092e12030804031707200c0d03051c02030c070506060406050105092b0804 70
    0x4612060941400340030040c030a5202c0c1e003002840d0240408c00305072151601c0c0080d4081c624102c40074a4644000982903403000521441000c0d445000f08100803841c05240300426048402c800d5050302d8040783c00040c5e0a000b103442c00c01c5229000207020140140381440d480c0e030002c208010b0b04e103139490080c0c020300e44014140d0200e1103110443c02d69200b04d00885a134407012805e0140d07400b1082c038100f503141d00039440c11515802070b8441e60030162140c01c0594842c402e03043e111188640450705600c0758200300d424000342901803100a000604030381c2c0040103415410b00d007040d206c1d6201d0070112528946546802c183c0c816140c28003040c80c1e4002d04036517840500f050030b003400601007408142e665410300c1034550811084113620b030101c1c0c040c001030400caa01d150491140390450503a124100c2e403044429903040c407004519002804010054250301007030a80d002c00419040000181c0180902e141c20f92080401c0000307034030201000d4009510784100a102c50010400e540307003c0305282c005016 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 492092580 1250 492091330 492091337
    0x90c0b030403230415140309010b0910141507060f0e0d08090d0806011106010602010903090e1b0f0412050a030e0a0308090402030a0e1c0e041e09020d020607060b01 72
    0x7520142d0103250811030320546926420180313054640240501110203c0c0340103003c1c06a0320402c10041021000114418242000001040b4820400b00403082101038841859801c2005c1d080c0018440720000303104044040760314000e55026410400800d20420000038540ca08080503110280429000090f420640c54252182240042021140b06904031140c0750f056000c4c0480d005028060824540c0108041c900844140d8100c1580c0b46800f02c00e0b0f1004005079500c02c05441030503409254500a004000e40500441c1811500700b50602c2a1400505050900080c00c0c08111711241c12900181640408106520681d040c440c0e00d9281440c0141c01040488003121114070f0098542000d517a4020300140c1003984d05020700c00250002411210003079501ea0729640464002c0154502c01d01c4812071084048141c1b12000300000420481c65000f0b504020406400202d600d03c00100125411000608800c4138000202c8121200401030340014000821130b0034000640c024001343d500a88 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 492093830 1250 492092580 492092597
    0x1406010206070e0d0b041a0f101212140d0c02011a0d020d0f03091d09121c150905040305030a0c0215061306031502070c09020406020d1101090c0b030403 67
    0x601a03d0b0790030100720701580b11603464200700004803894103864100c0d0088145101d24500303c9280d46a006050710311040310211441002240d0b541c01001e0800b07014a1106400c0d000400d81d2080e0b4405d400382d030700d2424080c00c81031406d01c070500041035034007160301c27000709104800c24600701a00038008410404a518941d40d800390460404101c1100010790182210012000c2c9440305100c03000c841000302c08003c3d0030040051840203c080164040800401c02c02450034007140d080d103001d08070840c3c000003007014414980c0f8040d00030034540c10050400408a804080340d0400c11554031140c00000c0a1032805007801300340f40e88140038500c105061501000743e00c070105800e07070b9a140f400d001200454101c00c0010b445040211041c1e44c1f0510040001ca0190784030355450006000748078402004503408100017060003c414040001804803002c1145018109a0001d440d01c082400701e0083c029450380641c203a1000758818a08940c1140c00840c180751283e220300403030b9009503002d600180040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 492095080 1250 492093830 492093841
    0x18060b07030531030c050108090703021014070b010e04050d050f042102031b0a0e101e090c0c060c0503060a090b0102010905061003050d0f05030f1005041406010206 72
    0x20440e194150540c40381030500342d01a85000030600f500301103021004401903400c098604020b8440c01461107145206100c90501000500000000b00480c6290b400164200f01585032812506240e0009140030404680b0710328066009200f01d240003407110303c0b000c0c0001508041032114a008520540564404100341841110940910320315900c0c452020442000f0b50cc940c603080605c60300755182e0300340249d11139800007400c210001d1503e00c0100101030400c0990700d46414007074080c2c640070080390759500b818800b0001c101e0032400b6040082040900400c81040b01c0800c0b000100400d0b502440b420254140c0204140c62003001107640070304260b08024403502400a2784d10071403020b88610032043c80e1500010190181c1810181135540ea2035000011032414403000c3c0c483c0000551040865103140f41c203a20340150002c41d0020811300d0041c140b00b032039001003225000070b8450288081c0392a0318803141c030008203980c070960303005107050b0070000354501800906207e54001d800740c44140e40d86 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 492096330 1250 492095080 492095099
    0x20a050a0e0c1b01090302071e0e04020409030507051f050106141603110313080d0302090315070207171506090714030a0b0613090b030109080909090a0c1806 69
    0x9000c0c2809190031079000840d800c000e81c0c0030704040d01440c91244400c07028280b000e030844079401030540050b002150244081c10075a0b40f04c0f05180e619100c0107040601e04801c00420150203400284125110f07500301f03040c50712130002c1d1130220380c120741a5201348003940049010601d0a0107014034513410940002003c0b23000d28548040c43c00d030104001e00d440201003101c03100c0303410b1400031810300404c0142000525000c00140c400a0b449601d05000a03050901a61030881c51035220810180100008450350310701054800000c400d070300425072261204c10069003012210340000d08981c01c10300c450104c81c6400104902c00c200e1001c07100150f03032112001c0c404800382c219010008240c101c1c1c100d208000c210801103030b03c040a02000940d070b6440000058556010420b500719402d1440004d00c01050213110714a001c04084008000151039a902c1c490b580c080c00d808184201e801030000b0700c100d0814000390b0710341540107081d1440b0740d483d000001075481003403003140c2c0d4081c5003000c0803a88200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 492097580 1250 492096330 492096349
    0xb100b0a09230a0b03040f0b0a0c1707020d201504021806010819020f03010303090f08010203060d020607020402070f050706181d070207080703050307021305100902030901020f070f020a05 82
    0xc020f40110000f500300901a07003e64805041120714141600c6880301050202070010b008051034480841d006100b8100242500082c400516030a041c4905220001e45c0004460010303060f02d0a049000d002010509403400d6520140700d0b02134024080b000dc100c030049408248039074400c0b50b80e4944a8a465609152a0380407a100d41c0407400c50404100d146401422080c880705107a40003518028030282d040c40c8580080c1c0c407c0380407490b404402e01c910040341c0c0300000503110340c200847c21481c00d00001080c8030700a4802900919000074050155200c42e0102c0e1a81744d085000d285a80180d07141c80741d03941e034280c402c0c07c1c00a000380c0004110603d02041080c101c50740d0103050780282802001031840e400b00604150705511a166000030051001e0040c0300055001d071015540399070250040c00343c1302c0804446841040d103003204000003070710520550070613510050801602c1c1d60301e0012170760092003004a503135040540890751004008000d414410310b203100395107000500e60390300c052285100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 492098830 1250 492097580 492097649
    0x1401090c05010305190608031308060f04030c02040b04090b060f03070e041202010e06070206150105030408160302030f0f04090f02030c071709040618060b0c0a0b100b0a09 75
    0x110104000720b6110790000307600b041c0c0c506041c0c80d958042c3d09100049680c95848004160000b1806a0360320700a085180000c14910f0050103051401d0400c2c40f07104c0c1001080201030102842044066440f941d100603940c2c00c02a10411410405050030500070404903000b1b4800d001c00302103105e05080200300c140c02c0720786203841d510103034403540d0301c50a94103600c602c407108565a510b42e2068805d010890503000700789a40150000f030800d48106100170802010b104c1c14000200284400079507807604840005a0074001c40c2040c2950f481d00302c2c1507101d9a103491000c1ca4010607450700310880d480061044a011140410401c1d00780f2100105900084644281c85203080c40000b0129940b1100803070180030038900c540c6803400f00000035080740c03455000781c035088981504281c007031100d500ca6600904007190b4442e05242c0c103140070684d511040800104009035000102c2e201015581d414409440e418503007a440700861840241403074164411a100c20841c01c45581c0c500c8545125036440c0d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 492100080 1250 492098830 492098843
    0x101722150f1a03070e06030c04060b1305041b08100b03150a050a050a12080c030a050702090f160302090105090a090507090b0c120a020f01050405010b0a053f011404140109 75
    0x13246810314041442100803d4203402d8080c0810840d001c0d03480d441fa06014240b035094840d04e40711007500b1b082c48040107400103401030340ba250301241e001e02c42403031a103010700c16840e29034207564410320380f001c5481241d444004004030100512100040515244469031010745501d26105d940d0000c0004500091040030780002c60400c2c1402603030110b0092030b11040c001c000c0c003464944640301991860348980d00a01c006680400c48204603d41115126004a030020220a86042c4240c0d00214000c040807050b061603070024591600780d015200f5034104100080c0080d800e15a07850507440540012600c00000800c03001020504070640f60030786013110a4500108803107098160b10000ea54001d1001c0c00030b5101d46401281710401c01d000f8544158031400010a000100742c2c01d000c124080e0b90031042c443c2188002842c10005500301c204400450340181d0b4a00b1b04500031010554a00e55200041075420400382845d13080c548468180940d10174044216180c140009443c200c2d1a8460000d055 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 492101330 1250 492100080 492100093
    0xf09070e031510090213270b0d0210030b04060305030409020408010c0212090105090a090207150531080909070806010e06040608130c05040c0e101722150f1a03 70
    0x40c00003645c0a0820b2000f0761030800c0880303440c1c10203000c20a0001035628900a42c90014051001c141d0040859108042d12088000000360f03001951901e10203200030201a542c0e4150f100907912608450002c64021041da17aa5a4403400081e0195200d801904429070800d515035041d140300181800114415080709410214040011240703a03112424495100303c08840208402015200400d00c2501c80c86240200c82d0550b52050140c803002020281c1c18070380c007101c00c6c5030900083c1c04040048402d50440038161003034a4090380600917904c1d40d5802c1180c007002c1200240d005440d4034022507090325140a01406282040303400c0c4181d01900d400510b0a401203410020ba0306200c2d11024031409500c5480390300c070004141200c012040260004085100020f03003414803240c980b280a0f050301e0039000074150400060001d21000d440c860301d000d0a502249080c2e50000000d4490b9036000d0712002400c00c0c00c088000180401500d44402580703000418000071814006145580c0c10203009040fa = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 492102580 1250 492101330 492101339
    0x8030a0606090b0d02030a1b050a122007060e190c0b0a050a030c0c06023006030a02060f210f06090106021f020405040f0c1403100e04020f09070e031510 67
    0x5e5000504941c05042e125852080b1890b40055510a4100311380c0d1802e440341c0b21303004020040000c00c1000784c076041c42c14a8120303410f84200741b90854507800d81d99241d40c42c40d09142583c01040c0902d0031280502407610303011007142404c0d04881003107008800030102541c451280981038800c1c42c0400c000300b40200142c2c80420f001e90404610b440c100d081400940c1e00513150301c41a070b80030014600b00d1404a5481d0340303580e00010034600c4518402d010a04c0d8503c3c080c008280e8a110300f2001920604000c40c8582d8103404c644c0454044000e0307042c404041c203d280313013164030103a4195003010006110f1000140282410035400707040b60401d500604500c0032000400c810382461031500071600d0703000c020209880c0c894ac01140818507800d40006810b40139200c00a05210b010010b50000280420901c000417101e041088192071065151840e2922144000b440000350340307016a82280c0c1040800c101507401904658001000358150f5482100c00608188a503034100c455581c3e4440081c018032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 492103830 1250 492102580 492102607
    0x50c030a0513140f010e0105130b060310380d1217090d090f03080322050a030201060317270607081206040c09120b09010f0908030a0606090b 62
    0x160400300200038862030120940712410801a50710000003e54040b1001da0110307407091280a00c0c00c0da00e00003c000b1400d22903038100070f80c03450b1070001d8406905e0308041800c6a074244811100d0401c501802c0140034900700c013510704d410b16540b0014800725440241d00308640356801d03504ca0020000d203101c00c603140d26078a000e000f604503d0010708000c65801c1017040c400000c810785004481250040044050308030340140f044005802541c80a1840c1d0410400202070303501b41c81c0c1100a81c000a04050b4420680d110210a06034026110388101c003400010706806512500035070f80548030b00381d8410006049800340c2c1c4036480408202000341d0046d050281444140012036050040105241c14034035141c84203241c004c60712001c468050881808001e140511940141e11a00d0070301007401c074640003150320035000007203001d024200c1e204001801d80740e0a501002c0412822402000032000c1c50500484e2038004031184820710b80742150200c0d0a2740102c5c0d0480c101ca4001c15042d2410b0fa45d400c448 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 492105080 1250 492103830 492103841
    0x9040210030605040905010605040606020c06040b09030a0f0f0b070e030309060918010303110d0201050c1605011506020a0c120b0103020d060f0c051c0506010905010e0f0a090213060201050c030a 85
    0x140e08166403403102250640e10360150a0090b4010000410b00310702302400c0008032003840d840b150075580b08224a81050303c5540c00d80c0c0840343c4044405445190030b0011a00b40110020000d1400c803507100b035802002088820300d03055030b0142c060707002c0305e95600100366218840c404400b50b140d8400d00c000903180c13402d040108101080508044006603009082208607402038000b03c000c500c103c28220360807032042110500b02009c904c020300160510040440c240e21542d403c0c0f0b5a881040b142207014000250019a54281c14441111089aaa03100251034a10201007107030004610303c2c00242091f2200071120425030080c400754070a0f40f8541c2002619083da5408851643c1c4812100103c1e107114411041c00c454240c651503668072408088201c002d541c0c0c1a010141860007040c005207907402500d020a490081c2001d05201c0e0701400010040b0075880c400f903500c0040e03800007158400c40b030703005000449850b080d03442c0d080780c07100410f0782651130850b8204000c0805100080d8425601c0c0c000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 492106330 1250 492105080 492105109
    0x303030f01090f29240319020304080304060507050733090503090409031824020d020607080a020c0106122d0609020604170d020721020d0501020415020a050d0509090402 74
    0x10034485c0905018640d030410018803000132200e0210421014042c4441806050034000c0780031841c41c54650341c0d2040d18000540003520903a03540c00090602c5004604a40f0515080101da1200b140145002c02c2404000204200114640c22602c0706000c445d016614041d03a004003d181810003441c24440140480c0c401038003005240221040343d40c0c000c18a82d0003800582e2711762004000c100380c0740a070902014a01108542c4440880c51070280c1c0420350070303009009490800310b00e032207440380c441c0680981401c1c08019481c1440005115030480088001580b01d11240f008400c0da40c0e86c1560110800e00000d2400d62485000c60001181c503172000b03c8040c40146640e05058807000c243e08910007000c02282d26602000040b0f603410b4040100900404040e04124155001d094409881d5801120000d008410508030a030400c0402e40588010b0113100b4840d680101e500d000c02582c800144ad019280c07070143c103445405061003841282c3c2600720190201c1400d889942c02d00040300e008148 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 492107580 1250 492106330 492106339
    0xa031b15020c1608060402031e060f060f180103140105040b01060c08040e0a0f0b031b0411040816030b0a0506090c0a020705090a020706110421110303030f01090f29 72
    0x94444000440d248001134803140d030081400d0b103000d20616203001d25040d0307844240407105200007462500058140d07408840a4000c20f2a600d40902103090290000a025401800c0503003603801c042e54010140e040301d008030b0301988078021070800d05089401c00d0b00d01809082d03c00006100ba180202000d00b0214800c105403031805a61b604d404456940983d101d900080d00c5d038484006c8110103001c6d04c01c400c801100a03080e8008a240701d80c83c8203c001c45030900070b58136010740c4900d40441070705039001040d0840c1901d0100e060800c440340d5008190104460700354451011400e106071a10800c1c1c4500c2000e00f6401440c0c4030136180c0030340d9030007030f14004045200b000c4003ca1240c0381c80386010b004296648006d6200d030340b0307490030109403540b0f07080180c0c0c2c05c0780a006c00c211a2141c0c00c001101e0712030585604601c2c80850400c6203140f011081c4a9030140f00020030b0080320000000343d40d04a0703000c60010040401d039601c1000a4401519881d4401900607480310b9030080000401c2065a20081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 492108830 1250 492107580 492107593
    0x2030303061c05010207120f020c030d0c030e0a06020f0f0304050a0b0f130801060f05010c081209030c011109010305131a070302121e070237020603090a031b15020c 72
    0x141c3d41030aa80c0980001c4414005443d5451100ca070810301e43c2000c00c40300d0000d400e00094240c082942c400b4210207410401801d186e80a0034580140500e0303039880c40181012104c01d4545002079600d03400b030382d0140e200b8410100007110340c0601005543c1500d80007065203068502d080309410481d0060300700310900762401c01280c008100c1d00040400107012005c000b0840c070346840e000c950b0880b43c5520641c14800300d40705500014035400c080358805c4440d034040c00e15507207130998142d05d54040d44540140703075840c001480a11903031160140028103400d0360144403642c1c0d0a0b1880d0380743d8058480061112001c2158a4501203032203c40982c0700c4800c0c54018101040c400b80301c403070f000081e640c0004010391002c074000d0004045041c1030f80b2055900040015200b0b03185108101e6031580c08207095041c0344540b01e03d40d0581e1000c0c1c41c9505400400d126100e00307290000c1c6881c0d0400440403008200942c500b24074081090900e4112990856240310181494048200180d0300440901410f4003400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 492110080 1250 492108830 492108833
    0x28050c1003020d2c010e060c0a09030812061c0b0a0c030b1005092107120503090409031d030c0607080d063506130f060921170402030303061c 62
    0x280b0031143d20032900c0b101e502d04260b0400e442003904e01d03641514015a4105034942040050005185402c102910a01c55540703c0c060350445800340c5a03003004014403000140e0340000b940103481d250249804642c0c001c0406090150086c0d2103d11000040c20b5401c20400546d10701420b50104c810740303080d41408641c0384c030000009403988498442d0400841c2001c20b450000c1d0a0500c1000130020010503130840b02031078050200c1d83d5050781d110b07401981d03800b6208070007000020300603070301180380c06030041c08146022710700584404c0241d060f101c454494401540490701d0300003030495680c040a400d1a10f480095100c0d8003199120407180c0c200b245d1110710020310181110b411005800d0460030208600603415518408200100359a60306035100340140481c022a00701c0891201e81e101c202c403e80e07114149460300150111800141403038401500c4070032308034a01403100000400e2a541c024404642b4104900e04d80c0c0f09450194141d4024000159141806034400c400c0c9604403208004449a5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 492111330 1250 492110080 492110107
    0x150e0f010c02040f02030a0e010b0301051308070516060306080f070308040b18030d020a120c0c0e04050c0415090c0c0c0b030c0c010c020a0c14031203130503070528050c100302 77
    0x60b030f41001f00700e41d20390514220082c00e20a042003254118024481d908001c5064142541c250001911481d00020040f0070440d0030440001100812040d0041640e65020040d004003114882c2503014010340b44d1700451404086900002e90307030b000142d40d08083c02c5c0028010140c00c103082002200403447e10400c0c0c1a0350800c020f11590f00168014800e6030490b1170300a030202a017041c3e03c01030240782114000001c4601c25060700b9600d015460f0221a543d5091191601e140070081a030030a10307001442400304419031064050700c810700c8041c020440252001c44581420070009402c50100803014403d17900c0c0b001c01141c008074803000060a00f0400014242164001d00350140560301a040040401000d00750300c1009169003c41d1196040a0401198070f03040e49d43c00d1280300d444004001003070140102e9003242096080030480391913045520b00569030b688a401c1da817405200018410000445540d43c0d00f81c0241e001c005070411030340e420113018485201e01d500c2400d06800703005a5081800c0e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 492112580 1250 492111330 492111337
    0xd05060115030605150306010804060b12060417090f060f0c0714041b170402011b0c030c0e07020718020403081801121506080613050907150e0f010c02040f02 69
    0x186848211429461030700280c1242c1c440da21007030140d1403c41890955080c00360549900040c20f0900e02001d6940703140c00380081c00c2100b00241e00000000c00904e030180000350661140b4498010b0020044030030440c0405c50140c5081240d104850300e150082e41e0400201070005540901c400c01d003840c00d07803200300707082403079a402002c000f0b42c80341c032071102c2032030705001d4042c4500e503c07404403511012440004040d0b10080403029100c0c0a220042400c591260b20f490003604040904028107a40300e00d040c40485103c1c1c4400c1d20b188201c50307800f10743c0c400c00c80c0c0001e01802c280c0d002403014516004a0024510140000c0e04155509010002c0071426150080603100b01c2010068070305000e0400142044e01d0348545180d92910300040000441c507045a02410b84229050401c01c640e1070f4000100c04a50b29444e810015003400107010991000090490940d04511000d58003d00764507001c440d021a09201294040307c46d4020745041d500610b440c039a107600207000480c03c1c103001807810069a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 492113830 1250 492112580 492112589
    0x2a1c0c06020f0d0503100b0325030c0809070e011211130207031d061606060b0708071415010e0a0b120606010201060902030603060c090d051009020901080d14090d050601 74
    0x2c0200d10002c80c44007040c8008840d0f88611305029085003084101d4280c10341080c0904540c003000000807445070300d000030703040b260000d03030320180184c0001c60140103014020410804010500c440c000c00d0750068086151020744070010621a1161319050044440a001450584640030001d52100c1d0b07540342c016101421400d1410007598802c21031500403c0f40c805c0160080c51f4414810048104d5030f50b1600f2618943c400d094002104219801c2c1500103040b00d500078480d19a0001d5110300b0443c0d010060021540950131021180d481c2c01f9440703440c2d241c0802c0301e24100e0b422000501503800c2c4841d4641d00f1012403400050100440004228000c1e0074283c1d0b000d140d8010f008010302580e0900890f4080c045030042581075052032800705c0d41d61880500b10340ca0000002c0ba07c5541925000501a40103030000111a072808440000e4030007004103074816806840c1c0340001042d2820009008412030405686d0000402d10031598625103800c140350b4030f980203424869103004120208001c60280 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 492115080 1250 492113830 492113833
    0x160b040201091e0512061302040f140f011e0303080a0203070e13140603030c100e0a0209010f061e080403080405100c0302030f060409030203040b0a090e0f092a1c0c0602 74
    0x5400c2008018102500c940c1c04905c1e1780c805ca007040782580034a21411751031a8180d4005c21415644d00d0f10201800f80111440e007840800000c10401003004400707681220380301c0003a8401298116065000440603000240204903041c000c00c00c52001c950085500105030b1030310b890a04820b000207501140ca01c1440308403581c0307602c41c40b0301c40500c2803840c3da040502103008626201e20040c009446905000418201542d03072034040580500610003030f50b01a50040c1040c80d5580c4401c840e16460700d56029003c00903010012880c88560204980042d00038143c030750b00740a0f1b4513642c08990b5020002c0c01150a8016071410b510509041c0c000c1d10591500b90318056224a85034604c0400500d0081009100718117044a1030003007034001c0219010b94100c000301503520102448250742c24011503003c43c1442400d102044206113400c1f030860b01603a03040040d640f0034400e0f00130925400024040e42c0394403d8020240901920b08081c0c40c08809100c4082d4000300c0f415a103c09096184507401900075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 492116330 1250 492115080 492115139
    0x12c0909031201050102013b0d1101060f05180402011e030b040b061201060809031c020d05071112160515161e0302030403030f0f0b0f06160b04020109 66
    0x15001030300800380135020a2008000c828884240c14000c0c0040e80d0701c0a8401d141c42d20450406c0e032611403840e00a100310001c64142d40c2201600034003031880d051901541d54a004070200300070015000d082e0403154001c2200d00c40c00c494440034466024080c104078103000c2c4601c4203a460202070b0848010000c001e8030300150070381110007403009868071480024420b0504204140290010510703550645045207002c9440360b9441d4605881e61003006100f8008026407540e00307120940a800800c00510754510900003612009130940380c542800c1441c22807500500321140b801030034500601801a07140100a80300100c170788510303081521800c2c4040c0d03182440300400014411031032610301004050f251410f1441c0380e07201015522a235500305101056000070129003030500c00d820101e01a20403c0c400c119401708031748004020302c0d0304c2000d1800790f29146000d0070145460300686081704050074003440007144590700e529018030000d00481c140820201c000c2007035240d02105001402c0300701080581d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 492117580 1250 492116330 492116347
    0x80405270c09010215181e03030f060a0f0803031905060a1a1c020901030509060f061c080315010807020309030303150409050601090b1c050c09040303020d140a0c02030405012c090903 80
    0x1f040380d1002207420030042c0012a12400c0c0001040b01d5020615500b48a0300ba04c413074000640750340e00d903446485030100005010698000100c0114041d07400c0c030f1290352601c8906100c2d0303026100103ea08039440b003c41241008078204600c0818188a0160482d0746858109a10607401802c40d0f092064015408190310000c1d58061003400d411040c504020300f640d2604404e00705400d000240064001c5917001400403002c8000e4221100f0141d0064806460b0314102c08155903e030000c600040c001001c81780424242030003c821240110005000345d40f071661074850140e40c0c248060b00c1990070642c4c0e99150004690140000e5018000300e0340c000c0360684841d41040310160010542d041d40b00108034021002820000e640042080250380200855581e07080590080c010710036049400f40c1800e07150000c000300b02c9500c92051100c02010020f80f00107141c202d960740940d00845000c1070140986100343c0c0491030444104003400c4401500303a101d80000324010103003d4400641301d501c040347d003c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 492118830 1250 492117580 492117583
    0xf020406230301270605040903080406060e0601230702031e12090609010815041a03060c0708031f090c0c0b0604090302100b0d020409080405270c0901021518 69
    0x461020100d40d0390b0442d41841e400341c4100f140100100c0c5800c4650040d1050000c0c43c4c2c100400405000304104002c2c0782c5400c010f0715410040b9003c82d811840d145010800042c0e0585803809594180e40b45904005004000280351811120036441c4d20414001c4100690b0b08005414104c0b0047c801007082848441c20103103883c08200084c03c0841c1c060182407800d480e20f43c203841c041102441c05c6040303515001581040c0d4081541c50580090908000e42010b0307a2790000c121039101c083e0100d6280b40d854042042d0607000780701000b0204501007000c0742d241000c080185030301000300304500318219515400c1c002150500010349011030a02e048503070501540040596104d0001e45007801000c0340c55400a445018140070108e8480d030300c0043d029a40c6442842e141b440358007078002c20200d5154103100800d600b0070f11445100384840848846200c401506080d48680c2040c00710403e502c030028101441c1e04203106182c11031051b41d2140b00861100d654450141c0c80948001480401e41c1c202d45 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 492120080 1250 492118830 492118877
    0xf0c071e06020f07080c130207020d05010b12010b0303040603090318091a180a0c0302040b0c03120603190305160602030703060303090b0f03150d020a0806151507150f020406 76
    0x3c003182d400c00c1500704070005010039400d040540442c0c01c410b07203007038200c0410001d00624030069080300700c050980702040015070040d824030008a079824075441440d01031a0990300e4601c0303201d4054005100c2007000c180aa0042d40c04207100f4201178441050f0360000c0c2007a0b11042c0c2c01058503507203903600c00c01c000b03010701c0d0384441100c0e050399500110a01c0c1062805222005000c3c8400550f5501010b51107901c2a415100a00b13515000544d96003050100b06950740c0104c1c90b2000441c01103804500c4034a40011900044604100a81491149501c01780c900c0d80028408207034407203015a00d0303000a0010301c0110700c26009900d00107072003411818010514001604000308020003001103207004403030502620350115454a4401c0818040780100303408074280724000350045410500450501008030b203452003070000000014612180744200644141a0140685641d40400c88440440c02e03455691802c85580503010410120551a84040780d100e9480280040c001e040904540341881018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 492121330 1250 492120080 492120103
    0xd06090b06070203032b0f05060310090c0b0d0b131b0305010602150a0b0604030b07120204050109050108070e0a060f1412060d0312050f1909080f0c071e0602 69
    0x201c2c1812440d5011982d6403041c101160710011140701d0010901180001e100c032901e4441000b4800e1003025040710020701010b44283c0e203c2d0142c8091040c07088031a208003000c01e81c0001070350110910301a820382088e440100d0a5004d0340e00c1c0c5044503441e4a4861100200e000c4219000600340a0111060480c3c0e0350351a01e6020181008010080c0d00d03030009040d036102c1841076004180743c8440500c800104200401150414800b14001080c05865400c0d10310409081e21010383d0b610b03640c55030600300c0c404d5000e080e002c0780e90810b00b0300607544560b0300940d0002007800c0030b800c43c045000000d03107900615031084d00025400105c24031001e40c01386c000d01641940c40380003401c05020142c0700c0900b40b0002c00d0103014200426001080c14414001580c040d12801d1042040e82040324a1200b41e0808031040742d04040c1880750750282c0e041a00c80c0d1440030742c0140340d0714141251102c0070701507544404800f031076502c144030000c03480728011721800040d81740041001c0c454a00d8a10003904009903583c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 492122580 1250 492121330 492121339
    0x31080301180e1209010e03030702030109120210020903030d021c090606051e310c0507060b090403091809020307140a0806090634031a0d030c0602030603030403080d06090b 75
    0x841503a00c3c5440029507224041c02d0030684403440782400444d00c0c5003e40c080295140d82007034444828002008100082c0c0c8441d0340c241d64000140601c4c4105034498070a07010303010723402044100e0101d40c00e507001c0c10b5804842000034190801d80c1100710195901134105843d0f080e582c003010001c514200e0144005d01d60b005031180c000c031041c180024007010040500102a60302c2c4111120114400606240a0382080c60704120540004400a1143d0000030b8120b070a03a10342541501366103088600140b00369807659640e90014242405101040d4498003d01565600c0c2c00c408401a5014041070000e8900090394005007100e4908001e00e0284035440010b0a03003101013800440d11001ca15a980110019416905980d9400024042074500b51084108150700114141e5513541508503c640b01402c0300030342100c0204004200c0b8485200b0001404103824034005000660281c014542c4100c0080c01e032400c06a80703403170b024800c1d42710b803500410f520340d01c0005004440b01445080c19402050b00e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 492123830 1250 492122580 492122593
    0xf0a0e0a0504090b0c03070302070c030c08070b0403050c100201021c360609051e06071404080d120f05041a010803090d15150807180531080301180e 65
    0x4613040320140740030700015111280040020017540c0a07404036040c1c00d50100480795070950742d042c040791950003802400c070503028010000401c000c4c3c5500b035506982e000405051001c0b4141c3c20405502460300d840019550280141002d401d00ca2040c0414101c03804000b20394200680d8122080c0800009503444900160311441d40411490602c403404560000700014021810304181389044001a0300340c0041c15645146511402c4c0410424010340c43c941f1170182104503035420920170700640c0510500e680c004041c02c0a40d074810342e10400c03020111000040c41aa40d000c9203800c0d680229829208004410f811a08035640e03005600d004190b048041c50514891400042c044030000c80082c2049003000d44480c0f540c4003e5015881803c00d60494061160340c50803200c0e1504030b244154180300c190820700c24981c401501a0f40e100c1d85e501c24424040c000c0e09601324141c0010140b0507040c04414a40a070f0001d4071820056010f420071035030311000c540381c640262040d956110200344017a00140c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 492125080 1250 492123830 492123833
    0xf02090102100212191503030e011b0b07051606050f060a06210e160816050406050901270c021e030a0e091905130203010506010203030702210f0a0e0a050409 69
    0x1400c90765002840c0c0c003400100105c6000d8840c000e0601d40040500384501080004101501303d080183c42100a8840ca41e01800800d50b4030401071460034098040c44050000030070180c42070000f0300800604901080c08102d0548403401203c40894140c17840a5044007404190701c2c182d9901001841c3c01d15000300e00c100110640ca031050b8200d240021101d03101c99004035003400921030b281c141d1403940c840c4940341d035540c5600c80c1d40307040d501c184004401c0f80540c0480d0b10305140c003407401540d00242c000380f0307264a8076806030b0020b0104030807221403402490762252200b90700d0080d0b07607260080341d00500a240c3e12042c010300400c81100c000702d03079500c00c110f046105500145074010092080390600d110340d80b5000210103551004c98811416882d1074204800c00540c55003c03840c01c1d00940c020000c56030341c680160307038921054540c1c0f03000d0390220705a40c01d1000805110100c1c20f080500071800c4c00720030400d01a1036040020400c0200c0c0c4840d0824681d030030300a0254000f40b10440e000c2c400803025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 492126330 1250 492125080 492125107
    0x50a061412071203090308030f040605160c020904020402040e010f080607030618090201180902030a060509010e0c1602090103080304060b03010519051321110102030c03070315090f020901021002 85
    0xb144118451403065600240c14540103989110040d9040340d042a640c5c600494110344046085508540051138030307001c504003a00301d0100411040d11500c45c122014a03c3d02001090f180c004c03c01c0703a015408000116446481c105400e00078403405074030100143c200840641401c10051104d010986807400070001008941803202c03180f80482400682c140b01070004a820380c200d4111181119141c40e40019441d0455000358030a080d203400c01c1100544980c00c1214030fa200388034a11156280c100070545102d4090010a80a8548400d40511001c0c5a0100b0013808091b4019145d0660100070401807018502500c191a50f00718005c10285c90401050b4003c2e043c20040081081c0e0b4079400100c0407000c0b41380c01d003480e0380c1020f0f0300f190103680c40243d101c0c0100100e019000103408202009400b01050092324000c41490b43e101d400c554564200310001e01d141e41214000e11070b07480002030b502075244507408400c002c50401598403c081b07000a440d04540900b0310950920402460150740784 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 492127580 1250 492126330 492126343
    0xc0815161704021309050d110106090905062404060308070b060301090b07140c0303090715050304150f02280f090503070e06060408120a090b070203060411060d050a061412 75
    0x1411203030030131524505000c0c3c500400710150010305610800107030810203074100e21710020850094000380316258640c81104260b070015800101190b0111000c1904000352814124401000c07041c10341c9400107120004081c0d070240d5109903128600000c2d00801c1c4660480729960200c0d00368000d115060555848032641640107010303034200316441c49010111600c00c402c480c981c00d00342d000c40e034485c200285200d4a034841440ba1200c90280c4010b8040d0340c034015002d40703224030b1f041080045000c100e0081500900760b14144151038541c208407017400c140c1c0c50002c0400d070500c11201400130b010f080310041c1c80b00f08500702031401d10281e55820003c0381d034001400380a40c1c400003800c04e9a91a02804219140103541140c1c40364000c88013044041075015000e4024844190f86a00280f5601d4804843e288034040d4003075050f82144002401080104890b101800383c007900321031411305c001110030121001580d14007640c540b54a000c00c2003035500c0b441d5404030b40342180c1c4004040342c004c0c0007603510103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 492128830 1250 492127580 492127583
    0x1090c050616020301060b0a08071403010504090618033f020c0703050d020609060f220c1208180f09040b1312050a09060302040609120c0815161704 65
    0x8001100782d00101e42c080d206031000d501500030311985484402540268200c0d1105800189060000404461060341c041c4501440600760501e10b0b4200410b10025150880f4207440064880740352060383e8000c4403440c520140250368035070540c1c000d52079030f4807200700e0b035000180d02840030a0b040118243c001c100740c04241d2030000060340c400544180074101681a44003601d5070007020380d8504160340200c0c5192140300b000c420350703801c2c1d42d50a090201440703040d60802403c0d030840d00c01d1911000c002c140d00c10310502828800c0c0c1f815580302c08111444980d14021074100101103046880c90b010700c03040d590300c1d2800322401c004101007070000c141038640051000c1c20746100c3d900071441500c908030440140350741100801c2e0b1940480c180c098203d922200c4040002880c1d490001082442032003078909659003966180781c200e00d4250240c1100d0410b0009440c0e01e80f17030f0a8002012007080004440410315100c40a02c1ca181c410404000140c1d0f481c40103043c805c410b00316210320701a1f4150345503c035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 492130080 1250 492128830 492128839
    0xb04140111070306050412091a0412050708030c070f0e0601080f040606090f0e060609101e05061b060c0301080d27030302300f0f07060f0203011701090c05 68
    0x8070041207000e2a000316644054400303480c00e000e10041c05130050254440ba5400d48400c802140d8604076041203811340320301e960040405010900880720720b1811030040314021001c42d60215161010103045902c6290b610040e075011040400002d940b0700caa03400100086440700801e40740c2680003078650b502c000c0082500c00740c4c00300050b0400070103601c000042d104040c420440c1205e0401260010010758040d1101840f51400040c49450240171181c03203086c0c20742c0302640680c642000500d8485030300301241003011504102049540f07840380504810a0324801403c0b0510907020098106040070700b50034140300040005202448000409603e062024605000b0205002c444010440410300560000c003601d01c400100303140c0d0008840030b8100d030709802c0b02000150075420880c0342c0044200012402030a0112071100e01d001e1b005041e41e1241d05403a180380000c590f4a142c100d4200712501c0003000d50120050000a038030174243d00840c80d403c0001c00c03032507090b0b455000c8014400e10a45124 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 492131330 1250 492130080 492130097
    0x17030306010c031b08070b3709050604080301090c0c051c2a0302120a020a02040b010908070803040e10080309041a12100c05031611070308120702070b041401 69
    0x3c06110344140d000c142c08080400f90b0441e21454000350a43c004203041c1e40e01141e0307001254040300b2150414a0364075010303103045c8400304042400404030f2401207404840c15660301e03000002c100103201d01c900c5203101e11103941d074960501c83c0800842c0c0b9025010020052900800400510001940c1c2508125580012510381d00000100c507208854603200c1c2c0e2a2028100c5c2c02c0b14821082c0e00c1c030500c207110750255008803440020f09030b49800380c40c40160050b03003d01c1e0450050300b01540686103e020614002c1c00c0c441d00d51107207524041c0664003000040d40002002c11070304010f140100c1e00582c400411084107131424607130380c0c0c0d03034040d80350850301c60365a0b5540001c400455040c00741c0c0003080070301020107491401d038a0b540c40f520060b00c07241d100c43c100390030380d0f12080c8580c007182d1094441e50b010305500b206031401112501c065540c0d40d9503511594030003001007031122000d81042c0314a80303e1131003240f5107608001d0500300654012100c8100511052110722200c4441c0480100c0a2800460 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 492132580 1250 492131330 492131333
    0x4080114130b18032503410c06130506060105030c0403080c1c0306080c040b0307032607060b12120a03090611070b010f170303040809030a1403031017030306010c 71
    0x40d07114002c2c1d00050031304580032460312010700c05c0c05e004942e4000e403108aa034803002ca0507004141203a02141e0548441c44850242c081c5d81d000840b07860304180e50400c0d00309552281041e182030000d440240060302180181c2c01001420000543e01075401e180550841c24036503504100d600440c00010038800c00410390144504041010300551044038041941600d4034a0010b40101058026540383d07009100c5088440d0400e030042400100025004000d0782d4516184d06050a024060300707003094180300801542c0b02c03000c802400030036010b00f100080b000d21a000700708181c2206487d40c001130b00520310302c50580c40d020b0152401402a41004a0002090715040e0300030540403140d1907005c00003182d03942c24400504034081c16200b0301e410000c1c40584815210000100410700c030b8010398070800006002405480150682d244c1c00b41c00c580400a041d568400070015030130f180c1d042c541c400b10400890f030302255400c40052508040121820300c40641890b00ca2000400f41030500c000c80ca0100f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 492133830 1250 492132580 492132583
    0xf02030109020d2a050a0e07050f0316030614100e0105070206040e10051f030c1713051c0e0d032109020114040501020a0201030e0f010204080114130b18 67
    0x20845a00a04100304034107985416040c050444c6002a8800c89000240c60b00c8641c2c0c2040c042540c0d4010841c150540c0780000c022070303281c03009203080108607007888410300d040d0041001e580551144038100c030241080030801412140564094802030982d450760a40d191200c03003002030700d0002450324108440da490b005035200c0c411701800a41041c0c00080c001007101203d004540255414503080c0d00b4159140104101c280a201a2407540d010000b540102203000c2d91003240509524104400c03078045403020105000307800c0390a0310300301401705407107801c00c801440001e181000040c414551004440c800030130b165065203c50340280713004003050060502034100c41c03081458811800c1c08036803100712214003070154001c04074045220000708045602015042c0d405a40d0103074001c002040960300110003402d14041184064090300740e102150140a00091026000e040d00125002c40201481080c51a00034039120500c07105107250030016030f502e0001a040442480c564071501c81600340f06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 492135080 1250 492133830 492133841
    0x1504151b15060b0706050a0e0f071e0306020d0b01021011070204020d022a0c031c0f0e0907020c120309100f0306091406090f010608160507050d050c070807060c0f020301 74
    0x20360a1000114a80c4c0422429030030083c81012119402d0002880d07610380c0703170366441d00c036903012005d5003181000340200c410140219070000c955a0043e84041e80d60707214841240c1c007483c11008820f803100603031001e070b58040010840d51a9210010041000e0207a641d601074003541400030b10898001809260a440c9034060b280703040180c18910603101815242a030084050613030160a5020340040c400319440c0200d0340c0900c3c05002030fa082c0c1c140741202c02c2169407800058540e003e005040c800e850703840d200d11040d0780c0304040c2c0d5001401c0c070240b80c108001c0d0700c4080855803a0640d10800410001ea1152401c0404160721420001d61842d040301c001e1300582056004612001e1602041c84503d0b485010464010360b02521444100e80300c040c14002904401d00400c0081000003000c04c80c40f0740c10803010000840c06140c09401d2012690310581801f5903200c2e860006000810450407180c2d01380540d000420700000100300da14170300300c0098002c00010401a018541c0c04048206544003034110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 492136330 1250 492135080 492135089
    0xb09161112041403070b1c05061c050c03162912090a0b130b2e080a020406120f060f0e010e0a050607030908030c0a02010b1504151b1506 60
    0x8280c0c5550301c846000c0c108410701c403c55442071050210014416400604440321012240e1500c071451581c0d0108030040c00b009064150001304401d0402d000c0014200900002440707880504805052001012701e0481c00c042004114000540e040085c2942c0804c1c40340c0809031240360940304040c03800100824041d46240b029007210180801821101c0071504815082c420741c0030308030351740340c41c0500d040001302d500000780240781c9a0040341100319842444203815902910744c2d002844100786042d00d0b85c501e82e01c141c005a00a41c2c0140440c941405400e000d0b2460300c1144c0300700c0b10076803200d8446800300d0030064100c80d603c00101d0f441851540040302d0310003240c002481402d030510612340d80c0b007100c0441981c0d58010180420100361290081d604140e420100540c2141c0302c01c500d0b01c6240c1d100680b518107541d42c440107841641c59245800d17140c01c99403051039403114030301501200610ba094040100300403901804c103030b2000c0386c100c8409010780c010f00580407610101e0a102c0c000c1c0140d401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 492137580 1250 492136330 492136363
    0x2071e391e051c0b0f061e0f060c01270803011208120408070b0903130608130b130303140f0114012a1104090201050f210115030b091611 60
    0x203010303504030503a03443c040854850f40302e140407503450000d44900b1702020749199502407844011455903810254441d200028000c05204035034034550009000d5a22090590000b41d450b0b504c41c013a00420341007414a4026401d0740c2100520403595044024801401f0f40c031016074040c41c890003441954000c1d10001481d0010f2114241004c3c289940d16402940b011030f9440f040000190041c0300101c103a40783c0000168003892007134142401502e44410041c12103101580c80328540e000f040e418000c481c002c809050031017068541b28100101910028001c2500e40c0c040b9409005405c0e0402180390b04403001114052807108881c0d00403565901401d094907014600c0b044c40c0c45880340014860f12820348151841900c0403060802d00003502c000040290214806104505101d41410000e2407000484240251400103000f80140505001e802000c611102c00aa000c85103805d44111541a001200c0915007454040d21000002210344826420000206041c2510140070062441c400140d0369 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 492138830 1250 492137580 492137599
    0xc070203010204140415030c051012050a0501060f02060403170612100f0b01030e0c0d0f0807060c120b0f04020f040b0708070b100308090402071e391e05 67
    0xd2120407004c00180c14800c6180240707424540d80021120703170480741c0c810f406c0044d803481e1100304402903209074102c1c028019a00ca401400843e82c2c1314452140303003e500c000601d0b50510030014504001c600e80300d01594001d00a000100783c109000c50b80c1100700d5a51107215545000120300d40b0380400101d40c456108031a1450394032800c40c0c0200e4140d480700c4108200e00c0c101900114240c80c01e00e814254503030801c1c0d0200309942483d80390105880e00500100c00354204564840c10658840c001c01e81e0301d2540c40b04140c4601d54801102c041c16904518244038040e07107540000c102000e82c10205104650008001c84045404030603100140380041c1c885495261038104850b103a07008941c21250889118001751354115514002030550303030401c0300d0600380306203c4c05020082d070201740309480c0320401305090031301190701444080d40140f0030344250642e0707040018140303045c44003030007004001a003114485054412084280003150030456440e200508508031007202c520541e08440e80149111 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 492140080 1250 492138830 492138839
    0xe04060b040912020c0612060d03030908030f150f060d052e1505131703041503020705010e06160c0606030209071d061602122a1f0203120c070203010204 67
    0x240c048803e196644d400355014151220304000c060722900c2c06044400f080000030800e681064228041010300c80c0c18002491a426180c0f061150411152655580805010001007003001e071341504031a803040d00c900441702540d000103140c038082d100c40c0a4100b0340d03450010314003004030301d031205555403c66200143d020010f070400e5040282c2e4007a41900111052020030a18402c1c011140c0750a00b640003591050301700018410881c06548001220388810700004c0b450a1018502d101e0068080c0c5005955544030719145094070305100d0180c0545c0c12440400c580c0f1040300c0414611085580303044041c550740382c600000140190381010790804a00c0b070411014980120310241c01d02e08068a16144500707820400c9404e10529030041e407004944125013006003805a180031180f944401901c603034100c0c024599107451501c681c510100d43c000c0f0303555625401c2042c8010340041025104105042c160400a50781b07201d03415403903a00c1000c01e0f000488030f400b0b080c1030702d00780e941c010300965840c0e50f41c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 492141330 1250 492140080 492140093
    0x162301050304030827010b0405220305070c09020d061401020109030e0d14060f06031506030a020402030411370f0b0304020109120b070924080606090301020d021206190e04060b0409 79
    0x38147c51030b01407031404011802003a00e5003c0c0000300040011101c0c1a0902590220740d80d4121000032174590108520100301583c1c6800600400c071000da00010380a40351550800e401306040c2511415645401c42c0e00020983c0f0488403c00841c0079241400c00000902d00494504410130058155000d43d0062003200049007030010b002c1e2004404a50b00c510204801d0a108401034546c0c5500d41d00858401005007003a0300595400b07405050401c440140381001301d1200d418050900b20001c0d1840f102034010302030813030780100400c581c0a031032540a007444200d0400100c139000d00c51403030300e0200c00503046a00c64090341016000c0649402c10014061416104081c010703150000861640c07c0041105140d00c0002caa01c5106130b1041258181243e605442501c405403c46421110030061003030142c80900040c065451030b40e400580e034401c0822540006d082c042d180034031415100002e510300c6104080c5580944d0401d844900700ca803100d240c40801000c80a6895030020705000c0d044060204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 492142580 1250 492141330 492141341
    0x50105010f080d0e040f02121f0f12021e1e09070827011116170a0c060f0b0a08010219020c0a090509030c16230105030403082701 57
    0x103410841d0560588508040303845042500c00c5900003404984076101c0e502d4550402c900960400324010324115224448010013242140d02c040c03c2e240d1140c01c1112241e520a00f4401000311410300c078401070401a800f00b55120a00c006845003035584503e01511030b842c1c2c99000301440042c0000e44003045024501c8401003c0e211072442030341c0500001d141d15000d01402440361400d00c100da1a010b200b000c0c00003072848100e030520000e40d81c854200128100071801400c0c064044c1c02c0003c0700070a240f604800d030001c4098017080c0078100f40103036969140c1003c5151903007944808041082000916100c000b00708a00c00746c1d9200080c0800040d00010640c020440402c160440b1843c00b101a00160303a40d402c00c88540b03403c1801118200b0907400b080d81b0107a08142440160f9142a40c10b170910391800410040c03440940d140c1a10410100e0020b0034100064240d1030081d00b07545460b017001810502008001a040c0000000000c081c03071122000d14941c1994001011920030802d80d1140c000c18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 492143830 1250 492142580 492142589
    0xf040225120507080d02030405070803180f1215090f06150102102c010603230609070815090f01060807091409030403020f03030d06030609210206010e060604030602030405010501 78
    0xd407042031036109148148112940150410751951501c041c0260450081d440104103032044e0244203408200e000d824801080c03605a0320660540c03004e03464040005501440c0d0310144600b04001110841100c04241c0384205010b401c51920156130300b03e2024281841c0601d1802180281e904003d802c404946194403d05000c1c1c0c200e400080403810b01a045581c4001015413511b0b80c100c40c0080090345d40c40f030030080c50030040042001c2c0e51320317580e186403c2d11040c80740c0e16101544019040c1301c00f040200ca0f0b400600d540040c1a80c2c0d151082c4507403541c4240410390b1844e1840000603050140404c5424200b03034001000b08000c55440d4486900d50096018100806042031304244191607154462409000b410380611324051460307003084060340300002060b405000610420360f21010074456034000718024071000c280242d407854044070074400300e50700320648031900c843c54030501d900050090640d0490310541c8003d444020020b5214055035200401c1c15000004201c1086019002107040340c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 492145080 1250 492143830 492143843
    0x20435150f0a0b0d060b04020f0d06031208070503070318230d1119020a03290606030c031501021c051206010203250609020904030e09060910050f040225 67
    0x50702e941086206443d2001c1603e5402601e0040d000003040440d0301028511728010700051901300c11211a01c05500161000c1c0b40c0d559480e07a04200344924024214444851841d1004140c81d11100150050102030420420540d6505a020340044004460510a40c200f808200e01203907804074034110001c46003403212240600418440070902500d48030080080c80d001400c103448000d600000208000034060307921001c001c10000118651003401c0907100b10900040f442d9040c40c1325024501440a007082d401113400f0000c0000c200702410a80340c1020161003031441c1c44a410300100c0c50200240749034121414106000007100c0d4005000b001c68102d42c00d0351401d207070b60307a10059840e0f01600d9100d4200400d10982100c1c404602c1000c5a4190702c610b20004041225401103035060b601241c6c01c0740400c12400009843e07240200806900282c00c07944c004451034400c0c0000d242002910525000d41900c00048143d40d9540d0103482c08002411403400d0710042d18000c00c0c8004542810030341d202c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 492146330 1250 492145080 492145111
    0x11040801050a0e19030315090213080607180b090315070905030111030106020604150e011d060a050105030715120f0b15072f0a060305060406050402043515 68
    0x904201080307540c90604407001801d84c3c0c80d0151020740240c200c107210050050b154040100e1a000c8500c068007811a0422011100d00d0030802141e1030000040c02c84070500c505500140d005c18010804402a14481c02c07034640ca071440c500100380b41440c0f10b00e92080d0150186d04112649070700100c606c0403940c00328002d01c0241481000040c01f440b0038050360005800c024009408504d24035140c0c240c540d01084001250321000d443ea9084540f900710940070404406401a0013240404c5019002a51040300300650351400f00000e9031080c0314410b110141250ba51091402030055046145060078600300740640240b050380500107101c5050000c3c4a419940720491000582c4826070301100d900c10f01540c503900705660303100d00c00600400e0103030061042503400f030711315124040854010309031a100440d41d8100315040109940b00d54000501452060104101e03102d80240042125844e8146007050264828003d0308102d1308000031601d680318511041f1a00028500034a12a403c002e40d22040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 492147580 1250 492146330 492146351
    0xf0221010b04090f030503131209060305090c030c04050901020f0c0601080d0809060601082d060307120c090b0d02032a010c0f02010e2404080c09040302030d05060411040801050a 78
    0x1220030043c000307088a880a000000082d00450055400c80c1d174903070f038925a42040365513862172400f110801d41d00003408101c040126507054040c05402c6607501c0701410b00100240003003540c8040380301d0b0051003941c80da404201401c0f1300790b044030240d072090b4010aa94550ba40c0c442c513590743d42841141d0030340c8102c0840c540e050784030b014424018030032100a04044c1e150a8011200310201528a24004070312410707251210700d1f03121200c071001d111040c1d6035100e8a040c070100b500340045030b4003400410f41c801441c0e000003115046920141eaa00e81c8001540403468030108203001280745000750188a4036601200444003503800c52000e6000b501c229100d810345600449642c192864000c10450103803496100560007070345130441014000e014054800d802c50010007a0351021310386000b080c0000a400d1014501c240981c0c0102e080c01d54440446080941d0001c0d96449440d800c503402a9540c00070030040c0d655504222882c0b03240071103e944554a0303003400e600070002a0b48208410b03140c10301651 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 492148830 1250 492147580 492147589
    0x130e0c031b0d02041710020a170717151f0f210e16050a03150b0301090203160303020f0a0c0e0a09050105100e09010e030d090302010212090c01090e010506030c070f0221010b 76
    0x11002120369171481d49c20001050f290b0183c060103000d4109000740b8030f00d65841101c80b001014400c640103101700303c00540700001e00180b8070154008100c4100662803d07020250000d0509041035114039150f4100103080d004220340c0450106003500381c9040c0007001041c0e403000102d00321121a42061b1034425607a40040000c502040c0c400103103642400301c8801040000c0340e0100e50316500240000c21602401d40c0020308005e0281e0f0002d040303115000c814014140e0401c0f858207581c9100c4010918140c80713440d0641d51510511401c00014501d00c0011854001500488500e55201c40203003c80e060003104001c850f038081c011031000c0309909000900f660414000c145070040300c0c00246140000010007680981170801d020b40c203540d020000307a800c0000f2240703003503c142502c60140c03e0710001500010b00b54ce00c154049500b013003c1000520250f42c40f482101d40124000701065030f211110b10300f01d103080341f0411019600c004d510342c0d001c85800001c80d00800f0142604002c000607a0b1410402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 492150080 1250 492148830 492148837
    0x203040e0f1b2208030a09050612041b090c020606010e0102010b090f07113304050d200607080916031e020414010308130e0c031b0d0204171002 63
    0x82c5420040b0b64080741260384900105100b8009100400380340c0ba401c0d6407546070110941c06044141c1c40000d102e0202c030b81c0103400c5005081e0845905d450585401a070705c0303003400d0107000502928902500104201c00140100c0020090083c05106041090301d019407220003c071011408aa12440551a10b41c410311a14a085000030a2202d194031107040341c0d441e0750700c0203100e0030911540003420300c40c031481001507040d542e10000c1d04000403881100c24900fa54928004602201c07688000c0c0b01c00560701040b01400e0407030030315000300c0c4501080c02107600c92030700d107661801c980180c106209800b070b84120810303c9450010101c0e00044100c44043d20785080750701c0040d00c0c040604141a2140107d0b900c40080540001c101180300840c906441c08400030a80c800c442c8030030300185d0111b4982607428044010f040c00c00050b0024540401403d0040c84014415003036a03207100892242d026a41c415904811080b800440d155511408403010540080144000a110b031103143c08200278517000711f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 492151330 1250 492150080 492150091
    0x30309170a03080c040f120203070512071503140a09051510140613060c0b1e0109051e01120525290706050402040c0207061b021c030203040e0f 63
    0x10201c8107801d480c115076000014150078141c0108200c0080c3c0058400300f00d00180a55101440c007c000342c0c8105450401250300ca18041c1011040405920b40d010805504030380042c510400700c0344001108030b0007001380413220007103408800107124103e1800d9011146841c81032084500700100c2d07118420b0380789411200c00b440e15a0103402402004100c80038048c641070090407590410b460f0500108c40030026401a000207454081803006100028000030b42007995105200b1800b10b0b14400014400c0050103a2001151034a01090080343d230500703e0a1944442c2c18039002c0c9507190200c0b0100108203c005035042c4c45240104d85254603043e035428008000d90081c1c1c0242c82ca061080d41a0090f10382400d810014194034116496035120001c0c00c0d5107100311800940c61901d4810001216007081c07a5104650002034180b082d103402a14031008990380e0303540b0740e072007141301c1c4000340010040f03800e69800c0048c034094503010590008094429542e0004007041f0559a41c0e42040034517808851 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 492152580 1250 492151330 492151333
    0x207240f170115050415020c03101407080c09030d0f1214070818030f07020a06030c02071a0c0715030c0f05041e0506190e151213050d02030403030917 66
    0x1046080e840f018040d42402c0d042c2800d0b402d00e5903928200b02e00041c003008040142e0814501c0075040d240038060f180403100303441020000036441c41e010318820180144524207004005000c1854240400705880700c9200003800c50310220030f000001400c4110340103102c00800c0c00d80c0500c41ca04038060150496403460003024120503581e4501c00c984880f00a010406060821828000c00803814001480c080385904101c5070348107050710510000c0001c80c2c1c401d404140c075000f0082443c503408519002202c070790312000300070520300507102149071151002d54041885000710000390481d01c00078480301c0c140703d0b4804004060954006849110060031580e001a608100501c48104a102c81500844910103007016a039164004180d0303980c400e803982c3d02004c5030b0100010200782e00421303403001c010042e0b49000c03440c441c104180c01d841c028400319190801b0307142c0c000b0b20301a506a200b8070500d50890100c3d2800841180040c0d01ca5200303000990006012620100e0014401d122108034860180c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 492153830 1250 492152580 492152627
    0x70f050d0f0602071e0c0e0601030e0d0c020a0527100305100c2006040b09010c0e0103110903070605030f0604020304080a03090201030b09090102042909100207240f 72
    0x1900c6100075444148100c40b030b1955510f4001501015100a00301c6501c5030000c6c82da07081c1440998900884000c00c860b04040c1410600c4540b024007140441607001c540c2004250b020003840010304d10301c801e0304401d0b000b244122140f806030701d11901c60300400649086200c99604c458140280040740c03070001912075400010b186441502c140e03c5290782011500c1c0c05d01c0c0364010203508900d4826580200a081d501c0f010a00061005103407003282c02c064500000c00014250450140008141d42d0303016042c1039403201092851700c130b40c5c001c0f40d81c90304000301942d2000c1c1d01e03100c2c0a00355070005c1d902c09c150040180000380035410140b00b02c030f000c1d40d000100b603401c101c400d0310304034050a99540128101038540d03101490649480310007501032130b204000903803034900303015000e001110b003500c02e00540e401d800140b20301e102034001240c60308101504c400f06203905035141a460101d840d031094041c0d02804694028051307a070803140c00f4010980d50b98451034442c00b002160801c1c011859140d41c200d0306c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 492155080 1250 492153830 492153833
    0x306090e031e07051009140f0d0e011403010609031203110f090f0a03060c0315050a0608040503160302070f05030d0801090515030109050303010305150403140901050d0905070f050d0f 80
    0x348030b140111032111003098905011503450905045059142031202e544a03140c030010040b00110764020400500000c8c403e40304001c06541c0d903040d02e40c0d44041800130f2100135610326441000d030902d00311031380c6070000d559581d10b10f0002d003c0361440c80140c81800c48582d684c143d00d0301c00d0060010504140d135046061200401c0304c00b49940c48002c00540c011000803032038550341c40d2010340394001c5010b41000a0140f071741e084003030140c845000b000c11080840c88028040c40e60354021601c291406441e0181d0240c4d039506d031507482d6114a104018612100443c035008060f40010403105481403c001080503650318024150350f00c0c00480107001150b90900148110911980050350160030103c00141c0552140007003070844494000903140c035000000144207200d003c20503294040d07210340c014031039482c190302d001340854503c070101054004c00041404a90381b181042d5080300c00040c03000c111242503450496544e01c1c09201c0c0c2d80303071464070140c000341030700d4030300d40f640503494202945442c5500305 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 492156330 1250 492155080 492155107
    0x31005061303060516110106031a0a0207020a08100c08070203090409170a080411030f100f110309100518071a040f0803070b010909020d0209040f170a0306090e03 71
    0x260000740314070041008000082025805201c2c0150b490305d040307021120f04480c0040c1042803070500e12250341e05000302040022240c0316625046031013002030000503110001200d000c1d1180240107035111007000f90100e03c845011442080c80320801d1010840740042c035100740c81041e0f040340c12001580091004510701e08082d00031401c0305119600c50540c03034100c002e02c201130b90403102c0c200c000501503604100030808000032001000d88104c00800f104200e00360300355540e0000c1e0102ca201c59440321800d1081c00c95a400c10031b00005d0340085940c680c901084201d42c0c505191402c2c0d9007807030400d0089032502d00f11030f403846d00085038000503001131400e00c000d902d4004052400500104820400003c204a6242e070110180c41d1076800b1350350311981800e000c004991f040c2c1161202c3d40c0303402400c030010380d5a001c41c2c81c10301e03034152040716443c0d5850501d04213203000d66a01401880a4843c0c29000040d110000c1480c041c107618100201a00c5800132000c039000c00040c000160b004100e102d0380000b5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 492157580 1250 492156330 492156337
    0x70e010e040507030501060b0a020f06220c0f09141501080703150b040f030506070201020f030a230f060102190f17040f030602120703200306060c061e070503100506 72
    0x141d080b544000c2d41d0390369241c2120b900ea401708c1c080160200380140b4103a0305000306554a0140402091030781050703060108090500e2103c0390098018440c40700c200960940090000d00300500156001a0f903404001c1c0582140d440482007030040c403001505407842a0040000c032001030751132050030369400070154018a4441c1b81e803001e03942071000000c1c19440300401800900300c55100143c0c09440c2d4900140f074a0701c09040c0005690060003100011908031040e00d5200c46181380201e1562000c02e0300464000f20681c01c4131405c50b01408000c03805225504042c020402071742214141181c41441d0403003903034940c80042480b4203150444e00800e505100140240c005001d0b11480c0594a42c01d01140815540c02207079816008030708215851b0f40d1100d110740c0440c0d1b6090900450100c008070003012803440551440012010020503220307240e01c03003501c0405050000b1294a0300b00364a250044070010510b1603444c0c0030b1100010403062065080d43e000e0800801400c0c1d17050304190410000f0b40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 492158830 1250 492157580 492157583
    0x1180c1517070c02030a2306010e0a02070609080a03240b07060e07120309091b1205091f0504060b0f01050a030c1e0f02010e030903150c160c06030b03070e010e04 71
    0x407000901c0700c0942d6041c03003081181403040f55488603606c20820107003c80c7d01040448882038100c407004001d00c90409460715401529800010794995a03841c00000910f90b4200180c91400c1c089540000075815500c005c1c40600c60000c0c080e0081c03002040d5441803a03040c0608441c0e110203125090014000750800c0310f40740c0c00030b0705841789552a9040781c100a8042802a00020700651082103641c0c118490918008882c0b50101c040c4e0700400d4010b1300101d181c1c14078101480c2e943d400201c42040604c44280c001100140c68549100700c5120070000e071406503802d03100c5c5450a810f01e034180c0f40c0340c18020031841042c1c40340340c180141807070141e0051603181c2000c014840300103458038601010400d00856601c254480d204c0143c424074000b8215000e581c0600100da00400c40004550360001d440c2c0c41d0906420042c6030a5583c07448006154014a543c040c506507040002e1401c112481d00d8a000340c1e5926501084800b0821301050fa65981c00c3c03040801c10a003801c0140540c00801c0011030340513 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 492160080 1250 492158830 492158837
    0x9160605090904021c1208090a0209010e0a0f11090a2c040c030f03030e0c01080906010b0c121201031209030f020f030c1e240906090d0501180c151707 66
    0xc01c3c0008081c0c2030b0b031700c1e041d007200c0078041024142c3c00b43e600540425001080e0750300910f1462101c0d408a01043d4040c010214800c004e0030000d08a040b042d0002d0081100d0168207006d03601002d548104607402941540d48500180000031a2614108411040c0001e00003442004c00095004146552001801c26038814002c41000703c0070030305076010002903a2082c5c4e000034661540048450030b049050314640d041207005018003208243c00036245054650f5140c3d1690740d01281c60500c4d00e0810107510304000da0002140c0b50100300441c241da10704076805a03000c00300543c14041f085541e00703400e02004084c151070000300c60140c04c052820700700041000d41196040d81568000808400482c80d500744910711040f0441e01c0c5080c4a0902c030340713408002031001c070f8011040164040a004181e180fa000c0e00b40800c0d1842072381d9440e072110380f2403a000703c0200310655641c0100d62054032819001d540740c90200c000090705081c1e0140f039591100540e903d6944141c03000551103030b485400380c402402c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 492161330 1250 492160080 492160099
    0x2d0b0c030705061905010b0304030e12010b0a030606061b030504030303020f04031a061302090102060406151205030c06060a03050303151906030209120115032411030916060509090402 80
    0x400c00c000341c81c01940b03c0003204c50b0612000200700d003694416002011080d1044c024000040c0d00480c41400b40242106d480810305080c20000c0e00400d44100859408140d010000060001580c405401e46510b559444c08030181ca0310004540881c81034000c0000b0004c00c410400b1a210b40d0180c52a4840c2100f00351800d82d50352a00210401c00180c030406d41900c1d0ba090020074500034a0480d100142d131041076091288030b400213525160000d102821482e10350700f10301042500303614407a0107003c6070405960210400d040040d0b6940100908618510410020070f08521302442c1007012643e102d0011031450341d4503022454040304120402c1c1d0480f4030903c5550845440800000282455640050300e034156101004401c0800c5502d412141c0d03d000e0300190803868203070040081c0d0fa040207100181c1c1344020340c21080c00d80310441c41c90000d4605036140c04038805a000640c041c0b5107880c100d490b448001c950040341840c440c4180c0340400d034104a2000c1d281416030445511900084c03007500c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 492162580 1250 492161330 492161333
    0x80603030301120c05040509030c15070e09060604080102120103050f0c0904152009150412080f070b0f04020907171605090a151403070e010311130605042d0b0c0307 72
    0x41c0c7e00252850340c550381006c62482c040da5010050224001405030b5801010701f05a0070103450044085492802003c00c840043d0280c0c448204a800a001c0c190085503150b5440015110706202030000722004e000d0031076400000940081c010341d0004008183c0101c0c0c2d166950307850000c108144218485540754800800b1900401115000c00d094003040c1d1941e0707114000800254002c9000c150741004000d100074070a880030348100919159101100035130356248603d0402090007210350080081c2003080030041185454150140660320a40e10148a511548026198000c3c40c204035000c03030804c01c00050b40e207041800418130000c8942080392030b00904c000030403960303046900008855410340c2c10460040ea03200302c0401c180c500b00803902d821400e200000a000001e482011030402d1303110100000702000d200111907801e51180780224070160b41c0e06024200380c00910031041e6041d0461035813900b0314400b051006017060381c04600c1c03920f9030401c11102c440d038002c030304414250302c401c0c02003d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 492163830 1250 492162580 492162589
    0xb090f030c090703051b18061e0f090103060902030f04021009090509030c07080a08090d081605010603060e01060608060909030c0d0804020f040608212106040c080603030301120c05 79
    0x70f00402c8103907808511840e241d00c40321841c0600320310001e0010310400c10349501c0c503402c007100c000e8418100c80340c0d80e441e01303030200072010680d08aa005060460004400c884124400300910030317643d0030b0302c06001c841d50300c0c80128100d00084901607540213810000600500c2c0c90b1000304038001841c20203111045e1216080000c0303903000c88410000d07906c000b5404400c02d20800c001402010007100410985965070741d21219400b0f01c400b000c0c090114058014104502c40064844e40010710f510180c0c001d51500f4002e0190407144000d50340705140182c0031103510410700800d01625003545030300b14141c03601c806210050342c008003501c800740001d01080c429803900b40885854902c440c2d0ba5490642042d00400c0000c0ca02c3d0416684074501c1e143c0100001c203001705002280d80c0c1451828400b60403049680d5000c0e124036031460000842011024200c80207000d0654024181a01d0802c40300798a0407050318502000d4417074907819801840100b00e241c40c00c08094a85a1142500c0d0002d1a940c50216 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 492165080 1250 492163830 492163849
    0x12030c0d0201090618020a030308060f12102007080711040204120c050a0e071d13020d0e0a0b0c0304050106031a06030d030b060307050c03041e050901080105010b090f030c 75
    0x3001030b511608600180807950041000030400d003000c050f44440b0a0780015418480345c4401800d1011000008065a4400710301030101d4401810701d00c9a03c2150240a45072070024100c16a500d1a1190000c52440c840c1441c00c200c0071407500b402c1c5001d1507a2101c3c12180c0010500311a2080e21340c10055450700c0e00e002810080c00c422040781506146841e2010280f007598121602818165038200100c1c0e0184034255007041c51070901c1c52680c0c0000601c0c081c058800080150040d18020141c1120f0017546d0041602910303101c1c01700003840c1c48202e965100e04411030040c040c940d81d0008103014aa44000861f0014031030000024455500c0d80c40c6c1040011034413030403240b0440e100c00c1000906052055000311342080c5010032009040381d001450500024040400b000030201b52941c02e001c003001100d000c1c101010642203410402400c03401c0c04240f501450340192044400051280014010181a034880008560500b402c038020321041002d003d440e0782d803610a854508030543c0301d41503031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 492166330 1250 492165080 492165103
    0x307020607050307030906030e03030a0e0c120610060c0210140705010e0d030b010c0f1e15020d0b09070c030302032d101221051c020c060c03041112030c 67
    0x51030316114241006041800035512a07c103150031b00151000c0a20040100c0c1d92280404400141c181c0002800700d242c200c0740c4032440d410000c6040031074410700c0e000842622502c0300b885134001d02c83d00d50f1021900e954000c68000d400070004041e02c2c0f111800f44116400120b044d628007410310310103458103401e65840021040340c0c1d4105d0f940d06042c241e4076003d00420380000703080c81e42049003141d03611f8103111450071020309013005c00c00745035041501341c016201c0c00369040f2030002c8440b000c8000e080300a600c458041c0041500e001d20114480c181800300510450032901e84805e00380311510158080e510040001d9404010380c00040704e01d400002e0341301d08402070008a840103150008000b082140590040c0281070119500c042c001140c1c091201c7d081d2703030340c0f8203d00031000000e08155010300078002d0710044045074031070040e10900c1c158040c4c00541c4080c0c080f240140c4401752aa103e070301c01500c010f02640a4114060440d04200c00000078440616041380c0c64420a1305005081c43c0e085d065 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 492167580 1250 492166330 492166333
    0xa0503040b07022b02011110020c0606030c091902031003020d05010203270706050c0a0606181b0c1b03020a0f051504050117100506040b0a0f0815040e030702060705 72
    0x2580000c0d8140b40e89240b0765040048020710304800c5039200e019044c284194024100180e0500b800c4601d14140a00b410420790342c0010341d01da00a81076181d4603280d048407428044e11940c0c2c1c3c403c9141c68a003203060f01401c2002e081890071648102000701030350006010040c0c540d92000000b0050301c405c1444980c07103000300300050316802c00d0300c035800990f0701c100030105004e0485030340b4a85400c408181e140499080d410700a80d00c0c0500c03001304d07040255001000d00070b03910f4504005415040d0040414171844900c1c8200150b5045000215440c682010303c4400207008003a0303c1d0010300030900100e40d12401220740042c40340d4035400500c3c0c0462541100c0982501c460b0100410709100200300781c5242c503081500d04290610380001e04201c9000c01e80d6400c1c1105002282c0041201c8140c0e03c0509030107000c0035038a5407149044030040e800500c1110008101c40e4009441c02d2044016034000d640314001003203242031003410400030700784104074400c007400100103800040e07035010020506140324a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 492168830 1250 492167580 492167587
    0x3030a09031e0803010f05041a01020c040c110f01060812041406160b0726040b04030c081e19020d090302040e1e070303020c010801140405131203150b120c0a020a0503040b 75
    0x1401e01056424112441281848449c22406c282e0307004600c501c1c0007041650002444a0000c1040702d004162210b603c85c1409042c0220150203010b40140055543c80c0b01160000b10304407178141d03c13910881c814842407104600c500e4009207450b000420b01c2210240d081e202d40c2d0820784964034150020707110740d400300d90302603800a1100c0360482d000c103038025904c5507014180380503100c840f03800d500140000e0410204c07401450410200405440f040200c440c0014a4512080900b000c590301c00301082005021400440c4403840c400202c406c410f52050b69420003040c075541c01d00000c0c0c01e0b08414481d1500901105054161201480c01c0700c001121008005881c650708029060043d540c500504020900005000740304503860030100700501036400090740e58902141090911004a000b45031004081590502c103526810407504104140d44000b00b9607601d40d01c0b00150710941700c8104030b840070407001600408888018000c0000540155064080595034103800c550058200544004012 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 492170080 1250 492168830 492168839
    0x1e02060103120309050303180111120a0b04061214031b03041d0112140c04020a030b0405010501030b1e0f0607030908010605030115090b151306020c03030a09031e0803010f 75
    0x406001c00c1c81c2c0940c1010405138004e82c0f60291248001441c0821050304d40600305928102503100204480d16906103940b150740840da00102c240d4255185400d07681481c0180181d80f410703109900898003201e4002c15401550f9540d640c2c2d0080000e44405103000511942a13940d040c601007088894542000d03603030f51410170704001703034061620705c618425007291001445205001801c6050154200740c0340032400110014a52a01c0311400b200ca0304076001090180382c2c1905034200c1030a400c4c00300c40602040c0e0301d8500440031035080f00e240a511810f070044451100750516502d0010040140c4100480c0b0030700c0c00440c1855120340c01c1107000a080c00d03c20040c10b9828480c04d0040c00084000b404400f2001c5800d030f41c101180d02033342c44500d41c0e400c20229103588508215519441841c10184c8172950b10a040074811210b108000140c0602c620000300ea103408401c40749400b9a6440b240741d428110303158020100424031480e01c502c07804140140c0800d0010b070185000b840130015944556042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 492171330 1250 492170080 492170093
    0x602030c0706050a0b210a08190e030a11010c05070815100608070203070303050c1216182411030c100e0303060d08030c041802030601020705120601151e02060103 71
    0x1c02c04900d0301d1601700038030f01c20b51b00c50341940414144078285180351411030450500380000000c2c024803a520001c0c402c14000d402c540c020810f602c0b03646800ea03081c0e101d041810349580c0f104038002e0012803201a401000c3d070103103106004c01030042d002ca402468451420500e0b296072089401d1800342d03c0c001300044810310711840005840c691070655a40c0c2001d1001941d28065100001e0616072100006104046114155103450490a02c10291424007454171080040d401c0000340c0002c9650400407080d800f400d00d56000c564a0740c3c5084001c401000166407400742400d4803104204018140031103101d0200094800485408050010303840c641407560b04840000014400e41d404c01e101700301c003941c0c8022031070710616041842c040da20303907803070500040a2290303800c804001030544115410f031f00c040f540070b144500401c2c0c080303d0001e48c0303560820403c11407200c0300d10201d03441007005012070b01544283c0c050940a5062201c8a00313407600080c03205109060000f00107902c4140100f0901c503070f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 492172580 1250 492171330 492171341
    0x70e0105090108120906090607020d0b0910060b04090b040b060403060501230907080603010e0708010f0608010510090c0e120a020916020706270803030a0c05040b07030c020d0602030c0706 82
    0x24900014025001d509413003001134011900d5080c42140f01098102d03e60726000100e6000c1e40e8020040180d02c8010301d494126000207031072114440c80b8944001c0c17000c9140d849040107650b19101c04a050500d0315000780b0140002c075001d260000c0c0c0304c0b0103100a035218840504003640c8030784404201d540c10a80010350445900c0343da06040490680b100d08551156204550000d1075450a8035281d0345a40210303000d0300c1c82085920041c407070074800140030076042d80000c040004004c41400100d5a076082a42038a0081d20b806e0910b04104204000b000140c0d40182c103840402c0c01e040405251040c0000c589102d442c1c0c81095a41107002a0811440d01c60311556000d840450042420044040029a03c100c036004500501c103941619044101103c181e809401c43e00c44e03c1c080030b40741c0315409140c480d0000c0d00c50590450a1181c40741071240a801907800340e071034540c40c0c9414450b00743c408982c890b03449001680c001351000e0400c4003113201c0340002d512884a1300c0d10155600d0007490078000700c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 492173830 1250 492172580 492172589
    0xd020c0115150206070527151b06010303081305010b0301360804090c0e04020f130b0306091501030e1b01090902030405060a1e0e010606091502060711010608070e01050901 75
    0x42200702001740954108050341c69541118054031010b1401e400ca00b20140188550258000c0d054a86401c030b8920b01401400c88401c41c440d070900382004030202c0c65a540c0b003800018003044140c00000d0300c0d00c510300c50000b900d41c02030001013107a4030b52a001c2400c40e00d410007440b040b071207608100314440128030f01c1b41c001d6100103000000daa041d1a200c070a4180a02c1c09540b40f800d481ea1035400000c4d108001c4a0044a4001c1045507910240f1841440b103601a00702c10000011480002a10481000030b403807040c1006425190030f41e07980da041e05400d03100503500c5130505680c0d070201c40c8256010000188041b90082210100c144401c0c0007404059403644070070b4601d4010010400010808146a42c0003110194003050394212405d4044100302c409050140703ca10f03103e801c0001880c1500080111542a200d115101d910f8004042002c03500c02c40100150b4440e4010582c400d1041d850552200c451400001d040c0d5202e9403218104044c1d03a0100c080e007400d0100500c61840c20455460040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 492175080 1250 492173830 492173833
    0x5070e27030a0806060d090b130c08030406020d030f090f0609030806030f1903020309060c240402010e090c0f0703030b1201060503280b07170a050603120d020c01151502 74
    0x320380b035030008208600040c0f6a82c010703c0c000c00d0b801071100e0590000840603510039010810740c9421225240e020f0f50b601400d03a81181e9030000050b0717060b004007c40d000e81e26141e010b450301302d103606030603800f6041c10780000c0c91030356a846071b44022840b040b00c001c171400d11801000c44c03130a909040c01001101c1c00341c15148a41c20490468081d05000104440718a0410740c2d0803410706090305040e429409000f40b00c0740c200e840019000c20024001c02d0f15814111440342040542000c080007909171a000c0314000e01048685910b41c03511700e0103c0400368441d1400b80070900e000039a2183c4661504071400031004641c841c101903241c0c1c6008141b8101e0100048000c1103a1440c041c0041d0342c0d88401c038840038400000a136a12002e0114000d21800c00b5042115603440b410b11000040041e004250003803029100701d004034002b035029010390707409500014000e0485a0014040d034505030301c82047d10080550030803107610346810a004164506802e03490100c0721a1901c0003440484031107a4401085 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 492176330 1250 492175080 492175087
    0x1509120f0909050405010b030a031106011203050906090409060221060f0a15031811041805070603110712030c08010803120106050a02010e100510091e020705070e2703 73
    0x8681c0100c066040301c001c20000f14440d00c944c20f0960040018650007500743c003440e5040800d05400420480304a868001210700980e0f135580307802c039000880b12000b400500d0400503005203250010151103007100080001900c0f03460340d80c43d24202e074440501140c02c00141030103031040c0d00e403103081c0691042069401d0031108510000145110310786010748a0100410315091400f10310a40c40050800300200701c01c0c02200c005d0074a1030140018004891289062940203550302103044070382220640e000008002160922a0a80c0a8001c1700303083c41d0300c400140403030030100710001442001c245043c1c80000d02c52400c04001450404143c00202d0182c3c010055803403051050015a41101d15601d402902c46066420480c0500040c0c0f8002040d8400c1080e03070510a00c89900c4580600d400c2a14190219a144004415105d2101050f0181c0c0d281c0200c003550710b401500105903992140c3c0c181c612a07030301d40a14180c0d511087e50f1405000520510031600380203801030b0250500c0c4001c00031400d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 492177580 1250 492176330 492176357
    0x1b01060e09011835040b070606050d17030c092716080402010309140f0706080108010905030f0f21040b0a02042103030e0f030306030106050406031203090c03150912 72
    0x40c58501c50402d41544c548101d981d144020f444440381e00c1520940300c050340c0c07695a00100516908035281c00d9603c986005400941031601085044030307540d000e12900461401030590f040d0642008246c2c81d2032000c10000450703269220032860303945c5098000601d81d2014068081c8070b403020300500380100c0c0032081c00e04000c070a400030203850f4029424a0b0106480516291441c0190041d04d4a00110300c00c1001d407041c0c00c240414000b0660345140d4030024903a84e1100054240e0b0b00c1c03018050015041003140d000702ca0078900040401480201c3c08520f000d10303900c50200e840542036035400481c4101410f00007007011322000d0f250411101541035007802d052103000f000008d840d4614010112803103c0240400d4080d40250300b003086180180c1b80380090341e1401c00c4c0c895101302c552510030351801ca4040f071145018490348054030313040300b071303a041c0107202001c03d50003030580c1070007528500301038140000042c40e07820489003180503155001c15507401514100300b0252680c101d98041c00040c01c5210b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 492178830 1250 492177580 492177593
    0xd0606140409080711060d14040b0c031303050c0c0a031a01060c02060306090a0f0e0a1b0609050d03091806050405060d020303031609090e0304080607090b07081b01060e090118 77
    0x80600d90460318070124405c580c0006001840380b043c2c070840c04d5082407441181070340000c60451040c3d0252085070100c0d030310a0200d40c03a900c022070301000180300c1d02c0c0019001c244110090f0441179102411110581c0300980018004995640b04a460741181c0c981c1013000440e5410050040580303040046145945600240050200400702402400c0c144000352114089400146144210800030403840021800c0035032a680c010405071210368484254800100b08500c2090403140140c5d148100b59080c00c081000b091600d0400b68200700680c040818a0342c03140c1005699524102400142c142c1b410303040c80700b038410081c0020b02c1510038400301405600c011040700e510402c0c3c1c0c9025000e00b00d800308151481c80c116041050558a090904d902c0701c0300000080c070580d07600000f118016a074104048404103401c1c0030b06046903009006050000c0c113044054200e0201982e0411042245545801d0840d038056020440c0d100c00c50302800040d80083c82260300c18031440b12032040c003c195850340c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 492180080 1250 492178830 492178837
    0x90d1409040209031906020d110c031b0f0f0706030605030c0a060f09030c030b041a090c090a0609020d050703061508180102091302030a06150f0f0302090d060614040908 74
    0x8078060354001490b80300035542402503410750508000c506042c1354181c24030344000c0d0008024401d0701840c00c0b01e07104091800360141d40c0600c0044000310f2412b180303246070040400012030005c206201e40c9004100000040c8140f4651101690081580714540a002800d56102e0360010307000e40c0041004450369115868280240c55090600c411200340c80b440460f0903000982c4041c01c0003010070300110812088205150080c1e0041c1010b40f6140c50b45207240704049015510002164441e00c18a0114142851039651061400b440040d90503030b6540c4074410b0342c2c0500000070383e05544500300401d154141c0b04030000382900940c8103616501e02c21010b40902006042800c52941c0034503545100d03e0309404a40c5c0440380a80003403000d44600380c1e60703006074106a811404850078103501141c500e00c1025444401811035480c401000840071003a200d500b00c3c8036806040503001c0202e070206480d10303016495902c0c46140000381207071400000341b030120030729460940301e2401c000c0c0000c04070712450140d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 492181330 1250 492180080 492180097
    0xe0a0b03010e07270605070c050603092112010303020a050709110a1404080d050703122a0e120304090e010b090106110c03061e07020604150b0d1a090d14 67
    0x84a00e124241d4a00705032142c00d61300551001c04400021905580c001c1c09408000c1c450042031000a4039902004040c0c0022108400d81c0d07400500e40309100000000240080c16010141a2070f0040542900d29212001d03081a40540d2003540c0c10000c000082110100600c02000c0030810b000c00000a80034502c41d0003202410000e500c40e403500c09154840c2164001c0140e1011500b440e40080340142c12034120400c00c1e004503020b604820b04803911343c050743c9504074140c0085403181c200b00803072103d00060001030f00c2c10050140f0040c4030f140c8070016134070540c2c48000300540e12540f070030004c1425200e441e02110800c0c0d04040011160b6103074090341905494030303424080501031146646501e030044001d000c95140c8a94400e000d94544448149a040f112004c0944241e9950410a83e5580c4080d41e00510552000c0c541c0a01ca040c02e601009401900901e42500010705031034400209055684424110744030f0317010700020060400c110051375000c0d04100d41c503070064010045550082c04203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 492182580 1250 492181330 492181337
    0x14030607120b060c030a2a050d0c03050c060106021c090503150615160606061106040303020d1401031103070501020a1104020d060b070302010b09060d0b040807020d080a0e0a0b03010e07 81
    0x8103505140e40b150140c410140d0b07070104986c0c40302c40000004052082d15480c0501c880d6600106600c28076420074040c0c040b0b0781002c0100300c0d2200300a8222018030400c14103608102040c44a5115060b0502065000b0b00d929801400f00d0013403508035001c0d05004c014860184512040200440d84012030991040b400d2000050342c50381d41c00c00801c49011158400c0c5959000001c0c038070743da00001d01d58602046000344020441c2540b0368009071754503405051526203c2c4d002c01e00040c0060f1181e0001c20319611950808155841c086000310406042038008627440360034501040c1c040c0c00d08011380b0004003400d100034030000110b41c0354140181c4c030b0b6404441c0119000500281040000d8000200a0844001041d910800d60800038001c1c07640c0030000303124608140c0801c2c0c9502c0d04000194a030758004241c1c0d8400d0701e983e03450001e15840450226000b1000049103c00310f503845014003054119030f26540002003045081200c24030301c4d60801800400107200500c61126080d400940c00f40207400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 492183830 1250 492182580 492182591
    0x9020102010b03060405010504150501081504063206040501050a0b0f090a062c0102030d0b0406030b0c040e0603060403050a0507061b02010e0c0a080d1d0a030605011403060712 77
    0x40340541100ca0742c2981510031030381880200071b8158085441180111700000d02c1c3d1008855503001e90b00c00b031107040b0306544104075400461204200982d0002d00c03c0c0f4000680e42c40c0c50707407001078103070f007a0040c1484d41840f841c00c614030310340c03883c80301d81c1c031480c100e8041000d90b0609000840f134140078080e41459030401b1544410000b148022910280f000600c108003590343d92400514a251100855003440701c070303a4024600c6220b8012400100e00c058000c0c0d810441c0460b00207004000c641d007440d50141e2546030010109841c01013450180f1400764401da81e60342443d200214035070000e03008034004d92020040002181e44181030341d07101d02280c600325075514103a090500c003402c00303010103480b00b902c1001400d010755015405054135900e210309a403856104031080200d4400385100d00e0200d42c201c407500b001c0f11031055080c2c2d801c0340c00c9103413010b142200700f6012500614079034000300d8000b680d9000500150350100c088002c41042240217003d2442c1252004100c41c030076909844032a600c80c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 492185080 1250 492183830 492183833
    0x30f11070b1b1e0306042313020a030c0b210402060d050c0c01050a0510080c0306070c1b080307060b062802120c0d091d01031112102c0a0609 62
    0xd208441c0040302c812042108100061004140760b441521802d2050345040c2009510050303002158111f000b40741500c0100d075840c648d807a0206210100c080740d100c0c0135582e01200240300c80c0040d6018060745403034603495000200e650000d005210b6107400b258000c0340d00b04001617071200c080303c1288044690100d0b00b030b120500d07900280c1c001c066140d11554240800c11032002120b0380132034401d08001080d407030300a0390f80e2241500d80c48945c2c600c0f501600548006203585014205209100c2e110784482d4a400413400215140030402d6081030300030383c03c00140c40c024000d041c0208080c108040342c1da10714080b0303100030b10b1440e5036003007200c400ba0780d03203060503861194002d00c050805500178114050342e5100c28111640c94070100550b030004a82c106001280c01800160109401c54806c5080030090342035856061000d81c58203001a401f035001011400c507080c084c04051841030042c2004924041c00c90101c0351b55101080407509000b4900f102c41c8805a80012004107481e00000001440c0409 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 492186330 1250 492185080 492185131
    0x10608011e06200a05100633020703170306030622031404080a030c021509090a090c15020f0106050613050103020310030f081801081006030b12010507030f11070b 71
    0x50f40c61201c80c43c0a0000c0c1203080c48004075021190750b0784070380d04202c12900c44482d803048403c401920b40500302c1116450f08281d801507003c0b0002085070041f01c00042ea41e41e1048130384c0c0300002243c4040c001c0401071000c00d0500300141c03600004500790005110300540c0ea040100107154201800300421405002080e0800b00c6c02c81d40640f6000054a01841e4141000740c4032014601040703015010f4401c1d00030040407020159403081100400c140242e440d6000820041c100c40f2805503246084044001841c00102200566030317a01ca03000f40c000721106421060840c1c00c15803201d40128000c00001d00303960301040009040d20801d080060702d80e1110006404003040715000240117048841505e0140318654010b4041a001c0d81e001c1c5800840c06001110440420b8608103001c0000803030034041a070103a0018203140001800e801642008c0186003400d45005a5010740840c1c1d1311400b1884203002030103088160902501c4403881c045041c0d44031041b00300002d1851002d51000d403000840c0400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 492187580 1250 492186330 492186377
    0x30f03090c08010917030108030318151305060901060308031602070e07180807260c030d030b120a050703110a1e0e0601031503020402090423010608011e06 68
    0x10030158001074036440e144624024451080203072104504004030503180602041144c0c1a900140061070564554100f40303031495500d901010443d00400103100840c00340040060b120740b1142d2151300d00b00440d800c20505280028015403c0d59040074000c2c40400e034118110784c1c10210040c1640b20b01c1c0c1404001f01d04207600c50b00030b064800348041c02d111409034014000d6445a8245440c203030a01d54845049590b506d0318402d80f18401c41d19060300c03156441d034403400b80040c003140d02070791443c00c640000241406507030900079020a960317100c4080d030f606102c0358000c41114480000c1c5020b0340c450311425a0b8401e5444020500e1046e2100c00038640c03101e0700040001c1c058100c0300f03184020f07680034107801e00c5064001e1100340035120300050700c29882405040e603262040b41c00010860704680a0102035802145400c0c3c2180d00e561000c09180c06441462400004200110580f0b5040000060074802c3c10fa2002e2041005005001c41403094280c2810884509040c001c00307032610b40e500181c0c03511 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 492188830 1250 492187580 492187583
    0xd1d030105010e0f010e101a0c1015080a051c1806020d0e0f0f1014040b03090f03030f2e061701060f0203090f04150305030d0c09050d030f0309 63
    0x1401c09000043c00040000381c0360003249089003410041e0380b1038180d100002c0d001c540042c0140c1600c041000303418000380c00e03014000c10311700b206403410007400706980c40e0903040c0202d14030301940e8078400c56145113290760810107090618050421000702d40c0754141d83d80e40019030071300810040080d0900c094081c1034102c0141d560a00460301e11659624080d48030901e040c0c050300481c0034160341c2d00261408402070104444000c0120351980c0c0400d003400104094000304806005032a002c600c0e1240fa03003005800141100303503515a0740c1c42c211180314144070700c98200c50351942c8240b060045540a0754100c541c0150022200034002149040f0180b400541d0f80d0401d2070032030364100c0400c095904c818601028294201d004036166601c61045070003002c84202000103800031310a42d140c500c0c120700420f05c44030b00140f02058040e140c003003015590106a1080390103600006032001c114105002c1c25814404604190f02618600b038041010500c403c1801400c001040140504140c0241c0c0304c541500d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 492190080 1250 492188830 492188833
    0x90909071508040302070f050918161205070803040308071b1505030702010e0d021c021f200c03040e06031009030e1302070804090209060c0a030302030601170601020d1d03 75
    0x71000001c00b07010100281ca056005000760100400d02246000302c80b030450742c01400d14107150b56001c1d81d07502100740d0780126102c81d00850b80140a18211060450042d08111503146080b2042c2e140042c600065a80075056503002400100081629074064507401074109140d0a150401c146070364055041d99000491240c6185051543c1d05612801a501c200c25540007003101007005001d655544c1860600840181d00045101100300103c50310301c1c4210f080d07801110050382030b582c040d01400d04110300b07840d0807a030343d14889410200c0d000400e445080025003414686448044040d840e03200e01d000da10020203819021070100c0e01c040150440b00045580100301d0080c0f00d182c01031042c0c0210419a01c107046a0403000d00d426000d2088440d03240c0d002c000f04d442c05251a240708065088006116440001400490185002804002d420074400c0c1e0300140d50b450310034009400320030140e02401540c8900c00030030070301d82d030001002c8a4036507007420104400c040003e46016803005001409400d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 492191330 1250 492190080 492190109
    0x2071a030601180306050a020d0e010b0904260d020d050c0c1b0a090e1b010203090d02040b0a0302060c1f0c020613061113090e0a1a090a06060b180405060609090907 72
    0x7c069035940034040a0150740c03c00d004001d42d400180f4242c602ca500340d65071291414000c940000c540704542184103a10014014014000780003110164010560448410341c00013441118840d0074480d182d0b11034040300b40f06041500c01408169141050100020201100c0c0b29903070480c7d0301e9185140003046468402d0111103104078040c0e03101c110040b80b0f080d0f0500c1f052111038a075070011059600c43e000160135a80a07418036020400640010302c52950003004c500030200158407030500a00e481c2c1c074903000800a00c030b240690454481207498085201500d403045961041d90b0100f0380c540c100f0300112090034441c2d01800c110009110310b9648c024401400284007030290b2074080302000b241c03282d001c10800c422480c55641d45442000e10018107411319260b80c00d03e17000c4840c80850300100e80700c04446c590001070fa500d104603869900b1450b907120001c200c000724418803242d1145172038001c0d5414170240c01d0140c0407449502600d10b80610555410000904803902003245800401141d002c0404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 492192580 1250 492191330 492191341
    0x412050109030e0406062c12210406050f0d0e160e01240c061b0c1e0b161103120621060a020304060b1f02071a03060118030605 56
    0x30700c0e20010440220740000b0a076038480ca420320039803048800f0380d1039190044404444c0b900686000e0b0710845016440c694640b0501c1d150541081d245130500b070014001c0e01c9441400001350002d451200038410020082404425171210a486400b070350750710704070b481c0e070244c4507082c019001100c00c4200741d10507200201c2c1c58000a0030990102c4940f0800d10381c00703903290b442103071007846a0451107940550b2822a021214800e508107620240504400143c0e02c071400d42f1080d0007241003000c20b0004030141020700c103200c0f1000502c8810711200d827802c07006240c1d581c2c1e0005e111000805014002c0b00721024a14103500404003c1c0340111001e003138a56030884a51700c910314038015246280502c00070004d29800c14286091900b5912030311000300911707642c4070b0902c4065800180211a580c0d2a0b400304030643d1215090305032810003440106242b221000402441c09801c1c4c0c0c81002c203592101200e5280031024000c42e130300114280303003906143c0d00b8596031042030150b0b540001c1280b883c040030400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 492193830 1250 492192580 492192583
    0xd0506180705130602030f04120302070f080106091b021507020c0409060509060c0708030103080313050a050a0b4b09010203060315041a0406060b1812160306020f041205 74
    0x114940380f140c00c1640da40300c0f40120ba890245420100c0c43c1c41c1c00704020310001039047c00511f031803803103441190f0050b6210000f14007100310039071040318503a440301014024225140210140d40103100d155090036100e0160003540c9a0322901800703030820340100490300c80c0d40b082c0101000e419000d80184840059481e0a0008000490720705c002405034801007032244400c102240c002e5038112101c0c03401c590039030300d075960268400b8220200461001400500145040c040c6c41541401500034002400e504d040618000310f004240d40d8024030045809c0070010142c194801c006030101c114100200045404142c241c440d550000c0558004002009032024054006601c180c0c8144c0550310a00f148801c6088100c00507034006000c80100f441000301d000382601c0b8140c0c0640144804544213a591110305c555900002d0031040d0207100003601304070390504812403200c000000313000748207989400c00040f0030301115000c018900ca4001807960044041e02083e1405010010a40010b1102c2443c1c001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 492195080 1250 492193830 492193837
    0xf071b0f050616080411031011030609010e0105030703060b060c010524041e0507090b0a0f140f0301030b04080721030c08010f0603020706110313051e030d0506180705 73
    0x7201d862050b04005108026143c1103115010f1041d140c9403842d80b9103035508104c8902c00d00d810354040c41070012070348a04455004411481e965071484c15a40d0a1040078030540400507004a414160160010800e940700010101c040302c5d04100006240c80007140014402d1042d0741c0a03411030344c01d18051110058500c40c000c403c01403040d403030911080707280c0203002c26641c454008589075820b01258110709809600032a40c00706080c0340403602c003900d8a21600c11504140540c0c00000c0342c1e00c03010180c01e904140c5041803140f04204140c144140c02c08001c0f55444140001401ca0164170040b03410007100806962001d64807610746100d1500401c0d0000b8142030707494030900000d04042a51501501418445060702d0890004495890a04805a001c0d40c4540e80c00c0718030640e10298001348050b040003542c0240034407001c1c2c1103191214242945404c18180300036624111695240c0b0422600004840d5460500400801c00382d44450016580c2100b034070500300c07801c030b20300c3c2000480355114009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 492196330 1250 492195080 492195083
    0x51c02070c08060f090c0a090b01120606020105160212040b070c030803040809040b1801140613080c01140a080105011b0b04030c05070906030519240207290f071b0f 72
    0x113a0740c2c10394416440d80c1c2c0d01c0603d0b043c6940c02004c101810700c0583c5441d0044080020f040c1003402c0c000d40b10030000c40444402c1e6100d000181d5590041c0300c000e1204240c00020701400344000d18903252030710b0551450340b0452040c5002e00d04009210400c02144003010001550040c0105407a4a0641081c1c0410b0f4810041c0601c01c070300d05001c0342c401d458400c0300400010f01c00000d6000503802c12110710519100411000c0d80128240a1110854241100d15000e0011080039044120010700090706072080704142c0c9801c580144801d590700c0e0307401424141103c1d400d02e0300d50369008024004040603820608064408491102080207064108649650300e40c0305408481503903070340f001e01104581c007500004204d03400c5403082050350001c081c0b01031280c60190380d500c01c42c00c2450128100707401c0c110711002d4090f60041980414000d441030182d80400d160b842c1c0100482d4014500031041c08000c0050707a2125882003c200703c10f21a0b00d05c10340c1c10385c90712041c1e48005205c2c04c1c18880031180300710 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 492197580 1250 492196330 492196351
    0x1215010e03102c0d080c09060a0e09010602010c12020307230909060a050f040b1c0b0103171e07030c0203011e0510261906050403120b01051c02070c0806 67
    0x42844903040b00250708283e0108800181030109080c1400b1a4680070107004100005818041c0000079900c1c140182909203403a2603007041000000d00348411700005910003401d5914005410403101e03041202035100c041d02100042c1d490341c54440695442c08041080850301003000c41c2c40c030301440a80014200d0301401c40322000656a15400c1141603159405115082102c3c4c89160802e402c094000780203814000709402d4041022600405050711030190640c5c581e440b0700010000d0050b0840d08101080d800c110084c40d21141c460b01301c1c2e1070003100203c1c03e40c1030030010f0540b050521a98019520381d40c010000e2054101d0106280c03028002075108000e40e42c81d0802090784c0456610342c481c07c41c0c1601100100c5010000d404410008441d1501c1515000f034100c4145020403040c0c2c96510721b4440d00c0006858246420020710b00110b1920000d1510310b0601d806440b40c0c0c11009658045071246844980510b07404545d0b0081d0050000040081c59625400f107480000030802c40e2040c1c00341c50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 492198830 1250 492197580 492197621
    0x70b0a0f0b0a090c030617070303110d0f0e040213260708070501050c12030c13170c1908061005040c1b08090d051c0f051215010e0310 59
    0x108240115410282010b0740300760031040400c40e10640d50441c1c0c00e004024140010b4150390ba480912008000d801c0c046030642141c1c03030606c10190890f5400140340f00303820061202041501025000c0d95007013035500c040c44030112900f40e056817140c0488500202442d8071503232007641c40c8100e0f400a0341c483e140d40b007203103506c1c162803025035000a020710898200100801c00989400d0041d290380c0d001d1910681d4a0081d45100f41c600e614000045d07006400e0050210f541d2800b14601800c140e4454206070070700400070391850021080040c0d80ea00c0020220b581c10703040e40580704031090b014055403240910303000c0c2d002045400b0950a0710340045540a450600941000d80390844002d4801d00819440d0f0001c591410041000320019100126000d044100103105075250145010449120b08400c152a0f10a4040840e0702c256016050a254245103040c100d461080d40c03200301e00100030188040c3c1d485602100c688c4200701070320301190b000d02628407440c600001400a0459010181c254110b40c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 492200080 1250 492198830 492198851
    0x11090c160303050601080c1e071a010311040b040b010c0221070308040e09070503190c0e01030b100902030615031017070608010e07050a080702120309100b0907020712080f070b0a 78
    0x20803c0780e0303412030100000c1c2012234280b02405038075023020906440030f1048004800c00e61071000d2030319010354002c1041e40a1140356400700019240d5030300026004604113481c484050b6003160340c10480d991f04540005205e00481c1405105074041891180c9a00c40c4180020070302089000038019654060f445000300da03103400c041a91048640301c0c240e010f80c0051102045d480d003180c01000d41c14460142030f243c00795143d242140703503842a00141c441802003c28000c0141c0c1d4415007030020004680300b90304503c1c01c00300150002040c506491800c450001c0001c021150ba01004405001031101001e81e9214440c1203aa448625004200100f4021400454002c2024403e01c1c0310714002d6071010f15045919074110303101d61001c1c14607819446450340000f1041e03a650013940c0300c0d800d5a00200f01c1c0c89181e001880584095128160151071486c0602800c0799011480c007050701d41404d500700c0c242903030b454049034605ca020120680a1404100e80d000c004000100034044c0131034030310a002d4940f01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 492201330 1250 492200080 492200101
    0x510031b060c03050a0507241b0f0302090604090203010e070927091406091c0801050a0504020901110f010603020109080d08180a0212010e160311090c16030305060108 73
    0xc0340140c0010419145124000911810080280c5103403803a2042c11325246644c0c065041c14041d4019040210540b417449150b00b951103000780c1421069004031000c4000319020b404141030301c40c0c0d1010103400107403581d11615501c0c101c400a20300ba0b6030031541d0f5a598815100307040e0040e210040010040c1500180c5541c40c0403d007030310840c40b1103001160f40b10481c0708000611250b030044078884124484e180d941f844c140300c66807107190050098020300d0f5030304100d40500c0d29150518002c0c4065800144a56211002902d054500c251401642c8080f081c0052b41d40c40303249040d10400e84202110146003000c10340207002224400c0e08d030f4102140e00c07145541e4440310208a2500054030f4500000d4284141031a00000140e40c1000d07914640c0c1140c0200c0c2c151040c07860101c49680d101c0c5620700c6011401c218940880059840003120f10781595141982c9910b0f034000c0a110340058030200350300f540000125400c40150302c0d41002488014900038000d403404540b024007003000240020b40c0d1920 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 492202580 1250 492201330 492201383
    0xd09060b15090d030e030d080103050d11122212020301061a1606060503121206090709120201020115150f0e01020312090a080c1e0c090402060306010c0204051003 71
    0x1c041e0316003824100c030b0b01c050210003002000140d0410100300328040c0c10340c80902c00b80c04141129910001d403507040d030a060b460480e1781604042006140c0e0305941c0b0102012404016907201e11200d15500c10364506100c80c02d060340b24041e030300d01103c01070000b40e03640c0080840305001d100798003d00c0003960780c9400000b081b0034000d45440108041011003500d564040d020a001f40c8985c07000549251074101080c94a9070725418411060b100050354003e02610b800015407010040303980545c64a04441300030200f1443d4403405030203090008504085a00030f400043c3c080e002e007841e500c20542e860b00b04401a0700348901120204200205c0c9252862040040203001da9060300218a4090080b000d8800400c0080158680d0b02405c444030000901d14001020403c04c60402410710032900394601902c1c1c08090460305c4141e00865003414541c6036117040982c0709404031002038480d0340380c80040e100490050b00003980580b03041c0030400700340d0159846400b680d000d90034141c281c001c10050002000d1f07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 492203830 1250 492202580 492202609
    0x7030e0a060504030605182a03010b01171e04060c0f021209120106080d03090507080f0a030e061e1804140424090515070c0c05010e03120d09060b 64
    0x381d04010604c0801e109810103500400f4400000f1031010452100d1810b01202e0b00c0120702001f040d6003c0340101111200041421a0444c002c01a00001d4000030303240078660381d07400b0207500308480096140c02124401401c001c2e42190180d0240c0303884d280c0f1030018800c80030200c000c039443d242800e40107440090020303030b06000d4644030b910b4003004400b0445403416103100060159200c401c0461903010070700141182c11025100031410500740e00c0e00d2814905990806456a4001102c80803a20000070350409480e40606080b0001d50320300340490075034401e0072a151a401000d0821210300c2c0485002481080310303a0300020710311160b80e0204019290b070300c03c07032030940b02c0d0110125000c035540300b10014a0204000407000b545400c800004155030421a007680e545c0c00c03005801e400410029225a40001645414000175803155142404054580211810002e00c2c80e14142e49480410130400300016520545071688540e400d01c001408414001300c600e1824500c0c42c00e581c0c20314401c00300b00c48 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 492205080 1250 492203830 492203837
    0x11011e24060e03030d0603060e010605011b0b0403110313060801120201050706230a090209150319020307050d0803092b0e1318020315070f0c0203010204080f0307030e0a06 75
    0x3610340310040350003851003903006503d0302080011076075081c1c00d4466140114400c52022820b08509140c0a0850340355030700003818081044c40b2049000c246803011480c282d800703404016180c40700d040840c1e0300070088074089028400024407500c030007032000490701120a00c0c0d1303401c2c60580e00d400140e401c0301c03031301d4100902240c0c0c18094040002d196401c620b60180c0c010806003942ca20340c40c0241d9544d081a503001815aa55011102c15814580c0c0015441444c50103400c45c900188004280d843c0e0f0041c030740d5000c64a20300034034000c554040c0090700003004c000742360841c04a03003428005144d5005030b03035a44007442000b40080c1401c64411081d6180c0e03464948802e8030542e080c00582d00700521000907a40000f41010500ca41d02461249140c90340f20014005543c107014414145026039802c1844045d119100800504a0b40300700e040f5450100d038907188a9260b410320200303029026a03044020580194140c10380c54450000c00b800800b402944c0707001181b4440400d20414240600862002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 492206330 1250 492205080 492205151
    0x6070206031f03030f030b04150513060504050a02181512181203040b07030e03030a11130e1006050310090b0607050601150315120605040311011e 64
    0x90310345880a03641c000030030b2034200c0302d0203042400400c0082c441d80085001c03914000b8210012640b5106508201030181e508124001320034003c0901c10700c182c41402c1c416120060308514510300c0342c010000800c00980144100d06000709018003079000340954849841d4010340350503c0b4602107a00701c40d2100711325001c40c9000e242c080e1510001d20001c0499942c510301103107200c0c0d2001c0403c02000c0c030303d041c031f10100c1e103034100f501d0302d00c0380f0100141c001c81c00c060030409441d400c00004001c607500801c1c8400c000600c00c0d0b1040600001d8000c562242655222411002444075086a8183d10070041e461040c124540c80745d10079200c501080d1074070b80c0150581281440206000d5210303c0d82c40c00003c000300d06007030050b99482e1501c20309030032042020204500052125801d4044c0a00b000c0c0c840c141010740c90301f01161082000c21219014040c5502ca40114003894010700b01e800102045c28000e00810241500005015441d000801802c1e03107000c44943d8100c07288403240000d252640582081d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 492207580 1250 492206330 492206333
    0xa171e03040f0f0c08070803030a05070206190515040f02030106020105060d051519090606080c010203070f020906061204050a021309020d12020123011a0702010c03080a0b0402070311011a0607 84
    0x3e04400098125444000d454021a000f801000400300502408000b19624500281c8407010780304090101c00c1554842c0c400d0006003590420300e166a001220030006865548403540b0108107805101183c100d480e00252000100e8140c004505a410f150001e0100351100414084440d52203180901a908400255070008070104052504038445010840b941c90252054004460246804403003540d0f8880041050705028090300c1b124031030900185042801948030900c000035007400003440b90345a900040c2d40381c1c1c0c6100590b4486a8030710b000005034903040c509540d84410001c0207030710508480001d09031403c81d5001e40c0001031750141c42520840c015507515121410880c410200395522580c540000500c20541e03003149a145402c100380319450070104000d002075203042c400c441e4004000c0480943d810000c01e0180c41c0d81403500c0da02075078a89000000804a5005031740c0c1c414000a03d500500d40d10810925980340510001c01000030344104007c10303101c001c85180d030005000d204080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 492208830 1250 492207580 492207593
    0xb090901120213020a03020909010b16080c100e07080c042003070e031b0906090708060111070302030a0317060d0c061409030d0903030807050406090311030a171e03040f 74
    0x107940a2010b08000c419642108120b01a0781095a0100000c1d502040f42d1900e4601500c00d07034014020508914a400b069014842001c1441e41c40a0007007840040c80c1c41c00500304000c010900d078040c2c00d04118101028170300544030f2000380300b1082240b040180d400c0c0545068030481010b4040748011401005402d2140011904002d01d644103220f007410030101240ca0034004014901d045130341007640c1410300c0b4100039401c103001e40f074075002d06989010800c01e00c0e0444070003500005c00f400d00800383c1d00080d0320586429015003000b505402880710030130404da00700c145c01007240e606180204803031791008240210039100c040068440341340c04004000d040d000d40ba45240365052140101d01d0030940c9000301e45404019801680041c1d003c1904005043d0f01501194100c2010703d4600e10700340c50309000820003505808080d0407201a010300c008580c0d4100100740c48142d00230201c808a11141030340e40380941041c100f00b003146141c00c041440c0d211844046910903079010a0040a5035900e48885 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 492210080 1250 492208830 492208859
    0x150807090302090601030f051510080408070b180a0b1501021902060d0209150a030e030a081f0918140a02012007030c0b22120f03030209060d060905010b090901 70
    0x135410f06035100c54407a0248458000c05114215003002000d0810141041c0039039a8900030001c4104211881400009508182240c9009400407454200c1d038460515a0044800d1070803400442d01c69a0202000c105c03240402074410707440c0000100318501170314010790300c807900481c10401d20030004100e07200600c1c003c1c0140140c0501d154005050420f110b02003041e100d600004510740301004076a02c51410f5040c010150b44401041c041c6080941c00100900350300d2000c1e01c604146200034500c0301c0e501e02864512401807903415814404002403101010f040c0c40518400e44900b103290811316203200c0006400c0c42c0c0c0c2c80d41a0f42e14241d10380340d9001001e03400726902c3c040405028030307000040800d603c07801c24005081210051075952131009800312907202156140000c000c0a070004205c20382c60030084a401940003000c00000e000c0710f00d400c50081c41501d0703510ba03000c0d00c0852044081d0340e07035501243c10b0b505522010081070362074648010013030045440040e844100c210042c4880300c2c400840 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 492211330 1250 492210080 492210091
    0x10605090d03032f090306330121091101020d1b05031b10050a090305090105212712030c0a05070f030822030827061015080709030209 59
    0x8404a44138007120840504c64007002e241e016034002c00d1030901e5107000d000203a0820408856610142c2d1710ba90940340307400102038040c02190031100b850059900606000c42d220800c0003c00318910461500e08004080c1c00d0421303601c8880340000c5541c194000a12600075030301546403480101c0004c0c0a5030980841c100040354140010301281410700303907072400d6145940e0040c003c0c0c402c880c800501c4030212840140500c0070b0340e00b400054400320f50000121400340400b1300e40315642c1d0680400c0c840040342c150f02d20031f501c42e0054041228041418080714400b00c0b0215403046051042c2000550310f408542e40030f01d01010810120f191250042c004007400140c905146007400d40a80364104144441042030f004180844c04119491140001e000c0c00740e0487c03044440c0201d16504c0061902c5001040500303a01d00e10031407411421018442002c4a108031401ca0b9401d01d090709421048641d10312a1005654064181080c001c4c01142311600c01c01441d6601d00460340355808000406a000d0403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 492212580 1250 492211330 492211361
    0x60f1515090512031b0102040b09010c060216050c120105040210051e04060e0a0819060509010b1c020f030f0a060c050c030a03090b0a060308120405030f070515010605090d0303 77
    0x1400503554443c021400301c504069000b850b20354455445040d10128203509a15450340304200510400c00c000c0709130303032803c0740a10b045005500580382c800300a1107210342c00956080901c2c201c6040100c001100c10354882d05903001140d81e152081c215081c0c4100350b030000d5101288504007882540301c0d0001e44196405041b00703000c6c41e003d110b071404440c0d010741c00c420001248061070b0011810300440c0003004243c1c1400a01d00382e0b20905184c42c145910080c000c20880d140c0010030301c6c10300d003504018406a40144442030458480fa005840702450b0761040b4050901c1000701c181c1ca00e00440d11034002c45103400640b80080081e030700c000041001c81c0820081c0041404100e01c00340080001e000c14a020792400944002c8078102100143c400521018900c2c0c2042d000f400025060000d44403001c0741030b5103070b8665480300d02d400c600f140660808100c001d603020420f0750901030000f070a0450480000032022550340c850008880c244200071050390401500381c6020f001034031903840851003001456 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 492213830 1250 492212580 492212597
    0x3110114071130070b04270f0e01050604140105030a0308060103061a03071205090304141215010f08070311010c142e0c0e06030a06050402040e04060f1515 68
    0x2c400c202031000503d070300d6036100344806516155001c01c21241d0060f02454444600b000d02c1e005640180c4800d0880e900841c900c408020802400d1079004940c0c1c03001d80304001d1140c0455081509c0c024041265214440d42c20000e00c80c0d14410054400e034142c1d40c003e8007400116105071000e41d07400f6000340c581c604140d070721440066442c40c841c11400c103541015500b90754904050390010580134680c031410310076519160911101c450000f08441c00c50380031401c0b842c1e00920740d01c0050058480c40703282d40b11502030010641d1050322031091943c11b07200b01c50502e0013010f46032450281e031740e4481d000051410240c1c54610740b80b98060b0900302030942c4946103c00001558031411800c0040c0c07014840d028080c075580c0114800f4120504041c4102080c80401418204401c002e001c2440d03070741d280e4040c2000101180150b811504000007170308001c1d000350340c0c0344ea540002c0307442d02100305d90640d1020b10303151425081f0005401642881d510303000f10301c02682d0402988400040072101450107001c40c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 492215080 1250 492213830 492213859
    0x8011a0a1818020a0305070801061e120e0a02150f0711030c10020d02010c1706010f11120a0305060303030403080a0e010f090b0402030c06040806010905060d1b031101140711 76
    0x5210039420b01c2c0d40e8520243e124040010702070241c600203421001480700c950014010300754094078803d508418020884451003044070b0549010840c59141e01d0401d081003400071045a0005940038454405d4841c2450480c4160100d1858050580b2041151104202580c041b0703080c07440d810f0007030300000c040c1e030040d003c01d1001400b41d640d0f510f80500503030015110029007940a04c02c0f095442c0d034605006842408a0010201160009000b2030500414020400f440b5201e0540210800000b0703080703440c004e40d2102d003840240c020750f0707030000007904050002e00c26050101c2601d0155901d600c0d16055900c6641d024009480160440e00c10b541d0395540c0c40801031032600409070302c40d020390f0342c0c6021401c00740149070602150000300c40c000d07075040200b000300d50703800620340341169503101c2c0018080e228100010b030400505680500441c40c009030034881c4030074a46080085a00c903990030130302e0700d1310000195107400f1581d183c0d0800181c1484420040f03180a0031940c1c0284004003a200e150020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 492216330 1250 492215080 492215099
    0x150c18031906060f0509010b0a0207050a0611240415110706060e070305090d0807020c061c06060e030a08070c030209040b01090b03030306060406030e070b04090c08011a0a18 76
    0x100301440c22001c40340451203080c081039200300c00181c61050b83c0d070401d450804011404221041c404d001c072040000613500860340c82406520042d21004081858240c0d54540c024a80840c90035440e01c9030085558104005c41e40b400c206030a454074007034540341d949d0f440d1034004a049000c0007844d074040c0c80d4100101140c207c5802088540d00c503034030001d00c181c1004162606194024901d20925140c0014012070a0000030001414201450130050341d030b4805c00200d0910042411550b0406400b003100c0c484040c01004800c0c4c0503000d00070802c2129170347c0b1000c5444000c0484016019004960081c002c0350740d41c0c0003440d480340941d08949003140e81c0d80c00b19162141c110b4050310a500c1c4c6a005104402103402400d0440c1c0048000310300b1814071000044061040d8460301d0103042e030b00c04955017514400d000381402001040c3d20192200c0c2e07989911805840c1c1d5000b0500000e9101d80042503422100c801401819010b10007503040020603242600c01d041144c03102c91008120f03031f034009010001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 492217580 1250 492216330 492216343
    0xc010c23010603170a090e0108070324061701140105010f050703050c0f15100e01170c130c0f17040b0c040911360103110702030105040b061002150c1803 67
    0x445907041170751407001100040030801c6503040b0b9452030401100402c8115130024040e001d5a80100080414414031850000210a03c28150025a080c03840000340084001200526021490001e1211901104c10b44103204001d0003258041896802c1c02c003e1948204090440b0300d100703091113440c3c5141b800c0074514207080a01e00c20301d194851000700703081c0a002145160002d0500310b1040900c0d007040000040300030140a250001d00e0032100070300d5111420051411031142c0034003003a2a442514407490701130f00d1a0440b000100380111005140d4510828071040c95121825000a4545946c0c0e80c4000c0c41d5030180064030b900300c044c00046021180c500c1082c3e0100e04c4650091b6070b43d8248804051000340200030103070701c0b00100e02c51070740a41040c14400e011001c02d10b000981169030b80c000c042035006805002e500f6600c2d00c01000704000780e58040300e01030038003190014406a03031a4800c9a5446105403411a200798420114561180850140108a624550301c2203100084004607103800c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 492218830 1250 492217580 492217613
    0x6030f0f050f070b0405010e011e090801050606120412110607030e070b04051c03050d02040305010504140d0504060c11090c0d0f0b06040302011b06020a0903050c010c23010603 77
    0x103800c0e290408210081088400302889400034101152030300301e20603198095449218140850790200c440c450303103d0440b180d002828124244240d5955a000400c2c3c0d1201e4000c6001c2907103440c0208105141000580b00c86404000100c8146d5076140e90310005d000c1081c80c0c02003440000400385040f07400500c0300360320400240c0c0c3c0014001c1000c6807007030314000d44c550010000807403c100c10b02c015100d40c2d80440c00c418a14610420001c1c1d18642268903118107a01050014070114000c000c012040d040700780528003941c920100c3c250001c031003075243c012143d851408100c0c20401040490b006200c1e440c8268080c0c40040500807000b004103481250842e450984a01c00180107520030191344500b10786442d50050822018407448081072082c441c501000c0c3c180a440d4585011416803019040c289551048081d9150314807645d000c1e00354000c80c00b00f101d69001d007030800c0109510808401c1c0c1419000340046408a030740e2408010110b9200b00c08080c19500d0760004404251450118680311 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 492220080 1250 492218830 492218843
    0x612020708040e04120306180234031101060b03131415070f0e03030a1407050f0604031407050d0302031302040e1b042f07120e040e0d020607080a06030f 67
    0x245441c5c0350105281300c0070080d0800781072401905104001140b1541c0e0103100010000580c1c5140d2011a1541000484816810422840301c1e00c07013614418050341451503c40d0311890301005141c11941d084e202e047c01401d41100d814400503800813420001c00e415140070300c048810300140035450360304100314403011803100c034881130900001540c410082081c0700d840c2d2030402c7c0715003032480001c3d4032485a80c0011003040040806500402d030358100312004503920204803401c0c00d940441a64403080c0454042c2c0214441050050300d0008035011110025801405440660308580c0c00350002d40025180000340399144050100585851042c42400c0e26a14010400c00a0383c0a0b0743e504003001c420028000d60510070408190000c080301c5500e48002c0a0300c2030310007841c410903a003035030049510140c1140740d00c80303820103140d0f0041480d0400352000e550030310201c4000c1020725a644400418100141e000d140050811880ba003c1d403600716102c00f01c0031404079602e456600f01da00008405803400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 492221330 1250 492220080 492220109
    0x2150a050310050d03080a0b011106010801151509030609230c03011802062508070308010905070306150f0912140c0d031e0915030b04060618061202070804 68
    0x2000ca018007000200f008890800b0340307041e650b50050035120050b05608500f612440070842a03802448046a0000d004040300c000d0340c1e64103056400b030150180381404041d040d04000ca00c61042200c95a1540714641f01c110302246581d0300d140042600100955000d106540910b039200d132003c1804030b400804a0042070514107480805084500c00041548400c02a90180d001622401c0c01e0700c045c0308400c0c03001d05c0d0700100151b03250b07101c403940b2000400d03400300003e0720000c15410001d628160389400c0010001a0340b202c030107a08640160090401e40301e90440c012035254490300640001500c1c0d46080251907503500407900c401d4000c030004071203c89402e550740240721000c10042c90a4403084540c800d07418619207002d0b012502e6569183c0d1000d00c507228540c03504e07005031174540040182100320110106640c10040082c00c411050512039401c0540c00100c0c14455041c2d200040b181c1041e034018549018815a400300c0381988250300e1035000e00640c000f041744078015100606106907003050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 492222580 1250 492221330 492221341
    0x5130506031311030c0a03110607120c052814010b03030c0d020c0f1f0e090a06081005010e060112060801180c0801050c07020d14010c050a1412060d02150a0503 70
    0x40700040143d1a8025802600b0820150303a55600001c104c83d0000c038410300105503800420343c94412000090406203090b0551000f182d0300c518040f1401d4027074800c0d00c24460005690f4903005a00c403445413040f0f0b04820440c004601c00388441180d400d107403c000541903040c84046411508805540e4521350804840301d00070903010301c8112441501200c03a07249c00001680042c3d04685800c030082e03c00020141c40003400c034010315050b4585c400060080040d807401c140300202515403405202014001c0c54400711005915019141c16503020240d84032803a500c3c140111103401100c00d04500403611100e0010f602c100038800d000010242c0c9a0902e90526182052004504030340c0c03082c10340360b1404c1c0800414403411002e40301625811070364806104803070306240020490521420740c081d440c110160768451b07000801482c0301807890320b50091040c1103c00b0342e800350180c2006c0d11800f4000000058581c030b403503203040310344d0340c4010803102da220101203600b007290b000803002d0404142c00100384403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 492223830 1250 492222580 492222593
    0xf1003020d0606020307050304090903051e0a17071205100b0309060105040e03040b18060d051311010906170702032803060b0301140d061b0e100806060a051305060313 73
    0x280680030f280011031511445550b1170741e07a0305c900e04c10316070000c0d5550046002c26108904440150541c8407040140f01c2021585452035403290f0342c1e0b034001c0b4421000c03454540140c0002c0703500c661042c1e21540350141803200600c003c2d2800601c0840520720341e6a0200750410315001442c041ca105c0c0004041e190b0521051204491100c104841582d20500040089507c403508030743e824040d1a458030b11905a010106280d4028030562140c40f50800007086510070b548d2855682007800b851101078286050340040d01e58102e00e000d16070014803d0340196101604080c011500248107104032464180c0010200420f1000c04c410000d00b48850b9807400d2089902d809810b0140ca21104041e10b90b514200314000da80070600c50580c09800e03441000400e00002c8d9205441c0e02d01c2d81c48070b40c4c00c40c0c00c4c100310007000c104103403442d684101d990103c0b070400144a2031102e0300c1000c0c06012903262000034070b030070340b12904988402c901080c400034000c034103a120b81c0007841c081d50082c071124001800300d00d000b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 492225080 1250 492223830 492223841
    0xd02030d0b060415110102090409050d0305011e1418010806013303050403110102041d15030c090a020403020406060f022a01050706090204050103082a1b0f1003020d 72
    0xc2e10400051006010310741580110004034070490074048110f100d4030075010b0180c0125148241d002b0310301159001440030200f1512101c1d1016070301001140c0c1c0391900155000072102c113142d1110701882c010f0090303030070000390f801601c04011f003001100010803008640b0b0060980000c14550000001004201c40200171000f041015a295032000b44e1403050403000e40601008031002c25455030003040c10f040c0100e455084004144009540e0781d610361034030b800b100d00d9010340031303560300c080c1da00060301c100e01079202c5954044001c0c00342c208480200200680064050540e418865007004004010788c1c5a00c1040002e09150b207620225030035822010342003c06c0b05d80103541130b13180c15005602d401129010841c000b107090030481c0d1030300c0460405a00500300745a009411515140002c0240541d0001915010b05040000289641c220303241c0714507406a441d80840f254418020300c00c85801400c01c03403400c110003a09c00010b4000317520014070442c10202c0700c50007080d03002481c0702c4503507080c0c00381 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 492226330 1250 492225080 492225101
    0x70b01080304080f0d020a0b0c070c090510050f0f060a110a0c060e010807141c110414030f0c0603060d02030307060f050901090b04080c030c03070c0906052d0102030c0d02030d 77
    0x251000a441740e0010b521100340c05e100608074018980000e10100d40d25041c0e50080d900700c80000034290726110701c840105016282510710a03084074000403c0e151112080d601c0c1d130005010410070640103401d100b01d0f60428140b44090080d0a20404a0b0407401c002030b0340707028090b0342280c2c00c46160a4000d0251151142c0040c108070fa10f80c100802030707400135180c2c080da4034105200e5942e40881c03201c4406083c0904e14040400381000c070031800b5916403c1c05007095a403000e1445504c900311a0806984030034480e08016a60841c90210055142c0034002e5584007030b002d03040808100a03a4002421540403460880d4a260764034140d8603105810f104259105403c00002c000000b115180c5000760440104000d1180d4000103110b84001c03414401c1d070300500000c00131252504080c0c68404942007c0b40107010091b07250000001352071030801c203006030a40051140204001004640000f601c50f142a17440c15484100240300c00b17110200031400110011382d02031074458407901024030560740b00c0c2c6030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 492227580 1250 492226330 492226333
    0x123070210080f040f0311070801150e010f121502031906080708030702040213090504050a03030f0501060507030f090503030d020d11040b0a0f1b0b01090b030a050709020f070b01080304080f 83
    0x1003000f980d01881109030015000704103486010940d1404a83d080c0c9000d420000740d010703c207000101c484054001c440f0950750143c0c2c0c0e03100c075510340e003007051002030903c12040c4440016a042101c54502c01e00544443c0c0980031025a8544610364035050380d00507680d5800c1818036130201440c081a0348a000c0107004940043d092403442e151034a55240500c0c040a4032503980020324000840324914814000c150400c01802203150500b484d9071103048207481034011900300130350b80c0d212803410721403030b8162452912107504000542c0c80460300302c00750420079010f00208510203e200e603810030140034903207c0164007583c0c0d91243d400c0740c0241e80c20b00b40c034105801e00c28002030050405aa080e01c0c42c0e0100d40c500103240300b40341039044409040040d13504641c90100300091043c00000c18059040c1d801c0400c05000c4180741105165941c541c80002a029401c020420311a40500307400070890000310b0b0314514200100360300e805d4500002a0b100c40340320b41c80020100711924047c0315002e05142d4510 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 492228830 1250 492227580 492227597
    0x301060f030c081609120b04030f020109020307141305150301150e0a020919060807080105100c030503190e030705060705040f21060c032a0c110123070210 68
    0x200c043d0503101c0180c01614903030919403040b04014460000680140051100c0e2410f4600b2820b1004112034207a0b015000148030b1003180045074014046c480d00305a028006001c21071820601418451010100c40d0b0322a030070810700e4050043c2c5000300da00400d10120750004c0d400781c1c10100350071200003548905405216140070004444841c02c0640d20920425000d42d0350000c3d0b400045a04100d0303605000f0b030701104075001c101d071079114035407602c070700d0f003940340c100c1d00f6602c45040241030007006005800007600b0030201c0000900c584050350f00001011030b04074421440c59444010b4808109030001554004120041404403c118541d00000c00742000e038509818000c10520103403a40c010403000e440c0c4080e400d0340c000404032810450301c0c0c001800f00070905104000070007a000d045403c54807040c04520034500c00c0121101c20310b0031f440907114010a05031541c1d440400003c001091410b000410154102d030140e00c0310725604114401704003513030f2100148100518851a80500d00c204003141 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 492230080 1250 492228830 492228851
    0x325020f07120507150507110901051e0102240f18030f0901050412030809010b030d020a020f03070b030106080702250b220803070309080c3109080301060f03 69
    0x101d030200a5074480080d1900188a07828003d00d05211548181d50509003001d4a04049a0010142115502c1100d60480704030842c41001240502030244961040c1865100c2c0c00c1c0041306203401c02c8424040c010344609440051348981e00d5028001400b100340e82134410000214064015568454040b50005140b60800401c40d0758a009089807000d904200184165a9a02840c03d4800506c0d0703a108001010f28146030080900320306940210042d800c1030040205490b020070400c0d403100f041c3e402442c0540468003001200041c140085806006030304002c00c40c00d280030000c0d03028260300d44650701f00342080e00009203072400030034485080707408481c41140044201c1d40f08204942e084600d943d100e9080e80010014240c007010140f65240400c1000651800040040c260b0b40d03009072212801e0503620008a40c0742c03d007140000e50700c002252416031500700f0248020602c1884242d000b0b07034604c43c0c40344000866003038900a40f011080800100250741d07203c0c04961000007685400d0000d41c454 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 492231330 1250 492230080 492230083
    0x40f1401092310020705030610120b07020721150519020904090807050a03171e090c0901180b0303030103020d06022b050a050c0901080a020901050c07120314071a04030c080325020f 79
    0xe04500801d0103e6141c04100cc96108100a50140c050110860409140000800a5030180d51000c0b42c0b0003c514103003140201c440d120307030ba205501848001d00803101c84042800254800c03684658040d81e0b450303144010512040103003030b08511610003025100c0c0c03d8280600f01d10b030700100c01c00b6050b90260400554080128801500801c540141c00c01034503208003007828810305c4003105802c800b02c0c1c03000088000b50808064a034158440701007100300441400c0c5502c920003400b0181d00000c62420010029110b940109a90307180340814407107a05003800032f00c0074655410898001c982d228030a01c6080703001c0d44121908101034102d05e0b4500b524850018150407001071011044503400310301e01a0a900810031580c103c1c0c988000d0b1583c147d00e510002e150380b00c1c00c40c400d50000707401408014900c2c20314012500c400c0d41120051030420b01c1c4a0203e20039180081c011800c2014010413480082c00740006140100503891861121411041d50201c0141d02c20000310215403000140780c0e2603140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 492232580 1250 492231330 492231359
    0x50408031b071a04020109120c03120906020304120804031a06030606010c0f030309050111070819030c0504090e030d050a1415010c030e1206010803040f1401092310020705030610 78
    0x50383c9031915240c0e940d030300040e240025036901c421030651021000204003c01d1000c1c503016070340b1400540100c45240360003103d000e1490300840d405a8410031040c44518504591078107820720581503149455203e56407420250139107031150843c031f100501403158501d07040c440e0380d500a00a00c1c1c400c01d005081c5e1a002d0075521402d601409040c1e481400e001840000e4009000c003c03500781005a42c0d41030392622510543c0607040d21f00a126046211180b5070340319008101004032543d03182418582000042001860010390049041c8401c00800c1e032064403a01a6030301c42c00c02c2c1800028aa207200c0007003c0d062400034009007030030203110315501d0f1503a00903100c60103650f0549130051500b01200e001c1540301080c2030a002d4580300307003000016079080010080090b9420341c4c81e2008295a1210420084141c07501818003003030f6408028032032030100707141c49060250603090785804d40b840780c1c3c003090490814160750001a0408c890502c024101000300341d410030425654000312901c0c208038044242c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 492233830 1250 492232580 492232613
    0x9090506090f0a09080c0a14160312030e1b10030b010912171803150c0403080a020c0a0308130e1015120c0804210905040f0906050408031b07 62
    0x103840404120b9084041d4054621560b05c84449540c032008003000740c2c0c0d1240e00000c200c826910740705040307400030301c003240f00610b032010030345181182400d690301c80301c0c4803c01c083c3d201d00300f580c2c4d82a40141307100108162003816040ea0074a58180140c1024040d00c1c1c0c90700034200c0141424030000c500140d900c069080d0841e586007590028240c0720b0305e040d60064880409000c1c1c41040031882011262005030543e400807c110110382030b4004040245010f01d0040b556043d003290280310800c0411203a200800d40f06059105032180000c03401d0008542d440e0a0b042a10b6418000c03c48905100a400320a405009520440d084901c0c041c85103c4155540b03010310705002e640e400c0820b114500503a414029180160418000390003004401040d08900300d4047d0fa08000000400586c0c110180c941c4202580c1640c03030142090030481800043e00300509002c49040e940c050304800708815100c1c00b40902d11485501d9030b28148020561540a880076000110002c100800317000103c00d10003c0340803c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 492235080 1250 492233830 492233851
    0x130516031e02031e010e04030f0807030b0306090a0b0919021504030804080a030e0f030c01081f030b240907030b130504080d0e0102091509040f0c0504060909050609 72
    0x34501000740480300c03082080305400103800441404810a0b121504040f0244075000001d00350f0390340c0403507000e020320a54010740031601d40e8080030702c5244101100d5030f01500d1400d0200b8400b01c508007080ca0807001b190700c0c40550300034120040401082540d09600310040c00c0051188a10343e1801010708044e500c2c000784906508080320115030945002d640081d0740040c02d080d00c81d661100e001d038880140d10000c03000294405006000d0b072030054070140d50901e01500400805400e070b001580c1022000c0c00c40d0101e00031103000120342c0044001d505001d54882d0f800307112181440014000c003a134030b20008114a0480c24511503d94a40115082d0702076940e150102d05080d0b9a4041405c00503402c5050610341c1c1020100b1082c019510020300d00380d42886030400140c80003034031943c200d005041103198004c281841165403a0740440c090480e401c0010000215103420b110301c0b000b00c6440c40d100c24007148020900700702c3e45422011010080203852801d000620b030020000b80c5080d40180090b400c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 492236330 1250 492235080 492235091
    0x4020909070f062f03070308011d060402130503030a050a1407080342010f090e011205010b090702070e090a0309060f0201150e011814040f050a0b010b0913051603 71
    0x240720302c4040401361007a500103265020449045085d12070f40700d81c0301500410707801800000c441c0f80341601441a100c504e00a500552158410400070b94440340d05011840e007000004505560b090004010901d00c1e500c89603600d251081000c2c020b401c03248920455080c003440340c02c0104260b04102c0380e02000b03a40361148882d60319071001801c13038080700503503041c0b5103501501100750030b840080b0398a11000341c0390269801c040001c111418071aa008050014900400410214980c0905070021600c24800403d021000c0c60210309000d00844d1101c0060703014103010010810501a100c0d00f14000c20094201080130352000740800045e8404c02c3d0401400d80d0170101e5881c400c0d802544055a104055408180d4070b240e890455682800f0310401107891080d400f078814958492919690105d0748a21600d075501d480390f084c49c3e540014203803031a01840514170005042c002045002e080780e500903c0c1c94414110600030402110851980e4003840c00c000d0100105c5103421001d500c40b028030b0041071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 492237580 1250 492236330 492236357
    0x1602030a171308031c0c0302040e04060605010306170304030b04030c0629060903060c070618060f05070c020d26040b030402120a17030a060b1204020909070f06 70
    0x64200c40080140414200c00203203805480c0e440700624540c80c502511918454031001d07400c1d101e01c40c00d41c4c0790038031400484940c0312400d1541c001405105150400509290307503a6941c0c3c6254a00b141c040390125a6181d00388515a09071040700d0140c800341c145140942e0034118000d070389201e90700000c7c140c05079140c0064105445001c04412241d40113906021009044820a800000d4407200c540c0d14507401c1c00c01041c5043c0902521000e0384020b0003491aa110174108030400d0b84000c0040d50200d0301d07807160780144080384801050084c4500e400054400004c8551012240090140e904000182c19034030301695a000c0d0040060350403405020481d51a07078443c541861380060542c01c4107002040000d64050ba03030b005544264000d40f9424a200c4140410302e4450348a60b200800040d007805020b148640300e0b41c0034591101400e0000586542c03140903171262038118029a0b14111107a20810046081404071260040c01e030000910a0390b05001c0110340340065801511f0400c081000d80c043c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 492238830 1250 492237580 492237583
    0x80f010b16170c06070f020d120b03010e0708061026010b131505030610180216080a0e03010b010f0c060f1406031612030e040e01061404060902070503160203 69
    0x50602c2c0e0081c503045140c4144000494150001c00c02e5030681d02403080005c896a005070341642d5481001d83c094840031900760400e582004998030717980d5550f03568800c0c1542d5501c00348035410800685000500d603151408660030301d002d600501096402c0b048010421500c91109088150180e298000c2130701c080304000d504c0d00520548510a03801642d015440d0120381c0c16a000600355a041400c0c080110380f503105250340d030b080990b0342c214004216081004a81c2b40c90302c0c03054504601500251030103404022080c0c0c0160060341c01e5444020000c0e041501580180d0000380008058009001101c50b40b00040c010201011300d040c00c0c40031080300a002c004003913210a02544c40002d0410620202805180d40090300300c980074024418608485201c040c0400140c0c101e546550b025007030400300b40d80480d540c02034064440d4000c4d48a498803403072103800f0701036000985440c2d212000b03940c0c814ac0412058840907409588810b204020b0000420004030413940303514031860174926002800d02c0400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 492240080 1250 492238830 492238867
    0x60e0a021c092001030b0d12020c1c060b06070609060c2a0b06060c030d05150d21092319030209010306020c0c1201020306010807110303060112020d0e010e0706080f010b 74
    0x980c1d21540b11a0380c0010401d400080c50b01c4e23441c2c1a800c07101d4060501e0107112180e4510384180300901350080c10b03100001c0040e00300207220a406442141040855915401514018201214a26105c9086811603035000810300302c0703400410340c1d80054803c1028094160900104094526482c00c3c0c005403080d1143d008488407413050008481c0c0c2d91082d45100d0004000568012140503840b0245401310304c1c00b40c3e4110300058000640031486070800c40160807084001e00808240500e0001c001150055007000c02440134404581c0b84c501c1c85031310100200e00d15038030720b0748200b80c84010050026840f44e00340b09040d41c0d4083c0d00103a031a0ba5049183e45042e00f80710403154841c91800c030010128a043d00030314007540d4281c0b10040700d0707140e00d0415501c220302c000e00c9900550040c800181c0d6036211ba404514134502d8100c00501d00702c8000180c800355655000c2c0c5e010390760344511700c544490381e041100c000244001d203400301050410680901602c40c0c1172054448010004c100c0e0100d003100c25950 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 492241330 1250 492240080 492240101
    0x3062b03080c040b070f060609051909050c0a060201090309170d1103090907170a02070807060902210f061806071d0316051e2101060e0a021c09200103 66
    0x826031114000e20300500c054600046c210784060404000144403602409421702603000c010040d2041016002814000d185204043e00c50384514a8200e00d191103a8600c007001d0700842d4004209580c0900700070380000100d9000109241030340700300e448844408142d15680c1c4030a49404c1600c52441c0103c5482c5000c0d4400b1a5804400003050110650300004003d520090382c1c1d100c103c40e5039400300c40d0b80490240c100c000d81b89007003c000f8440042c00ca540803a031a40e100401d01042000b400c80d0075191400c1e00c1e105070429901000341620b0345142001041c1d804040660072181d8a0095254107842c0c2ea00a0b2440e01803000034019030030100d0948183c5044541c020f400c80395280040501a190003544e445054007401e200703004401c0c1044511641140c648002d000381c0c7c2c118081c000c1d161038148044900c50119580e40a010a412000c402d640f80150128200581c40e40c03c080400303e22001d07840354000320107282c042000300288405c11144403130440d20a555005108101c0184d0203064402d44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 492242580 1250 492241330 492241349
    0x120706031e0635030706020901110114150a150c02030703050102120618060a03020f04060314010509060106081b1b010507020a050d09052d1503062b03080c04 69
    0x418018002e030300740340142280026a1030400d50b400100c40c04001c10f01280000e54100f0050034001c1101e680041c000c828040c03400d03c200f0307000144228211030024152054402c06c1d407042c0702c100c840300000318448900c21503815024a28000014034000781c03058603441030000081034941035640a005000c005c542200080d503494018020760300d2032110031211140f05140d5800e03004421114440498841d9102401003043c070745c11030302040000c2800441c020341c071a44561011001818050307552f4003400c81740c000810723241003c074461070410f94142c000d2070170454030508224807842c06100c0c80c4d104490034035429666800e4044a010451125030003004e49600380400d0140003070b400030f00180c840b400340080e41c211001600040318200039901c50303113070b008100540c0c072030bd0038588403001c0607809800b51000454801c5407011510300c6620060300036000d403010040006606041c131001c0d04d500b03140840180101d0001503000e04522007980d01404004c100030000d8120800d040c200c50141c09900c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 492243830 1250 492242580 492242591
    0xa0b0f03071502070b0708180f1003050609010503210c0114040318140a0330080108070602010903080408220f03050f011b080c070c091a120706031e 65
    0x1101c9074203980b0000c40c060061203020340000702502150259420980c2c80322044e40342401c50b01c0001540030071081d400340e002041c00603001032551281c00d04416500c241c0c5011440f032800c43d08000c22208140c1c03140f40603812542c80c0507029200e2000841000000a000584481080f80814018058440100006034a40040c4004c0c1a0880711a0301d150118450100e00c49843c0d00d8040040071400740c049400c90300c119018000107105101840a10241800c1e4001e800880d000640c440b00c05400303810b000c40c02c96001440218018801e40300541a1800244444005540d008080c0c8500404c00381801c00d010a2040000d010250b0108c94400300300c40114083e5201c42156003480d2403840120303004e06c18a06d88920000d0180a000214010031a60200c103900314642070306d24003402811440c155800300a2440040e0540850701c1c05400040b00c00079103c2060002e40340b407943c1d120130703441c0328071481c03035140c45030a00c00114401520741074603000ca04c1c80e83c480f141c0b68611061800c030302003490628 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 492245080 1250 492243830 492243839
    0x81906030c170c0f010c030210020d0921020309041815020d0e150406150b0310061101020702131806180201080f01061202030c041815050f03060a0b0f0307 68
    0x74a412030940e541e03500b0760a2450800c80d5030507554000784044640001d9103180d140015030140e0403807a2083d0003401604c1c8d64100e001340c9041282c2c05030a10056595a640c2100c00b8402c40d51400f08010b452141c3ca005014042200a5600d005241c00c0302c0c030440d00e8100005d104040410354084245e80082183c1c4c1c088030b06d0301c1006c003a4008034419103000f0320f81080d030754214400165281700b5481c0206020481c0c1c50300e490780c50240c000d13000e200e884411124030004002507044003c604c909107045280d01c5031410b00600901c89110b006851516030300500c22180583c1e0f501c154011040c1c2c034144002751401e00764805500e0201101400b40181e890030316800481d450502165104070b1003603844000c50b946400d6803281001084c055080054009602d810305002c0310f80c0210b40101c6035060050030706035528085aa045407001c6030141c010b803900701054404091401000107443c0c103c40c003d95080040340480e554140040c612290315440e0107040303415480700d05034562400f1019040d9850503856 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 492246330 1250 492245080 492245093
    0x815090a110706060911040b040302091806070e03070e070e010e0112091a0c040602030d180c1d0903090f06070f0c0e1008010504020901032004020a110c04061508190603 74
    0x136100300d82c10710f030404010440010103541110f040d9180400810708190454081c80031080004260000701c19000c0e1420034140d0007000070b14854006079903a04104004036041c50300346145903010444141c00d9605200300b294200d601d81000d03510a00e020440c0610860048400c0d0308101e8001c20b07064a040641702c280520802014004222240c122006898120034241c0a105a104120040c0c00c00c0c800002c441304960010038030103046540d0604146042c2c0c850500000c00307030384040300448954925101020100050960080030403000d0741c2010104030100b400f0391108100d0600c1403c0c00140e800411843c4100c401e6240e422001d10740c092a02c5501c1ca40d840c00c400d8603007188541c442240021180b405006191040f0381c040d140450701e034a1591044040e08840009000e9800d81c1105907c1c2900e443c40540750152981e566600030b00100000d041c10052800f10540c021418550280310304030806581038401122031401c01e20f1039444003400d11380c0c000301d0751220a0f01400c0403000010b0080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 492247580 1250 492246330 492246341
    0x61912060f171510260a03050304080903030d0c080601181208040905100602070e060f0405041110080106140310060e0303040308160c0608040c09110d050108060f070815090a110706 79
    0x100300c00007881d0039401105d900ca942c2406651070f8a038024400d000010b0300c2280034541051144e003103141400b52082c0001d0540c3c0103480010101d80c0e8400300080042e038030070130540d040710003820702400201d84511511418021402601000c4a4041c0c9820421110f0801c580081c02100760410007402c081740b08100b01060751040e8030041c4a254808245070655803001c1c2d00502c4010700860350300c0c60010a20000d840e0046c0251042e144d007a24204880e2a403041044141d00e641d60307540e995606041000d0840a480304440e900e041003401000100d030f0200300c40c0b20943d10141410062808590006840e40c1300b00e0b0001003003100041115043c802d82c410303060402c0c0e0b1048802808041d1141011645000206c1c3e0240005820003020001e04406910941c0f20f6141d070b4000510700030302c00807803d05071002a800a00b8981c03028003003264894800c864640c1102c0c031481c000400d401c0141804403200004186070740f144e600315010840080d526070004510060260805803690042d0804500410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 492248830 1250 492247580 492247589
    0x409060311041103310b040b0a150303080f10030c080a1e0201050901030902010926120307051b030d0c020c010e0604080703030c0c05061912060f171510 67
    0x5040804840c64143d501003624810f039180426517440030180c03011520f042007504241450300c04451859004906660200e610581c00781c80c2074516404d260803c14125411b440c0c409003605241d40091001a50104005030080369261010019460301c803003d000345400c641c0018440b00c844900020540000324100c1c03017080c02007582c10232054400c43c00c24050744805c032000b0f001840400c510302556000781d01c06094640185449485103413204c10b00401d000284060b1040705070380540c1e00b0002c0404000b60030203a00980074031400c60400104c040c000340100e288480403410326581980d07010008000b80d5080503402e642c18801c11441000107515601d05910030b6000601080004555051020841c0c044070000d50041410034a552801c0781d81d207414900869003055280b5002401d0340c0d40b10045c182c0100041031900c981801c1f0a4090094028400c042c0d8005050490820130000c19003030f0141254854001d50f1011120a0910780c02c000156009041c01c1070704805000821410001d60300644 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 492250080 1250 492248830 492248839
    0xa0810050c0c2a090709090504260d0b040605151b1203160f050f130305100225020901050405040510050a06080f0703050303070c0203070f14041d060402040c050409060311 75
    0xf00800018003c403401c04444c00000300301c4420041108039840d85c03046a0107405401c41c0b40c8403041030a883d170f503a074101c82c0300142d00c40004107451614407084c2c841c1a210036400c40e404c0240c0c914117000300e08519003400c585c0c41c0d1200045070490100059400900881f00d601c42a64041c2141d40c03001d56158000b500c3c842d546501032100030340b01e01d0040c020761004082c540ca4081c140801c0680c250880d84c0720558a1065400348100040050380401103803002c43e09551000d48c17075100c00100c0300c0716111640c101c00001c0306665071180250b00c0f00e030034040c10b450003a86c010509a40e542441f9150610500802540d6480e050800c01d00341482d52003281910b141130187ca07180c0c041c0f41402541c0d81201e000180032a0400c00c003241400d4028555400814405002d48440550b11403500f040703c0b03116070102c440907841030310280d030740d24007433054a610005441c4e511a400151180b01e82e6603040c0100024000c50341c902e1440e9600f030144068030020001c44009001c90f54580c5080c07990076005081c1503009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 492251330 1250 492250080 492250153
    0x204140306061806010c02060c060403030b01020a0f08070c03020603100e01080d090e09150103030324060e0f040e010c1115040b07050d0f110a0207050a0810050c0c 72
    0x1030318001ca03485015a4000f44606010114810a080e440802400345030511840c5025580103844400c00b170251010183e01070700052409040190990301c01061050440d0406001d4500061861702c600c1c150b07540120140303403200114608000514507503000654444008000c1007213402c1ca00c21030506940321301150f501566640d91400ea51607020b409884049107800d0000d00403145510801030344250700303204880a100e649015144080003c0e0801c0d00069100d61217405141c01034100e44034480c8080d146004840e20b42080240b0b802c4220035101e01c60307068890030030b42c0c80e42c441d0003d4251001400c002c0112036046036024000c110300c00e400c1c041900600c2c0c0d0030380000b0440814144140d4004903107110b03558401404803000d80c0008401881296111502000c0c2e41a921a0301d100b50450001945d4039800b40340c0183c0f400c1c0c481d82c0702e144104000308052103100e902140310010030310700110106140e180d21481c001c243c014440031101c070b44204080380e001049003454910043c5c10095540c40d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 492252580 1250 492251330 492251369
    0x50a050601170a0f110c0d050906040e0a0b1c03090605070206030a18060c020c0a0504020304020918010905030310030201110601030c06030b04020c0d020307031b020918030d090b0105040c0302090916110304090204 93
    0xc4500a1070001039110303002f40003c1007140b02c4000b10980c403d299907000540361000c42b000070780c0c1d4180d0344181165006080c40e0401019041070000b0068481030400500b414641da0005150b440010705510b50291101d400705111520000c01e0781c400c03a4001000d010440c1c110700000d540d0410683d00310f102d100f4080000455007428800c4030300a540141882d03440d40d851200c0488510f0340320500c40203d40d42c4032040004548107001450040700c4000c048115a840d40c0001013400040d281e5541d1260000b10040000034040b03100e1038100d80650902080c2d94002c440000c0082c0601009e2034501e0103910f01410400d036011005081c03441c820344aa1a080714503480c2c0410340700d80785800a40008520020420f030282c401c416050924598003100d2900100700c0800c4280c070100b0104403251b0b290315006014620f02405651410202c40c80c4c2103051821510015a45031005000b020440000c0554208814450307030150b85800812000c9aa40e2a55140850b009500034441c6a0205d2007140e031510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 492253830 1250 492252580 492252587
    0xa14030d0c0c080403080f0714070513050603211303120f0203070f1b09020a0903020f03160e0705040f0b0309240712020408010e010e01050a050601170a0f110c0d 71
    0x28811a00855a41d01302421940c1c0c03a00c06030310400f071001c0b11303800c140003440025280f494918009a40d482c054031314145440c0a004d4244d0f0020001360a00c4e0501c42000116180000c459101440c910506000c07440a41403a0700140304890001001c07000402c400301c01d006106002802c00b014503a9108010841c08504984901031210008c00e221035030340406012039850b05d0141204030300c0001901c211a510745840007240d000c40b1030710012490704070081081d0300c0c10300400d0300e8800081d03000d0080d820b4144400c03c1c019425000d1440f080d030980c00450902072141c819036003d0540d140c481c00368542c03104110750550304100c0300c15043d403041c10306020b0140d00c030f4600d0400c800fa5004000d0300ca522881001e9a05015400410040503400d001c00100054240101c00007a401c400c00041d050010303003082c1e404d6039402030010058134100400c2c8210313a6409030504121039400c24920003a07855129094004d0481da04540b00ca29042c18249030111342c101004010012150040b00c0c000d42e520311094 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 492255080 1250 492253830 492253847
    0x131b051018140d06020319020c0c0a05090108070b03090c030a140601080109080910021c0914030c03190309080a080327071a0c0109080304051501050609010507050a14030d0c 76
    0x542c3c100016040305000199940c0107150003120048501e90b00403061054101203811941d450b482c5544041030454550400240e0900139000c182c0f10303171070300d0342c1406052540c03020107205900c100d050000c00201c1d03c18003440750a000b450000c1c1581e000e201d503405c00310310084560f40180d105003e071a0000074200c40c14403a01e01e03501d500901845c2004403500400203284a140391040035801445070040f0488006a40c284c82c80c0794689800c59243e0500d08080200c58501da0542c6c0a070b0310450440703c9950b0001400451000c0325038074022003120614045032001800d510105a0b4401d510100c0c081089080166101c0d034458104c058651400341086c03d0010450041151160031001007070140745041030b2090100300341c000c001840c026071080400d084407071050042c1d5104d80080306102c10002c0601c80002d9403003040c14030402a50400002881034420782440758188080001c0d000108501401240a4150007510045081c0c484040c1c041c1c1701e5015514100c0d0721803801185075019801020308 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 492256330 1250 492255080 492255119
    0x5070f080c10021222050708060702010b0118150c050304030f0213150608131b080c011707120b0402030916060f08040213060b03090109031205131b051018 68
    0x109a11a100c000159140c3e020030808550341740044003c0c500810400c201d981c0040000340010b10561410030b030020300f190382d20f800040c100301c11f500d40c1001426000fa848001d40d00b03000c043d8401214180360a4806601c40e010040850001150000a102d09000ca070448030b80255080b0400701010b85100c011035184d0400360a088c045050300b40f119a03c250758865210811440d048540c8605d5100c2030103a0664101620b41c1000c02d220a000444080c00b8441d0311f20b03030a0821204071280c0d801031003449540104260100101528007000c0c00702e45800c08010b040c0701034011940da00b8405107554860203c28200c4e0007044882c03900040861003902c0890452402c1c0d600ca10681d04d0b60360802c0032032801c01e074080c2c001e0b41d01d6550200b826210740c401103014010100001030310001d14030b009406102c4914414000ca85488100800204014144c40340b1075407110241031422a11000ca855400284d006103405c000c9108031251415000031060f000700640340081d03682d0582d05c0700c0c0706c00c0c6516804032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 492257580 1250 492256330 492256357
    0x130e060306101d06030316060b1003060f0b07082502090906101211040501080a0302010e1b10030e070603140f070519030b1c061503051b0105070f080c1002 68
    0x707083d0820900d090341c43d00544000c1c00c0c0c1e0700e40511550300d03010740341507014207907111640c45221603103070700d01a200d4042002d403030f0074140314441c9080002d00030703004c5a120304280d5440014001c001c0003030903401c6810000000d0142c1ea00c2c0060598030002c0c0c0354101004030b00903516900804e1640d1070010340300e80308000782441991850b04000700700c405800c00c40002c50752400c00c0c44c040741076543c1e58000c0ca03018100c900c0040146c080117050007030070344400d034100389655040800c0f460552202243c0c84490860247c600380001c00c4441c0b421401004141c8000c04503015009000c9241541500302e03503a0312944200b5a09140c45400300f00e50054010b65444003c035004100341000d42c1c40c0002f819420038028240000d00400450108569401504403855819900f4240d80100441c51192424011059030452840e90a5541d82a901d1640da0380d1122111028242003407180c0c410001c844005d5405034807403105e02114078180c0070a0b0020326001440713000e44440c000d107a01203882030740c03041c2e8403422 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 492258830 1250 492257580 492257609
    0x402013e191e060b060a050702130209030d140c01151502070b0301292a150403050d020408030f040501020c0108150904060b030a12021b01080a0b0105130e06030610 72
    0x201102e0348401c10301d604981c0241c03540f68442d41d90390740101604d88a6429100d41741e84652034030401c204614601384401c0618418820f000700e40e140040c400e0703c803228608111416004034900c2c0c610900407040e10b9030b250740c20900d00b054603a4201c10303c10201c2e1300d0403540816040303a0702002d0380c4440040c026802001030038001045803000e40041c205690007480c01da001c1c101d48000121b1a2540030350060000f040303c00160001c0ca924580d00500d885031040c2c00341c2502d28a13103500844001010700f0142c10850017007607455490880e81e040307900402c00c000c212507548a511000442a8005114103405806886807690396035000700301d118402c02021410780003549c8220104405003e0182003906e040e9640c1015107041d4030300f080b1a02560f406250940c42d40000700d01c009240a03282c80060b8155031512030200d5042e40c02c41c0c1c030586c1003945240c01280540c5e03e440129014003907014102045080b40700000707100314001449a000c0c500940594015a0310440d0244200c0c600e40f042144000c520b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 492260080 1250 492258830 492258863
    0x6010f120b040605060409200708391005010e010e01030f110a0e0402102f01090507031208010501050301050f040506240a080105040908030402013e19 66
    0x19442610710003030080c8001001510740001ca03403c0e41180c0c000e50071a9036140704200d2940b140d00c0201c0304440c29030414514103c51036076008030a014400c0c11a0080880704450122402d80c120443d070548848441d4242501c141f412065941451700c0c2c00040d894030741800459514668501d90f41658484150741500782d1840d40c401040108150041e03c90003405081455595a418080c800806c0d2340554840d40341440d004002054040705420003e014071070094186d40c2e116108180001180c003215140c80308020b507845805008070344070083c01c501811001000b041810708810b104a40f1640d075030b20650380c8540040d01d05d88000c0c040c080c0d0100040c80340314131301d1425402243c2c1c0050050103101160f240700603240c0003e98080c0e0908420b60001c03031621036085c1d200603c58010a41114244203080c01512000080e1002800182c100020720300c01280b6205420015080441c41000c0700c8503103002078904200700103050300d841c1094000e90901310903080b04035108a5405400c20001013610429 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 492261330 1250 492260080 492260117
    0x180a02010f12060906030302251e05060c0105040b0a0c0219080c0601150e0312040902070f08030a06050a1d070f11070b03040b060109030b13020111010906090b06010f 73
    0x5464184007002040407a08150102c0b41c02190001c140308107001c01e40e80c0c154600079043c0041100140d07121043c0c0704a0003002c109122404080b915416289138101c4480349440350045440c2d00155004507000403079030350f0b017981544441d00c554095038010901341c0315010101c060b0350354105140d0040e80300c0c120398000e100c9002c4c0302410851081c8840c500d81740c2c01c10300041c140f403000d13440580303110070100e03008417081d03040780d90042d034074004030080e1520304074070701d012942e500a0b801840000741d400700301130007048040e2504405854100648170384a1038420440c0c0c0c0541890b0184c94020100741c0400184152050945076085003100e140d2201652002821100000c60016210030041485c80501030301d281800303131001402c46190610785e1b91926080c01c1107401800b9100300d0411245810810104400d400940d811440007603003403440410300e000481d0f007000081c4419409520341003c0101300b108581c011844c081c4506400c43e056a5243e0056644e20007112180000c10268a400c4450449 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 492262580 1250 492261330 492261347
    0x30c070818091305010c020102120a09050a0b0406090507060905100f14040305031e0f0a0f020717010b09060f0d020405040525060e03010b0a0308072406050108180a0201 74
    0x24181d4081003860309900015182003826603c64400e8040200140c00f030000070b00030a03c1c00351080c0025031a22401c00781c500c4400e04000c041240c00ca650f020b42104000081c41007008540c3c0040c0408241d081031300b0050004c1c00c0428007101c5038801e40c10000380480c0100680d80880c1c0c0d0041c03034820300c0ca001b14402e880f02e01c1c181c80e20b18100440d4110351204000c020015002441c003400045895401100590034030240550f0031210601c0e0031300440c21240304107000c80e0381c540200e281400683c0c06480c0242e2910090f500021020440000c3c2184002c4055020b03060405044907c0142500e580c418028844419501c0a8100032050b40c03c4000d400d043e008290014070404c205c451645d030702c0001000d031194108003c038040c07550b0340d01044119803040c04a01d0311003045008001c034020304000201303c14000d100050040c28046200401e11444403078410b4034005e4070b5000040c07101071603450030042482c0c3c00740b14081102c1c0004225414140d2176180c246119401c010a00124580c0040d100c005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 492263830 1250 492262580 492262597
    0xa050603070809071a120f040c06110309060a2c0906060c19120f0516060f0e1b010f110607141603080609010501080702060705180a0e041106030c0708 66
    0x1324040002900310010b517a260188004249001d0f1100c00c2a840c07600c6401e00a4440800a0004028803010850b901c034034030300f1200d050500e04925045554917906501508550650001003c140c1a80a40d041594181051801407401a60b00c200c0b540e003000d40c452140a0a0300310031071000280240c1014001080d900407124100c54049414409200c820300c0c0c41c801c200c0d14024240d48200826422000d002905d00b40f90411a0802906111014062060001c00703011140c49910406001d503459000445840c40030741580c0b581e10381c01200d80002d02c042c180460000b406a404020900d1046028140a005072000b41980e0b0b12208012280b010300041085010074003004009140801003091200903031181d1642c282c5171624204001201505900560500c035034502000039941d408113481c0d41c00102c604102d512100c40000c040281050b50010940204083c107020075141040320f000e5100b18840c54100000d818242c1c00c0c000c56000688011000c90000e004100002c0d01c250042c041c0c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 492265080 1250 492263830 492263833
    0xa0303020c0c0901030c1703030103050604020409060e030c34030b0c28030606080403020a1709120f0c061c05061f080a0c030c0e0f12030a050301140a050603070809 72
    0x160b1030580055007400080c0d01c2122100880703001080001c114211252503c0b528101850840d855501d03116169500184001c1c444c1c1c0e9500c9180c010060036520511203040101d040303c1c4c594400040303042d550100d002d00c1411040950043c505404001c8401070030641d60b004130442210310710b0341d51000320040a0910811031005010144095000b034940c08030003406c1d9414001d444a140c90047d040380d0b401e4100108014a0604100c08260000780303010b281544542c00461940d06028040041c2c0610b40d00144d0007424983c00140c5807000180741d14405003000290359a500f422001c1142c148990600c082410504060700032911400781c0c02160f1141c405461a144280000002c2000341801c0d06d25a001c00d0440e02845101603040c03003210401d11040c142008101200c02005e01404070345807145108080340300c080306d6a91248003030140d40d07900c1d0303204507501c40048900150031900240100c0400f4148455002524500400c4420484001411007891a03e0b00d14003190000c0d8000c100c801c41e0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 492266187 1107 492265080 492265093
    0x1505011e030f030309020319050c030c0d1b08011b1701030203070b0a17010617160504230a030302072309060607151e0e06090a0303020c 60
    0x1e407038100000032003000c0c07107140840c007600540074000d425019261102d61031000c4a05814996841001520300c0380900e082456610b580d42c0213200c0c0c1c400000c059050110f0030b0f2070301c0c5031808001d05200c1c00e22036889142c284d0075142400c2c50f8019100d01d40c102d0765212603000c180c015201c410341c404603945503d90340000750b4840d03007401007030a45e600003c1c42c3c50b000340c000d070286000c0d80c50341c0c900d840c0e80b0b689d43c80001d405a0b9803055800f503901c41460001f1001c0c484149521505401b41e110242031a0400d170400c000500c841c625803030407201154011440e6034903200350303c0055200e07030b00600d0300c1410214611600c00200e46585442000b03250905400c0e5030308104039501c81070035134443d62203c4d07003820800482082c0344610300c2e1b483d02c1d00340f8841400d520004511007200c00e149003407014078001e40078190b07100000c5500c4021030700700c8514440007900c641c0061502c3c1c4026400c0300c81 = true := by decide +kernel

theorem cover : BRFrame.Cov 492086330 492266187 := by
  have h0 := BRFrame.cov_init 492086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 492086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 492086330 ≤ n) (h2 : n < 492266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
