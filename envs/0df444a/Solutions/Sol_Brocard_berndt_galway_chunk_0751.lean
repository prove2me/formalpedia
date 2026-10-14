-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0751
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:35:09.991782+00:00
-- url     : https://prove2.me/submissions/74fd8172-b46c-43dd-ad06-4281b3ef2a25

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 134892086 ≤ n < 135071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 134893336 1250 134892086 134892103
    0xc0a082206020c0c1504060c0209130203010623030105010f030b091203070c020108090d090e07050706020d0515030c030304090b04020c01060e010806150f0d06090209070f11060405120714 82
    0x40c01003804c4000030f424404070002104600c110740209020800c8600d0f004001c0005459040311914119514003e1900d070303103081107070040e425619040000c1401d10310941010b05a241140008480501040805007a11000d000e41502610608000c2001807110080d29810150030401d444900704100448180c80e003080302c2002c005240742c031500b4103650308071454580115460000d8030800b8081103010707205040034450108034824510015980d5031080c416121082e074804815584d803290100c0410107400c058a2202e1400721305e9031060500d140000e00c1c4592100003402a601f071034a082c1183c0001c00f525601160010340030006d0a103100828800d51019240110703000f0354035414800d0a61400360010322007941d54400c0c440c5d0007060307a0345081c440042c090403101e00043e54190300d8044003500603424000e4006281500f80024907030488840c42e068a99075603465121070429400c6030782c1e40c0003aa1b002d17082d134121300180400303061000010a0b89900810402c0819500028a40e01e000c195 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 134894586 1250 134893336 134893357
    0xb010509090708070314160507020312030c04180c0212030a090203030316022116030c23060601180e07110604030906030b0f01021506011101091a0c0a08220602 70
    0x3030f004010f1003580500c2600c07a60a00002078410914281144661071840c100b81c0c1c1c4148000441c0003070440d98104949840c0c0003080d410540c0b28100113054440540141c0078a028240c4099441c5100d003040d44141c020b03010965000302a80030741546207841030351010304190025038840300d1060147c0c800700011401070701d4074070496440e1954018001c1c10a800c090140b01c880d0f401c1c0c0c0150020041c04020703640000c2d40790f80079034448401c51906542403184084000d1041c4441c840c500c01e003080c6103202e417a8040f0300c48103460080d0f5071400111741400c10040c005502c2c404d041c8d8180804000c02066690280050400303500303404181c1e503203a250841c112000c60000f08891810303c8029810700440000c1c20080d5442c801c250b0f2210700103512140600e08281407403156800051035a8800e02c0380b1907480c5514402000101060704114121840c02d0f00c12002500b00c13880031840440c0c2900c100ea400421581d51100c0d82d841d0400046c20100180d0b0040f5015801800c42c103003c07600d82c1c402408502c40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 134895836 1250 134894586 134894597
    0x5060f060a0813051e25060903080a170106020102070233161e0302010e0601050105030f0712020c0a020a0b030c03180114151002070807050d06060806010603060609080d0f030b0105090907 82
    0x3e48503034603011140740b908491140504180b082100f123802550002c00c0e02d070721541d00340d1110348020b421540c40034103242c49040117500400001e238171074041d4010000540240c90107a08452000301c1d081201071021800d511a032541512001c0420141c00500301900200682580044164807030b0036045104001007402802d020444204150f0244500e000c40724644010b440590314000c0064001e010081c040540d1004040c0050442441205071014607120300c80c0440d141d240d4843e940b43e844c40c43d00b400f2030040c4c030744000102d403400310101035030301c00c4460114841c619601e1001100801d9400d0f601c5a103199200c803070b0f51903000d282000700303481040c8031800f90f02d00c0101c10013005104e40000344c441d41075400c901c9082c02010004550f00d81581d20544811429110616241004000700c0c1e0000d003590050000110349542c2c10780101c800c0b514a6903e49001c0d903110390043d604c1e095003801480224074180d642801c89402a0008003003501c1c1410450f090002100c0403404c1d084044510b80c0c000b40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 134897086 1250 134895836 134895853
    0x1f020316031110050114040b030109021504090e030304080d0c02031b01140f040b04060b060d09080c01110a0c12050d020d0506130606090311040e070905060f060a0813051e 75
    0xc0030090030210f9100341c0d4041c0065403400000c09168104804028041c40c1ca660180c00700741c400350400f039025030f40603121440013a400a4444200e401070700a540a86040402150a904000090701e0085d074100c07411a1400c403212044100070018503003502c1c158002888010704800243c82c080041d00040350012860800014000d401d0a000401c00c000710100c00050102144050b00c3d907951042d401040007a6000000000507468000c800001c0b4105051560003420808081c0c0a0800c41501d02c00901441004120f40502400381648100c00175643c202c2c1c640114200d110100302d10074803410050300d0032450151034410303a4400004a50b10b00d031210240195800c20b2000e01b05104a40c8004111042c100300005050816920010349400904a00790b0040c3d60359500c060464078001080300d034519918aa024050041220618030550f04640f1003211030a010302110003d8009980d54120303540c44801b035519070880880b0a03206403003000c5c540c03034005107044a0360b540050304000030240b24 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 134898336 1250 134897086 134897117
    0x5060112170a030609050f0103150b04060b130806070915080705090409080a080105010e0607080f0f07140d02031306050c0109080a05070b0a0603080415121b020d0207051f02031603 79
    0x41d03002405070301f1000a11001040402d103840390901d441120080085802c407580c00c00035025040d9904090010b0b03e0011b42c100302510300305424007c45004d40d0984070250f9900b01d060300c1882051244070200d01034020240950352003080b40640c880f1080c01c159003003c0358400800d0444103044003c440300d050001e00d10302c0d2590400e0f00180149400d280801e1280b0b03c02000c02d069004030758000741400380c0401d10024081c401400d0300c8054400c201070b00d84800c03050030020100c507045260320f0340b54041e8120507580c103031020045034188055401018892440d010040300c250b40311034615415550713110070381000075043c0c3c030007414035082a40d242520f07a000c1c0d0604a0050700007800c070301902031030314600b000000d160341c042e60101c0c0d41500b62b20044510820b01543c100458541b045505440c2028600b140e00c4c13900d20b6001c0f0260700c1d50880d461b0028144050360b640c0c4c3c103401200d074030061920b00505000c00d80c0e155104043c0082c0b0644c0c0c10400d100200d045060f0a24000318040b072000812031419 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 134899586 1250 134898336 134898341
    0x201050703230a050c1006080304050f1804111008040807020d020d0605040b0604110405030a0b280f0c030b030c090a020c06010f05010e011b08090a120b0a0501080a05060112170a030609 81
    0x406e08103e07003000710070f140400050783c9102d0361140a00800c4801c042421594802070720920103804420400010700d05031800c03044500030900058851001e440754119014441c0380c650f032143c0da01891507803900c500c0b6000c100300300c40b1200049030702413040e0b0740300f00c0014541c0c080c00d07000b2403184100e00d0860400200300000e641c1011040e4400100030b100810a03075400294201c2d83c107400c00300c20f001c2500c606012440e01625400d440c400800c102010303a01c807004903405449040d051a03810002c26041b18411415105128000c070b501d0792050050310054a02107014540149881c04018500811a8082801c00318240d21103401900380f21401c04c000d503000032003a2075068007442c188074484004640c2442c580c2000d10041d03c0600041004441500d41c800132a000e0040391541401e596502d19100e001d41c20100d070700781d001604181c00003458600004209480741c1d030000140025030700309201d0307200713006c5c05410980c0c0c90740785514050305980e4004020a40d1810f030303642c0401c5503410080c0e01c406 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 134900836 1250 134899586 134899603
    0x427060903020c1002062e03030503060103050f040b0420040c0c1106030c16022d21030711040603060603140f070b19020708100b030c09040201050703230a050c 70
    0x380d26254810880d41d03601142240e4005910329000401d5048076511410340c00e01f1600c0306407851207840020061580000140d48100000d90781800117540b0a82002844081a038000302107100c3d4001260015100c40d0444024104e506405e010310040d280000f000d035a211078840d4041010709900005111100072100300c190b81c141c0d2503601d541400c00e0303a03940341d114104e0396030140d492400090086540c0d07014035100c40f60703d18400808105c1c0140b0701c01048007000b948e95100700c40741000c04141d00c1024000b0f00134481d1420142d81030815986a01c41c00106107021594041d41d5058040005000e610035070340514000c039100c1c0c3c800108139044c10710b0182c0800400e00035502c001810000e0702d44001c101d87d10554810182c80c2c1d010810310f004d910b042041e070458091070007030140301f502001e065400003100b40c00440841d04405020410300c00c42810695000c0d0000d10108075000c0070a004150002c0340c0d80075409100300c0006401202c100ca81c1000221900140d000608101c24000c00c121804 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 134902086 1250 134900836 134900839
    0x409150902180405030910020a020901060302041e080d030902120303090102030103141603080a0c060509160603020c07060305041707050a03030c020114010312020f0a0c061103180427060903020c 85
    0x1101400c180d1070305a45c81c0111904144502d4030214031901040c421b000611146074041c140340c0c040c0d41c543c2c0004e0042d4000b03024020b50b621007240065800510540c078541214030341c1d00907101d101c1c0d1050044024104a01041c1c1c1c00c5503000d842d440242c03208200130f41c49010305500058495046140c1003550311031030304002c01d543e444412180c4d2141480200013003100e80c401051039407401c13100740070780c0d442c40f4001000d040c4d01d142c10100f041c5444040740c040c18614040030301410301d60315010160224000e44c1d10740812903000e40c800380001e50083d440580c019000700340d030398044603040391410b5080d030240c4012201c1c0e4120301142810560540108500080280028408503601e0000a8000d14051002409544104c085c050000c0d0084c400c0002491246042e280b880c812400d109225406030b20030036000900c08100c02400c0070700401a240d28126002000c80c100f1a0001044050201d00b286105080d0106e918096003250605420b05528450b6038041945140c07814041d041000c45000749 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 134903336 1250 134902086 134902129
    0x606030b060a0b0d0507031d06010f1a09090403050c0f15010b0403020616060f06080f0f0712060f0b060301030f060c08070f081b030c040f08010c0c0206090409150902 73
    0x9000ba03507084400c0e13600780c5a12500c000b4440d981d03110110058030711490f241c0a402000c403944880010041243d9040c0c401d0070884080d103075600d41544081e091119003104c0e81110604c1440c19528004407420f40040c001c0c0350485c00e1200c09200d003814464403c0f07850301d056000700c2400e0810305c1074080290042451051480c00c180c9581c0100702540304401031004c03034803d4180e485082000c940d0181818403150a420440c903515002020761305d039084448545948180c4505a1001200140c210203640703540000a840e001d4545c1c07508040c25468075181c034500d8490700300c059280c6034100518029801340c0c4880c0c403058402d0600008541c07000b0100d00822411008110780a90402e20044012446251030952982c0b015070030f452a10000010002850001051203401d041d10f801500603140414121050541d540c58401e00b210040c2da5204040b031202c8140c0800b624160001e01490074016001080c410380e55a6603100d980c918050a0081c566a0b01c2c5480c20340c1401458441c4000620003030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 134904586 1250 134903336 134903339
    0x51509100906270c030e030c0109020906030309010905010507170d020720010f050d09021201091e031407050f0607110c010203030f0f04051207080301060e180a0e030708070606030b060a 81
    0x14482084036400320240c40c1900d41c4c2e082c0c400c0520991143ca01e9001c00c1c0103a030b0300c444800e840d0a002e0700316020306a11030703295500400d000d4507000c400c98412090586400101d24900001510103400c4040152042e100c50096220005c11407002002c03110382c904401a940d40d079030710301403204040760f0000880303400110002d580142d0704581146150b0141e81003451f200d41c91901008054000d442000707400c1800c0507018104284150012040284035012444855103d105500d0a0540313440e00580021000d0b0303900b0f500d038120140200b007050301400a89040d0a514400b06250500c20342d11076000401110500c2c250800c103000c40310101ea82440a0740ca07600b041c40e06440c03160005044040c00041c1040801c041200400034422445c2c0004185a201c0a0038107106003650400d12414000c40c1c1c00c000d843d51a8030b0180f0b0100c90a80050924011580358055594002c101e000d6240d601c0b80700401c100c41c040340c2d140014020441c420303900400e5080c11071520410110300900218003400b000d010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 134905836 1250 134904586 134904629
    0x3100e0a052515020c0f04020705120d1b0c031b05010c0207060801150504091104080607050301030605060108090318030f0304230102030c071206060b070b04051e10051509100906 78
    0x20f150b4421001146d010410041c1440024000d204080c0c00900c1845507402058598180101608258808030000c00c403c0c0c02814400d82080e82c0000d00100280e0514000c000003070040e0507040300400b0360341a40540c8080395480f00c3c215000d01102030050780c0f00300701c20061a0b600c49003180c0034202c207040c078000741584110050514001c900504880d90384420f40c00444940220680e4018010441140c1040c28a80406443c903842070000b235070f220b0b0030200094603a50040070070901550041000310301e80582c01000340307040c10085140039414082d54034140101d05080024201512040300c03114540c41528440403114103803001e440d81590000d0140b214440300c041048002c40c0c02d03002c2640d42100b010703e07000004101c2c80d04211401c103000b00c0d0110601002c000c20f140709601c5003040300c2908040b5058418603074021034840400350b0100c004054407142c00d400058111440c0e001c020b103804a201e00148008000300d40c02841c85100c0c2c102040f8940b120300415008180b8003407a224020090003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 134907086 1250 134905836 134905843
    0x6050a050a0606020706050d0912051b0601230301060b031801061706060607110603040303020405040f2a03060902121b161e0606030507050f010302030603100e0a05251502 75
    0x110340014403034045503088208c903041e000300c82415031140010007099903441e07020340b0716000407110800703000701e5110700482c0310000643c0318140c8a841100a4040260102c2076522208562030990195242d001c0000c60980c3c110145002d132140c0c00174014080301a0740c6241c2194455440704200154a0700c02c100d08010100b40e42c0d03080320742036408036601c003501e080c801102c040da18021a0481400402c00083c550b06901810644074210b6042c08401c41500c414402d0f075080f540d550351035116495890013040328140201459440ca810003050317082e0b9490365601207820000081206402d054200203525a454001005100038454001d00f4513456013400d40c4c44941305c2000600a2100c0a840405801c1541c6c4185e0001d501120500c0002d8803840c081e92150079030301c10301d0300503520b2106c00030b01c5602078001e07203100d09000750041151ba4141100600074142d040c031103c01c5409542c69a402040040c040c030010307841071a028120404120741000401c0741968014644041e00903840c104156021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 134908336 1250 134907086 134907089
    0xa0b01050f0f0f040b0a0f0e0103020405180715090b040e09060907030308060f0f031f0b030109110f0a03080d02070507150f03050919030210050703060b0301030b04061806050a050a06060207 83
    0x6940c0007400112200100e03c81482641260703c0342051f0701c1c000601c01c0411140281600c2c800d5a06002d252500c810b003c0000d824105003001d40d8001c58010b0146000145032459084007a290070320120b40d9410a101845c4e100e034000100c2c5080d040104505020200425500007400380c00400c3e0003172035514010808003001c0d2205102d4070740ca402c0003080e0350303800c2c51000d6081c1004041d42c205940d034007005e400201c51640c40c0b00480307050510081e440e141c184184091103030061207ca09d007051000402000003035036900141d1000d000704012000c02c0c81c002c05882c00b5143c40c1d500585d144800e04025140c0b0102e0f40c0800900500c4c4552003003110740c00568080d40b808181030200f044c1e12215000c600f045800c50301400741c620f0084000041c140c2c0010702003203440da0b8150803c07064a50b404201c0540d09035000e1426001e8042004000040c4000704003a0312a0083e0000104041824035594000c045202e0550b8815280c2090083c6000f0b24489c141d00701d408584200700e41454031102a4840156 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 134909586 1250 134908336 134908339
    0x60e100b030a060308030705070308060405010b0a031509060b07060e0c012010020c030a08090c090f0c1903020405030d0801030c060509030309090a1509060e130302030c0a0b01050f0f0f 81
    0x300100d060b5001a400441c040c42d407200f81d10f03460b03191000b03004089801044040e03000444181c0400c800d82040d1081c58160b40c61100207074030b8071003070010a0340a400b43e1030301c20b1071a1195140010710004281700783c0b0041c2403900d05850707581c4014101981540d4018040c071038075402c81c40c008200d981c2c2001000c14428103110803a41c0c03040c0311141d91400c040c09094514842800091801da0f24034000c00140f400844a0f100d0207020340794003207030541e030764410310115410150a101281d4505187c221155012080c0100c0d01e10340365500f40b0782c503400030145007110082a00441c007400f0900e818041d011001e207039480d1041042d8515101c0099000d036070711445060100001e15160139480a01c101c0350410405480309070790341405400d1500400c0c01d00282e0700e81d07070780680011803201210700071442110841018018541c9075510480c5148172010b40880a5103c100190114104140075004040707014070707032440786903141105200d81c0785800d01c48503214000c51300000d451542d40700c4100703044100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 134910836 1250 134909586 134909609
    0x5030d14070b070810060309020d081608040303030c09290d0605040608030702040b01081614040e070f2619060b0403060207030f0804050c2e0210060e10 67
    0x141503040565449154006081c5405200402441c55000007009024016503468020710540d01c4d1012002c498100900951000804040d03e0100e89000080c0c10058441e4419542c40c241c0b603607da155550003540100e0209465035841c180481e04101d1420052a41c408c84207184001102c0800c102d940c400000c4008482c00b0600e03c00100c1c0c65480107000e490003500800000d611850031503030380d8100110480c400c80c20001c01d49a207521482071180070b1240c550044c2c2303403d00c40800903507403051150301c00902282c0520001a499103ea0390840c010740d12510f0701215569443c0c0d00401521171600496238136083c5002c48117050605c3c0003110b030310010250851303000300900048000580003550041c4406040458040248444c075030092841500c43d4860f21805e9400300d5050340d036104202c0d00600160410b4088810340c1c2801410f000312340c0001c01e54001d10121600c1c940800412002c62440103a0285e400250203450394490840a0304850451000c24901007484000d4a8081d0081116080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 134912086 1250 134910836 134910857
    0x201020607080f24060705070801050106030b15030903090d03120c090612050a06080a0b150d120309020d080406030e10022a012009011e020309010c08041211120705030d 74
    0x3e00d851300c68820f840000703110035036a0303445080050b500d0708280204c0700c4a502c2c1c0000020100e0181c07050540c0703000c002e000002085400c0101900381d03000108110001e000070844000381e941c074128641c1c1040c2c8240ca500c1d00f1590010254811961205403004c107021151909101302c44c3c01c01c500081e07600b42828045100d5944540c01c1e0083c00c000c0d48507040c14420148400200661021010f02c10303128007074025200c503800f00030806444500341020340900702c000203290150707102e07070008101c481c0054132400184000d5952800503520a031721407800a9aa01034030b010042003889000c800d550301190640c14001c0c03503102010220485400c3e40d0b4030451014040344070000c01e400800c4090f00d01c650080b41e40d070f514580c45040c0e500504007a800030740002003601048403241080050514680d00440c02d11a48030015a460000c2e510f0984d04400c040c840010300082c0e4074880d1070983c0c13064440d40e0102c401c613002c0c0450b4814010340707070900d904822001e01c05624001681d04850925140640404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 134913336 1250 134912086 134912131
    0x12020a030e0a030f0f02010b0604050402160c0b0315030102120f06120a08040e0606070302060403050f04050402032a120601120615020604050c03190b04021f020a0201020607080f 78
    0x38603501c0070704101409a035518006250300800038460b50b8809464400d100041140200d080398102e140866000a043c4400d200b181800e50247c0341c801c01e070507402e026155064032142040d0141da4413840005c00e000007003200701204940c244201c0308043c1c000703605040440100c000f040c803000f404a006c0c040c0810003c2e18907543c00b0f0003100c2c5c032103081041c0c41c000c440300c0c10a2407070b0f03038040d0041c00340c989090b43c003003038690030030204a4110a4041d4050240c90b2600d94084481d640400d001c026881003d0002181e950f603184000c42c040d08002c0d180c035010051000722107128441c4d039044940948000c1c004114111000c090856111809103003158209450029a000504440c1c200306000200380b012400d10640001c0c0040c0540d00031422641c03071220b003c080694620500640070240400c82c90400005541c10340355581052008149401000c0103414602004401c0310715400143e10035072404040d5601885200d412250031f14145055141044040301c001c0c1d8082c0c0500301840840d5442841d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 134914586 1250 134913336 134913341
    0x409020a0e04030e01080f1612110c030c07060c08180438090c04060c0213020310030b06190501050c0a05010618060b03010503280501090609050d03050712020a03 71
    0xc1c0403410020181400c00703041c000d1000d0300000b0b03003d01160103103002c40d002c6180d20050034400d20810085104000e9005401c98264a040d40c2044100f81c480c000e00d91507040e4203010740105065000110b464002d0204100d18190b4a42d005034140300d14072001502041d9800201d421580107141c1c4526101e0304500442c0081c400314a640300030403194504a400e44580300c0407084110f00b0321803500d852400c90001c000c2419020343e044c0105c0e40b4104010004580590740031200d0b80d00041103800480c030174405290580e40102c813551200b89040505004002080f000e040c1c2181d42a0341d8032a00100742691000c1440b020300a49043c00004500b6181c0d071030080084c8241194400000d20403141c4d030f010446841604c0030040c00280d418840c010903200415015079048550040c0102404006960b50038200030900b0708103030350300002d00b481c880410024042c03d60480d00c034040c0004d04041c1c070f003400c504200040c60a10101800d080922000c5a8047c090781c0c0400312400c40141d0301d44d8107000c00d500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 134915836 1250 134914586 134914589
    0x302030405091501080601211d0304080d11010b0f040b060c0a03050c010f090f03080405150c04060e09150913020307030515010f0b030403030207030504090e070504060f060c020409020a 81
    0x5010001104110303404000f10442c4000c00420f803910181a2941001920b0403000d2080003540c044107840030703240201064112981040407034881720341007440c0e6800141184c5c020380141e030b0750358401d280120055511103d041c2126000d1002000f20600340b50006c0c9003001500d030410702c00d40c0c680c0038000c22a07031800211559005064205c403900003e503d809401500201d1000300c0551a01c2410240070313103e8052003800b0b42c1d00142e41c41595a0070b40d0187c51a210240050300c10344901c80c0101041100c440101c0d01804c9801c200c240c4940c0b412500500354981401c005008130f9a007020f00164901415407410f030040100c80480055035a00342d17200c0d20a0219002a50511036080004140038020031a41001040322420600b00e80e00c076505580d0b550b05900c1180c40b00d4100700006008644070794060f05001d48a45842e910b800c0c3d41c3d0901f4429501d07003440c0c0c5501500104001c03c02803800c1e10482e03000b4001004058037003850984041c285d0840118041c2c0500d40350f10041c42150b486206440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 134917086 1250 134915836 134915839
    0x81015030b030f1510080c0d110a0e09070f0e16020309030706050304060501050a0506070602070602090a0311090106020d020706050702060408070608010e090118060c230d11091503040302030405 85
    0x10005100c4085490f51a18060351100030052414081071001e03006810707540a41e006c8000a007a1246a9000d0101340120003409541c010010f00c00c00c1501e54400100070010441a08500200d04000f140c45040040d2944070340ea8400115104000031180360600581c032040850320139002c9102903c2c01d074114450003a510742d050007070940202e4556000805540980e001d20000c1003d0b81c0c0350428001c005940340180d41e440b00d001c4c00b061002130003a030010103006205440150070701003490302141400d043c54100b11241d2100c4451040c050038041c0096004200d148002d04008500f60406034450000b405040308000e00000c281c03055481d0101114001c04100741112500c0e9a25100148510b50a0055440b00c051640118a1464050251b4881419403095400344080c581ea685002400810480014400c0040441003006116040c1d040d0607a0303020b0005644071408a91a0b0443c0c03c10f0350030032034010051280b1443d544071000d42003074194401c01030741d81d03c2d200e609003a40395004540c01507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 134918336 1250 134917086 134917093
    0xd1713020a1e0b0c0307120e1009060201050a06030c060c02060f0a020d1107030b0a0e010e0d0e0102070602190615081006050901060c0b06060306060403051b0907081015030b03 77
    0xd00d000a2003903801c0080b0000044420554582d40003810310710071a0350610f40d036070081c05000d01045a41c103240c03528a0542c01e11f60809540b6801203402008541e125101081800030304000064081c011580e2180e40010200400d60031030b0368014101d01c09018034420800e4000ba01400c5440740380481d2450108503d00503207940c0c816800130f5071103c101e150400000c605240f20380781043d000039080103032030340450810500d6840ca003040c80100300c6013421b042c04c1c1d0340321440110410b030203128807001a00e00e960340301c00f403136406000039181c129964480011503100310480380300e03402d000d950103480315402080846c0d08411140722103420b04a680040001d40103459295030000c0305948628211401a681c01080f680c0e80c0a003075030f10070035144c4060315652640d0300050441c605440156405100242800e04040e00c1c0d80b01d040c80c0c2000003142843d0300340d40ca51585014a0180601c2c3d40c1f26800d8a4902e80c58509241c0041e854503c42c070666181000038a02088402d020303400c00140720310054201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 134919586 1250 134918336 134918339
    0x50703090203010e010e070803030f0c0d062c010503070f140f090106021615080a0905011104090b091003080a0c02030c10080a0608071203080606071a040606080d1713020a 75
    0xd42c0e000b0202da86c07516205214501c000106240040113880c864440003800030a26510b10030030054030340c0704146e0101044d6640c3c0340822884100030130301d40c0804229403000000311101540000c02401a00810f04c6a0300000c0108540224480031000340c86104c09030340c50900c1e01d2400300c1c072050140102c0d50f61001c50040040303006c603400200301d0b50700198600d540c074142c0c1e9901321007001c020900701100c001900750000034a846c4800c0e00840300d402e05c900000901d00301c40d0410703580c80740c000390001107550382c4540c80c652191030040003594110118441c5580342c90701c2c6590b0a9528410075070319206100d180030514055503020701c1041c44075500a000001d10403000034009040b0502159400a00c901c1c004001c214501c00242c0042612110410b020521142d501d06075100b42d00100a00d500220400141c2c00140800500c16640b6007002566640340c10107203000e00a880d85e541012055502089824070142e03800a000e110000c50807404490036260700c20360000d00c0c1c1d0344400c080d4008058080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 134920836 1250 134919586 134919611
    0xa050f31050f040b01260303090a0515281b080402040c030c0503360312070503150d030302070615050a0b07080d0c0c1502070c0e100905070309020301 66
    0x40e0800310260600d020049903641c80d0385008012001d035000707415020400c0044c05282840000e0500c110071184500400081c0c00005500c0c59204990b08402c580009105804000003045100300768503802880406501d803404000e1000c440c680a0701c0001402c0e030b411101d0443c2c0c542e0100c15200200960344011100002028110320003e4030b00324021454200d40c1300c1c079540f0a00c101090aa8941d944501d0350312065410b094020380c070045034866095a0b4924022424150102a40c605180b00a951070b240304402082c802c0390010840d40601070304004009030410f075100721400c032260071100480a181e5505084009010300c0000905d1140b40410240e51407010a540004481048409515094550550111038090418007c003030400500071102c07107040f1a08070304152400c030f00e040c0c18103046a8079481602c080100b0401011a8009805070501c03481d10386030030103405408003100940c00e2841568200d04110f21070115000c0c0e48001141c000c03840f0b03800c00c54800303400500070310481040c0b03034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 134922086 1250 134920836 134920909
    0x2090d081603110102090a1a09030106030f0308071106060d141e0d0905220b0603070816050c1507030f020408030903150603030412051e0c090a06050a050f 68
    0x1401a0302040030095403c003151814000c40300404009801040e841745000488661140b020b04101c5187d4800e000d1046181c40900c18400190300924101d00c0700307003090a0240890502800520030025680103a550313180e0000b0702c99802810543d52880fa02c0704500f4940d6041c030351040880c90706d0107003192504494100300c4190b00180b41d01800d58480c098404030594900b0101d00c5004e41200d1080442511803a421a024a0000341081302184020154000683c0ea41c02202c0034404980b02c44140b10002481c0d0710803075a03041380350130002d2621804005150740c6a01d41d07003104c0c22800074500000c40300c91081c1c100c04810706104100f551219220f214485e200d800c9001ca81f400b038490251b19034121111078602c180101e40c0540514581800c10401c1c05010791044002d03036030341c880c40703600c4041c920140c001d4000d00c0c42e0b8600540881c4010004014182c0006801d08640c0c5050000503c900d68810524400700c8104507440c1807030901c65008102202400e5200c107000c82c3c180000842c0b42d92545 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 134923336 1250 134922086 134922127
    0x150f05072303010f0501031a270a05010f0302240409020405030606030c0604031707050d0e040e060405030307050904090c090203071704080f03060102100c03061d04120302090d08 78
    0x141090346180c036400240c200706001c00d12603c0c0310582402410840303940a644185550015540500804003600c40030506881440d4550f0b0a080e800b240e4041c002205403031042c0d006101401c4c00e21043d450304410321148607450002911507042001c42d0000301000740d40d80b6041030142c1d42d030381c2e4480703903160b03210002074110707110741e42c001e0047c0e0000034030506d40418010b0445400904590400303003140c450410703440c185030300d00d040f461081002c280442d104214624202e2990765560790195400c406010944624030340b0204a94001e81c14040058000f00507290f001d8a986030050301e078056400000d001d0300500c240541801070340300000c16048443c2d0021032080d40f4586551306401100050382d1146042190060910b110600150818460010045411940500c12160003010301c42422040712003044040001c01e95a0368100300c1d0301c442c40d9001800e035041031940c0d01d040c50300d9154005d011481480c034004150380010104038503a10700e203a40c404207130010b0009403588041d14104a4034040c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 134924586 1250 134923336 134923367
    0x40308010807090212070e1504030b1e090a0206130314010e1905120a0e060d0c020d0c0c090903090806071101051312080c0c01021201050f06040302010c150f0507 71
    0x42c2030b40420011911300032030b0f000104c60040f83d040d90390344a034101e51240407140030a0b44442c40591010001680c1e42c0039001641c02040000f2060420a000c40102e00c04066402010071840040102141c0302259081141e034060314034507501c00f18032510198203503080e00018465500c4120b010b200240551041c00f03404904012542580d0001c0050310004010700c0c4001c140f43d00084c09c80f2029114100a410b209400342003030042d000002c1c001450680001c800010780070b550780791001d00158101300c011540501c50500e192000015140c190101650f8018000000d4aa40000c0308042c0b0030b0f00040300030a0724000781c490600701000d0040ca0001d00126a805a43c02c1030049a1b0507541c5000e1014a26408050040941090315050341c260100900c034030380000d800e2000b050150020b000902559000184480c12036041004105c2446031643c80c403401004103200500060341c104540b00c000c59002003d101c2c90000c48800c400c054000c20a20100450502003807005090b00580140c00b440d42 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 134925836 1250 134924586 134924593
    0x180a090c1115010f090c03021e09150f07060929010603111c0506010c05010608030706110405030601031e060c030c0f021b1002070308070f031107050604030602090d0b0403080108 78
    0x1a2200c5003031011003030041c1521549108001c1198071745640c03003100b0a907a9030402504001915548400c6c0c02620080c04103075120008032000145040103600500e2107516842c03600b48a040402c0d035046005c1d082e0014091551844420f040c0083c800c031244401d00d04164505001c1001242001c1c203100038800d2401017802c04451920b0701104000b5207281d0720b4000d45c0405020510554203014040160500b03040c0a0340122440110360300f0301800c000307804101c00556036864585416801c85140300080c0359170400600007400650f8001c5002811250040d81e01200c142500c01c5c150300c803c0341c502d00100f80c03d291554030311100d9015041500b07190440c0e207865240c00b9806d5010303070300c40007a0120100100e81c081022540c52408520301d142480fa284115215991030341e440c080c465201100549070101006000400c0580c04042d201585594101070310301c1915103404181603016601006002da5004261510151a188400301303010b03030004090740060909080c00780050200303000e642041d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 134927086 1250 134925836 134925853
    0xc0301110910030507050a0c11030601080105070f020102070507140a090509011a010804020906090903070c0915081c05030a090f0303060503060601020c031b030f0304090b0321180a090c11 82
    0x40c02440303020b10681240d102e1b10700d40b1143ca503085414515524045450042c460b001c11200c1e141002402d01134414200005100d00b482c4c503000e061100d150f0782e103004581c010028034000540105122045800c2040ca0318a49408440011880c042c650042c1c40024503001c100203a107801500011f40690304845801c4212400c5001150350701001c4601a400c04c1003c00802d01c1030a103003103201d80c050004015a4140b51081d5103501810707255921441c101c2d0b86480181c6041e0303021000100050490754020504500b07011a00a500440310404500313010300400054014051a04501c00c0e840d84642d807035a54200514000e0020032803800307180c6c02440b07420000bc88a50000414040041004000302203180e80c604007040400340c1151a0b0390540036881c451130380c440b01080038101038901c080b80400c8110400c001c1c9403410a00324004806117107000312003100030110004594051814242c1d41d2071070700840002c5280d1010a0b0722400c681440c1c000340905203980b060103503985003080c40581d010070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 134928336 1250 134927086 134927119
    0x905010e0d0f0303061701050412050703080f0601090f1502060a060503030f0c010b03010c0c03080903030408090f010e06030a06180b031e07030203010614030d090602030a110c03011109 81
    0x18150040c0c5030005860072481022900100030081841d201c0c0c940459016243c045100320428a10010002c981d11001804100a481c0302c0c01440d000141c540b05062440d29100113259107400703840e8907185a0b114000c903c090744603a1658000c0e0034900c01301e0010995520805102b0030004234004018002c15011904000150003040b0032204000e009604128025135145c22035800025030b0303241d965a5404120a076202070241104c8000c241d15403c19082950038080c1032407400800b02d96864104108020000d0f02c400b003070b00c094401c00e40e40c0c60f04585207540141c0e81d0a0009054541c0010040200000c84400f90071404c2664800485001c500300c0d61420601510125025958590090000042e400c0705007401c49210540b900212911710341d40350042801c544840c2c111007207083c2c40a030154418201008500341c8610503140c002e616500e4494025220b000d0004003804014081034544035002081069882c80c490043c000c010703800d41030181c000c03146d1146008a004000c150321441d2407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 134929586 1250 134928336 134928347
    0x70b01140f0f04020c011404061b0f090e0601050d06030507050102010e030403021507080d1406010f080f040b13050714040b0303040e01120c09020d0e07270c0207080303040f0201090501 81
    0x4214002e80300d01056100502000043d401c09140c0f580c1c15035989403c6c0300107810078406140503030b009110005012980c0e40c3c0407280e0b429000c0f5680d0501c2103a0300070518480d032000030042220114448208a61a40c400488007807244000c2075071001c3c20040040144200401c000d812207409800070402d4003040765101d46c8901851101039800500313141412008050784000707002e0248910301e12031405200c00d01c145c003158640c0041140e0325039054100101d030358204d203c11442c901103092403011484d00300c800c02298080104010714461034007003c0340d803042106443c2003200340d03c0f20560b0300c141d849000c08040000fa880d01c0310b1040e03040c0a801925820044122426a03021040c80c0e2000d070f00b413102c8043c8a6035540070440b04041084400100c4607400d1000d06014640da08000c9000951040680c3c5480d605403c121a007580319000b41079264105c050b505c180f85150500400d05006240007603040400c00c2c1d00a1034076000010411042002e018a031207803081c400d80300c1d00041c40d1100011103a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 134930836 1250 134929586 134929609
    0x50c040b03120711061c14060a0b03130318080a0b060d0506010e1e090105270c150403050105181b0901030609060915202104030c020303070b0114 64
    0xb81ca810802d0740c010900700030740b8541e444400f8082c1440d0850b0711504000b56001e403020b03e02c68a40d1980d400003081880075440303801c0b00c02200c08400c090f05000347c001d6548400380040c0f401c2001480c8030010580521f000c4181d101c80032070f050740020b64440d4129243c90780448100c0703940c03d1002c0040c08501d003a8620700c0340550898028011030b820044006042031000c4d000d10240a0b10b41c005035140c40403080c0081c840c1c60380c4c40011940c1c1c100800130440b0b00583c03804070211101c00b0b01030600c84280018400e4513859084681d000c0c921030b602c05503640d501c52a040900749509010800241d119580317000b4512107000c00456444441400320103003441034142e07001da40580481e00420101c0d4403038004a819500aa0000444c5041940c900421102c1240e1303045172036880b204c800007200040d600b5034042d0384882c0b0420346000d40b0004405845011889c401c0044049100402c0c10306115140d900d0485038060101da03038916481c10f02c9a40a03c003442010003801c1aa50010f1041c00c3c40030900e071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 134932086 1250 134930836 134930863
    0x9050307020909070305070b09131b050702131a030d0c020108010512010e0d02010501050109210209040f060e2b120519091104060605030c0d020304030912050c040b03 73
    0x103080210395400c0255258020303041141600c502d2a003c400319030144440c0c4000d0880e140126945c204160500545000300030391081c3c2103189c40c1881e070720000f541550441c00b201c6450040d039182864400102d95040c00440005400e2514000c04444a414904105018004c80403500c8488065204840030060001e00a0002e8002401040b00d400d0030501e0131b0000303000300000f280100d51060070302d243c00242100180141c1d1140010030641d6040200100a824907401c20760030a203040d134184a01840c03920009002c1d02403940014184174803e0342c1e14000c2035101c0e0050105612034822190b580200801d00d1042c410707600915010160403698009a208860304c42903103115150301c0141c02008003c0c0b030300c0b2480c44015200084410288070f2081890300c0f40001160485040c0c0c280070031540c2d10303082002449010400d020042401701300343d450b00100c0c0103016a49590301c1c40c040f11030040b00e50140003c2d10b100301d014820002c022501d4042d103241aa070411840215101f095598030382c1c0e95111 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 134933336 1250 134932086 134932093
    0x3030818030a03091401020307090501091208091207080307060c170106020a020409020103151706010e060a0306020f04030602040605071a0c0f091c050a05010b060901141e041e08010905 81
    0x1544168080d81014001c14020400400c43c0c10aa05c0443c0c2664400c4502d040001e40c0440d0a004a60304104100c0180010241c0054101029601d90b66207114100210344200010704140030000d00401401c07010349220815241c48611615205002d440c0e00d14040300031a00050801500c00c500c01000d0703040b02c00e994020080c0603503a40911004040401d0b0680c10541c4580a07200a0031190f05110002d02605000901c0f000300018a10306020068105900c4a0300550034429940e94024000c07050300e4120100503901c00810742110706034801c03940020710682c000b203030015482c0c1c1c004014101c1e40d0701641d421840aa40c64440301603803101150240c110303803001e2081c1e030707200045400035010466018069242d56101c0c81c0b10341c030a107105003008685036440022045c042007421302038210000c105540301c42c00d0003802030001c0c0c611800d03e07201140314900403a0b901c0380020007000404a4100b14014242d441d0f0f2944507036054500f0b800d04110140084460020389040144241003446400c400075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 134934586 1250 134933336 134933347
    0x1080a090c05041e0b0402030708071808100501050f040603120315050402042d0803030a050403031805010606030608150402060901021c020d0306081912110312010303081803 76
    0x22000200920300007614250212074021400e500c0d280b0405544481d891580d51128400c0c08141c07007540c8040d41024020b038014814001616000f52070190070004504246140c21000044500490010f6000a4061017585220b00755015182d116505031082a1143d05483e400d03402400240c2e410703803000508a8100b07a414500081c441c0c0d1241d1002d0f03400111044445946400160581e045030300300500502481d14280504005074000300c4912041c2d02d46840c1c05442e142e40161240001440445c48036190400102003502c25800040b901c0101d400000d0705001904003140201100c1c01000c011a150410101d0f00100000b22084000701c1141000d02e40e64403903007880744a4110188160562240e0545c0042c89298948000903e0a56034000c2002c02200300380101034030440d900c050001e4100e140140b0450307140030034060b00700e5001000a54035014801003104c1054a03400d168805000200d2411607a01e9004820360499000740d490314102c0c2c45200c0c5100039004000c5100030076900800a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 134935836 1250 134934586 134934601
    0x9070c030206150d2001080619030209100806040f020102240406020c070515070b0601030608030d0525031506030b01050703230c0d11160302090c07120801080d020c0108 74
    0x1078103c5528009010b845400e0b40700d550341c0c2c0da1040034202036030095603105840405560701600c0c2e2517110318100c606c1382d54120302890704140031015000c080d000c1d00300b00300010001e4401854001c010f00c03a000c1201d12500c0e01e800c01c81c00601c10108101c2c0103004140c8110002c1102050740c0544003c06103407507609444a80e40c600095120166903606400780b510300140c941c1c0c50301484400d0202c54000d10342c0d03e1943d407403c0300550b40c004120314141440c00c070041c003502400005450701c1c803903201790000f02500c5803800d5048001c4541c8103400300403800e0b071070b00d00650341c0354100307001c0c114001c0d4920800e03985070b000070340580e2844140a800a82e0a01207440400c2c89245644c44040112503801161075050868003555031050070108031903800f4150310800c05a016001e0242c1c5113a440161040c8550241c0802e04000c00c1d10010348a10140004100580148070444081c103a209514200e414201071002c1d010140902c588022401032903804521913002044100044605a50748001b56681030f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 134937086 1250 134935836 134935861
    0xc0f01020307323708060f150a0309050c04050103020d1209050a15020613020f060c1009050c150a050a030c0c050d020619090c030b04050f1501030209070c030206 71
    0xc40c1a40301d2082024907003102d40b940f002000e0021034041c903074428055000034100341d000390002e0383c44120b00b4419a84002a4450000380d00042d0444281121254800004121020713061507a400300710002900b0903840e4055202da18964424000d8840007450300d4104402c80d4002d00c406904284149203030000201c0d080303120506105507040a4803c551550302103900052035030442c07002c401c0c030410640882501000100d51003400049d24406402c0c1c2c5030302080b008012820014001d00010646144400040c090745992543c0d4100c1000700c08500c0c02c2032561050100b6429000b90860f41c0c80000121825044a4150030350b0f842d40c40c601000036400f01c0041c001e606500042040b0b078803075000010703028481140c0c42c884030303401020740d400c200e004003445441d401c082010f071610300721280001951400c1c03014100c0c1c5d00200700790b035203075038074140319003021300305c070103003042405840350b20302c021295420064103a0b8020f40702c2d004250b41da81c1c019103601a4132400035015a20280000d2800c0c1083c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 134938336 1250 134937086 134937137
    0x10110c071a070506070203130902130b0c0a1b03061b0c020d1403070c0e01080307020310111b012003090312070905030109050609010f02040b031501050f0301030302030c0f01020307 79
    0x40744060b2611200303854580c24150181c618400607040000d030349404c0c207c81c06034071028060450045240295041d406d403816010740c810ba002c103000214804811480a01c01141c601745c02034010036400700000c1c1385026041250108640300e07032600400707400900010b540604200441e4070b540300c01c00129000c100328130031142c01c2152047c0d0101d0600c805400140b001d8550248501e00304d0403401d0a20403c6200010f058100140e00c0c1e009100d048056640000c0c40d0100e106152000265100704003001890780c4103201000340298000e500030000b900056100324a4540c10035003400040e41054005409840300b41e80380880c0380c0c01800200241c03200201d920303801869500701140b003250740381e010a0130b4900001d0140c409400200401031880c40a028949011242d00c9045282c60304000110403036000140055101c10300c01c3d0003e500e07690142c802c484241c8010400b6075169030b943c1c68001d581e603200c1900c0a0243c0134640c140ba044101c14001d40703010b4078154452404142040d8800120303100395 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 134939586 1250 134938336 134938379
    0x30f04020607060f1d010b0109091e060609060807030b010503040605060d061a0a1401020601030813231e060a0c030302070804060806090709060503190f0e10110c07 72
    0xb0880203000540a1141250000c2021400303d04007010b60300c2c5030030f0114030702c002204c1e990405207030319802d0381c2c40802d00046d24411400022060790b0321800000c9042d4881140b11403500c0e04801080c01a0410228011200250f4800e4060380c0c03003a000f2015a508401150701282003480890001106070700281d078000c80c09000f003c980111a1075400a4408000000340e054081842c0741046062038011500a80b40500a20f02544c41c0900002c0d9180d005100140c05410041b6171250080205441c260062240c0b43c1d082c2c00a904029600c82c0d030440e50780e1954800c9407200c40b5000500c0307815502540c403810013400c01d0706000072644292903661070b44c00120101642041707980006803000010700094401951034000500d0030100780205250050440303020300201403420003040c1c0d80081103070340c801c40800302d80311805080e420807009400e84c1110380c00030508000390440e094000007030700049010782c181c06004440d0f21019455036031180074608005508252420b002100711040d00c042003140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 134940836 1250 134939586 134939599
    0xc0a020f03010e060a02041701050615131203030501060908010504020d03030209011b0812010e040f1b1d0f010b070c090504031704050a0b0c181302041d0426030f0402 73
    0xf80d0701145003002800c550760104542d012400780b002502014040c20a005014001c010700e040110010303400d0100d07440c0e016442e8100184583d1841e04901301c1e00d0003454030090380c0c2c04100c902d140140c01303041c0034050807000400c2000b0000d00e2503014050140210b801600d010076904843e14100c010354072070003a250511441803004090500340356000c440f014085c0b254203450b000d05104a45001c0c0307044c0e1104184d103a0030360502000c0b60028100c146c0b01684081c070140840e00707040c409a040e0340281d0056a214800304405000305229021803445605550885501607807035030a10315450080a40180c20007100680c24080c865003580007030741140c040c0c180840d54100c00d240742604404211000c98a0b604030030005002c20880c04e1060f500000c411840320309110a0100d05541d09461282240c40f529290312a140949120760440e40030342140c0e0502c51102c00040241800d8100968048511200041040c42c0703038a12601109080c5003136503a0700b813443d02c072071042c4a01150041c005903070210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 134942086 1250 134940836 134940851
    0xb07020918030a021e0102040308030a0207110907081b0301290d09050d12050f040201080402010e13061806260115060c1406010b091002030c0d020303061003020c0a020f0301 76
    0x14041000d40b000d0f601540c002d0580540600c82c03020602101140c0c60050f81c010b000c107000181c1c51708240c80d80070a5103000180c95400c03038148000700156001d10f4a40001400060080f982c0d481a110342c070618840d0805415500289101c0445100900c01c4140b0600840e02e010501c1c00b4441c12410b0041594082d5400c0c000d42c2102d5030100c4050000884881e80488030722040300360803940e02010343c072051404022515282034020140000140000d0420189500241c00c42e03008030f9080186c00c1025014000000c43d071510340008003698040e00d24626004620750510150a014860070707079001c00d88005003d110700095010341040342610348a95522110348071500038001c007602c801800c2c0c0b03a40748c084006241c1070020f99000c1107240559982c03c184014894802d0000864100403002d0b02c0030340c1000c0c4501e03401c80c203501445440f0603d42c042c410703a4034140f80d0700202441c00f611040358200040c0c918400c00364102d209500211209811100140c409450600720b480e410328030240001c500903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 134943336 1250 134942086 134942131
    0x717131e230a0513021306110d0f17191107020d0f08040e04030807080604020909150103090b0108010c080601090e0402130f050709140d050303150303070b040b09010f060b070209 78
    0x9101e49402206558080369041b8055540c18a0800504160400380001d42a4400c0c0341d48800541c10800240003100c2c0305090114400c14012490304080305201589060901c4200300503510036924084030b600701141c4103508100c120840e4282940240a69050015551102982800000d0650340440c05002c0016014144500c0318403440c03081d076424000d0319001c10050403000d00940800d008031b01c10b000290850b124001401d422140384040f80305203a0040004034080c0054030b40042c450021070000051030501500322200d00b10140d110417085a0341c2400440b004460382c403d11041c816281d01042c094200280c4004c010850340c0b0b0085203081e0f2190043c0c05a903c19501c010024142500802c508891080a9840b072281121090105009034841c5552400050145048525400401c1c6135030340d010800c4602644e03000c090925185818282056500c030b044500d0815942016030f6171f605a40d0622540c4183c030b05d240340250400d80700d03809001c030644004041c085100404e00144124 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 134944586 1250 134943336 134943349
    0xb061c03110655090c0504020c03040303030b040207020909060601020f0607020c06031906030f0303050c040f09090507050a08030c01150509010b0717131e230a05 71
    0x545029846020716102880203861400000800e0540d50020300d940001280c60b688001040c1e840703140714080b20b40303054103040000d4480c20280c1100d64803141d1000b0b44030880507800002c003040c018100c1400b059030720300910080c0e110b16000002550020007050002078000c0d030240012070400f500c0181403004a9012036102e440691b10703621154420304c2040695a8100282d10f1001800005015181480c00c406591400340c03000306ca2054402000046001e08003601c4401c0c40307605004203001103642d80c00d20403030000d00810f0550001e41404000703512400840300300d03002c8030300d81c0e03d020140d20714000c5450010165240121003034001d820001030143c1d540d00e020000b500c1c0100c003442c1d440010044850841d404d2404044240c82003800c1088203541302c4501904403000344540e0741eaa4040381c6440350302d040500c0d4107800f180101103a0543d4019550107403c05a42c0368210f0101851030700c4031000c00e40c1071181f14240c0c64081404101c4004100c08640b0450000050650040a03440340c000502 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 134945836 1250 134944586 134944639
    0x12060902040b30070c02010c02040501092909040b040201030e0a0c05030d0806150304141603060c020a0203060a0e0f070306020d060f031e030e03010f09050d050a0c0b06 74
    0x2e080401207400912916a0215460001a40e083c8044841680d86600b192401e00800740303010301c01540201015039005951407004240e00420402c41981c44001510040000140d5080b400c8201c2c0107180c0c00b025a01030600b074003c401000f1014030307503480d60740c01c107050030043c8100d0405484400000c10000e08000c9690714600c40e08840c2102e07030034074003414940f034500003405007001505001c1c000240c442c0b050824403203240c0410f103030b80d940d11402d120302100d0040c80901c41da40b0404281d40c01c038049076001c950030f8a03c00c0c202030011150000c8203e0b070310861640302941c16008080072511551056025119107061070707003038032507031040f01d040310b0b0600360103500540740e103500003a1220220f44507209003400380206040514100e810b41c0c071030120f6600ea406a8030203800020700300d101854000d100e52000444020b00a0185070402c8102c0e0001d080c40c09811070710340c4100c0c206405603901070f105480216201740c1c1c500e113840c8440e03114000516070180c8101d80107040c04800c0040202039000c0c0300b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 134947086 1250 134945836 134945849
    0x5061c0b0a110a03051b070b01051c0f05060f01050103020705190c18050604050603060403050304032105011d101a09040e070b1305010309030f050d1d0a1104050702030a1206090204 79
    0x1e0280b0340503441140c0c074000c410f41b004140004210500c0021000b900644c103640313003900d01950030301d4003000b101c40850030000c0103000f1400f0560400200b00000072041d1041900c0c02c802082643d0305c4005400307038002c07810f004120ba08a45481821192001002c011103801010307021000c0b55540f01d19011480040d9001440d40c0c1c8036400c10065042c0f0b8000c0540212090b4010140c1d4179090b24020a640009440101001550b403550300130100c1112031400314000700d0004000e10b5945400410700c40d0071900f980101c0703109020000e0140140b403102c0714200c4d05401003a2030b0003039040f8054001540500002a4030a076500d10402c65000204826000390190b666141d0355800c146401c24101c0d611a40203a041500b00a500c074006603110055602d03400c0d0600b066a21854104070b030368080c0c17208040740310184d841400d60203401003000580740c0301e190003103c1c940c1c550700c0201c4c01e000a03101c00b1500c0c4170240c3d10412403a0102880344122031488081150005241a101c20100090368400e91125 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 134948336 1250 134947086 134947091
    0x1410020a1206140a060f03020d020d021207020105060a060c0201090906090605031006060504091d15072c06030403110607170702010b0d061a091905061c0b0a110a03 72
    0x40806508502c01e9502a000c1e07059a035215403041c0000800d00c000e2400f8403420000804ca03100801e902035010380f0500115004103540f00c01513240c140c00250000c8000320460711400000c01e05050040c81414050140540300b0001e071402c00c58203803003030803001004a04004080300006034082c11846808007600c05500c003c200245880d00301803400d07940d8842c9100c100c2c64400304000c4242c200080b50103c079201c05000c9028110035414241c604207840090a06000390382011024035011041244104825102e2100d03c111b0b121031391300301007022044101e0034800700c4a4900e051800d1400303960701c9446450860001c00d60217001ca070034100c0c20344040c3c1c0480c003582c0710109040c203658030751580103106200801290701c4400004036958500d0501031b02c0182c2c1e400d07130340c01010040c031008601c80720041d00a54107410010b401ca081600000901030314039160030007040d0740786403410204040710811140d072003610945484450300d2900c007510034000319a6861025107504044405420f07030302002d8400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 134949586 1250 134948336 134948357
    0x501210e010905120f0301060c020f180106091502070e06030715081b090303030a0902011b0309090b0109030525030b0408030712050c12091603050a0311010b0d1410020a 74
    0x50361524001ca10013003c04031051290b4400c2c48180c03c140d0b8112202d920348090090b072680041007011015a884c1c0781c101c074840c0c003211a00c0741c025115504969650307a07904c1046079180d03100145940c00c00c04140040c0c0041004000c0c142e40003010507089413008095910a642d038041c0003d41040c804101c030082007548080081c003681a25242031041250170441d8500722800300000c1c1c49100c001c240c0c1d100c1c10342d624054019644110400c20224070440c6003265010441e0601608403050340c860051550f0400780040900e510900400b011030b94850700500c81d45801250f5826403294500e6071004d0002c00c04400004110a40c11080c0103030701039034203182d8034240144000c05007400c580204a01d5410001072102c2c0860340c00c101e460b0180d2061104031785855600c020750605012856824100d06400404814000c0205a00340d03414030a8036a20448040e8280031403c2e110000030f5603502c10309409416020034890406440e000e2030302025601580c00080f00341d41260407804852000a40943e1f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 134950836 1250 134949586 134949593
    0x2041104170a12081608041a1003060605100e0112090f0b0f060109060f0c0c0906240804023f0d020d020f0604080a020a0507030b15190501210e0109 65
    0x41d07083d01032505261201d02490306000c0c2506200c402c603a03440030040e441c400103050000400380d941200a0042c0300880604101e980400002d00c14001920150718040780042d00e03190910881c4e5600c519912148420700340000103403000582c1ca0329004540c2d0301d5850f8500010070707104485843e248030304403180840c01c0803803a81c217182000910303003410322140d0344c400c0c40b0003500106181011803452511580b00c040e2450921050f0405074010b40c1c80c141480ca002c502c009000b03000c04810f0f0400d00601071801c900c07580440b0320400568020f90800e09000031810f407202042d4880c01e20250000700c0c10f01d4000041c020407000038070084174440c3c51b044001540c6900341c1c14480181c0c80c4001c1d00c000c00441d0b01f00000d99444120181c80105104000550000c03102d0092040c0200a90004107440045a0304d0411910302c1804503200308c440300c0e401001c00030318500005034011615440b418080000e042800545001c592450400245803c62440f016261114040c1c0480d007800f44002003103078011440d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 134952086 1250 134950836 134950853
    0x8030403050601030c080a0b1803071a09010c090605090103091a040f1b0e060d05070e0c12070305070f08040204110c07080106080c01020a0303051510030b120705010203040302041104170a 82
    0x204048100c1d0000180c03d4046a80d1461036900411010000c508492289c0805451807180000003032092818840c4041c001144410091240c50480020b00060154020841d41482c05000700400300d0024401d0744403551180e030103060300c41d00c140c04290314840503000b180484042101c04461280495105108210b071140150031803924140c5013030a00d0381000811180808014203581c001d070314009400081c031800304112401040c01c030545113a0303400c2030303031506049a10442089801038410310108003502c2c0319218840c49140d85a1f1000c01e402003e070002ca03040b110280060ba0700c1a00c80b808486100108001000740c451004000c1034a2490034403040d09451442d030120305c1e281c0156140003802c0e6000b00310a82416030504d40055240d6506860100c048141c81c1d000b504603020440410700c041e015070052042c00000c40d800442c5003400010302e0340c0c48110703003d000d0060304140800c02c011b0820b9046400704822060b501c1e814240c40c0ca1b4200e141c000300022400c00e540c04811640c09010401c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 134953336 1250 134952086 134952089
    0x60b2206140a12062c1b03041401060b0c010c09080d08010506030a0e06040f0203061b0f1308010e030a09090203040c0611100903020718091a040c08030403050601030c 73
    0x5050072840640d034050740780c4040c000c240040081c40a1404401c0d006a550381c081009007041e4100080c031518070514500c1384550558460032241c250101042000040070060912608001c0d0b109147d681c03140d540107608008103076502c90700c1d07486100c04521481c0c04006884003640758000051000c101032001410849540d10005003a00240c9182c05d8941e0b1003001941510019540183d498441c01803c100a10322841a0f030705902071902070004104501c3d9410a206000302d04840254907960800b60442c0006509205840002c00c401400f42d80d026014042e815000018902c0e401e41d01c9914a003502e5000043c3c059640001400c548895040340d0074001402c1481011815441c00c0e40d41e82103403d007a802820140041440d0b0207005480800848181c10200c0f0001e100c01c0b412444c002e981c552045c05601c0c030f641c134903072035541003114a84500303191141c10450035040b030344908440521440000d001a07840c441d04180200e0942000c1006000652080000b05200d40c0355050503151043d49 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 134954586 1250 134953336 134953349
    0x2130b030703060911090d1b06030b0901171e0109020d0b040c12150209060f1c050604020a0804061113060203030106020c100203090103050604020912030c0c0105090a18060b22 77
    0x10080c8040c00e2420410a581b001c800540d004c180810440c2009180c1d051426640230100000c1c030800721340f40e0385c103800c26145030704240d03070900c00b40c0d0701c40f0082400344c1d0181440404c1507000a90420707050344103003030010209000c5000019401c000e600899201d0080341d9050350480500030610040001d22208800200794900840000304a141c2d15080d46d02d001e281c07a40c1c00950041068802030f034803401214001c0c6241c1100315629901110101201d4070300100e2203221034a0032000030f46904050003191000b01059680f100360b0f58643d500c6100410090410f180500c2c8248041c4520403001100b04001e8411034004503201d40c0f41180080c0782584c1400598007410512020401468000050b20920402420080f41e00c1d583d240200e8000d000d50b032800c6610290f00c0c0c001c56581c1c800070000380703000ca07505016115209070420040d19a88168001c03250851000e01c0c0130021810740b44040d42d00340201c01d0000c14143da46800713154250300f2030842403040103050040c0d82400801d00f080080200301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 134955836 1250 134954586 134954591
    0xb01050a0b0d050709090603060c11031312110301050718080723030a060c030209010210060f12030201020d0504240c050a110717010903090b09060307050d02130b0307030609 76
    0x80c0401807150b8019401d2089140d5101c2c8049080540548660005031102032010041070741c0d43c4c24a08041d150202a038400b044445581541040c001310403147c22800c6181c48a0500c2c2c0b40110030102c0300f00b04103054815800c404503000309580c00b07006007405a40c0a90303415640030200743c406044e4103a140d200641981c4000341c204001e04980d4410030056080c0300c002980700c0303041030100b0b05050b88000c0040c1701600c0d0268003250150164003030500f00000b80d08442031000c5589136070040f2012802121082c480307210f41002221403541e0140e050a120788009030802095803070b51416100700360f030201c80d924021614125803e80715540540303110483c0302c0500000207130780c0000e41030b03202c0e0104400409ca00b110b0b075141c5c0792200704082401010869084d820a82025400394000c1444580444c006440c600d00010141102c000360b401c1c01a005118900c0d54581c81d00554155106101000301150240900000c14452105000007412040c0016540e458041d40082c1210841d030001e000c0c251 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 134957086 1250 134955836 134955839
    0xc0801020412020906040905070b18030601050a0e06011b0c0e060105030610080c16080904110a02030f091f021c030c0e090c0c030406030213060c020108060103050a06050a0b070b01050a 81
    0x1c0c650440c0b284070740d8058803111900c2d204c210101d0040c1c50400e0024105200d00c941c0054201c0c0e17101c0081c81d000c05150664182d0714440020591280303020320030264030440b516401c2c4007600c402d40300190000c1c014101150300301d11940924060a00946060300c11103244a01082140d4102805e41e500080900c4c00c1c070314528140c40001c480308088404002003044a00019103000c00883c00c0358191801060395401d1100c00385000d140c6644820380d0140581e0400c1810045540d010064910b81503c81e000342d8207048880640802503006001301981c030443c1c80c505101526400200080e01c0303034032940584400154103c046d015106441521800c041c079011010000079440407030359070840000c590034078003a01e40040704a0a802440c460740818040060001000c1d42c1550041c1442c0034035003662010749a0321041070351600c4c681d280203400300e55107100081c82d41d0300c00e0380300d140e2208019400045036522000402c80301c4050340c1041c11054000607421090201c132240f502e0040c5400c0b9407803101c16 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 134958336 1250 134957086 134957099
    0x604020f070f0c050301090813080604080711010201060510020a020f0901180506040207120c140d0806010e01031b03060314070f03020d050a050a082205061606180b01030c08010204 79
    0x51207241030191110329095603100800240107034140c002d0800400903c80070100c3d060449840d44000c0c084101000900740c0011105008100c903481641c212400505126903a100e0030780309503178a10000c0c11550303180c9002c140d80c1e40c1e1842415942c10302c1c0c1d0080c480705616106020008041c050700e248070b41002401049142c0700c80030f48640c0c108010102140b907445400200340640a40b1000608481103002d010442a50001c1c208410500ad2142c941004491141c03d607181c41114a0000c0041c208500090702035000d0392460301d011a0615002402507030700801c5c468401610800326000945440e030070000c1c06071520089000c0c2a40700040c00c10689002d00c3c0707074407201152000030b01a010031000d41c424010700340178060303081b50004155081c0102c1490100d11a5100d10704250700044180d542d64540b100c01c01c8080242e07080904410b2800001c24511480783c0d00401c0704039040c0381c65403000542c199005e51802c0d9018802c1d22040959411442c0c4004020f160f5000510035a01c1400100003070b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 134959586 1250 134958336 134958367
    0x6070c030f0f03030b01030501032a05150a08180d03050402190f140a05090103020114070b090105070f0e03210f0d02071e0c180b031b041b0804080a03141806060402 72
    0x120200210304c0c1c0c1d02f801c0402c4280395681596000303a90181c0d0484c4481400c410100092444070b64503600c1359000d580302000d40c4414079100c209812241c1c0031590b100c8030f0030301076841141c001e400102424040c40500c825a00502c1168205060800008800b000089044032000441c942c0032610404030500780400300d2520001480003904022400018800c441058021a82c220360801500d8003a03103803110f111406440280d81000000780c0e581c80700c0305c000e4400c0c01c0c2d6442d591030040152201c142c5011010702c0d40d14902c41c14401d0014204005c5018040b124010000da4245c1a00581c903480c00742031042014a01000440c0d91045403442d4500141514585d0f0081c2c64010042e0b0350f40145c2c10100100900d5034a82081e010305c100f08101c0c4000b40068030300003603040200c0b0700340701510280c1202043d0300c20f104041c002044204000c90009890900502000354031460005092042c1d022506000001a513894403108100911070300128014058141c0c001c9040d60b042d40b40403410381010300c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 134960836 1250 134959586 134959613
    0x10f0908060f0a0b0607030f09050109030f060b01140a0e0a08070806160201020d0609090b1f0b030c09040603080406080703020f180d060518010501090b0102060606070c030f0f03030b0103050103 85
    0x4800b03540c4070000342c2500c0141c0c4040c0d0350324005840140c4078852882d001d0200200300007111301041c3d280d20005620f40c0300f1410b00c000d40781d01c0320b000030141e402665880c3c09072912845142c18054084403480712007076001c001e00350b0750300d241d91011421107c550070701024200c80d401911981c0c002040034440b40314000741958101150600300300428507915812402030040081070b0011070f041c05000240c001440d0040001d0600a07660003010751110b42415881800e4014070741e40c0b90003215010009100c2c403002440c4c4c004801d01002d8034064040740010100c4241c1c3e042210400c2002c1424031059030301c01d154036445400c90408524180350042d048030907004000c400d0070505800c0030f10786456280d030240e155185611000c280143d040c26080c2040383d82c06141e21400079860b103000040c0400703ea00031740081c000180c0241245403a82424442954400303201542c0b140f00160300080040c0481d0741a02c0b40300d001305c0ca158010060f44c64000c1c00d8030120001107040504000050010581900c450352 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 134962086 1250 134960836 134960851
    0x90303070b0c070b0403030b0906030f0d180e010b04032d0f0501020d0c0e190e04060216080a08060a0519090c1427010206040c0509060a1205010605010f090806 70
    0x410540e03a182d4800710354800c070040200008145800d000401d9015082070034001c1c0100c0701540340d43d442e801415035030f44d40c4540520300341c0c0c000c260301c0c0302d41e50141c0341c038074038440407411032205240c2c440305001480c0c64280e00003200c0d07203000a820424400e0032825062070741060940c402c45e4059504800c00c20389400400035002c40039607244001001400d6040b90fa2818001105204000300342c030005d01a0003100d18120700410703200c610603450031086001e0350152070045a1014a98a40e030b22403400031b40100c0540d40421200d0310700400800c44040142460110329580c3c0c0d03031189490303014850b032034038280e0060740688428040c60030794184441071001a242080800250b4210301c80c0c003103961004001003045040c0d4000384030000c01034580240407020918080d9010030202200049030b590100b15009001c50700011000d11003450702c04a13140c0c115800820480c5120b454070710300040d5000c0503100b22410b070b554503010009560041040481380d401402c02d0001c182c42c3c0f00d00252034400040c4901e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 134963336 1250 134962086 134962103
    0x40929010b0d050c2a0705040606020304090504030c0212061e01030f0311010b1c0606060e0901030f0c0b0a17060103180605060409230c09041101050313140a0b09010209030307 77
    0x14107840c0300310162511503003041c1210210454001d540c00c1c000c5c2600d440c500c09409407040100301400c1070300071070089460b1a8015071416140c4015100117144c081c000b1000c00c8409152000584c0e00c880e0100000740c00c0d0f0000d0310841c24245024105101054408602c0095200040000c66440b00c800308401c0d805082040d051910340380510300610f00319054960000c0c842424201b00600449015030b081d01c42d10040000d607844080a41d007a040b1182c403160302c00905001440001c0751424030140d503502c5070140080c1d2a0b111039514908c0d8001008003030009499000c0404003030117100c1c1041c1c02c41030a08042011260903201d6035580c0107200390240030140c42e84081610b6454030707400701e02a190481c1415200007003400101d86440c0c0700020355403007485503070785040c41880d200031000e000d50f0307020340c1510340c1410303484c019180e54000034a94000300c00b070349445c000071940f50a00700e0011803030035015150303d6030381d46810100904041d004840c16881404028465100002211070298015289 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 134964586 1250 134963336 134963341
    0x10c0b160905270f04120c0528030e10053a0c12060803030a0908120a0605040f0b06030f10121209080a0b070503090c040929010b0d05 59
    0xc0d9401d9141da48440d40011090101a905030349540901ca41c42c1c010002402190f21803101006040c04e00f40c8000d03062a84900c0c1d82c12005004041815910303110390141c0d905031018000b82001d2044554401005003030a0040200b0141c0c807204a903050001100c81c441c103e4060703500240340303004a08442784544640503030070390050034000400c03403003900e4244080a02c9400368584030181114040d0310010071104418056158003a00801c1c040d1104407009505540e1180700744c4c406406003c00135650000104160101041034802840c4a015030303090208484d49060144812116a0191400e03110f2030301040747e2141d6109000c50750400c0e0071000e40180b03074442e0000c3c2c04010717000303a010b003842d4849900700800f0080b1081400b540c0454a4440c05d00450ba1508010f84a00c02900002d058240b04d00003e40c0e000e00a602554009600744c0455155446010108040300c0b007181c029100f071804000c40d2920381b403441c0d0700c0c4028440c140c050f00700305525041808029003e03541e8030141c0607480340c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 134965836 1250 134964586 134964631
    0x509060403020a0f1410021203040303060e070e130c050306060a020106120609020f150706050901180818010507020102074505010b090a0306090804050a0f08010b010c0b 74
    0x3640c0281d90000d01140080740d0343c0c0207000c01a02c040c8070b00092042c00c1084000c0606e08400d480506d511542c010344140c00b4401e0001940d030340010022005d15a581c80040341d82e43e1229100c0348a03a903a44c40d12000d1600b88020011206800080c1c0500b4a0801c01d60301c0a02e0341c010309494010781c00761174041d2124a04101a805050590803424a00b800801804144403c0380c00c0b65002c00d00070b4444640c954108814051007107500002c104400c0d800300f0244000802a90180e644403405100004400303080d1030342020b1f09003d00006842034030001c01c10a03640c01d88240421a64003090821a1420076180d00107515181c0f20301c0344a001102c420341d00350f550045007120704000c0c0705c400c1e44880c020031040d41d040c86202e034111500c40e4a40c609000450741c1d1000e01e080300c0404078010111985586141d07200c0c00030701091310040321002c071305120000c2d82d0b8980e544284040d080c0c04010800e070034107017400b140c05c4074004001035040080007500c040c0403d03d00030b80290040c01c0106019480d605038031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 134967086 1250 134965836 134965849
    0x1002090d0f060f1b11070e0402061303080301080f0f07030c150509041b02061315020a03060506070501060611070308070330020309010606090b19020f01020304060c0807020318010509 80
    0x81c00d007083c9a0500340b0b80e000320203420741a041d5100881d102e203009180c0303601880340d40c1c2c4054011038181d410501c1c01705015240500c023905d507460140d440c00f04242e4981c0d072010120740080e030040351550311110030040c0700401031124490100c0040014008079141d616003444038582403155a45404521340001350b02072280c01220240c5401420500c6a00c042280f412181548000003500600540300401d880104400314040c4803500302050381e1040b8a0500668001c0d4441c8440100703065440307800007000d4541c43e0150660070700410000400d2454010003030f10442074011004038603045040c003480001e514600396100542c0500d00f020041004e5007a945092010001c481400045650601844081c1e03400540c45042000700902c90107544110641d00001c180c040c420914009004109025040800040d40060584101c500c140c4034070003c0703400ca90094905891407510f4100100c04907410221075604061a44001c1d464400300500c1a00b034404071541c494104000000d8000303003a512031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 134968336 1250 134967086 134967101
    0x3090d060e100e160623090609090c0d1d03070b131e031202040303020709020904021303062a050901080402060903010e01052706040602160b0106030e1002090d0f06 72
    0x34030300f08840c03040310003a5603603010196120000d20f008540c0104425102e00c1002106004121030903400a401c0b00c4502c0f8181c00801013580c115000784040b18044e0b0360b683d0018050b401d12210b00d590f80840090302416560180e00d0b1319071100c160700364080100c40000494110a802850401180d210901d118080405020003e000c14000a04214a900210040e5805248641c546d110905448410242a40110b102c05000b40e00029800c1201e1119900106103811006100519010004940340c001e40c100c0d800c1074031001d6480c55440d441c040340b11010003414400c4507014989240c60b51000b002486903205e0300e410082c10802090071501d8903825288017110050013800710303590202005008000c1119000044506001500604500c01c1c3c201102e43e0b034a03501030500c40d41c0381e442c1c49010703500190001000a90036201d40c3c003c200c55000d100d010b0141030703901040d05280c0d0b00201d880c0001d480d021400c000d00c10000c0c44240e03942d070100100001c0e40700d0220104407c890070264001d1140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 134969586 1250 134968336 134968363
    0x3010e1902040b18120609070303030e19120306050402040e0c070302011b020f1902061207020f010606090503010b013002090a092c1e0c030d03150803090d060e 70
    0x410313070340c61003803181c4604030100d80d0a951107110250b40505083d6a80ca098640341a907410000c000d0020070b1007070300501c1a1665103022a06010a04908480c200d5800700007680d500051030110001d407503050040301d004100c00c07602942854208544090701180103090403451540000303000781054000e4101c41c070500c09414201080141c0908041e4a032004007000c0300c424000c2219450320b04020310b1051240b150064001350409070a084454030103031001e092901584036000542070108024025280134020b030380d55040380030389803100b0b060135a641012098103000080d1401041c1050528035001940d103444103081545000038544002407140c032140c103402180030003020405101c290001c240c0f40f070070405000a20107012032410610060305040c0340158111005c0080c0d22451101c1c88800c001c8014141c44004860304000307032501a26501041c00b107625064100d000002c003003140401001e84501545c03603c441000040c00004109500400b4650b4505000e120702c0810005054406032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 134970836 1250 134969586 134969609
    0xc01031d12090406060503010e040b07020703210807030e2802040608030318030309060105010807200c090108010603030203090907140c0109060f0b01020a030f02010e0106090203090c0603010e190204 87
    0x1a000300707521a030000346280d001c1c3e4108000080c10b01e1180b4100c1e41220498403d41d5521b440320359a41504540140c41c0e04118403600c00048040317001420162101403803507940f0001d03d640494003070000c41c0010a041d06040c90401c0b203c0707000c540803030050710f00c03c4107d960100c2e0107903060254240c0c012200020390072501d030240224091500000650246d80d916910140e40c4000b102d02d50341d82e110031100001d00750455001000f180d400b07105400d40000722400c04480812600341d01000c00004440b085050750300801c8c04645c1401e000c04042e004d000000020322081d425a18040d42c0c0f81f20340c0d013010380164804800075100314070805021030040b140111703032941c4989100c401406406900c9056548500c0d12003040314002a520401f944604103030003400c40c000c01c5480654850052801020565480e0000301441700028030600f40a420495401604da003005544546071400d5100c0150248208100500135016a01c0d04030703500c1500382210001d100700c81c1003404040c0c010307a841490f5541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 134972086 1250 134970836 134970853
    0xb0711030a020a140304180c02030f0d0906050c0c151012030c03020c04090b010308280918090b06190e040309050f0405040b070e040b09070c0b0a0e0c01031d 69
    0x1c2e40070840507001d90292115070108019110a682c41c1c0c0b040d417241e82078086031002041c1006026400c003021044481c0140e9081100300a051101c59001348102c059a81d918010031007002800d1060f00c0e000030f80c0c5d5a0380c03030400112100e25a41e60f6903a603d1070003a500d05000007071944045458420203410460800c5149030503600e0041c000c1060f0000c00c50160003000c0c540c03081c506080c030030a07618075000000c84180743d00c0c54a490460354862a1607400085400301680303100f1050b602340101c414640e07510b044041d45000341c0c42c0108000140240c07202418903440b900031403010208141c102c03604542429034030b013104a8403a03c4219076440240528420ba0401c400c0c103270428940c1085580590360002118003440c1000101c1e0000c0310000c04150b0100003140159210303000b410164140a880024000c01400000d0601c880072030720384002914000d40354003006405208550007000d615418498500c0140e001529500c486d1034131410580c0d03070100c8610154126070018524507500003943c0030351 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 134973336 1250 134972086 134972107
    0x10e0301110d140a0c050403021012140105030f1219020f0f07050a05193006050a1b0c030503072a0c170a0602180303040e071d09040b071103 62
    0x2d11030340800f0010301410900290503156180500608410680e0314145000d081d5800c204429543c1100d800400505d89030f405044640d9214500c009a06000f80c00119854841014a0549840c1d04000960010201c001c0126888015144d51100220f14400c0105022004a1070900303504c040b2691482803402d01800c1c28008241300c2c00b03035841602c079008142e444a041c4100206407008115007156240700030481c40c0d41e601c0c0d08081c00c008642c07071001e868400e034050705202a0551020f0354103d075508107201c4c2c600154802d1001c0c00c080c503d03900c04000340255001e00800007480014051000000008110a1090300044021100b01a07882195004800c2c0c480031000114011142c80721a5003001c92900b11024103400c2c40300d1640020100d80403140d59040180d00684411a007140480118136021303a8180081d0010307003460b8100503c1d03858507440052215124240d1200c0700c103800110701c40c094580c086419449a02f04008019a0700c038000c0442d200c03046c0030a0107e00340404073320000603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 134974586 1250 134973336 134973341
    0x7050d0509030105010f0302030d080a0b1003020d061a0703050715051e0606040f0911070807030804061404021503040302070302150c011a0108040314070611190e010806010e0301110d 80
    0x400b68004c025580e29440c00e006062210300002c1c0d07050b0300c6100079481551042c66100e50100c0e00030400715080600801050b03910f07903140c0c030a01c042a004a40504007148520881005003515900710706c180744400110400c607ca5a603015003000000100d900500441c4a203205d00034400d150208101d03d0109071030001d0b00070720790182d9051440607011550510381030f0143c8094485410403070014502e4000d0141c0101664203600540d1071041c0001d83c0070843c4880a00821406038a50f4134442ca810f203060022284c10300d0004010140070403d0002607207444140c00340464414200950703d8446040603480c01146500c0250b000070404107410525034400054802e412000f40240106000318158280c084482503250340020100000600403904c40c025009824488540381443c000198450005590200561071000203000030320f12045100c02c00c00c44100c1896103440031142180400090003050003914050400190742410b00d0710769020342c0035050400340013140c40d54920340041210301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 134975836 1250 134974586 134974597
    0xe040b0403020c0d0308060d03170a02121b040308092101020901020f01060311010e0604030510020a0f0201050f040b0603010b0a03060f05130c050103050709080d02070311010201091a0402030307050d05 88
    0x14024411500f02c9400d210740340501e0a03900d81c072a52400ea41e0001840000f42241c00b06030b00300140705d402c5078000700800441a001c1e41c1d05650240c0d5425641c45800044200908a44415100b004c4403c1800040600381c4c1c00b0f69520080742a52008160000b4040305101c0406a01520b0444030001d03490748154001c24078100c003070f0296542c21802c10441401c03100c03940710141060590341b12101d503540c4500490514980700421b607505143c0c0386c0c0c44251030540e860207204000d5500003030000c0c8041e0010921490034520340f00078045458604003000e034220300074000411401820000c526195004c0d0466400c222014084580d81540c034100f500150042c20b032981800c03480c0c58042080310650100b41b5101581003140007000b140b908004400030007009050b4401c20880c1540854158014000f54042042c264000d141a50035410550180c0c1e040c81d1411341560701d861040300020310f00c50a00c42800d011070192061b03960303450020904510401354020410701480c160a2162908040540b5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 134977086 1250 134975836 134975843
    0x81902010f17040f02030319080106140406120905030c01021303110409170304020607060c051c060510030b06040b03040b10050103020f0910171303020f070f050108040602040e040b04 80
    0x10711410103810292018503090340900b0005602c1c40c0000c0c0812542242030b04000d1010302100e260099040f551900e1124505405001074120307001003140d0369104950b848540014800c1c070b49864a0304402402c0c04681500c00d40e180c41e1075652420910400340309480a00031614029980d880c880c00c00d5603009001c9001c211818245480c002d03101d800c0c18441c8050b8168404806591541004000301d4070f50001441264410801c0000d400054000d00a0700444002074403115200d40800e07818803901008030310800821454240104050b954140d8142c00030051801c001849290b4000030640034403c0d0303000110300050000510003008100c40d4864410b4490245c201049a200c80c011030603481110359001030000b09004103009480c00f140400c0f900b40719410304008508510101088003e07040700c04611054a0000312802e25130103009401d008004200900101403d0501c00a0b1a8120b405601d0400003034070b0008042080c0741e030454026010400005d0355500c0d0610706000c1d442811502203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 134978336 1250 134977086 134977097
    0x1407031704050319080301380705011a22110a080610030513110d020d050d02010e06011805040c23100f140c10020f0304030215191508190201 62
    0x20782c0034010131807201c05040c2d07110348035501c1c5901c0d004c482c6440390881e5000c80050001e0480c0d0641c3c1d80c1401c0715100402c01d200344070030748404160821a00311a0a1031354840c1c0c030300380300b0b400c01c01e180e840d00c0802200e0401c1c400b480403c0c0400022010042c0307940c41e0706c249040c50026a081c1e00e25000028107100b00001c5911400a49080d0003c909661040d240699a10203409040c00004e03d07611848119400180038901041d96540000305007800d401407d8806800c81000180389a5081c010040c224031150300a11041d4507001d054506000c040801085150342c0380c004c01c0030455580e00d08001042c41c0d0b4110141401e80e100d0581c400c0b01c0c07e4036090311802010b82e0034210a40942c009040c0f103061171300c0d0182c0c1d05420039411007e43e4481804e600d894002c0204c00c800390641440900027840c0100c7c4815101d103000e1070082e14180f0503512056856a12604000451081c85a0000485841240401c0180112941a825110301d42100c1c82c03d00664558150019400e171070011103d000f680e92 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 134979586 1250 134978336 134978353
    0x509180615070c05011d040c0306030b15030c0f0627180105131d01020a120c0207030b0408220603020307020111040b04030b040c090e030703030605010e060714070317040503 76
    0x81d026140714000b4010020658500208450360049204540b50a00588421141c401c6140001e048030b03620a0502c01203a0ba4210600074060015120360f8007002c00002c41e4800c0c548000002da94440313000c0310500c610f04c0405e8605003501d511069451160b07540700041030421100840c5e0b00c0c60b00c13030344140a0094220030000001103028010180c120781d0003034401100196030883c401c000d4581c200c212a0746070804084106c500500348010480c50309180c0d1000e0f03800180e0b40380441640d81c010b062000f19070041c1001c2c0080703841c8243c203a8210394003440f070341d40c0c0d4842c03085ca20607581004004039640c65401e600020300650150000c600ca103c0c950300800600840f100046882e0050b0301a0000c2d0031801d03c010b2000a03560b01c2c03070719007060140541540b695500d90803032040c0d903450006050030b80c0001c1402c0d01050741500070000500024244603150100d0340c00819214010740c50081e002d500c000702e80701d1000c0d0307003072007100d014540184407840d00c01c2c008a010b4000b030b80544500d80c000d1150121 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 134980836 1250 134979586 134979619
    0xe030c1e0601030f03111f0207020109050303030c03180a0203340b04091d060a0c020d030506090a0c1101050408040515040e0a02030601050408160609050d1104050705091806 76
    0x180c0e02d0690f540808101200b070095142106c0301c1020070010619841010319810068003030400340c40502107074206c0544c0d1500c00f071000609140361a40309501a51042c414040303440a00410303030390300c000030740715064420200c03810300d903c0c01c40d080c00040c1d0940200d00440004200001041500710100095615451809a8404204591413155000c00f11061006106c014000c0d04104110460b5078054602195884001406c000c400c5d902c00c0b03400d903901d203201c40c0100d4052125a403682301c1030900301300519020303021400414004210301701c96507131000358101160151883d504000e14510080100f0710707103441c0c6009a50701500542e4410072070070391a01d6000c0c0e010800c59041d503038200c68244498032780d81242c5000e9040a450b19041c0541130002186030070b010000d00c00518542c02900d240e042c900b8070041c00c440620381210b40111020300c102c1000c02c0c0c140510403503912003503400142647e0344103411200da0040000e11036102c0038445e107d002804058032040c0c000c0c502220402005200e030700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 134982086 1250 134980836 134980843
    0xf0d050417070f0201030f0906050f06030d090608280f0501080712020609040c1e0503011d01060c0f03020106050d080306090f040c120c0f06050a020d050f040b07060e030c1e 76
    0x344001e211108241c1003c0055100350403107000c5131541e14010801d0f00c17050395a403050b10000c44820034111690400c00186186c01c0100c0030901c0d400342002d2200c0c605040e0000c1480c18014040003010f0032501c082c1c22000b9003121200300c4034245050800c903495410503690003400081c170460758144140c076400300714020780341d00c180c10840e070051486252201050a005c05401d104d803031003080c8070344188059031024813a0300300c0d00984010740e00c07107a90b98106200074603081c0304500003005407002c4000500c00741d5008200044c060b600a101e031a111142854100d000d0040c6400558001080091240c10003101c00041d50040030100c1e8640c0c6507507602c4103d0311000780c1c00c40d00501910301781c1a04002c107901b02d682c4010700728042c2407105c0b2015101c0711240301e0340d03200382c1c002d200240001900d4800c103541400341c000207102c04c4c905149084540150410907010328095281c219500140884c02c0080e5540058404d004910070749441e82d01c0720a0590300c07107220741c00102b01d45c1e0340e0020007240e0f0040030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 134983336 1250 134982086 134982097
    0x20a090e0c010809030403020307060f08070216290c010b270103080d021e12060d15020d06080f060f0a051e0702151501110303040b070809030f0d050417 67
    0x200a086034101e00c801101c801d040075003005854002040003101507201400800040d01240d10fa03145008800038004141c039100500000864001c1c100920311025030840060854a400b82d400558115032240ea0301e0340d150701d651400a030080060b500c85403000642141241080c03c507007145045440706004030705170394110101a4402c808000520000d07488002604d03048a0700980103003000000780302c03442c840306400c0d5540302801c40400c5440005440164699001d041914449944202c07035450445d2800703c3c801041c6003035004203070031000841c1a80f0000041048000701c1d102a0040111580c0300c05055030403240384d44105000031610035503402668090341000c0c034558110010501009000c030350150540d4114010321040c46541c1c0042c044080c06148030200703080c21105880d00140c5a0305140c00c0841c0c55405c14020030012801c5544ca03168002340345d09100314299240c0e11101c1c15032103001454540b0b9a004980010340c040c89902c040d00c08c40c407440c0d20ba00600c07031040c101c0350f090280 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 134984586 1250 134983336 134983361
    0x30106140a0605070f05010911040f0c120f0e0a0c0303030b01052b020405221a0307030b1b0c060610110606010f05040f09090b10050108221a04020a09 66
    0x40300c00c100302c0c981c4540004c18506000307000c0b19280410580e5420300f950b8031020700745c03044c2800002004003803900307110724550b00f005001d003001000d6000c480504403565140d82032980a43c1c0b4001090220490303000003000200d4441503034000d4a283c070f0003004207007840c0810b03000645024071000c620b5000d02d0454400e0120365120030580300320300c000b004450801c440c0e9400c0941e000d000002c1d142d221f80c808181c481c00e00300341d400d020803519881c1ea000c071500c1c50249000c42c5110a001e000c9078402041c0c01c4141c0360840781c0d0800c20394079220801c03080448440311403032401002508001c00c0001090b61401035030115244000e21214100407100e43d17180203d441601c2e08000081103540d1f0180629541c1011035041841c141a0b82d4110018a60300e152701c00c1c03403415111002d072400c00c00e075140b045500c0241c01c5210b1510900780f5000802012006103c240344111151a0707040c4564151011500309602c9040602900403011f035207242c03905c06590407801400c040c0004500340d50580142000307002c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 134985836 1250 134984586 134984599
    0xf030b1906031a040c02030d0915020c030a1107051e151b0c0102210c0705060a11190b0403081e01060917060403140706060305010c031517060c09120d080603010614 72
    0xb50481080127051412040381c210740d4103103948880e0141170024118525914000e10780320600d101c0c003d04841282e28070144140c0007904144226601c90100d144030900624408011040000225040b00c0c014001c0500108010a00c0007a10300c0f22581e500151240e40140c40b90494a0001640c2d50203118450300d03402070303c0a001002d248070100160007222a0701046803800380e540d8000c40ca0690004100c3c50008524441c0c00320000fa01b00001642008654040f015609850b01d030f0304148000074000408010174480494281030380407208142c10f4031210a8a00d480d41e441034041c0030000310340b10700c244448586200c18103c1c00c2c04500540316640644810703805918400c40d00c80c007503115031700880d01a50f4513400031010640034480d40700400000d8500180303144c1c0900404009066030390010103490318800740c4290003200030400980100c2e0640702c00d031f00c5034035a40008030b03154281c03000311001d4030460121390100c5502800050141400381e000700103032a11590f0750b58200300c490340c4440d046031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 134987086 1250 134985836 134985847
    0x607140f1c0f021501030b2208040501080408040b0f0304020f010305040f03030b030f1f0501051c02010c021c03090302012a1205070c090204030c0906060f030b1906031a040c0203 78
    0x14020b000d1003403060b001c3c1c4161220301503003030240b00c8104801e800644441201d0020054908054108040081e0b43c00c0243c0940d200345603114407d81c880d03400343d10b0400014802140c1003080180c140c03806801d80240d02c0d034940d074445000041e0f9400885081e4414501080c8500c0d15500a205490140740c0045a0240160300c03910280c6c00340c0107418401d6050b01c207045407101840c4051000070b000d2890219403030740c054403014600d003d88006030031007031080080000c090000e500e0b1460540d0615828200092000010300000e0b000040d2000003035101d01040502904156105045009480c800d8072041c0d41150321200840b2841071445003090101d40042c076210214240e0130326021070100510f2300713a00c0c3c0852540d4880500446510040c81c40e600402d0500401007012220406041058001c0010303d14201c0000e10f41c0315500285001e259441c04010302c561241100002150030a0102c0c41d812591500024001d0000c15070400b1607400c07001441d10203140a00405000302c00642c011400c09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 134988336 1250 134987086 134987143
    0x50906040b06090d0308010311060c03030a0f090204020f09090c03060d030806030f010e1606022a01021006150306050402030c03010e09030c1209010f020c0319060b0607140f 76
    0x1d224800c01258410024042d41038207546104042005034426900d80909525600c0d000f0220441059910300c00c00b801e0003041504000003003583da20400142d00400c82d0200e00100384010070b642840603401c40e00000302028001710200082c03244c04401e0300d10301c0460790340d81c3d6800c1c1a0702080d204107511a00c0c002016001c40c1c4110a2650400e13401800c2d1012000c03c04c50860071101c07602c2d4141e950345c101d810401d00122280c1d440c00000c20030f600281c0552824007d02d9031004035002184624110310302404144c9900c200404080005a8101004040c0d111041c419103010080090f100290404070042202d0800d8000e0364025030303404410500b5642040200c0840400042425450344000e1002041e01107041281c0c00c54006032504050387c6503480c0703000410b81401c0c034000c6000d542c45020700c10100d403400203c0707240c03a0f540c507a61402c100c00c00d4a040005000c0c002a49544084045080781c20b122102d2038107003800e2085411101c031070040c6072242d5220012036140b003d6103180e034540c10114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 134989586 1250 134988336 134988341
    0x30b240409150609050402012003090d110904050106091d0a062f040e0702060702070b03060105040b131418070c060902040f0507080117030304120e030a0809040b090105090604 77
    0x45100d610b001d05450425180b07602250099403041030f015031107106000a65030400010060044014049280040200c000b03c0d44d92241c4044c607070041c103100080304140b1003041e402010388100241507000c50300341424918007a1000b4050114000d01c3d10f08190206a5010f044459003488a8007401d0041d50649400f0700504400461281002280144900d01d1056128000e419400b1804081d01d40342070103400454180010b00c62000d542c001810321925036000034480040303402ca0750352640c0d60358032580101c90b580030b40c2d486402c14081c00f00e17a2002075040301c1044000e0340d00c440303da5208000240c3c208141200c8807446008500c8400c00841d5070a0300c542d080355052402400045031a0070345602281c00c481880301034013a07103a0384a0501c03038440d500007422401000c810941e243c50341e86541482c1e840344400741c1300070303d895130b05da1681c8400d03801810503020900c80141541e0744020a414080c6c2c4c140d00000f1120b1140c1d2030b10400e03400078503203410041d0503503a01030105c10080d0307110004c0c07100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 134990836 1250 134989586 134989601
    0xa06050705150a02070c03080406080a0509031605030c1504150c12020903150a090606080106080c1908060405060a050906100b16050d030b0405090d0503130309120c030b2404 76
    0x5843d03400300320400c0414200c104190007940304400c0340b582c80d480c01c00300400e03841000d884031250b1820201406411800081668601d040e0b0321804010044949041d0349140b10354054092280152410f40c000340200c0440c50344990b001d0780e1000b2461226010f110100c41032420034101007510140e01c0101c491055000d4400d07600c020b011101c00b0701d280f813912200303034804580d000c0c2d80c6a15481000d0400003d40100f00060603003100903c4035604209201e078407848041401406191940c8104620031604900a402802ea440c2a00e40c5030400c0d04185458040440e500340406081101181900340c00043c014404c078031005090700740c0c43c00d140e100011503001c0034002d500d1b10b00156940000c43e201740491094401c00e80c03400034882c1b5041c001d200a0311001013400318560060011512000d4202c803c5945c0458140b180c011100340310300d82030342e4002e420380040e0140603403003451038104100188010242c030300a10010350030303988190320400c207040c0261003860b0f0000d15413000f03041820180c10500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 134992086 1250 134990836 134990851
    0x140a2306060307180e04140d0201060320060715050108120901170406090b07080604060503150f0c0d0203040813050306090703020120030c0703030e01050406081b070605040b060a0605070515 83
    0x69813a03501c0c0a424000c44058078256180300c41c45190180d03900d010401001c01081d180020f02c80645161115221005400072065400214a00c1c480e190360710a8102d4255030340c400500c01032070042c0e00079003005010034000c100c1c191207404c0c0f4200700c81e6201c00a40341614016521202c855041030b2400484c08009081218980c0e110402840000c541d406598424191556040202d2600004101c16607820343d001c0340c02038100c00504c032a041503070001150f102000c84c038017401c1c544074807480411070301c40c0c00f044540340c610100912007040688002040c18415609001441e43d44480806494100c26a01c2e500170740d001c044100300550041c0140640034215a80b14009845105081e03401e56008105145264204100500405030010060001c0d45420b280040c245402d040025045410207009840008014104c09a1040080007103c010310341c449410f01c010b051501e01a00c90b84403c2e984a40700710a0a4030216a56104009071800a03400c0401041c141c004203141e80e4041c2d0f001703009075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 134993336 1250 134992086 134992127
    0x51504050409060f020c160f030302060604020c0304080a050c190821040f0f08100204080604031202130303050909070f0c031b05070305030c06010f0315020d140a2306060307 76
    0x2900046079480500300f07482007100a002c912070f00203090366210342c7d29007007030100481402c012700200b580050300740d50080c4240c60040e500d80e2550f4a19141d0700a40c2e21802881c420802c3c804100440030844141004017a00c4028088100c2d503980c0303aa440ca00d01172001d103540403540395804542c5e40d074030702140c140200c402d45203000d0329109004004d020b01d400030b2244030400e01c001c0100c0070b4100140c954907110300d40c0450406040842c41c030b480ba400600044c01300101290240d440b07018650482e008000a02d059481050381d900d0b000e08107410031b006ca144142d11010009041500880c554502e0401c00d50381d482c146840b6550984001c02e4410f1400e5200358005420380000304100a40d0340510b0080700115228940829941e1030490305800103d07010740341000801c0051a42148e50421040e08076002d40c444041e00349540040981018061620462009001d10301b49146d000881c0d10b40c0c201d009106d0f4210702c6041c5855284240c400c580c218a08000103040d1912800c0c51801e140015841d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 134994586 1250 134993336 134993351
    0x40b0a0e0709030b0603190b04080d050a0902100f0207060c050304080a0b0f070e151c0f0e010c031514060c01020c1018030801090506030f0a0c0303030605150405040906 74
    0x24040d14100454040c000304400e10000e10501401c2165181c1c0480308500604000150041c1100784032640c100042c102c10201002c9000c0211550035940b80e00c0b0303404001c2145161095490025000101090b4000c0300c0c0e0f181141c0b5024400c0741c6800410403203400410006250800444030340340026800c1d901c9010501c00030441c0c820600080000c140520399a804a0520f085441058800a0000b00501a0003200c010007620b0380d20a00c240c600e1514003080e00c45203400c070102e000300650394800c42c140c0d00e0601c0c1030380689090340c021181030080344020090b034042802c2c00c0c0c0885070140500b40c82144d080d0400c21000f48680c1154130881005000c913810400c0a507001400d98000350741490303c50300110304881d407504851003989900c80c0d8800d00000c18041c540c03000b401c0e4030010301540591326103e10004100fa24100059000241e00c01c1c12980d90140900340082d04a44a01046002a0a200b0002041c1c03a02c0c03c81c0b000340c007404500d41e40c80c140c076010400c0018512803d0403240700f503c0780d91 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 134995836 1250 134994586 134994599
    0x5180907170c120709060b1206190e0405060a060603020a050f070606050303040608220b2419031b050102100b1801030807060c0305070509120705150a11031206040b0a 73
    0x1045503030001000140130950804200c44e0544601d41c100c82c480840034000010011307914080301c1d401031802c0c0c4401e052066035030601417000744250022a022200b030000d000421000040c0c2e24414142081c0802c1003a48601003101a8410f65a0b2400000d1041c044a412503260304000c0074607500c10f450000303030207a07500c01090840d0801d521003004605103004000100c840e1a010388a5004007109034040307000c1303603601c1a0b0b01c8030000d402c41c2d4002140060f81e024944648004403c4607800400340d042060352000d03a40013410707035800100e41e40098544000c100103d400940c0301a030345c050700074117840f152a9800034001c280c0402503d03403080d08408204241c80507000c3c218003840c080c8481c260f5800150400f003080e10a035040c071404251403e03080207405a4420159a003a00d022102d2920201c50100351515000081d0010b95024180c41c16000d696207030100101402200780e1a01407140455002c4207890f0300440d8001e8821000b00400111546403551007124491b0006100400082d112513 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 134997086 1250 134995836 134995849
    0x70311130e061911070602071b08010209030723011d0411040503060906040816050a1505102103030b2e02100905070302010c080d0f050105180907170c 66
    0x11900c4400e42c202a00303000f0b41007080d03400b1152109072448140070403543c40341130781c00d07910542601415256020a0b12000c2240c3c41950100c4607040803485905981c80700500350003580030255091180c4601180068650261609003044101045040700902225801913856045050b24401e1080c0c2d02c1071070888981d986c0c4a050b00020509118a40b46c6d410042850329011016150342c1481c1d0110080200081c103401c210341d04185240c00d0511440307100d1402e40e20b05180343d1401050034030701c0f54a0987c10006a48207610824030648100781e007a582b0004580500c0c3c04c01101180c010082800d04003081c0a41c0040c4990702c000b42043c4500303002c03c9420120342c480c6417a036560708914a0030609540341d040141d5201d01e604524100921100bc0d40e520f42e603148503100007414402010001c20902025006071045108031789030600902c0d0300503150360003c15090042ca8450b00403602c00b4080c2131000f500c0148a0890380c0c0081c07040608050420010400d48045c6030300d68810054895131949415 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 134998336 1250 134997086 134997101
    0x190f060606051e27030708010f2007110603070e090a090302010b060a0504171509070e1503030a11030412110a090b0d030815040908030f1807031113 65
    0x35076409480d005070035001202c00c10712003026010b10070706000900030242004c002482d80b0ba1100b0b082d603980400140440d0902c800e66201d45e43e1355182211000610300d072034025128100b940254081030340006040d0f07079002d000c0c1d107070003400440030a1010f1054bc1030620003560001d00714140280401c8141001510410003100d10100d15516803149004060702401040c0d84144111861800c1072201e01004006011314480e844c2e05c025138994401c20800180700ca0780c5d0031400b650740b00b1811300e051501641d039001d186c443c602c000030310800054100d441d441d010030040d801c001c01952500f4402d56040f20345034100032001c0e071507000400000550583d00160691070303520076901030402e0050b00041245403030155104038215420400d00215035960004020402a454141541161034500301c2c89610745444c18229009850402e81d40140000b000142d0311540406444034019502c0c00c41220541200008030080c40d848001d042c40014048880030820300360140c241602003045450301411b44405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 134999586 1250 134998336 134998349
    0xd020406090e07060806011403180303011502060f22020f10020a020306010b0403050703200a14040f06050a0b0703020f19020a0f0b0a050c0f060109020301090608070305190f0606 78
    0xb00d12030321405040c140103400c001c142c1130900881e42d25119001811100c50150001e2407094004000346030060080c038140070080882003242c1e00d030760f110f050280c2e98120684416016100d40740004d43c1002c040e00c0d03598400c02c524081aa80b14800c48060900001c00400482e40401c103007030703c0c0d40075807a100d0b202110740ca00340c3c0c01090038501c103005260601c40d0680010902c400200010300204000280d01e604982d40a0f911545c6c0b800026901c03110b0300074032400540d03c402281400a40c41c0c0f0078410001d8640000c40e01004001e07c2e4168030812034006110b20354119208000030030018500c14007416074640280103541800c00e01018440c1448104220120710000c030800d140113505200d900c40340600314007204c08000600f0b01e44026000c0c09400890010800000381010341c0c40410b01155401d50400011640c0344d50f1610403143c0a50003d0090084130b6140c0440050307880000a0f03541d080f20741000c090a45030031004801c00d91803121030701c1560091070040344200061101e10404000b00344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 135000836 1250 134999586 134999591
    0x1e01140d12051903020d0b06030411060901021504080307030b04050402100e0f130204090501080303100909080c01091103120f0d0b060702060d02040302090a0b090f0603160801090c080f0d030b0d02040609 89
    0x6c030f403129101160a040c20460045905004120018203100107240c8000b808032401c0da00c42404d072004038604400c0032109500e0002030000e000c10410700101540c018401030710b090000500910900080b980221406540045c0700381c1c400711101d0003106029036260029202d07000700300104002c901c104201059100c4e460384d0000b401c003d030343c920f403145c10701424603030002d1840d504044107810507807881401146451079035000c00ba030421201004480a1985020080c40038074441e04048039030b04400c010003402405803080700341a191210046036034081600001504244280d100d100040285124040c2c1050f4108183c1c40540d80e1940a4103210b81c201e107000d030707660b404e42c03051040502018003d04002400c1c4231280c1850303130340c1840395644041403c402c0c0c0c42a50303400700000e141500110300d41d201405000b0000c241504103401c40000203003e8942d244000342c0c5c3e107c42c141c1d00d1840300149100c43e00004100241148290418562994000d1203201c1c0c0d04c80341d030006001c58420f0740c4061400b65 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 135002086 1250 135000836 135000847
    0x20f07051c0c08040b0f041809030305060105040617100302040914120403020a061101110309010606020f030c0d120e0d0c0b0609091f0e061e01140d1205190302 70
    0x440194101ca000c203142d150a000c0705a80d9640c18140d07004034064040002ca0200d11510f0258034441601c00400000c40110841201d01071500700401c1d442074144c000078200030009103c0d50207901201c00310785450b80d40340c1481b40360750704401c84010060104501040409800800344e511400380c0092240180090752400901c50422460a407008003070100d1504203200810250740c1c1c1000034000c80b441814214458490700440034010444c6d4042d500e420900070007408200081503011006491064007140c01e502c8450710320075038a002d0304400790304581c00003000d038041d240314042d40d2030038201c2000081050041c0902150810030150340ca40c001030206030f84e0105000c2140d0710140c100c5010b41d801c0b205428900c02c0c581e10f500c281c94415200d044200361341000008140c1c4117a07102c0c0351001c29901e550501810040c440b500c5100b8880001c910000040f0b003860180c0c20703050401c00c000740000102206591200700d41c061040b84002404014400792a10700046101082200826a030060740c44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 135003336 1250 135002086 135002113
    0xa03050f01080109080702040f0902090c0c010c0e06040504090212010219080a0b01081618120201030e150f0a110c010b190506030604020304050c060f0c06060103090809090a020f0705 80
    0x2803005901c40411603041c4001440456030600884003056015240070401c20080d403c00e10140c45280002904141c508080250020800b006040350f0780203a0002d001c207008001c8100d030b21194088a15902c00402c100400035850b0035444029224405440b43c8100310310b4149280c2260030109030405c01128103460704455030742c004000365104c0300111007080420304a2000810f2054020081c5140d03004103a0919006409105213441007400d2100c10350000e40c4650303032200a006241c6040340401c0c140340035903641003c007186024844180c0000f81d441948d8510150400d9103024003868003842d90740d481060a801e03114000c08883e2140d02c00440c0220b444014040c01100240d2000301440d01d03d0b5051002d0f5807480f04032508114211005a16511030382882070800d8480074005511107000500021003515a90282412405013000d0b10f40d640d0710000190182d40107038800604160041040d42c0c1d00746000d008154100050060040c00c20b1b0f241c0d29480c0f83c690040d00e099521341e01c58454040700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 135004586 1250 135003336 135003361
    0x60b09010e070f0f0e040204060c0203120c1915090b1e101e080102070308100801060b030c070c090e0708061501050405130b090703020304060c0c350a0305 68
    0x5001c0640c0c00e901500d001e0100a002c1e044080c00841042488102c500415114076140001c805000b07004550b20b5a1f102c101a020100710310b4100d019019440038141040d22100039640d444039001c01a05035200c01c0401c007140140078000c12a5607413102d100b40402007000e0310a46410910540030f8500509111403000c50340182400c03508041d030324240030003140d601c8200c1c141084486503050704c1c0004104561100503000175410801040d8404580e036014154403e0040780a403201707440700122a510ba5001e10700b82d42080c042e440030b000040002c070b229664070034003d101050054100710003c41d16041410151044150340c00019400a0400c0c0500740c020320003640c100710406510130040305501d001074100e0040e803044a00c60741c1c000801c41a180c0b40354001c902c0840000303100604a190100c0d01400a4205a80917111203181c894080302c014010320300d000701e240d007010074401400703204002501525401045502020305484032200c2d00007440c4050080e001013601c1c0824549800c3c68070116 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 135005836 1250 135004586 135004589
    0x1215080f010504080a1b14070e100501021f0f05070306060e030c09010501110a080c070f120b0105040e030c030408100c08010605030a2a120c050a1d120a060b0901 71
    0x209034075000902001400725000c881c070311440d41c10403a5081c820b05540d03017013407112000d019100c02e480c7c2c0c4022186681c00301c2c5000c2905c2c001904400039480316100c104002070315004240c0943c0c02031580104994544251100d01c0e42480c0c00428650703040441e000c15a1020350702e820101e600c0f0101440100c0e000031001181d6142034009043c401350a90000310604030601c9118148942014a01442481404020032603904807096036600e40400f00c20f1642c550640c41400c0700c40c103911002066075031007002206051078010b0b90203102c690806081000a050034911765801e84000c203c0c0d05070844051028000919402d1b02400c202152100004145e90a054007441041340610050000b03940000503290403080490300003a10a8a007002c050400f040028036103030b0900580d811448c8150300c2800b01d107a1812020081c04090045c2105490034090305a0000102d010b8103c81c103a0360403119003116424a0003082c52a0824041200310b041a40b00001a00c8030b13a00d5400890749802c00741101030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 135007086 1250 135005836 135005863
    0x20a0210061707090506011403010e070801090e06070f02160305070f0f05130506010203040f0b0306031b03031602040902090f040c080a031b060905060108070317091807121508 77
    0x40007502d1041c100c0c2c0e1560b642d8020740104560b2030011a0301a4072071f01110b21955001c040950380c9585030304d28102c01d42c504540c0790001860b510700120740e4801074000c66451000c5400103008641f0b0b5900c0580318100b48441036801c51048000416441041c0411800214042d9000e060031a0512090044020580d040032a00d01c00c0e81c0c0d0200802c0c0c0b10206285010710b10f9560004480d1107102c0101c0c03d41c070035540440b056400c040b1000c07402c3d1905100950050900302c045800500010340103029500090b1040c40d80743c0c0050203280f002c034451680f20850075100401c00548182c40e680001d20f140011f440e462503401e55101080200404180e503480a0680c0c00014210310701156402020902e110760903031410b001b503010010402c1036903045803840940c410141c401d95030311000c280707907a01550701c0188c03a5400010342c0041c610007420101c614030513018200548448071002c140700d2030003018010a0412458220741080040244651094192400302071690a480e103a66645080c084c40c4905 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 135008336 1250 135007086 135007109
    0x50111010c0207060c03051c021207020a031e052205010f0804050d0c08090a0e07030f0b09010b030c041208120105090f0105040b01090905040f03110f070308030c0706020a021006 78
    0x111505030001860001c40d0710515000705c0c05030b8980360444813801060540d100145c1c0b003158049503003900f030300a400c214954060181c0c03207503038520040740d588901c601c014000c2140c280c00e450190710a02d1021008540500309a071415480e10b2144808880d94504d801c040041c2d040c0078002980c0c8400d10802d03890092425020900701500d0b429240c2d00d0045550040c07086402d91041000321003001d441f8491001131590b5902d907604c86a01034180c408031004e0002074a401054030b64440107210701d401001e0040c00c000c03403076030a00d01c200b50b03d0f61000d0001303040e1248c14040021115031305040c141c4030512641e02c0c40d48a0555841c03040c8011700681250384907880d84010041004002110302e4110b80c400c60380492013883e6880180d601a12582024000504100410050090550010781e080d482a43c1d91040086100721507900d616440e8012059030700405001c2000c030389964003558100841490180c0792852a075a20002c0360f000c5d00b016000368201e04105144038403e413180350700030454540720 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 135009586 1250 135008336 135008351
    0x80d020a050303012601020703080403030e01060b12040c33110d030b04150e090d050f27060a030e01050907050a0308070c270b01020316060e16090605011101 69
    0x7440d0300c9000c1409140c1c507500700290180320480c0c080c82864605c11224000f103641d1042d608004000c00400c85007a0082030a0401180b1012014410710f0200c410101225003420f6100d20011103041c000390050315403500041e80030031032215045011a100d60320404112090310441941506440405e00328020321201801800c0c1024010484041d4050240340001d01a00714000003002018451106642600421004039003405c00803511402a804002120003000105000310b4141c86400b5003c52042d50601c41040708440545c409081c0c1c0302c100100c2903005898401060042e0040b45a190000391138403401c800c039280078842d2070740050306a0082d0240701d051401182d1240914030004000c1280010a101401010b254010140001e40b060b02213003190381104003441a10b4051540c0001d150440180a030341c000004c132103540010a00c500c40c81700c03d41c0c945500a14150303034071207941d0082c01401d500701d14125001c0c00141c200104001a000c0c10240010420300701d00000d00b0a03030307240012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 135010836 1250 135009586 135009593
    0xd02010c02060705150703020a020106090207050309190306050f0402090907151d09040809100c0b0105150c0d0201051006080408181207090504020f09060d11011710080d020a 76
    0x56061285070180d42042d602c51140c40e2641c40c1ca0030b504451007903408903400340646180d042d001801d142001c0ea00134480b0a403100302c0d00040348283c1070001e04a61040003072090301e061190030001068155003442402d66529203482c000d40f00100e0700c071800014124100411032410ba01c02e81d8100c92100d005120079401c020a085d43d007100c866086040c45040c4001010402c80c00c5007070400e54102601a41550a00f0720340b8a00d141c001030f00b0316100b09900600300455501c19400d07080c0340743d000389450a80ba441d0034180098010403840003005400708004607010581d08100c442e4500c8503a900006891411110810000f21150403c030304000060051002041c07425060f00ca00c42400c5205d00b8000d00070314009141880d81c611510000d0162030340001d001c20f00c6500c524840c5009990441640d802d0804105d48800c0031104e80b40d0007400078203100c01140740000040300740e94043c14a1081c10a20081304801c0c118112903e61146440750418842c151051249004d0050180010403400c191541c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 135012086 1250 135010836 135010847
    0x8090d0207230a120506010803030c03011802040803280903081206040b0a060201090302011b121e111c05100e1b040603021b03040b09040515040509070303030b0d0201 73
    0xc11482c0211085140b80501c40c0c004003258000400207110b082450340d140703008958424403960564140c003c01d00000307440d038400f00c2180c1c070881c00310358070900e568200b032416001180c05100342d10040c1e60902001c20041c5081000b40320b44015086010340b180c1c2260140506e9580e04c292103c1004029a030400000308011300740ca0706020207020b55041540d501d004500105600072069a101081050004e5070700c0c0c06500c06030825000fa0300070f003e080540c032941076001d140d984007440080e1101030041e6200000758000300c81051001d540503847c100f000c00503c2941e803c2c1041440c00403001642c40c125118801408a6000249105100c1e500d040c2040008030a0307035119000b1a0b0045400107048501410103522000c90841c01403a01c651316150000e000350405c05160100e00000315131104074150000664085402c01c1c80900c1c6480404810300018090141c40000100e0b07150500c21704c81e0781d45004452013042d00b04000c20340140343d814010166200003003007901884c4280038240260368480b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 135013336 1250 135012086 135012089
    0x501021f0b0d020409080c1605010509010f140c030a030f0b061909050301330e1503010e010c030507090b040b040905060d02030a06050915010e011e12050106030308090d0207 76
    0x2020010701e80030901c0c040b5a1020010200a41c0b15150030041010484004003903c3c0c058001400c071483c40b80b90361555410b46c42103000f2580410300c18000c2546542c0701c0e03142c11040b00340c03a2500180844810700c01041350b40184030245110780010501e0b00149a2600c111180a60445004e211040300b18000c540320f442211b50405d090002440748100550056a44000802015008119100c0e07103030118600d0005d0191048504003a083d00d000c4a0010668998240d0700040310040391925031100746541e070600001441d4240d5200d101c0d40944800c21300c50001d1090301600e0110b4603140240c0d00411740946034200e11400a014001840b43c140c0c050306072026103902c02d0001a40d40c407090000b030b84150010b80002e502d032150b14206000c000140e0000390003000309070101e0b0300100c0c0f40b24580207814030034050385c0c091700035040c010030002d201c0e00d50006a401c03542c0c0d0302e200c1250b1110380d000c03940305128105984582d1500700030810036512400e8154086490320151020484000c002904c9540a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 135014586 1250 135013336 135013393
    0x11802120408070305040e010b03040b0a05070e01051303020603011701060609121104060e040c031e03020c19050915150c0d0c08090607030305090f030901080106050a140a0e0a050102 80
    0x4503d00b000c141c00703001114068544200003c4041d0b9580c0000c0c0080c2d8401c90f01100c81d84c804d040400c00d0075240c0d0003024007401031510b400340031041100045030b86411a1400d00c801410400001001d80c4441000794068030300742c0820440880c02c1c51354603080d03520a1b40920301304100424104401605008141041a0b12090260400d000358000501522003500f207666425a21005d10040001d66a003400c21070b48954501440001441154425001d05d41e402a006d40c204444280d010300e40642c81347c1c081183c2160a40c200e03519400402d111880c2150240d200420000c3c0080e058580786c182000752454645560b03280104103000c003900c44902420b807909111040c1e002904110b00f1005a904448020b4400d0f626030446060007405440266100b5049000d40442d011021002004840e916001a180c0950b40d9190031f808407400d600c250500010000340e41c5112101100c1c1c10300034245251181c0e510340000302030f00200a4031540c560700090555108030038840c17000032101e01d00088101c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 135015836 1250 135014586 135014603
    0x306040803040501060e15010f052a0102042103020609060705040603020a030905010c030c08060604050303040b0d0b060301090c020c181303050c06010e07110102030f0a0504060207050706080118021204 88
    0xa0b146415070242800da00414005041a0700f00010360f41d000368a04d10030402640c3c1c913008151802001d4425200d82d580d90901f6041d400a15840051700c44070729103281240c140018901550352138410107a022480c43e0510511078880010b003456410000709400a820102511103400c00d40c10191840c031883c49900140364022400d100c0d0340d0301940c0144c2036035410078020b01050404660040040c01409580008140d030b40303010451606107403081d507040d1040030b0001d5103803c2c1020742d0001107800050000c0019074440c801d546158640310080c50084c51020004154403500300701c080d04041c01e00c00c80341e0064010950400f000443d20300300541104076200d140c038180d00e5604085a8034854498980601d01c0b40c280001801450107801038030542169907040043e241a0740058282d12040d11001c111465500c041075000025900064000f449218014505155a40c43c44d0070106544d002d0b20100d07241d200100442c90f5a40ea8480070001d4503841146800310600c64000d991102820182c400314 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 135017086 1250 135015836 135015841
    0x30b01020307110d2406060804020f0609060d090c05010f030203070929071a06030a05030a1b050f060a0e01061212050c16091a090a050c090d050109200306040803 71
    0x111440344d00c000080d00b061194074522056400c4484030400041c928200c0c0d0301e00117000035041d10034240c0901130341c2e000b04008420f000400c03c0084e550070031007020790f020340708003e42c942075941c034480c800700c03140300b2003600200f686000c0001d030641ca01c1d107001d4000e040c010000c20075900c2e40b00c000344003958074600d4210340340546824080e14040d50f03e807503014484000a141b0040c4900c1c0010040c04162000100025580304005c0c10b07294001031500030310603032086c0821007501380261407117544009100c4690400c00000d0b1561848c14030003e105004580061b41401010b440364051300d074401243c0c10084c00ba603407500503032403080c1c489514050404c10750f038040003050714441d80485140956000407100c00b0420300d49080c2c050100e911801841c2850010031804092000d44254040500100750000640c0e4180c5424090b100040070400402020406180d070350750b541c0f050040c0ea50140d000095a4007031032a00e40d9081420030040c455128590000e090956400500d0035801680720704d19a413280c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 135018336 1250 135017086 135017089
    0x20d0507171c0212040b09030309041a1503100608060609120d080a140105061b010c1701080c030a08070807020a0b09180c190c0206030705120106030b0102030711 71
    0x414290407000301c601d46040740064455001411140c0b400403019240d960801c8070605a03502c0c034491001c804c0105090204020480515001c0c0c840c03800c018041d41d1070280d0304400182141d000460b00da03e00c0c041080201c441c0d00b4003251440c006000340b0000f0785075047ca59003441d8641c01030311075501082000f60002d06283c540600740d80388044083c059101c05820350030b100b501c2d9680003540c04001421080041c4200c5110300507101d400041d40a1140b0503428038042c4207083c0d2001d00303d0303c1c1a1503035400704401c41c071091080301580d44c1c2d1681c85c10008803400003024050030040e404495030758444907824076540d03000301c0c0c07402c1c0d90b9922110099030382c582880c00c203019019484010358009589500094001140b0300245000c11041712903540b8000c14518010310b01c44d0546804000c00700a100520700482042458840c6680f681031046030700300f44e5030000c2c6059008444a05c0012f03008a0754281d00322203500c0f8540902100e0409204a46a040000f0756074000c100002d400280101c44c80c4405 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 135019586 1250 135018336 135018343
    0x115090c02070e090a0b09010504020d0209040201020c030747030402120316061112010302010f03020705070f031707110103020706020910031505030c0a03020909151810050103030c020d05 82
    0x70401074640340706070f244c9640a6034449440a01c284c0310100b2450004c0c42c9480e0601c00d0314403d0358010304072007008519801740f00640d07800400490540c03061304104a203547e000c010580060207018048800175a2714030181c00e000c2c0f001e0040c4810121008a005a0001c04102c55414070002d03c140c0341d05d80d1b907140000f0341c050b00003000c05030b02e9000018100d40000d0413103a950072624081c6034148024044c2c00c0c0107440900c5003070828480101e0100041c00150303c241721058402c19a0700d000750400590361201da00b404155800000d1111160104104000c144081c410411103140a0f06040a10b00d8541807480c2c5c0307440c1101410542e0025201c0c0c1080f800340e0580c2c0510381c01424444090660120103401450002121644a40c0c0700400088a01e03000410086402d805442480c419286900744449030001400388400f40c080c1010b440746200c2440c0c0010710074480f00c039041a109031514000c5042903441040a05084d0500c1c2c014070109421404c1020000e506460340d1402e400036003441c0b410b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 135020836 1250 135019586 135019589
    0x202d01020304030804030c080d0504080c0111010e030412110d03140702010912060f0e010b010203040512191a09010506090c0d0b06130e100303021207060905100203010303030e0115090c0207 83
    0x80d0f444c00304000c402d008914540c082a6030504041300c000d15403801040d2040d0180e07100b0202c19a00040501d10554420907411407090840e1001003103400d105255142950015008410040030281c20300040c48400c0e01c01d580c2d20282500c00e0310340801541c80090011080c10001c1ca840d502c0002c2c030780216440f079062240101111800c041d1094268070b80399025206010240c85920f04101c0070b01c051030760600c50203680e900141c000310700e001c0c0342c1402d00c030b86004000c503038a17414003684401d060140364603002d01c3d03021403051030401203030352411209150003103010346035a00c10782c588010400d954070f54040f90741d0084818110b664803030f0810501180a008140751a030307000700340171035410980c0554020220030350f440c1c4000300303809548020040710b00420622020740164031020341c1022540c0c501e4024000c2d14010100031440d10301d2516010301d840c100321000b085480e8008010002c0c558544a0000040e0140009222603c0d10981250f11040c450044d02844c564540313600900ca13000300310600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 135022086 1250 135020836 135020843
    0xf0f04030e060406111011180d060212160516020111030c160602010b06030f04060b1804030513050334170309090615040b09060c0307202d0102030403 66
    0x983c1c4944074400249840c0650124070000e21440324140c400396141c0c010441139684941400d804c0860311004a18042d80389004150030241e0000054040303802c9000404450420340f5480c2d4550034071419078108070752802200c00c104081803010340d11039403100010000040c0c0910f0134403181104003074600c2c01c5200d10041140c00340b180142000c1035200d4181d00e201101e58540003003201100090030f0290340e02c01110181044910140082c1c0003503826400b00440c2280900000c401200303402c248503103c4030a48080d40403c7c1c0104442c0e001c500344100510141c60203a000e00116076061301d4440040f40d03d01e041c1c01d0304c6000c04080801004182400b1402130071290001d40c0c48008081200d5120b0380702540042c010007102c40002e0303943c02c1841c883d122030304001d070b8418075152a08030311050a400014841340e20072002c002c40300d91050200084c000083c066400d00c00c01e102003210407540c00c06603940c4a401202c3c4c1400040e00d4160003a84501c040d940d6181b000b40740c60468004038114800c07904000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 135023336 1250 135022086 135022099
    0x1120b04021605060a0c091205190503041e03080702010c082506050106050f0d021809041a01090b13020c010b06030c040f060801150c0c091b020111030f0f04030e 71
    0x151100d48849107144142e0040c01038800315110216240203451b41400000e01041d0280b40c200805c1c040040c403401c2c1c10780039409458210b44a0308900200200020301507600c2e510100b01801007010030340605407481e07542560f00c00b00600c1d558695802c0d016508001e030602101c0140301050242c19400c50f040d60040f00c00320100c0048031504e03c1003d02c407120701a0b402515240020591600403007c4030320002d2000690303400c201820408001030751001d050422415001c1400d003200c6e842d64170040d8025403003a4100722004038006114451300c0c01c142d000d0303c0007504143d1406610388840810007003007100c43c10050790710320101d010310340503080c0c81018a410510010400511840e618003800035903590b60340000040340c1c1d6131000c444402c0d00303004a940d503100300388030295050300560341404954030a0120216459440b105030007119449a4002520110500c2500c249a4280310b110b9441e0241f056036801c43c184a04040e400c1174000382049a2144560080741c14540204403071420010010100b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 135024586 1250 135023336 135023347
    0x30b0a0e0304061d3304030c0e190506010509120114090102070209010602010902220e0109050115081506120708060c0d06060e01140a0c0c030501050402090f0c0901120b0402 76
    0x40204410013911000c10091010140c4a4580704015811215200328880344028444041c1144c2000d4124202e030b4540742040008005031082c1c0310a4000c01106004042504d000b42c140e0700c0c038a6031151004d000764940000c10030203a810406840c1a0581030324924900c05040c05010300410645e540900843c545030208520100150014003540c1d1094600200b6640d9450040e403e858000744025445415012000c845e40166064003000b00d032011030100305807449220f441c2c2101d640031400d0310f0702e035101d402024040d0728034076242e40105010030040402005110045040324006840203204440c0c1d48610440380300100a008054030070038040d0740641c200030095560b6a0f05c20290308000b41d0610100240340ca0190756020150081a100d4841c6544417032070603613031507002c6d80c150014400c02500580101b50003860240c00340d03208100008240c141030040004038603008200300704010702c00c402c1082c1c2400442c1038419100302030804442905400002074007901c1064aa960094408a01c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 135025836 1250 135024586 135024599
    0x8010204090606170910020a0c0b070c06051f03020f1516050705101b051f02121005010903030503090106030b0c09011d01020a170403050f1c0e0a030b0a0e0304 70
    0x2c090100c0b200c6494004a07003141120401c00400c044401c3d0002d50840089250451401c1d001800188494a04052086a260b50720422240181e0302c0c41c0c0090448842c0d40c0402200d0701c562604841920545441031010100a00d001036050000900480703021600c20115111107035040d040c1001507014544407199070301c5d0000c2403250303044251a10321a84ae8000380764180740144809070030342075032240c124115405003002041c51810303045600e0320880c900c1c180c00180c0c00344c590503c0c41c009540580c0e10010b10541d69960300300031b08103c0d02c940500d0010416603800c00703010b4049070b40c07600303003292640e4620344000c1c0100340139440a000c0003014010881004841c50003011000c0707090f220b003618000310002421044041c1c914880c0940e2040752042c0104a28903100070003941c01035009071500c0d403299500340c101080c000c00301b6003c0c0e10002681c208030b0140d4a10000c0d00d039007440d1509110180d80c0018031b40e20381c80e11000d8007c610860125910349500d401c0745807142c1514003126652942e810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 135027086 1250 135025836 135025841
    0xc010203130317070c0212100c0210060e0c03040b04050106051e01030c0201060302060904020c0106050301020d290915062116050313030509220b090612071703040801020409 76
    0x4000ca0000b03843c0340840c00050309000709640a00130a0780d4018200d401c55007031008011000034001c41d64411550003a0502c10079004448d85441c05038041d041c2c1d1080000304106850150b00b03c1d01140222808101c64009400192a8040d820034a0a025a111400e209004100c550446c6800030300810074184652a042d8540b00304c0042a039041180500b2218201d0898580303000c020f603c00d2003000070809526064018207101d944c400000108150f40d10002801c903400200d007111100d0300c8964103c022030b014606001ca181c08000d448400f8404030340000c2c03a660000f0b2481e041d003000e24807070743c2e0a5210a4181c42d1245054aa02c00a08a00c421495108081114070b200f01c220185124141103204a05a900440030042140c03c9880c00b0740c1d041d507081c0c01c6050700c150402c40f40800b0f549001d8464040300701781602100001405030059040c011010b400078516801078034200a0007566090000b09141161440c1491401c0c0148086d0150304501c1113510900d40c03980040b0b404142850682e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 135028336 1250 135027086 135027121
    0x30203030706020a121a01170609270703060e06060108131e0b1f14150c0a020a090c020105070c05060f18070305100b03150130030203030412020319050705030c010203 73
    0x2600c58230004800c0c2c15a6002100e000c44100ea0841a290b01181d80c0c1072481011502201d6440300804246186882d00742c40d0a14540c0281c403c15140e005c94941c00c8801c0c030503190055420710741191075140c801c51034141c0d06c0b0b801c3d03401441186944030009100740034490340e140301507000030084000c2c20322850700341043d420560102c0301c415044100080444914080c0081d03c078014003045508c2440654182503a00851803140d101c3c0155091440103990300400c481c05000c081c0e10000f00c012628000a003101d100821090034040744400d05008a50009042e40c3d000307104441c04170165542002d803018035252101d0308a0244100c21001c02008408074012481c0d42441404000d920b03951810195100485608016032207000c5005100007104015450244000e20009248108001041000a00d0b000d00d0543c0140c2020040c0402c000320030b0b95500094141e4801181042c0d0303218120700400c1c00c560b100b0700a0040008541040080620035540751042400c02103440303142503040c109004085 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 135029586 1250 135028336 135028339
    0x112060506010f0207060804060e0303090a0302070f050d0b071101020c0c0103051012120c050d0c020103050609150d02130f050105090a0e070911070c0b091306030203030706020a121a 80
    0xc200000d00316521584580000741615030061440f9441c0840075030390b42202500039151103481e0380a501d20010200011801428000d0091015030200e050084c01e11040f60403e4803c0103454908004503030b180c090205155400c40c2011005454a0b441070703401c260207800035000e031750000c00d41c4145030001003204030142e082030301d0070300072603a802640342480c1c4214084c0503804a01442d201d80070501103c045009101242030007040300250b510344030b1501d41c0407200c101c0001c5004c0d1050085523803502540760002015100e023105c600f0b10300c106200b00510300b210b85000c0e82e20340302050195a1591038030044066090700410410f000c4031482405071200b401500c0c003660410f80451001d5419101e100c911040c0130016164590a1900820142c02c1c41003a2854030305041c4182004200320035243d000034646900d40c00e0343e40c2d03400800e00640a002c1000030124618111081025032404030484200c217901c02e20060303072105402415588020480d490a824528142e0a0484010101040e50b0140320 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 135030836 1250 135029586 135029591
    0xa02041509140c030708090717070303090b03130809030109140109030807020d02060610050d1a010305010b1809061203040807030611190f110d0e1f1b150203011206 72
    0x120b00701000b4034041e200903940360000c0000480407031040801541140303128065802076582c40c4e500071946102e03440c2d00c0105810052040040641241c215401040000000d6042d858182d408818925a100c000340c4200b0000904111a58003903001051050780518154100c2c070981020f01d00a107403407641100802e01d0300700407071100317400001c3d1003014800c01da00411030380d550f038024003a02c80f44028549081c8081401155000651380c040c5042c08c5290200040079111010001026038074107034018160800b041014100401444001e1b00031000141c0381d49003180c4950b008181e00010210840c500c0c0c0c0004200407503800300c085018005c82c1d0013040c05000456944404060390720900468400b04c9105884072030144d805511101c5d0104128100440b5110801418600340700500f5034090000c3c4291480d041d9a180550b01c1b00c1500c00821401c803064001c0c0c11001d0034250a9a0f03891034070b8001d0513204800c105c00381e0041c45c540000043c0554917541c2d00d4007841c61000c44680200c46035070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 135032086 1250 135030836 135030851
    0x60207050d17010b09041b080906011e060e0d170301030b01060521040f0c15122705010b100f170c0301090b04060f030809100201110306040e0a02041509 67
    0x1403040256103402502c4954100c42a440c0403135140c2681c0c0070720140e0341c201781c80f0b02c44542e03101070921403071540d0020364660845600e46500d005050107016006580724600401c0c034540c1014001c480002921458140305031b2001e401000102c05183c8104010006220303000e40c1070f03c084005000c1d42c100d0f840742001c10b0481c0d0700ea040c152054019202c0e541e4102e209140b106806050720303031003a50024060341e009061a5425260719652000503080b417507140c1c480100070344080b42d100c0e0740e6000304101c2c034104024480d511900340c2448030441c00383c035043d00c13046040d040611030300394010a00603a0040950070f041c1c45020004c0c194600280c07841004c9003496401c54202d0504101845c4100046d4954030303e181e00303100c804001410741c034052540103035840401081151981d181240038602600145444044803000c011854545c21000411a41440840480c1303580b168192900018101c4000c40c0424103145410300d03208403018043c0d40130341040c5450003000d8901c12524180e8a14000602c00c44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 135033336 1250 135032086 135032113
    0x3140303070509060315040f150506070f060e12030f060103050c120a050a090c140f100c0b131b0f050102010e060c03040507080d050901030f05090a0f06020409020706020705 76
    0x340012103502010400401c840c281034a420070041d41e1140c9015016440c1901e00380206048070701a00c2c884603141c2d41d444400010180c01c40191004050131145a0715100c0d50b40d039102803810900300020402c507140c070340210403460144280c0c505880c80c1c01c145a120b2419800700d2807000003e45041d400b091800001c81c04048205048501e5071309110010115500d8882c03c0070001c050007406248050740d110741d02c80c000703400e02404400401d5140c18465412f80741e03604001d005040000000e124a1441d00b000d03c01c241c010400c2d0401c150403030b482400703694071510b00259501c4180001000034060350311044c1d45031043c2c16208180d5044c0788004145980f02e000590807152011010a01c0358021000903680041c154011a03101d81f0403001e0701d00e0035540720022492710303001e40442d0010400106582c082564180314922000403801c0090240342411000c080e156074200744d015202c024041c0106060210701c2d01194010002c0b038000712350350b410728203280009404c4130728121a40e001c1e035042051039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 135034586 1250 135033336 135033343
    0xa02090d1101174804030c050d021507021516031101020a02070506090406030209010b031b13050418050f0f010f0515131b031407090608070f0207050a06090314 70
    0xc4c1035501030501010461644041c000c2038845000d600070f550303810135052020011911605014006403419440300d0a500c0c04075140d01c020b4202034020081c84000078050394030b00c0e01a40c0028140040785665228a0003c26a510030300c50500c030048100103021401c3d14420801c919105000356504521000c440600e54242d01c140140400103910000c1d00740110700e801c20043c144444001c10010f5060f030350358046010f040090703011401060011040190040ca5403d050031442c03028203001d86801303210200c0e420208c185001d0203004a03602c0c0944040d00d4418885012003641150880340c540100c508255035034502c40308030440c1b035400c00803044107150315402481d0050403000106001c6482c041c0038041c0403650788001e11100754580300c2080724034845104141d0281266030b0042015060200c60001551002c0c144030304002a54008200e090351120a46400c608145030201484c01c040380101e180022982025900051064000440310b8100c04250103d0740b2410005810a50503d900d588 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 135035836 1250 135034586 135034591
    0x501080f06030d0e03070f090203061003020a02120a12060801020a0e0102010b090606070302030706060603060f0b0702010801090f020702041d010c020a0c03020d1a04110f040b0105120a02090d110117 87
    0x30036a021581c40a03e85008070b94221801502404988025a0b03030440b42243d9038070341d80319401c0380e42d0008c188141820801d1006515a106007402d52601e82e0348a40251f071003400c04d005114808010412004080c40307005510800b00c104481403040d25142c80c031850003980030800030f1000c03d5444a51180307650042c0207000342d800c0010102c0f0095921311007030203402d0788000c40c12011400700b0420320000030428403072a4040c200c0e03580c2c002a4113051012100260321a0741080f80b50300e00038007040780182c2e4000001c0781580c0c0207440104409080341c5009019024880000794000d040c44680107200712800c8450f050301503030070002d20440d4000308080c0d8485159000240c840c0700140000d2003d42494000e28248034404e00304d1840760464281c038019007000582e411200281c083c0051f000c5450540206001c1d20740844040081901d03950000c1d00c1340c450403942e800040244000500401c4455050390110300c0302070840a40d1503910720304480c51041c0245440d000c15a023101d64000d07500d0404101c0d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 135037086 1250 135035836 135035839
    0x1020d0b0306010f0e13021504060f08060114180111071e050a03030f050703091a0c0106060503010807060e1c0803090f030304020d03031a03030d0f18030c021c020411040501080f06 79
    0x101c90b0b20303450b4244103244543e850031f0360000466000d42c600786010b60020801000107540760740740510801001040c4000180100b4108111000740714807202d140011100768001c0600409024400a001a101c00c1000c0d00b13445c04e81d0244038000a00101e50f0b00c0f44081800300b0103c0e83c014942c4035410405500340a003c060006010241107841c850300690080c4240d5002e82440e1408683e00c512035003125410890f030000004001c11514000d00c0c0c02d01440000d44480d0602905641c104681160394006a20483c0d0421010050700045600e904910500608000a417802008800c0c20820740d1544152903a5002d44540d0800118030b000101c10380380141c1d0700070440c80020144d1707101240640f9286820060201c250300421206a5082004086094802d01e02248889240d074502c0708403107040c1c01044000ca00c0010b4071002950064044600550450b03903561010a210310183c2c1185a850000b03403c64600462014050b4507100a8412110243e845090300e0342d4904089001460541740136 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 135038336 1250 135037086 135037109
    0xc16150212030a020715091a0403020606100c0b070e030f0604030507031421061e0901090213080f0a0b0606131404110310080705240310050301020d0b0306010f 70
    0x40401000000295004143d41c20094240780554440c40d154560003025a400340d80d5a09805040011220f10001038591208620b00b2903c0c1a031400713905c0c0c003c000d048900c9802e40c20362024059000e58034591045800080111061400748006402807180e401314510034490707814444034248001501c01c4c032a66041d91240c3c1005000d0350141c0d090311303080d01c02501004062180641440c5000c20810305d04c101ca001079003150070050288a07400520790f00614030303010740602c842807a03142c2601c014110740b00301b90b00595070f1101207000f903d20003503a001507045000e207412070508008005640d03000c203400303080404c80340d480d0142007040c0d92142d003685c0c00b412200e09000704400070706c6c0107401e40d46c008060804a01c0c20f0050082100903881220700d40c0251070301d050700b41b02d41002084088003504050342c0b000d0503010450a0840c0c035a08034680300303000210000000d51070590000e468030041c50041c000390b441c0c502c8118020081c02401d01000d009106030030000078412000c0d84980100d8166003900f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 135039586 1250 135038336 135038353
    0xa0c050307032d060507020d030f0209060318070e130b1012060e25030b0708060102060a05060301090c03081804020a050904020c0703080c0f0105070305062d060c161502 74
    0x456081114075011059903c0c0707060a001c0c00b0070418000c50340700b0f0304c06034040e000c07022035141c025080718010351580f158284180410026900c8030f40c102c98015000301000d21000e2585c800e0300e0310b0000240c018005000c0c44405028600c4c2005258845a61045030704003810b541d8104017078021007141c4a401c9200bc4814401d4021482540c028915418a81d058616214040381e03aa01941e1104003001790710484128200244401c000602f0742000b02ca140541c41d90901d0f01c0001e5480d20003519200815540343c000c91910f80d000d5000c40500c51303204400c0803145a49090254094110410110326900d4040310340a035032500d0b108450701035107292a641d09050450781800002d41003805c11202900c203441001c00401d0414010300301d0481d84c84010310700d03410100c400c0c0d42501c80113424a418141003c7c1440714558941e4240360707580c50302c0700300d41c1a42d016412440d842887c002c026107400c1030000541d21503020003c0340d011204001070f4194000e0960b03540300786c40c0b03010a101143c03005030020382c003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 135040836 1250 135039586 135039623
    0x90c0409020d0b0a110c030d0b0402090a0b0c010e0a0b070f020105070206130c0924080303060a030f0305120705040602010b030f0604060216050f010f050a02070c090b0102010e07080a0c05030703 85
    0x86040c4c01c070103485030000e00c075031148960220317942c0618030051941d840450340b0851824180900d54260006981c10340c100381d141e1010840710000f41c05850481000801c614980d00350940c05030028510300700480300061924101081d6980e8140c421400103101900760101d0507005016440c01212664020481650740c00c020340c0103420844402c481240d1105800103a403d80760082403a4003400c1142d80c03030142913440f0b04141c68011a44041056082401001159070b10203010030101d80e00140f0080350010940f0b002c1300e15100b40c818442821040e0414412050303800009001a074141da0000c20526040c102015511890300311560346540c80304002600040032a00500b585440c039001d494403469680e901e090820a08107810501603541d0030720f410000d645805003d40100821208510b00b040f240c5a002801c03038603018201c0710b11b0311516130000c1039200b580880a0411044280c8040315202e43d02c0c0f0381c44500c5401d0a8461134103600c40444c1030b15010612100312a80403040002c070b0202900f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 135042086 1250 135040836 135040853
    0x601030e0a330509030306041407090306150305010c080901150305060c0706090c080d020c01090612050702030f13140103020f030106030c20010e060c0901090603110f07030206090c0409020d 83
    0x955410a04032000c2d425201d5101d02410307010345a014091350f200c1c58520f041c40101d038407111244808081950602c4091034000c8900400d5a82003040404c1c004214008210071034010740c001041903287c4031210055030b60045006000d400382d00000d106080941c440d88090140c203000c0607155411540109003401005401004458480e00b030101c0c1c5100d0540b11b010148403d6405400f044e00002080381c10143c4c180407240e494803003428800b96503030070a50002c1031000040b00503620140d0741c1340808e02007402001901d030071121007018965140c0e41280c010004542c64441c29021080707184034640f07158064007c0e141c2601d04440d00b141981e1070030780107d010700281c0381188284403001c5000715028011142003a88030488a001048120303c0061071031504c40020000070745000280002da615a17880800c05045030381e50714003ca01c08402d8461803c40d8403864140c2400c290000503c2c3e03042640110f0035900c581400b0f01540c50301c0361400c041c842510042e41000b5446900609a00c0000c1c40b480c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 135043336 1250 135042086 135042143
    0x2f04140301090f030c0308060901030f0201030504140d020106140402070807021c08030411011e0f180807090501030b01090e03072004410a110f0d050601030e0a 70
    0x80020030b000016071100d81c1c1c0d1070a4400241c000580f003003445028141c0001c1c1c034540001d4255107012180d85541c8400542d080c00520080c1016140c00218007881030180740b900550441c4401d69003252902c40021b4028895441842c00c0320300e80e03129131842c0b80703014800da82c502504040040d00d091400d90070044540d4810b040000400d46800804c004071b82108069486a13110b10111111080c0080001d0a03070009030785815012a00000e01004042e8815918010741d01c0034140060783e030440769404000004540c0105085106a409c006181116500f209041f680141c840b078895903241c03940c0e40140d90407a4048011a0f204102450000f00340804420b010b924491040030444440c50008060b602d0120300c143d460580070b0300b1011500442c05060f5044158503003000d55070401d0f40b04044103903100030302004200740c4d12b000d50303010140c0c03034821161006288001141d44500d01c20f0400011b102c00c1d01c1460009160282c9076858690002e8100902600901e85050040071404505840d0154 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 135044586 1250 135043336 135043339
    0x5030c04091703040303050f060405091209180907030303060e1b2115031e06040219080a060507090f060e0d0201030b0303070b0603010c09030b13030201150602012f0414 74
    0x1842100c0c01e00407501e0b0007035805544650b074003150a0811902c2c085040001404192081c0e18000c1848040c0748001072042c1150a01030041340c42d61038440c0008c0c2000181041203c2d403c0c0b1000810201c4200850680c1c2500c0c42a00c04001c03d035112014488452012602c102c20a8841700d50448021620380244ca01c5009070348191b14001c220b45100318501134181c501445101000c0051801d0340f4051100344000001030764000c0c064402c2c50019540c1e50380160010f40240841810944060700d2062000042e20100d0212031070541d103032514400810040f180c01c0d0004074029004203484007000380c1c103012110f555442d400721560000030480d4088801c10304a042c55500c82e16010070752018005050440d0040c4544071003132520030140350030354411941c10010089881c1c0c0c02d000207141c2c20130540e04100240e081c450084810700c0d040c1c1c01840c803c13071050f9600c900704000041c8240d05420a0100d401d003807400160304640d02c101300030080e40d0b051940040200600081c019150408600180060b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 135045836 1250 135044586 135044603
    0x4120e21010b06040603200a0912020d05010203090d02010605011b08181315050a0e5a011a161406071106070c02062802070f090605030c0409 62
    0x42c0c034000500b40d5401030f07004001294644440010402104055204114545880703070328001c20381c0d100070117050031030044040c1159001d8100040d9101c80c40c1ca14501d41c1c0c450000c55030780c00c0c4602c60540e142000640400190300345100803e0a510441c6005843e02110703545007618022543d5440c40c58001c62460344d01d0312070800b058891540d44041c0118010340c4c503080020342e13540500041d442413235140c100c0d5024222a0300c0400243c141c0d40081c9902c030303450000c8407000841c0d4030030300350189480c0158000005072900204103107080000c061a00b41c01522482c40e00380c4001d106c842c031141d40c24410982c84140c29103000f1101140f610003041c07901944d0400c0294401e0310ba4030118403003015030039404198080030801510303580181d01000c102c50280010403040c030388014024201c10070804000d01401000c620b10b816190742000c50030f508041c18a1401075810400e8000703640d000c8904c1844101c0b075088500092800b51881002c0a98101a015150507218881400301401c50240201d80e40e01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 135047086 1250 135045836 135045851
    0x110c0402090f0307171002071e08071502030709080a0c15050403050a060203090d021f02090402040e070309020405100311091b0307030504120809030306010c1104020a020604120e2101 80
    0xe80c14410140942400034007090032070030520806140103500c1b20440a02c51042019402140c0c5a010455103003490120220042e40c0f1803a05218600441800600311000d84414449001080c1c000e1403145100e69101100e5580d207003030036540c42440410150148090410501c248015614000340703200c03d90805900e0316940341e0718580b52480450381903812030390201c20b0244d56241403080d000020410300c0107010b000d0101034240380a002aa50b15821542c0c0042e00c1e101684a50301600c00504914040c540c41c0c0c038190b13801a01820a025040340305030300c1c140003e115200c807001070000f41d9810111100f0059904030502685c09809003160f40b90f00741055512107a062840011803040b40107a03000b042600f4245003030040018002040f0091022110402c45000070000075681d06c0107007443d080400c10300908003c401c45030440740c0d80b0b40140c00014140111500090301c140194811700c0c00081950040104950361400100003581c440603001c1c492840c4420f0100c020510440c0c00000907058 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 135048336 1250 135047086 135047089
    0x402090a0c02071502071d010305031b0705060d0e010b060c0706081806010303091a0f0a0302030403030b0a090b1507020901062019060e0d090b0705010f0501060915110c0402090f 78
    0x703401d0004d59001030b40502c105014512041140702d80501d0b4130314000c0205c0d4199a16261640181c420300d0b2108004d0364040ea85681c01000070400401c2c02402140d1ba801c100039480b130140c9201141c07007000e0340c28840903c01c01d040840464a40c80080c00141079410700b0b15904542260b00517000d50340040c1d08032600d0b510054107104c014029480783d2030f110350f210b00c0d102d80f039034401c440000c06d080c000a05100d08600a43e000c0300300d45815501e444c0c0180e0325555850240c00610007100d42542007aa10400441c1030b01c0340768008041c400c030458498085942401000c680c41c81a400c00941100728400100446e80c003403c410f440392080265013904451104040c0f610b0b0501410b40d140303040300402e50700c03410b2101911030200801c0540e00a0b2600c10350303524010300f41020b20303c254a1411000500c54040c17000a51007240601a8401c00340259655841e005012681c82d0044000c04000c0d440081d0801b4010b000300750501d000b0038090007102a45208000c025000309891540151b209070351900c55 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 135049586 1250 135048336 135048359
    0xb030709050112050d0804030507030e011205011806210b060d080d0b010e040509070e0612010204080f1501030c09051302061207021b03120304110d0f0314030402090a0c0207 76
    0x180003500d88030b180f10306103402d10518101d060b1003d801440350410070312021a0b8040c040764030f019050b00304900a0400400103c076803054400007032480600c3d0100101d0742c544034841c0042007001001090090981b61004042c0d0032241d2200695841507500030740300040c3c0309103440380d0b01101c0204105e5014019860b0711555501544e8451941c0c0c2d51901480020346e000910429180410b8508000900e45860100e0380c1c0c0303646000303012030105c0c1d100008085589105007440d00b903030030300000e6449035928451242d4030506064000154000e1600d074200d0a0140b04140e0b040700c0d0401c0e11030041c6850040c80000500001d4252020015415070304009615041d00034007961002d144d000a00740b82c1076000a08002103059107050910007600100f02d180e50000e040c662502602034070315900c0c0c856113001e400c901200c1003080d070010b080607070040c04e06c190340d054000002d000351504203a44240c566409117501c002c46c2c00070b5012814030b010402240056000c12001d4160340129512580c442c1010b102 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 135050836 1250 135049586 135049589
    0x50604090b012c091005180903160606030b0603030708030c0304080403120c0c0e1e0c04170303040b0a02030f01120203070b1305040b040c14030a1b2703020307090b0307090501 77
    0x2d084420400043c41d040c0070f00c040d5030008004402480d03550070600064080c4ca440070903510f0030326040000c20280e0000f070045803c1c28802e0034500003200d0311440c10170f02070905031106480ea0984e050000700e0b9401d0220454401591045082e071031555a15810413980d00050016202e0407400e00c40440060022035a9040e81705041c0c03034841c0050082d2900c101420b000e0340204003080d00110500003a0035510503844c1007407240303009040c41940c170300050894501441e0f0140b0403c0010b5451071842d800048011405540030314041003160f0b58210100c0e0592009440506929600600400c4801d0203a00f14102c168401010748404075680c00d15292030340c100b1540111010003207082000300c0c0c60188600f00700c40806442c14802d03075481200107858041e82c0141d0940c00b6100000286c09180709500400001c0030200340c1900701101e0602c000c120030a83c00d44207448140d107105000f850b91b1200d400d8421294010002c044403400e0208180c05031081400141e0144505103000c80c0051072401040d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 135052086 1250 135050836 135050897
    0x30e090a02030f0a09120c06020702060301091d030403031713170a111501090b03070f06051b150406020a090b030a09050d140d18021e09090304050604090b01 69
    0x603280d0801c0c2c15503d05440f0080c103184e0010345080c0040c40040d6042c416001c90401e141092480e0210320304048c0040e10880e84003d40c48040000040340d400d49941c030104200000040f1968500a41d0502540d01e02c1980006000303c3c0c3c1c507401c05c2c021a100910032a601400c0038000d40c420072070990799140310508110a0045401c404161301040300e80c095101000262540d00420441a90010080240c0e50602400000c940c441161481c2d0fa01e081007684010070403c80c500f4509503560500500701d03001501d0071142c4440d00301d40407511281c0080c401540640c20340566616480743c2c3d443c0d07002580701030741400c01d20800540004002c80c074400598824802d070301c0049200718903881c00354113008010b003c400a00000840f03001d407041048003034402800800600003207400e910174850325440368000c0d0003540945c000600403108890708100b030303280e110f0a07521411680c903070700691500ca000380c0c040ca982003402800304006408546e003042142d040181440c60f110308148188481c011020300c01c94 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 135053336 1250 135052086 135052091
    0xe160512090105090d140f07020a0b1303060b1203181f0801050405010e090303040f0303060317180a2114060708070e0901031a07020c061602030f19020d030e090a 71
    0x1a5000240441c008081051411111b1182c9881d007000d660b000e02a403000e03054601264501c115101d01140d10040d0042c045a00d4030b504840c0d14186070358181d8002125050f0400320100a03500b45080d0140391340000c0800b56080c00c44243c1f0100c4c0c11840c44641c00c1d44201c01c01d07940000008a480d21240100083c0d5460280d0341c10001440252401070b403203100321007100420049003c4010060704e030050741c80034034001490190f04044002d0300503074001030b205c44070041d005a08844103030024100c8082200004508020120401840803042d1240ca0b12071580c4480741208208800500c50119108042e141e11002e84014080d1400508461a00c0070924410070b02072a117030440412207062404030b0305181d5960440c1d4035900c45035500d0300c43e00c81c03203140035000c589d1990080c002100c1d80c0e0006020746885d03611280c481040f040c44500e040c0d010307011712240741c007850102045040d43c4018014402c0120307800c40d070a00071401c0450105600300f043c5c5d4021700b1034607610000414050010312002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 135054586 1250 135053336 135053341
    0x20a12030905150a1107081f02040906060801060f0f02061306090602040305010e06011e03080c032b0e0a0c140102030c10060608060105090306071101090204060816050a0e160512090105 81
    0xc1c1402201c810500080d906c0082c040190604c00140040042d6680c0400054410f86030a00c0001e130045401840801c0c2c144030000c6051548103103114100c3d0070658428001c0320205c80140c0d00c100c40140038130010b030810b000141c81084000c100f041c00500c02e10340014180c950380c440b10101e0308181c2040302c82c0d0b5110303414030030709a200300000c1c1d02500c0b074151566000c11400007402c0d00c8919500c8020100c040214041d28006401c1c401c1d2004130044184011031101c51001c070b103031004000d40c42c0428261400240e4070200d4000511111402c1d4007404c001c1c84541042041c0301c0b820401c5084d14114030040003150000c0000f40034000d040304480d032005c101e04d424070101903c0d2140007040c450400c01c0038000b400c0c19650008401e074200c1900d013414074442194440c618050310844034040d4001b0b0801d000019a11000184072030484c0c2e42071021703000c454503082049940c150502c0340c0128810b1100c04581d019000c401045c221503083e040203850700201c12000e0040917002c8070308050700e9656004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 135055836 1250 135054586 135054607
    0x6080c04060e0106050a081005120706120605010509041a1c05060105010c0807030e040b030d0503040b0703020c0304140301090f1109010506090a090504050a0f0c15030207020a1203090515 82
    0x1ca0307001e00b242000c0700181d9810140c0040a602800e401c07102049001c0340814101e1404d280b90902a1402030109100e1074400b50b4003d54408280c0b06100000d201e40181d0411410180b081c1c209442050b0b5440d403a0040728400c2001800401d009800120515843c4110959a400381b041400440400301c00b440406800c105040c1441680a981440b07103454110313001612041c122440554542850b83c402c5000e50007140060a246003516054494200701000740794101000e1071080d072261841c00425901c07102c0441c00e0703000314041e24241d80d005000034000560a111011180c10001c3c000040b0000140c2310f120503200d00940554584603d00020a51818002605800b528041d90b110b4a0140b1007008240c00780300e00e120304102c05540310049410007200344030950103507810072921003c485003400c24001d8240343c1e2103204214000f080c842c00c0c100e0b00900984501d150028807100c891362915180c00d07454440204101c04100550340003264a5541002c080d0760307026040780c0703142c441c000345a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 135057086 1250 135055836 135055841
    0x1706130c09060e100f0305100e070c0b060406030b040f14030a170a150909020609040207110102060106020a031403150a06260603030d021c0504030c11010305090706030c09080106080c04 81
    0x146440d014409419840444d142c10104c9195007501510b40043e26588051103500c1800302e0f9081111001d9042d070903c40d2403507204800c260f25038040d40d1081c0031038035400c04000494010788002080c8411140c006404602d0b032a0703980500c54000c0458a15003460103070130508560001040e04040303140c0402013240e000c4010411039103ea0034140403c03440c1400380c0c11030302070300c00c0d8420146001d440b081c2c00c8045403252002d64141d024081c0003035444480902d4080703626841090114014820b8500019406d480000e000202d00c2c2c00d0b07241d41291a00003604281e40f6072004085040d202c3c803802040f44952100d00f6000f00409543d51104658900422080702d0000c6034405000c0741c2c40960280412a500841100c14154040e0b030010783d201c011455000d180c450b0620b2500099207071204000038560031418280c99144601681c21741c040101006400b01e41d401d4606c03003100e51040c0741c1401014000d03070120080710400d0130400400c65490001a0035605943c103e1030301c980081c900c02d40181000d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 135058336 1250 135057086 135057107
    0x30c08150402040c0909060f240c030c020f1201050406060807030317150904050c0f180a050612010c1215030b04080708040306090609030f020c011706130c0906 70
    0x2000340c400015510900c0c584040c020784060700c110354840410030103c0c000c001d180010031a10340e052210542e1048401c050390b0180c4540d5a001d00c006c0303242500040e403001c41c00c060a0483d201d003400f4908642f403c03208001d9002c0200c1e00403403088902c10aa0303440c440c41026140c081800495286024030300710098400c03582c4040c80ca0350080d030040c400282c00c10501840b0420080d0f8000c441da54020401320f000700458001030300556030900b0b01007031120101c1c0606d0300e0401600e5800851a0300c01c2480064441c41007241c01e803d00d850003082203205590400c68100c2c00050000c0c1d0544c070030040c0d55084990582da864040b5060001070317114002c244c050000f00400040510a15030325513150a408a280104010010440000c1100800405400751000745800200800203480344d450311368000c003001901540491a5440b0350102c0d10710001d210410040103039501000d44244d132400302c81082c0301506665204880e01c4040084400d00c0c810300100075039135a14a07400902d8000c010f400a10700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 135059586 1250 135058336 135058349
    0x9040c020c0604050402070602090a06021501050d030e21030c01200a052a033004020604170309090901091208040b062b060b0a14090106080c07120801030c 68
    0x101c460a2025036407a0250350454030180c4000d07036200841d181c00c0001707124054103d42d00040105005c9032040c0c0c00a010b18046441c01401600c7d6600d404c200005517460b1200200001d0a400f0310604c54101410410301d40014100714001c12130118003400d0843e0000c05035441c042e0b542e51800010281c10140c00b600e503008031443c0d103280c40e00e40c105c02840c51041c8002000307244401c0030a80f040b10400c0e184030000040a0040c2d03501c8000444600840c90940641141c95848140d005026540c1a542550159074010407a903e0b061404680400401c2c0b900c4408003240414001500c3c5600d408654910914400c400020000302e9454035016007440541042c0400c0044800c00c000549801d00ca0340c0c01c004103d488110300c05054960004801e0114028003d041a00e031402e0f003040130325003000100f14012150615129103940d40b07408859010301255500400030001081081e00074400f1941120400e001c0c1450b100e0f03141c49860400700240910310014100c0340c010018814440c40c4500500303813 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 135060836 1250 135059586 135059593
    0x14010f060311040917040b12180d0e0a0f120c150804061505031608190c1203140307170a0e0d0806040e0d050c010606020a050a08070206070b0c09040c02 67
    0x10340e1034080c419100b41c2d20560040c3e6480a2410510060302801060040b842c0400c2d83d4507500e03500005d0007030708040c16407001070b01c5031008101d03100c0c44c07200c580554040c504010921003d0410040354940c1e508184c058019229034008690440702c840c0c1c810144c00d11110202500b402d41c500f03003c4420842d880b0501c1000c18203d00103c441d03000100c5900070350441d038041030304641c540840c000c1c2c8003070b580001d5262241c0c1c1e02c17000b030300241240b020b400c40d034894095803054080c407284c48801c5014031400905d4000da03c602030040c2d03441c8840d01c0d5040c600a1500061011103080710350030790741c0256140c201003018400702002100c2c00e0480716501800b010030a000c201e00010035161380d07c41c0d0201083c01c0c0401c4100290350358079143d0284041030f032040c2c11500007503204400907009134040390202400f5401c0c410042070140c00054241c3c6a954400010b007031030302464540c0d41c1d0580010f04200d91114003044a034002c120300c8002c607401900c501300d105d0b50702c2c0092810442103613030484002c0155007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 135062086 1250 135060836 135060839
    0x40902180418080309121803010c080c07060f0b0d0c090c052106041104060309031403040b1b0708130518060a05010c05010e0f0303070f0311030109020c100914010f06 73
    0x10708100e002030116603c281d000f40c5913152151220700780020862031007a680e001003032044e420690300c3e461101d019804e900800c0645052441165071200444100d030301070b881000300030005071544c1c6c800d59000b24603403000a2040e20900010752500c0340300e18281c1d107850f0119028000c0321214403030040c48450900303100d460328004030705829420b62a8032019552030404800101141c84680140c284410280c21859549481c0d01000d03004104070358050340002e106038a40d086607041c080480340500e81040380305400d540d8071448482c0d1400071000a1810b29000c0c42500000749100d40604442428403410305c08003400c10741840308101d58116904650204d105c00e0122584515048206465003842c05101d80318507414018050841c110100c0d00c58450350000303101400010002d180a000280d54034945900251012400d94917214803a2107048003c2004001300c50702e91340141150007080c416140d04501d6090003500302c42c04ca001c1502c0c4d201d80c0700e84101c0140700071312440300004214503003006881d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 135063336 1250 135062086 135062111
    0x1103131e03050c1c09030f03050d09060e0f0c1c050a08040305100e010911040b011b06060603050601090825030b0a05090c0414011202060705030c0a050d0c02030607030f0609020409021804 82
    0xb2046e00c400780620001103000c4050620880803103c085050003411710000080b0f24000d001080044c0f60003035a4022001c150400e014080b4010105010041480e00f036188180c1c099680003036042000c131a64824500d00b04005075840c4040c1000358040d41c05898050b02c418940c80c280c50b030302c0c03169480c0c81c1d141c44010130002d00140c1d060404458152000680c40480000507078a11341c1c082031242e40100c00d02c030083c0420000d42c0044d0261003ca176014002515200019640d4000600070410141c000188558851001c05048543c0881170b591241400340c1d01c0e100c01200036000e84210500c25143c400301b08071200d04010300b07800c4100540302049031440800090308081d206002c0d81030034400d121311b40000c0d9031f10081a1952281c01605803540c8803c5580c4a9030b641e40e50410443d054010018408410313405504e148118030f80203400b4045640d58548214020040c4028500d100382da80c00c00800c070105c003403010740068501c030103006a58100680b03050000c6100181650710482c201240740210 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 135064586 1250 135063336 135063347
    0xf010f020a1202070f0e0910050115030203270a02030f0f0c04020d1d0a0b0112030c061515050408060c031003020d0c0902130510031103131e03050c1c 66
    0x103030482e952000c5269210b500b00c0c1001a41d603c00d0b094040441004644000e10350720b82402151184104d954036003800400e00c080d10b40034466125105c04480b0b5580038140a600250b52000403003410254400c010603541058198000451155030301c200d407100f085040030811a01c8843c114001050350f658022170740d568490101b200c40d4003c0e9000305600101600580102c0074010126403140201c0190115080e40c900c0c4940060302c0800c4c080b4000250500c41080004110390140d0300e0415841aa4803020302414942d849945003007442d1030001480b0151000303182e0b00d00c10300da031f916594520b441d01161a103213010b403030307484099010010702c05200c06880625048a50594060a11400f1402d0410401e03405501042d4114000904c81c5d24030030701d507c03024003a2035040b5403050001c102c4500403802c50300c0400f000c2c120100b04101090041c112041c0703481400b44900c00518a0b5484c000c051500c1c800082d908501060002c01c80c1c1100c1c0d201400315880000f0350303028464442c980e10000810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 135065836 1250 135064586 135064603
    0x50105030c0f030d2f0d02210703050a1106090d11030306180705040308040e01031505190203180f0f1e060106030f0f0203040c0302010306120803060402090a050d0606050f010f02 78
    0xa000b03411200f043c04202410340369140d1155801c18000c0c1a540d104456280d40b02c1b8089080117005450f8802024400050405400700517018440d003030481030340d01a603843d4080710900060045500c041c0003080801c020280c85491224040c200e035501c081c101802020f40c501034075850b80c005008100c074549945c05c00000c200030f440b414006130744800006030355500c43c0f80c201401071800001c002c82d4590000c0f600a040324460b40c05404004a01c80d120f608607002a00c80d00f44488100081c150035841c540c01950304240303003c0c0c2032880c3c100c04600151901e483d82c01544581e4001b000c0c00b0710350401c10721008500c0441003205860341c00000d06a01d40701e4605002d100181a1389550401c0520b000f940070903103118034803508561f642802d00703110044a8051108030f0009042280214010256588003c44594401d00d010f0840d107518080002a400800185800821042c03001079a641c0322084011080e0040400042e0710f420034083c00100382c411250141440780c906200c09020783d00203902e54 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 135067086 1250 135065836 135065863
    0x70803061e0604080f060106030504031d010e0607060504020f0609030304060813021e030610050f04020706090524100b070305070201090b0a050d0501080601030305040501120605040f050105030c0f03 87
    0x488480e81c0002034600c0c0c40400428640020340480c012651441c00940821540c404030112190f40e030345c03120101d0664030704481c01000104c0001d0070312188001b80059001411050500d4800c43d0213010100e40c0d980c03c04a000d40e030f156120410f000a40c106503c032240c00d40c4050314030510303042c1c0c5200420341c1c0388241c1c45403004002c840c0c40040d05806601125409141d0b00400c2d055008102500c4020190303c803044080c402d01642e00844c0552126100740b00444201400d500500244131081200940003944141c03001912411040c0025406101043c190301080206000d8100124007103c41200300811001c40822420820b1004580c81b809550f886941b516000da5107042520040310103104a80c01110441c0c00070030701c2003189800801a02462154a0080002e6a46c07010442c1e0703540301c28840a00400d80401051229501c1071801d200d00710300e40400840c1d500e60300c00201e01100c00c8501c46540341c0e60f8071401408a45024040c94a40d00d4044500141542050300066101d101003045113 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 135068336 1250 135067086 135067099
    0x30307080403031b0c030303060303180f0b091305010e010312030c05040504050a02092e020c0d02210f070e07020c090c0c0a05060903090301110301121b03020d12120207080306 77
    0x10b5078901d1644c030300340000d03a6111440400070380d540d1501030302030081400708070b01285008d0024605d95000001010455846134581e496852502400311603075400044000d80140f083c00100d250b960540c00b40b40d00038641d41c3d864680702e40c07460800520b181e01001030348007014203005e005240719030312000b550240c9030100e80008850b100c00d910720000303200e240a07139030308000309891403104c8040b070812034441c1c035080004940c0000a6000100e84941203450a603501402c0c0e68030f20f0f0302600b02601d04c0503a41441e1004d2442c1e078541c1740d801034540006883e08448030703486088144280c000e4840b0b20368018800d40001c20403a146100020b04a00c002070045151600101d4006080c0340704124803450690808151050b40c180705003160707166400901024000d60074120001c05400594080b00d0480d10806040d01105050307503659415480c00f881e482c00d41c60a943d202201580d15220454012803080030b890190000401c000703080c0b2601862004502481031090001040e510804c807a445601245e90 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 135069586 1250 135068336 135068357
    0x613090f090501050907030b1f15051204111003110a12110a03050109060e060603070e010323070306060306060504030204110f0c0706020f0309011b050c03030307031a03030708040303 80
    0x80401011003001c0600103600780780c14000002400b082c5881542d028081c05241990342c03410500c007202d054800b42c1000713154681d04002c0e10f1110305802030a041c842c03074524a05980b0440e0b0703000d202420385090350501c4d610504490146000768824000d50154201403000754010404420781e4042e09202d00c2c14020442e074542c0e11070b441903105601055400fa5219115455040028000e08090260400e1145840f101180312030210513003601c140310080609103175680700c85040705e801000001e101e061540307840c004d5000d88240c3c6031035207142c4460210b403089880c201b0802400c1d900d00340e0240080c1881c15400b84102c0360b100e400c4030296178054a0101c0e800e14086e0000c1540e2081c0d03a0b041440f0712022440c200080b8010403a203044901c0c075400c480314144101c0c82240c880c49482080c0e8040381071110761108590560003004400c81c011401d03601c4015440000c0f030305591084502c440004ea8070344003602000b081400451040030164000c505052082e40c84140600c603601020f810302c00352138a0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 135070836 1250 135069586 135069611
    0x9011403100f0b190f0501230d050a0c0903080d11091c0311060f06090406231008070305060708090304080106090506090105010c05070303051b03040f0311061309 71
    0x140d03141e44000c0c5030381080b4420052005000510401c50340611600d40843e502c040580b8541041301030720202d5451000c1c0600d040e00646003480b03280111004d400b204081004144a44d002500c0f40301c13a940d00101c1c2900d0581c42c4c41d4101c400280440341403140ca00000e00c04681c4440503a100528100e200048a449180380310543d80141c85800f64465030340580c00f03154819914103480390b113202c1d44a21003011404168152680c0040710030a80300c00f08a8001041407420915075a080f501070324000840d14052011141200c0100500501c01160203042c0a0041c021452402c000c041401c0500189821030342d5058031000050030490070001d5940100780b0201085c001c030350007803903984000c114003655004140040c0c1002c8410511800d00d0034000a46540180030203046c4542c040054003d050035a60152805c2d00140341f011000d0300c41035102100c04404200510207889003413101e0a8861a500d440064600600c814134020281413000b40d040021240340001520703580a0042919518200c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 135071942 1106 135070836 135070843
    0xf07050d0b0609060a0c0209070504120f050c0901080a0308060d030e09040c18020d06050409080307030506011e051812030f07020f0409051f05010509011403 69
    0x3000305a106a000c1a0000c2c25035051030300303483c04138956801496aa0012450300300c0d816095141613204168004040c0c6000e80c681800d000c80d1741080303d101c510040021000740c00080410000f803001444840c00607065400943e503600001d40e59814609043c0d0108a4000c045000c034204004001e61554154a410800700d180109102040b40008c0040d21008014000494240c0e08180f41030420742d054500980c403202186001c5084410b51f501c070902c51850310710107130b00217904032040c0c03070b88107084e0304002507603549400060358a0b4240c0e00002c1034003140340c1e1042c0c2440d03800c10301810200145490490040c44000140025000701d00080705d29940706215040b2000540f10050000e02d20182c9090480198000400c083d50100d1204070b4240d008468400401c0724034003281a5016140700007402694909004511004010300521201c14540e03541c0c0602038400300b = true := by decide +kernel

theorem cover : BRFrame.Cov 134892086 135071942 := by
  have h0 := BRFrame.cov_init 134892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 134892086 ≤ n) (h2 : n < 135071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
