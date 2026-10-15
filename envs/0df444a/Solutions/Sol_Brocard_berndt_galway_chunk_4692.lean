-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4692
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:26:03.041277+00:00
-- url     : https://prove2.me/submissions/e784cf63-8d5f-4cc9-831c-a60e8fea55a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 843705035 ≤ n < 843884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 843706285 1250 843705035 843705041
    0x1090b030a0b070807110c0f061309020d02030f0606032214160e09030702060d0b0d0206040e0609061f0809030409060f150e0112020f040b0301060806031005130b180d020709 76
    0x54500c7d03000a40000c0c2166605040084011022210555212403c00c00d0754400015948680d42c0c00e030022a0b460142d5010790701452240482d003240010950328070b420055540300859140380300c1c0f401052603007a11000c41918401c040d2041c5005201c90454001c614a0154031907500c2c14000b0041009000e0307005906030498024294500450070444554000b80080c01411250243c03203a4072011740c40f0b44d90340d400d401060b440d00070300b602d55615168030004c440703044100c0707100303006810a10102c0d080381021000020740c1c440d04034403c2038000403104100c0d4000c00141142d8001d10082c440440c80c201030340714010080940d80424045240b81221a05440c510001c0d05014440c05000074407050f40c08c103182c40044285203a0051f030310041e58807000014061030304604030441020001003170468110881c940107660031000c0b1444440b6100050003500c00c1100d82c81d07002c0c4036840034400020b2241c6499504140d1680c0214880720354900107031b15001c0c0c400100801640301c0c01d001c010018182c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 843707535 1250 843706285 843706307
    0x3070309051005040e04060212040f0309080304030c12061b0e090603030901200a050a150f0510180906020d141311060a022b0e0d0b01090b030a0b070807 67
    0xa0381d1104038120642c00070f001406140b08110404c0340403000075003001115411200308882c0d00400c13080ca4105414250301c0314103580c87c220085103c4500204a80100000380c40480e6403100c0c511a04a04080c0c1c03108040e40c030024115403490302d400260001403002040e07210320302820744e2120034020311501008500d00c0042d0200340030b41c2040000b811581d9014410400641c10014a54201d440200c80c652070003580d54400ba015003e0102031404028401030580c0103480c14103401c1c464660100c4a4204840c000d1350b000034926403180081121400d8030503455030000c13160f00005000e0045455603800c0e64051506072105a585542815141c0c040003105500702102c1c0781090b941040590b00c10400d0180e01503118401d050114200f11410b100704616044d4003a0107803040c441008080c540c20104250000281c082031140741018140d00740788556125003504842030889507440c21000a006140351134040303405000d90b08489010031401001c01d8041c204690b41c0804618201c800105564048 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 843708785 1250 843707535 843707539
    0x140a050a05031005060d0c0308031602030a020718091712010b0304050303040b0c0c0d0305060312070510021b0706020a111206280e010b1e0d060b0a170307030905 71
    0x100e00c081c841900c001400654501412000040c140c4960f0002081c650117a040107107032514586c004410080e401014601036a240090302c0c0160f820700c2c0d800cbe61240a000401070041c0d00000041017190031503507450078804045000012a03a590342c852071016006580d03101c0e01580002118280c00000510f981d00402c40442c03186e00b18102581d8050312444040d1001e0aa4180e40000c6030075a05e108086031096520001254034080c82c1800240252500b203981c4d510901507410071345041c001c000c04540706030394000041d004086282d580b6800a41040300507020b400d5011003003000454003000308802030081c5400170944070990f881e0241000d4078440f41c1c0360290108414190440e90000713a0590840206080320301b5501080b05561268680100023052190610905118082041d40010315401003503d11201084050411220801d802e105054010100040200110741e66501c203c03400c220042c8a801c2c00b95940ba1000546554083c030b8201a402c00110141010b8015410360010082 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 843710035 1250 843708785 843708799
    0x1106060109030b04330f0501140105040308130b0a0225120f1406070c170c0d1d040207030e0112140c0c010603170705060a05090309060c1006140a05 65
    0x1103964103080c140d00070f0002041145d1210562804185941015040c1c1265440068600040380b502e00040d041601d60384068514000000c21480401904840c50380010f0b16914505455175440306c5540d4070107a80101e2000d180f501c00700341002248020443e2a040b940202119881c82410159201103404604050300103040200001001c0844108060343c001040082004190070a842100c07079940608a183c0203032403c110050b504030036020911030243d081d0b0f00c581c1c5503406104841d8410b50400380c02e5640a0034004500754806e06107000c50031074040442000300751076030206041c2c0e00081070131002b25006810502c02568803000485880c90300c80021311411a41e0007001042000140110303981110014048023901000d4200400855024911049800000384540001e80100c80100e4444c01160301041c000011401050302811001d0b014618102014003000425440406803003032600076880c1105420310144901c1d4010012490340d0490229818200403100c00903411903441880703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 843711285 1250 843710035 843710039
    0x1804180b0f010b090d060c0c02120d091d0f1003060203090705101e1d0303030108100506120d050a03060b0d0903020f0a0804090f0207021003091e0305070b251106060109 74
    0x9640641c83c1021034005c9000540004e0450040720823a41c0c403000690883c010500c0350302c0d41c2c00c0000e0b040115501594a4200f50307a00d42148405c01c6100300d1089000400d6800803d1180b405002c1d5940c0140ca036010070241142d5a5480c401a40c000300da0307182064004100130001e905040d81120343d9100c00d45030000b403c880100841d04001c0c10403a091042102441b0800304009015902d1500b80c080107080ba6241d41e0f440b08885d40c0c0b21103042d010b450f51400c2c40c022424600b044410035043c1501074018006682c07015800b2104d603003010566404164680000044c40181240204644140300354081552609801d010b0725080242c201ca030100c1d80200344410104050a05a07000d8496500300410030b1031031040c92501034010410046d520040c03003031940001a81603440051601c2c890880c99080b044600340141c54840c1c66540540412401c01201000810001105a000f040b440d600c1c0021006000f00c4054123106480d0f0a011031a100c0068006000c10850039601190902e0000c00d164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 843712535 1250 843711285 843711289
    0x302060a0509030409091b06050f0f0a021203010611070f271508060a110f070b07170108031b010204060f0f1103130e0703060b1804180b0f010b09 64
    0x8001000058100e6565010412240090040714020b1030103130720900c0035131000d052820f00c3c0500001c0807400c210f02c621000401c1400790084e0b0b03070792860004203075080c04c00040c04100c05902644102c0114051400c0925101c03000761f0186019041c20f0399644580c048203a40507162050f10b412140340e8585004040011004240781c8500c02e00c110546500034202e1129100302800c0000120310101036064030204100c0390000c0c2d540c1c030802d0680028004144010041d0080c0d10601030301c01c00c2102e04000305000306068944c12900b00000707180081414030b1812114480042c203801c44440c5820002e49400003040b0407020300045004e000c000c610b043c0c038010014184074068004075082c07243d02042c00c80d109006e540000300505042042d03131340e90710000105c04d41c7c4c0f500c0e5019009100c1200d4000c212440e01c00e104d882c0a07541e508540c02c1c50441401d1241840341414030003070782d00c141c44005400075500c00d1140b542000e4030860041195040089004010030700581000448034000c0c020b540702d036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 843713785 1250 843712535 843712543
    0x603010b03060c04091a0409050d1b0210141926010f1208070606090f0c170105060c0c130b0f011e03091502070f0c0f050f0f0105070f050309011701030302 68
    0x1070f06290304c00030b18103100002c5c010409a10b401b506900500e41981d14041c07000115031600c1411155645007030400c500c1c00d0000c0c0c04902e003140a2b41260544400da00e40703500074811b00c02e418540d055802e04058030b81c45101c80c400504e854440020380d1060200d1034443e50310007561103001c0003440101496042c84007400008250744502c6140c1581409090240709120003110020390704802c0522120b62603504a40190203550700034210240b503d81c2080c030082c4650f2002002803200b042141883c3d00c1c107010052036030401014008a0f00804440c54290740c0d46860901004011480115410740140c0802580c900c4208459044c0030303c2c0000356441c0540d108001c42402c07041d080c0002d101d195803c00081643c075598541401c2e40c40083c028080c030000c2d03e00c0f044161300c0b4a0100000c0c6483d505e03038801b50203140c891150000100e22004445103001d07880000045810300d42a0304000786903c581070481c5083c0f500703031a940c02c0003d1810746940d002210f5003499401c800890640d525546d0000d5503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 843715035 1250 843713785 843713789
    0x7050910050f24070f0209070302030c0313080f16140f07030609032606041508030a030e332a0306010903080a18080f070308030703090b010e0603010b03060c04 70
    0x414441c0403014140703504244060341500c428101d030f40391a05030320301c2d20302c0159940b464281e12400c3e40ca4000f464440c428000c0324070516904440300d0940c0c64402d507a5030640341c041c0d011140d201e000c2c0310b802170985401000d0b114003030406954200044032401d2800e11102403d01c0b040f070a8108102e04000044005002e40c1141da00410000d0a07900a0800312030b0300900810518206488480904c60b0406907103013140103c0702100c00b0840002c0302100710b00304800c94800c40d6910b40003800030460303981c000e61080d00104201001c6e581c02c003800d141404140301030020784207280004064441c00046001710311642c0403c50390f8980702008092101e040164050240465608600100158290340708901110040d0344c0880c50303c1d101d03100070001070700c4032039803402d244103e0203003220004107000000744500c0000208005080701504648034001290310081c414405c1c15200c00d002ea0005074040600b07030003055039410701641801c2c1041090b00790383e205604940b0980c030070310030701018803504c00032581 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 843716285 1250 843715035 843715039
    0x41a091008070303270b1c0c0206061311030906012301080c07060f06060e19030b18070e090109021e0a0b0d1d1c0212120a1d07050910050f 61
    0x1110551302440700c5440350000081116401c00aa0014102e00f900c005030524844a4031031b007e1841013444003000319031940c5001401030344050045042400e00d020402c4101d6403590002c19540b43da0300400c45154010b807000103040c1e00c00c0c00100302c1c1240c40c400d807220b055400e1400c0d071040703024200001c0c9008001b86c080c1d4240c4400017040c40400402e64042c400c483d9000c00240700e419a20000a00b0041a40540034043c0414007170150340001404554401c1d82d41c4011400415107034264800c020900c1c4402400c0715100b900c13404203804810200b168400e200346e000202d1a51010b00c103200194060103081c500a107a500c03400d1840f91340e0051020141d0b0641c0307003041d8a5103120705100000d00f44041420442c208980ea000300d51070004503a030b01c0ca5001982c2e09010720303501400c0403a600c0084d5121b000503050144140100410b40c044901c0c1c001d50007150101c1d0040d65081401e0880480800e05506580610b400300700130308041861b2944200500c042d9030007036203070402045402c100490114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 843717535 1250 843716285 843716297
    0x61303020c09070306050d03030c030b061c050c090a17010c2c011b110301050f01030b0a0e12160b0603071206051f0e010905090109021c02030c041a091008070303 71
    0x1d0f074250300c40d512030001031000034144280b00c0090300b0050010402000c1d0000024184420140541014812a5548200801daaa84011140385900c000b480c024040041c0100d04020329205561403204c5030010b8448204a00341401c0507402440c21910b11310540c03000d00c407442412002e0090082d40200007112100400e14049008000413103082e014030b5504c01c13140410310074140501140003901030030b14000380c1c001c00c40b42c0c480250307041f8400800d200003000c42800d0f90000b00000c0094018407000b100c82c41c110f64952002213080c100a400800540c429445205141c00503c0550108290042d005034080e00045040142c0e40003400d1764868050041501d40010884a03c2d2103c0d420500400920700881102c0c1c69036540041c00c6000e10506d038001d81020046092040e06210341504a54014081e402864000031214408410190309aa050192000c10801510f543c0201413420383c140d040c004158100c201007000445c0e02900158403840c10610034000d201c0e0010b0740c1c0341540e8140c1406 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 843718785 1250 843717535 843717541
    0xe07140a030c0e1317042126073009050f041a060a03090b0a1404020405090a0213061502060c041406070c0909020901060503160e18150102061303020c09 67
    0x1010404d6442c48010902d030741040c1c01c1c84904003408040d0040e50850720004001188031811000c1c5000301d01070107001c01c1061140c04000c11031041a1551968a04ea001c0b8149030840d141c111901d09c510400c401c10309071400c1c0f03400c00c041c2030101c409044202414191070007800e100c0030864a030b503406001401745944000f0310a15600a41c085010700e14000d04180e9502d0348110001d016207103000003180c2564404000c07035800c5040e0302401c000c564400803a0f4496954036002c00015190191802106004481126003d80c9031282c995684280211001c100386241400500c81105017208440c00c40d0017050600c40c42e011100c040b1000c5407154401504404142000034529101d40d6900501114000c41c0c00600d40c04180c0140303a020f130003182c46903e2aa660312044e40c0078881140d0201110b06400400c50141740038a034074004c140d1025011000c01c140e40802c40c0041102517407036540b00030780c04c01c200107290b03410450540d000c4030f810034164840700071340d9020390764030711081060f88502100800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 843720035 1250 843718785 843718801
    0xa08090a0504110406110f0c0103020a09080303100519061b02010e06070c090c0509010e0919060306020d060909020105190c0b16020d0302091c0c090e07140a030c0e 72
    0x101030140000800811102d03c2c481e645080319401486108041000c442d4408802e07680454242c4003528290003601c060030420004400952040c807400007486040c20b00840c16a008101652080814040005100c0c3c00c00d010002500c400306280c9400140e65501401041d43c00004404070040c0e84400c040320900e22700c01038640160b03d1a4050300719101084c0d0009102410f01d075070040b205254000c01c8010019401200c4622602961b0b9021841210289a041c10544000b0751300960b400b500f040c0c0300408140040564426602c21b665294012810052400c954402c0c00010447c42c40100007540e503a82c00031b0528095140d1440c01804122023050f1810701a490000d09243d21849101d99490f05100340d440040c00c484602c0300601c94074010311100d5009208460b0501c030000c00b6206010744007262390031844106107084414061f20040000d6106e418000d2030700c02c40071180603000e00c1c1d05100181e5240540d69091520600400100700046101c000a0109a841e9a40c2d40682c1d5528040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 843721285 1250 843720035 843720049
    0x120b090618040606030b13031d06040b0a02150a09020102060a0c21020c1e06070e0901091d07090506130501030209060402090f0a06030605120a0506010905090a06060b04031406090a0809 81
    0x1201408015106c0d04003e01e007404d0b80030008142c3d1090310350003d85d202c18078174081c1503251903003101e0300800100b109209180050005c0c04103007180384119480b0312402c42c0b04d8091321105480040034591140100004c543c8c050002030f0303021400b40020480d90500d524014400703080005a03480b86c041001080c0041002501125400080101140c420360401c82d04e400c01078090180c030070168001c44020a070200e1151451000310503006120b003036240d081448803001014404a5030113403c10407030b10f00305110707024800304005044d03241d4005402e04d045014000025103d44180400910b404014001079807081c040b030b03030401e0f03007940d0068aa540c40d40c04100504003810b00207921440f00074000541ca641500311609441003a2003842c0f501000a40340b51361024414002000394002000511030001c580d8402907003c203840341150011145038440d50304035076268210022280001400307200f403042104e43c0300c6004103648000c00c1180380c651000e68641c121074034005e083c000b000400c54840d81d2011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 843722535 1250 843721285 843721289
    0x70306080f07032303070c090c0809060f101e03050105070207120b040c030602070c050f03150412200f07050d050a02040b0a15031a0607051203040804090c120b090618040606 76
    0x50210b81c0d9414403820b0800c0c000e030711f40c80b40301981401d10109220341803080e00700900a6010400a0406403103003011a810301c10020102a84110310703800000c0e01c2c48841401d15410b803018021440c1d11b608500713143d800c1d150000e0894003950710100c002c100d411800d01c2c0e903c0e402e0740c0000e40c803500340d242c0c3d26002007003444591000e041c0d03d0000c01c51100340081c18501e00203e03007040701c64a05151058040c103071110f450710342d005da0b0101c0010001d0089982444107070000c80c100d01e4400c4031000c2d8100810710858445231480306951201d003000179224000c001300005007108131030040d26240c055a9060303903105903100081c00340d92200e80d440301e90b489008918010f440c660790409014030040d14014018500022840d403030b00e030351000004050601d60110b680550308980942158042da0f103814010354406081110302500802002803600c1c1c1d40d105074413084400395103001c403949415143c0402d1b2108404110710820100342070016560700c0c030340d014503101d642845c0381c51269110300708200140129 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 843723785 1250 843722535 843722603
    0x31c2d17040809090a0e01050901060b180310020c070609050a03081803011b03020c07050d02090402010503041403040f15080702030307031a0607241a0d141203070306080f0703 77
    0x1171124840c050780095200106880c0204510707920b401b907060a90395203100b0b40b07a80900c200b0511081ca0f0b826101103100e604040d04840449140200b10800c981c4903400360b00060b00810000e1002544c403204807801040103c400c8040a41940c407008550711803007165080501c8160216a9142c030203401401426920300b00e0702c040380d462000b014000c0d5100300c101840500800c580400e082c6040301240c02c42c03580141980c3e07031036980d913801560158009030042d01c0c041c402d40e108462419042000300007800700c0740c4003500d25500d80151507694103e00c0b404141445040c004128110383c0c00420703607a00c48032a10b0045000c400c00c0d9120b140c0440d07401380280c0c000f03000259081c180040c95034401035045110400600f0001003459450480314803403283ea01c0c1d10500038961000f40348c01c4404154041c00380c10840140f8182000591030002007640005002c40084100070b2915054482c03e0b0003003807920041d280e9014124076054442c841400300a00010b1885e0022141503801d8682a03940011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 843725035 1250 843723785 843723799
    0x7031106070f020c1906030203070912120806271f170d0c050a0303050c0c03030a050633030c0f0d02030a23040f02031c2d17040809 58
    0x88004000c20454a0028802c09881204082146402e024aa020503101380b03c0040c0b80043c20207504501950000d0704d00c03030400220b41c0c000b04100300306500c441071042c4244082400c00c2c0b00110091301c003c20040001d84110640b4003900c240b117850030b11030200c583c0d01082d0b1002c15600e00700032018a910240c00e88140d410030700780200e81c80d000000341d88000c40040b0204c40e081c0c4450441143c1d0700101e00401441500142501c80c0042d009400c1140c000c0d00181e4000d050103650000c00d403461300211043c510b02512081804007504154003208590a2500c21080d10300842882948103103a625008280440d000400602481100d3f400e4031102040307142e4903075446000c2209203001e50016921a03008515000c070381c004907903007903465000007510aa007141181c3c0e01c50311040501140d100050341c040c0140b4000e5007041c2d030200461841905036032542c0090b90300540340c000c50200161000f894a00d180c1e80fa81d00b8854010721200152241c08184c107026580303a145c00c8441c1c3c0100c0f0259604841 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 843726285 1250 843725035 843725041
    0x90711011103090c0f031f0603080a210516051b01020a0801030c0503010c121508030d0f0b0405060105030112050a3806131d0307141e0607030207031106 67
    0x45110300950050f00e0f180d084a5414404204200d18410207041d0164550300c45035001880c807000c000742503400c50040600080840c0e5948405135a5030001a41c1b1000810014190454281c034001e0f0200030041983d0800ae280b0b0800742d030a185000b805101014030074040341071103881400b060b20003561501c0384000d544504000d84090501002804122a086c2030440085141d060510940258034110707a01d040e01c14120100d20700040550781100729080c0c0341c03100c010a1480003000202040d590142000400c2440f0901c1c01c0100c071103042c03410b48aa8188003d03c0b407103a0344201900d064413811510404c414010b40b80841c980244c9541c02010200c403070300c91a030381102d0202c28500003181c5040028010024195611120b4400c0310300c56445058a501c0c0400380d500d03544010900ba06005003045551100401c4a02c1d5800c030001c121428208601001d07514401449558400c0101090540c070242c407821030103440b51001400c860406a012074808103061003500e02030284800e00050340c0e00e0382 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 843727535 1250 843726285 843726311
    0x60e01030203100213050f1306030506070f020304050603010e220f141c0509030f0303160e1008070311071203050a0b100806040e030903120409060e060f09071101 71
    0x100003440164030034050410380c040d00c0212402100c4800440e11070030810103040c0800c0058814090101c5034000c0704c4040f110981450500c5080f01850145000384918903120f0b00007003041c0041220322046400500c1f0400c2503460f800192815218400c03084800d55490507223000600c4041140702c0b8040c00c0044604c0144010580d600081d6400340d6034419416030384055807541c030101000c442d0f8100030305000c00102070b8400c0703020341340e8010000d05464410807040052451038105591500904020340080b50384960015030a124100050307c1202401d01002d002400c00320700100321000f40741c1c99510100250b00c000c41101d0183e0b600c00e41c4090300c99506080180113100445642000c03601e4803d00d1021454400030070940c0324156514680941e072003d09000c080c04041010100b18030050209407010f0781c0034819041c40c4802040d140b44c840746048048015501d0581c88450048003001c2030107015218409456443c0100350380345030898843d0340e401c894000035001120030f11351030803400c58517030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 843728785 1250 843727535 843727559
    0x60714181f1101110414040e03090310060e011e06050d14160306050402160f15050c071502091e0f04050c04052b0b1e07080123060f0c010f06 62
    0x32030164020403001c00c030f01d08580130030f00c620300801c0d0194007500080c0d40703135180a1b04030050f0415280240c90038184000b0129250000142500081e5526000c0c14000c240005a90a00601c8443d0704a4007442c028540c40d803039038185005441c1040b0000584440390520f64014612485a2070607a580c1403814554a500f50a0b4000030744d00040c0c01d040c00040c0c1d40c0307020300a43c0c8560748280d0b42c1e4040c07246503aa45143d50f0310204030490308192006941070a04581d841414460390250100d1669440c40d843d14000719290b00c01e1a12401d48180283e0640d80c6840c94080140a80903011400c4031442c0f00004010700d900d002c0c001e52040c100002c10030a00e604e10041c008441c01540c04041c01520102426400c400301806460110400c019120221700600e091980012240c00e0b2020841500d40070110281c43c100e60040110b130b0107000400007030302c4580701c2e40e10420300c0c404c030a00c1000600c00010500d22074959003484403140071450900000083d4448090152091020007416549406416507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 843730035 1250 843728785 843728807
    0xc090a090b12010c050f0d0603060f02190c03020a0209190c030b0f01091802280c0308060d05060a1a0d20030303010e0c1b01050702010509060714181f 66
    0x9244642c007542c6800c04140185842d200d40e07511400e0a00303185030b4080b0b140b9086110b00400d1552078000000c0403402a1141070762445405030301694600e27010700743d1100029143c7c6180d04103c0b00e1464000400c0d400300300c44000d507604560b1080240c0300c102d142560244891880354070285080035601849815601c10040c2070f6007030310342d20326818a90340150351b00069449513000f844070f1030700c40c20300f04108ca6000300306524405ca500301c10b10001c140f0407060102c034100460040b0f14155504c4d024141c112035180d0f0301071012201d103103180c0c20507903486485000c0604051a000e484d1564099080c194420b44400d4200181082c500e202c20340c1011807040924505408900034842c1c411202d60402004503410707a9200401009662a21b03008400690320440e541c0d680c081030100e442c11148428020540101515070010846080002ca5181068405803200042c0411242c0d0380340c9001c00d0b142500c41c0c6c520410119080701007214003007444030f40340003c0140301c2da11914455010039000201054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 843731285 1250 843730035 843730039
    0xb060d06020702120f251a041505030118020304120315090911150306060a0c110d0b04060b030c3a050607020706030501050f120114011205011a060702090c090a090b 72
    0x79078191481c01b810342a981c54490b034141181c8103a0610543c01010f0a5071212a03d1011807890a9603a05904411204280d402c400050000004100c82174101c10b1040729a10002c03000c43c40c5041640d184651302a40c40069010b041d1140e00d80300d41420301c10642d0000309040d00d0b00780a045a586412580b16658043c628840c602c05c0000050001c2510700b40c900c280005085540392a240c50425540d03500440b00c00c603010068603407101c016446505442c50000d120f10000f4185007003c1c5840010b840c0c00b03034040390095101c61408644c5544d004503505800419000012400a1241a4810b00b500b0840c800ca1000414200c2004101c000600d29103d8075496080d180c1c0f150310f4050881c25103400384261a0f00c60000320800c2c200d85030400050703c000054000001d051036403906001c040315026849601c400b15282001800d02a080c0152504400c9198800a292901c4030000e050750041c000042e0080051000083c20550860110ba01c84034005100e03070a00d03a80c94403244098407240b01198 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 843732535 1250 843731285 843731293
    0x302060d0e0f0303130b040f080f030403111f0b0609040501080f0f070b0a0f0216080d0f181a0c1006050103061203170603030d060f060801050d0b060d06020702120f 72
    0x201c45100481903d00070300a20017010846443e9440ea007500d90400b40003070380c0e14400341c0401d20004107100c00408110b01002110703901ca240c1400c0c0580051483c0d600d25520b500b0483e0000103450346e01003034034040e40310f00c880080d09861082c0414140c0c007586502a41003840d203000030070043d00c002003100748100224112180d0304ca00c2e0704401d0300d8051a00c11240c04040600c04182500d01170200034865a45610440d0b2605040311200c100c1c210280e0300965240d007007080da40ca0016403250f03d5542081c55802c05005080e0503a0050345080000d11035028203d60702c0381282e05040e00581103a80922802c1e08440010b001c0c1d5400800420581c41030502103440c1400008000304011a5081c0b042d40603224403400d201030032202c3e54a41ca00818072030740340c0000c1100d52032202d8075110310780c081c0c01502c004129040c10a0409080c141c01a00000e10540151903044001a10ba440c8542d001c001614181e020b40c007149030500c0640a0560020340c441d4241c041c44040d10000294112511840c1e4216 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 843733785 1250 843732535 843732553
    0x60c10060b070f080f070f0c091505061c09121805121507031d06090c011107090c03090204050903090f1f080c0c01020f03010f050f0d110a0302060d0e 66
    0x103103605202e4410000c20003c8240180700c04140010301a202d140d0760240322514014030740da03034124409400f50b0201c4600100318070500140103580b040c01c2c0e1038022084c102c0c03100c604190000b1601d0190724040382e003200181c1b0000c0c0894085400c0811181d074412000c0312814041d580250840c131350038202020003c409600002c1c00c4c50214a40c07509482040068450038400840c3d06d545000700030850818035486006c410800880f04480d903011030100c40c060040d0b400c0c03074805982015a0002454101f00c40010081d6981201082007012035601d000001480e840500701038010b4641134602949c040d28003010030001160100052082c00802c4800351951030101e010003a00ba201c800a520084216110b10007149000e40c94a64000307000760f2219041c441d000340360300d00b664002d43c9400c0498101000420148036100364400c017404045a42501c000010400309181c800d00c42000741480c4c0500c1d81d5407800e9107801001e40302442c1c024024581d224285140400070b070408481c4150f6030320440c010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 843735035 1250 843733785 843733799
    0x801020f181c08090409080a020d08090105150904031b030c0210031e0c0e1c050f0f0a1e140c03101118060d02040806100617010e070905060c1006 64
    0x1180d0b40c6000d008068550304100360303d4030702e07881d009404c0c1c1541080d0f0f90b010301404500d1140241004801550091002c0e00403140020b0141201a00c10b070f1b001e80c10001400440c02e03c00c2e00f14810a5015034899403e0b0b84d4900342112080030701c042c40c64000000c002e1050a040d4060540415640203441003403118030844012412110b2100c4000c0001109000c0c445161840da000120082410714101c001030441d10300255103c140c4520300000340650f100d22104101c42072040b03079600b100b4640a800041180c1c0150758880ca5026002002800d01014404442c5200d104003441c003031300f01c06c1482c0900c4040c1f15032540ca00340607890520034410031001525403080c2e8003400e10750b070300305088032400d140004010030780c00390360a852035600170380510210a141c3c4152010740003c080200c000c0c00035082903d0400f10802d8942c105c102085003400301e4503003d5600f602e013981165590404c4142d559508070081f2290603194225960003000080c00c6240c103140000c0f4200840003007441001903a545401e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 843736285 1250 843735035 843735049
    0x622030803160503090d0f0903060204120b06030619150b03130611090307030204020306040228030c111509160e10060e2d0a09020a0806030c0d0b0603070801020f18 72
    0x31408a21b9000c0350788010800c1c400d00d90143c21040d03e09000404903200c0d665402070340c03c242c1010150032482802030041c05807005420f9003000c1305402402c207500380107001558103000001d1940e1a02c0d20359440c500a0710500d00414018020710f62542d4507030810541014007010310b03000981c0c0d15402c2916130200007150703404807005c800c0000c0007850650b02e1030382400044d401c0101b02640c084e42c280b291140386082c0140b80c0c05000d100d401d4101c1c4015080320f0140840384440d1803601000300c404040d400001c1c000541144130021403011000981d41c40f4041442c2c00d0010070b03410758405079008001104000e0303d400038001c61200d0700c1c1c0000c00b6103850f4102c070000c10a180d00361303000441014040002805034070015018600f210b407032014525520104608044a5108000050303001130340703008140d400300106030030200840180250301e80080005810b0061044007410195030791002c500c195030204000d600420401009540f24150b0b144482d415411a1484040e074010100c110230862030401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 843737535 1250 843736285 843736291
    0x15010801050a091a040213030b0f0c0708090a0302060a0201022710050a020703020319031704080306040216050a05070f0e0717070c0212071719020622030803160503 72
    0x180c0341600240c500844540035013001601c0e0210380c058505800b580781ca0303500041c440d001d101c40c41d0b42c420302c0c80c1d45007400104100a2001340780c0001501070141d1b0041500440d9032080c0c1006001d43c80301130440024607000c1856100a51004002543c406600e8040d0041d0207610034644901418070b0016403903d1040851905544d400110742480c48106406000501510f40d0148126044640c407036000c00c0c60101c1041044a4038445c09182108160380000d01d190142040c0d840491541066a504c181d10b0101400d540d2203036030049441d21404010525551942e908182119041c0415043c255111800740c010904007481090000c04e42415410840c5c2c0100856510300300e0b0701e030034141d103016400406000c1e1801c000d00c01c0f5a41016940c0e4803000106410014040c3c804c880c500300d41002a0040503658094582118448451000400c0c2c40405455019102d041d90b8103080c501964010440099a9840b003036050008001c2c80340c8a40514132034117500e240004a054610320a6560780412 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 843738785 1250 843737535 843737539
    0xc050f010c050c01230a0302031008030c100e0109080d0204030501051e010e070e03011524051806070b04150c030e211309050411010c03051803070f06081501080105 72
    0x1c3c1d0f62001c582c3d44188014900081240910001d6818144c0050b00c0b80d440010348200294010040c80407201c60035400d400106484030041d0326200b02582c44540700c3d09050b202c05206641d403500070100030029000040d00c240d1110403599120007103842400250064041518158645000607040380c10b1910300d2884034101d441c1c1c1d070240d130303290922004080030010b10b0b260412801d4060aa000c0d10240203080064054003280c04025080102070f001c0100c4007240440744040b440c141440b940d81100882e0b410070300008900d8002c0c81800003040f1103100f0040c3c0140707903c0e861b17401c1100b40998603440700b0341c02d10030350410b115040a51008409071042c60042b02c20940100b50711600c10798218100092240c0407020003403c4c500c5081d42c04081c40b409a200710400c944403404c2004108803848402d10891007401c1407019140c2d191001013150250124040b0003010b556038240c10356800b00a40801008007a84c1d0034030058803000d004018680941d5034101e01e507454100d203066907000b414050306031040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 843740035 1250 843738785 843738793
    0x2030403080a0906060e090606011d13200a090e07030203010b090d03020a0b102105030a1202120a29060a05210103030807020601092d0b04090c050f010c05 68
    0x1030000b00c0001040144421203405948440c0058003064650f0901e11a03d00c1c10058103036840c15000140258071803070801102248418205001c030381d280700b66409100c009007400288194603940c0015400004400c00080081c045a074841182e030001800c0c1c20340741c501400c0005038490320700c20f0301a0b010a000d105100d850500c809503180c100b0b4100c0e0059540030380704444030807810751101482d6030810359001c00f0785e1080c00c00074090000a0040c00e42d03030511200c11034580d0f0210391581901da00030140150704000810b01c0c4a1b040d02115010366600c0c11000450004908000182c680201808030003068500404801038843c10004120622350302c2010748910703e0680b407100c1c215031942c0a01d0062190500c1c0c01c50020824588400c810701961113901c42c4581c0b0b082c1000c01920303000c81680121085070a02c503500e818500c0e95800d965560440044c00003a107074196608070050706984070035541151070001074506000008258a0132110b09079140740c1d049110200450314030034054009026584 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 843741285 1250 843740035 843740041
    0x901091b060f210f05012d0905101a0d0f0c020a061d1b0117040507050d03120f0c0306060c02030714122509090506130311010213090509010203040308 66
    0x1000351038114011a100f80009034216004050a046480003103101561035520700042c45002100c41c18044075400150035002c3c081401e076200c0b41420058018035130381c25110004101140c8840c40550b021b404a83c100c0031950400e83c00c45441608200c40c038401490070401058a101040d100b00c12007007150740c4c050240303241c180d101d181c040d052100102d0640c40101c3c130040c0c4070360020301140303080340c85110b59169007a6412000400700c0f490700b41000e08451008042c132000a20005074201103031800e8a0106541c0c203241001e84009414040d54441e0034200f80032501e48100550181218220301e480c104441d584441c421240c00294440c000c1d01913009000c04c0c4881401c043c100414a0b000804070103000780e01206050070300403980c191814064060302ca0100070210705c1c04907005071541e000d04104109280e11065a44c18024229202d0210001c411030140761044603400030250200c0004d40d900d134418140b0073f004030b60611480d05094039240101d00305c03140600849004036015034407030b00192 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 843742535 1250 843741285 843741287
    0x60501050d02280b070c03110109080706031e020c01091b15080a27170f03070e0406090c02070302130507050405152502040f0c0203030a020c0c090901091b060f 70
    0x101440c8004030b0520803c0000e80d0982c00002415541c2c0711320021303207a291440c94040c050080c46a840d5040c001148410b2040c041c0010720a02250031620300810f100d800113440d000c14150030010444a02c1c000076140180d40f005401444101d8490141d01800d00c40c90f5000340e46094080c05006520400c90a14550151086c5580c0d0b41040c04914001801d0301d41e13400346149015000314807816110710b02220014060001c0c03022820301c0c041c5e082c3d586412101c510341c40c3e29120040000b0b041c045480e00702d00c1c05458650182002e000c420307008000d860201c1801079074501452008070b1040c005e00200c1d100d4004103010b61806180c0a4840c0340c1400d0401042004031910300e040b6140798201846106125460404010302c40c429034014618001a107005200684190750341503c2000e0400740750824203940003080300c2d031000808500507254100403c015041611103168154800d124006101c141e01065202d2030316141f0030719104400c040340c0480114004a0380c440d070300c0803a0850400708091 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 843743785 1250 843742535 843742579
    0x80904090c0801050f06030706091d0403051308010501230319050a0611071203050708010501080c0d0e1b0a030f03031e18030e0103060b0d0c020c09090a060501050d02 73
    0x460320480344451410b407101c00250869804417a034950903280c0c030b018001c8074203003441844054101403500c802980d040007503401c10714080d0045000b10180103c00075042c1403145090b04e01c000c1c4002501c80145507910031040c040d000038014030f0754440b1440c85441000d0f070700303078201804a00060007500614114520707150085064200940701c0d401403940c1d142c00186035102e0882d01441c102c2540d903d0785d07401c0c141044400305100b1480c043c1441c00041c0580f480c1c1020410341100c02c24641180203aa491404031218024140c4a007800350808862032016080811003a0b41400d040c8010320701643c49108210109445105c054180e00414001c1c0c2c01207486900b0600c085d181148011a0341c15110900004442c219803c080400d02002c826900b00f65000f6007003d0171202c06d117000e0011a0410507120541e00c45e80801402c01e1f03544125042e4082d00134082c42e03d070380600a2104d0011703c0c02d8a000e40c1c841c0080c14080fa0140d00d8030002003403614051580c04a0303903402529605880304c47c034500320b00c3c0b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 843745035 1250 843743785 843743801
    0x121d0f0409230c061c0b03190305070b0f010e0109151205030c100e07060c0c03050d20060c0a0810051512010524130b0d1d0109080904 59
    0xd40c58012200c0492880c52030181d42e50662100303800c0c02807101c0303041801d02e451140308610544040009a540101405141d6078290345000006451030300440041d207400e4075602c200c0356920540790f0400600d0780190142c14064003606450382c0640ea112081d0006d04424003c50520408500c01440f903c107141c1e11000b200601d0b041d18603240c03034441440720462003114104403a41c0e4000107080001003428800d480e1040030070b00083c020003201d0308480d919940b5a0007a0320030071195180324000d0000c070010309002140c10105440c0b010401c5400244000340d1684d5010f111502500d82525000c030000f035442c4507038003004410b41080c8013a1000c8400035070141044206095085010410780e891106034040120701b4041c4c580c0c1c51011030800c4a241d401603224603c10300f4840665800740c13500700b400f110b40c41407a808455440144611580300031aa42e004008980c2e000325000d541d00809a00600081d04001c004160791200809500d003624a07500004207517100078440b54085060903081044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 843746285 1250 843745035 843745039
    0x3041205040f0e090d031b050904060306050c09011701030302070303054501230c031b0d0e06070c1e0b070606060f0c030c0b060f1c121d0f 61
    0x101e855a01c000028000749030341c00c070100c000c03110800e000900d6000c1150644625240c141400014582c11101c0b03100030680f49004140400043d40c1481561958403420181d40e0001e0100074900344904445090f40120034130b58003081840035150724620000307105a0481c4da01d54014031009055650459980e002801e00d07009807002c5070400d552800003031000c0c820b4504004211040111184003032520201486103060500c24404201c50062204060649001d82c550120503580c03210020542e28511400310340075008056000180c8100d04085105135540b99558bc8141c07d81800c507040084a200d6910010300c1e100c101d4800f00070b06a466030075035000340704003004409015074600342c601060340f110300103c520540c0c0d410180a00e43e04114203030010a01443d2446a121080c1c0d806456800e607800c0203020b04840100044081d0781e41100c0350f1043c000a841011244001c10380ea0100075074a80003100c07d11441d10308404440e00c503103624541b104034a620340340f1700030300325062111084112010503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 843747535 1250 843746285 843746287
    0xd020d0204050910110c0303060915090705031905013c0e10060f02030d200f0c210403140c0d0813080303040c0504051f080c0306090106050603041205 66
    0x28016076a103100c0c040c850194080609141418070484030b0460303042c5000301410341424805200c0c41d035000001c0d80d83c444010b44400100b600c8080c80040c1d01c4c645400f4941c2d0050031541002030856014000e10f0087d46e584850314540404503400c8000d80d00700b401030030814066025a450440307000d20b00c1c45203d42c2074441038221140650b6117020034440ca50009046181c0308014482c2c480051110140181414500005070a00c0f8000094803889500b543c130040303548440504025030284145004040c0000c3c4019584040c650540c0700c007504802c203014400d004010b00c0c0347c501c0710740091254005c103d45000c6803800381140c1d1040c2d10a038401d041d00e04c1d140b1452040001039103800160242d0b00380035600b01900c3c1d840c40801002d99031314580100203a80c00500c1484000f0701d103d40500282c1d41c08840204140c0d0b5001d030740b80d00c120837818144401da8203a020000341000080b549207410301c02541983c8056603040c101c6400d035509845120b4000d01c0810028012696a025100314200280307881 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 843748785 1250 843747535 843747559
    0xc012f1b071401021608060c0d020f0a080f060d050d0f110303041b1203080103080a0c02040f0e010617030f0a02070b0f040f0e0609010b0306010c080408150f01140d02 73
    0x114544041904245403901c803242c0464819030701000007002c1d180201c207441c400ca03414400d8036074595001500c8000b108001081c1e18003404201c1d01545c48901c1c420102e01d0b2118100d94005058107015594480e03101e030400e000c145141064039401c2c0d40e1a403c2030040118035000e020440d24816182d690a042010f0611a401c0e4494280020350046000c1c4003004d1005492034580380403401079131301c0f0044101a0341d00702e40009420540d92382c11260094025512194114800d540c80484200001e504c14503004a0b000155170b1503100b10131070b051440081001ca038691540c40e000c0d21100040281030752050010b0580402010020a2021a035105450045036124164089078100c40d01148910301c01003800e1001d070100c94020b90061000c803008c000d84c0e00346240482e001303035418003400c0c205000000024105902400c440c180785940039603110b81d101c1c2d8a130032441e103602100000300317014030b05031000c01e900303104410405050700d043d103000400c0c85168a081020b00d8100700f1303089811210440403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 843750035 1250 843748785 843748837
    0x30e010201183008041502042d150e0418050304061d0609060d0c03021606090506060609210a060903020c1f0c1509080f0c012f 56
    0x7116040d244182c82026116100c41562105a1011014401196007090b80608400e07404135074150056005851541c04110803803c101c080d10564200c03c0c1c03002c0b54460303c1c405c0d44c03107021842c0d40d444440d26144404581c603100001d41040c240c1003103000240780d10169514071f2030540d03c0441811801120b0802d100c03503568519085400650080700071508296140394030100500790040c100c0300448040380340c5083d16000444c54020500304c00000e1b60b0780d0200c0c009540c001d904844d008503100c0e180c0200c42c14140341c80005804c15141c112a18029000402c81e84e0600320b099404640c8010041c031444801110b9030b031400940f030051041e1718421001c113603011440074401c0e45981c40c003a6000d48200d0324003206010420340c1031106e0300f0b020302c0c83c0202c1d007140590004807000701c0d951104c51010812400300440029003c400d101814103400000c0301c00031504514000c11081003560003e00503c500854400700ca00e00040260010510074101c111044601400030401ba10407410050010b010300f1003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 843751285 1250 843750035 843750071
    0x60a031208070f0215040f1103120901091e051507120f020115050303032206060f032a0b0c010e07090608121c09020105040806070302090a080c0904030e010201 70
    0xd03000080707210403042c4030303500c1d6224011400001d2180001c0c10002c40780c04500e440540024006000000210384400030800400c0450807825001401c8170a10040c900c8c00101642c05002d0440c0461450003002401d2001c0c482291903c071902c0d04100285841c20007445001548002e140755407140400c40b00002950f03800c5088030ba2041b0713942d1a0080600c1c090081e08644440e0605800a40d83d15020421990004201c980c407003804600c030001c0b41c1c0c10000b54a524a61090000d050b5400c10354046000c110030303509402100d00800f200300300c0541d40340080303001000c03407034921081d24103000702406035071511401000c0c0030481800001d80c81c0076010b12241000300f04d400c031610250321541d0070054442c0c200000400140c20800c543d107051107050b000d1010b00708200c0300300e5a498071408260150781c041d03c280c8005006440542c0c00500d02050300400a40c003002085206001c098004182460001080324204e80003503c050700c96199078800382c3e000038003c03008904640d240c0c1252040d6007580c04c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 843752535 1250 843751285 843751313
    0x20d05030703030b0418150c0c0c0b0a1403100e060616050120130306110c06070908240403080606090406060201140a1b080c0409051609170312060a03 66
    0x7030b50004030138040f031041000340d441e8070221089004142d80c00101141500c030501900100c60140052284000b038010380e0002c2c82d010f80079100b10b04000700010142b02c11300080074a03c425580703150700c4a910501c00781c0c0f1130009031b4007200d850054440600a032a181c2086a41000d0000c2103a0b06201c0f0540b1a2600c6082049085600307035102c00c12180c0b1a1003d1040300d4011580146144c00c1c03803c242400c01200c85a0f01c0042c0441d91900545240c01d220707802254240103c400a803070b41442c1900000e80078801f00c0c4224020b500c529818005800540342c1c40d0f1821006e170115401840c0c450380c400f101c4007e03010345941e030700800400c244c00700d5555500c10640100503940011810411100d000b801c0349030000c00c01e40200742040c0f03040000729400717201e9142c07840d101d080c000700903142c01e601d04400c0d0045030003010f8881e00c0c000602050b10040c1070603415200482d03440e0000a9101c480040080ca115500f010407648180f040340d90020414203001d0380300d0710282030750110356075903114800780072144 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 843753785 1250 843752535 843752537
    0xa080417070302100c1b020402160506040c060f020c010f030f0b060d0e060c0322050a0602040f14030d0527030a121e09120609060c0203040513060b04090207020d05030703 75
    0x80d140c41c2c0b113840540c1c01401409030072030521819040c800440d0084810144038024829a400524400d8038590401007040707250308082200c1c001d26040c80c0441c402c0d405401214081088003422103813441c80010944210072042e034858520006514099000d403400307c2e180b032542c1d900c0d024424480d84841c03010303007101d1011032000300708050079111280c1412006000c0d00d028034001c01c10000081c0001c440140e1180c40350a01030311419041c2401d034245484500024a01800090001000403100022109443c10b03844c140c2c2d070883e50b0508060380c9140c2c03007050302d004c40e80921031540200030420300849038680116006910884050010707023889030b03400342105d4160003550541581c2e0741c07203051248104c0b2503101041ca45440b10001400e021076610030500b0104220708041d0030011180c10502500e644054244000d118081c8003075242d400c01d005a40c042d810941412100103102c0c0124000c480050003002d1800f03062000b040040d52103020300b0b03a0400c0900d1800c80005004100808a1a0007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 843755035 1250 843753785 843753793
    0xf0f02030d081e01030f0b09070911120603150423010608011505030a0305090d11030318090c21041425061d011d060a050d0606020609030a080417070302 67
    0x22085110140a2510300401d00e01003030303c01403001504400240034580c0e001b00310f41703d0a40d640d600c0d55140039160b41080b14000d050680c18190f54030000b01400b91604010100e40256550310203041c2c0c0d40380007450015100010340003183c00300f490a418035041c0c1e4880315008005c0030b0304640107402d569280d88005482d03951824a01c00c0e8421292203500941800c50151800c4c00141c2c800410500440143c10f12841c0300b000d59500f00400960a01c40c1d460014080c4c1e80c80307044100083c010311001c810940d02603644000010b68082110040340ea8080140310f040062143c0110202113110f00148112111180d1068451400300c00700444a2003081e02c0c00c211255011000c48641c42d500958084000d2040d580840c01c80ca081125152000c0c0d1030030320b072101035154144124442c410789130308407541251000401603c0035901c1401400000c0207040c0600030a0388e9030b101281e58410031203686d002e40e0420302c03043c10841c1c0b0544040341c0203401810f1407088000750580042040d84400ca041340540c8c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 843756285 1250 843755035 843755041
    0x4050307080601120803061c030f031409030d0e0322171501061d0423090307080910020322030302061008070b09130908120f0408070f0f02030d08 64
    0x9020003008026040c50009041994506240b0901c03003051803034010041000400040c0e8141c0310078134410802c12180c8000c100c980c1c01c60034042c0c504e000000094002a00306186410740d160441c03e100d0240d4000002189803684c820101001040c0b2036480c401a03010411038055071030344580e1030020b4540440700f200e0000e40303001c58060f080e81280744100c003550404004491031091030250b1504403402814281004002c04100c000032034549040075511601c0c0000402e94100000c032406204214030764141815200c0b01c2c1026078a004022004001b1113040298030700350b0510030b0307000002010f0750044a00f06040c1c418860b901c0c0c0407055101203460b40b012420018183e0400c5501d800c152000c0f0000402414045003584845243c06003c00c42480000d0b10040d50700c4040d17140c6111603009004000c0e551040c03170011443e0b8801000758070003030410350125044949000da09030080d903020310007501d490503e0340c800310400e51190701038900c0c807c82161300c00580c4050103030900001e92a41c0f005101e00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 843757535 1250 843756285 843756289
    0x90a06060f110c010f02030d0e2a060403021009030606080c01030b011e0e01111506030c01050307080112080705061f060f0905040203040c17030406020c0906010e0d0204020910050405 80
    0x100700d62074420001050a880c111610104951105100a185c900c118191107002039185203da0491304010b14a070680c44018601c011804620702d460381440b4514a4180f115407407898065101002d91112003000100300624003140d1001c07810117903003000001c1e41ea4035100c1d202100c1590313014504640040e0b0094400f0b6074903218001000009007000345019004540784050919001c03845824402c980c040b95076540c0c0a100d81c115032002e010110303105d070250004941003000040d40d0003800303489030034007249030b560144003a240f00305a80c2d80e514441c1c1c0c0c40c0010b0f104103042810070548802504001200103e5004c1c00401c0c4210101c4041c10070382500b441490300403207030fa58061010094200d84544400b070f0300c180000d01b10b460454015071283c550b42040c1003c04410341c80b0b000a08180588079861030310200c043e208075a960703000e45060034040e406201c4c207840101c40c1c090004520900901061038044640c19206001600040c00e081c55400401c1c1e02034420400c69004c0b520100f0100014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 843758785 1250 843757535 843757547
    0x13618050c210c090c0c0f0718050103170304110603070206100b0412060f1418010e0706140d09020a1815120308070219080d18020a05100201020405090a0606 69
    0x3003015801e12080c11003580b41603441c2c905503240c45210758050004540080189002e84889003282000c0e5001c4104045a42d035032046c061140c060001c4a42e100c98042c06102c1c42454122034010001e080c00e9840c3e000300c0340c582d505c0140100c60880b180d03c0603482e5511101c000d1031007a600c94000b03110606001075801060b81d40344c0c2c08042d01d00310400c0144981e03507603251302c118030a9010b1130101e41013200c02da402025000380b1662041e04106002040307101c20250742c0d032018000c040310003001045e00f00c1701c000e0384031034260145002003024540106040c0e80c05030028058803e810000140300d5001d540003800c48912944240c0f00320800c0c043d16141041c0c2e40c0315040038860620000240a450030450b40b1040b22503e1018007030154850014101c64002e104240303041050a68140c6000d140d842e00c860700343c1090041400107072900c02007049101c800c051000d131254000b45500c11281c980030410001022400c404404c41d5000c2c040010203459494a41e40a00c48400012501c07a08000008181c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 843760035 1250 843758785 843758809
    0x30204050913030e061b03070f02011d01080f180111031e040b010306090c211e11280b0d15030804050f1503040302010b0108013618050c 60
    0x42003020852400c0044d81003070191807101c009035804c3d030b01d81c4003411429109074914140f2228a020024250302004130800c119001503200340c032884c1e443d2543d144910102001881c1309030220b01d0410103d11620030004200e5030054014a43c40c1083c28007002950a5070b08052040109000120030301110110001243d070082140c0e080c503584a20301511907141d200c40600c00644800d9682d45d40c1001c1c00003011040010b000f0f41484034500400440180110381071007034055441c51000759611400b406840d00001425402440c1c8810002c900d0007004101c1415005000c03070796038450090144c1a036890030303100043c00900030041d11103c1c80e5016a0a039141c5100c09054441d54010501c001240001505c06440041d00da5680d0744c242c0b00013003010b14205c1841e10000740300200030401003540c150040e6a0070b502c01e980301195030340d9403040007002c403000361305150011590310754018041a0304031709101083c01c48140400da02d50f48014010382416858003d5070390380c100c0340700d40810741011880380e00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 843761285 1250 843760035 843760051
    0xd110c0d150e0706321308030a020d12020a120e0106091109100e100e03031213150605030a110409020a06020f0f0c0a0504050415110a1707200f0601060302040509 71
    0x1040702e25505d1001d0104080d650100001900801c0c0500d22000220300100a480c0300d0b400c8a940311842500a5a60200c3d824420000b440c0b400c0455000217041c021f0b6685090a6101c5002030071105250700041c160144034690b0070342d614800040e0003030103405030340000444114400d580740c10b01c80511082c07400400040b410300c10400a003076956201c050703e000300159107107444844022403800090546c4542400802c450100c4024840c802603034500455155104850b6221549100d800c0d0100740d0384548030b100c0d03150700103403000400701b2400383c1110310040b40200700240001c0580c0c0022050340f010f400240041c0d2003100c0301d0554900801604103031b482c0d10802491313404c2401000511410160290381e019035203910100301080481108070b15510762407281480f10040e8000c03588050703084801c40000040c10302e00d020b4104408617443c10f00401c46542c0f26102609030814030509080103d600000070b11075580e001400310002e10080d40a049540c2e805a0b4442c9000104407540d840500641 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 843762535 1250 843761285 843761327
    0xc06051210030201020d120207080d05060f040522020a030c060216093810051801050301030b01050d080f070615060206072a050a0c05030d110c0d150e0706 68
    0x480582e1700015003038038209003441e00d0b40745c1e4801c02907024003074054000018884000821100140200360704007a01c583c505440b440c003000860010481510000d4501d900c1ca100b100200f241d964444420280d5070380e002600041d00c41c0e64a0340c8282c0c520300300c3e078401c60040c0c1003071441422480d00302160500401681100b4410364004440014001e001c6e990b450f0445111a00c601c0c8000702e4203032110300d0300c00b0010680c24102c000100050001e40c004610001c030b601d0018000d80301903000783e00f6030781665004842ca203016802c2805100402f003c0d010700b66a00001801007100800c40600284501d6204800100c2d2007000040032484140458101000b5504108100178085900039054064103407500e1b0b0b440c00b195003e02101d07448001c4200d0140c000e02500d4071540921143c0601c1c502215000e90488085000ca140119030240420f42402103541002940e4452490103c030003101a5018041220701d101780041e941049401511306100301da0005401081010b030400440052420707071540351 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 843763785 1250 843762535 843762539
    0x504030806030a12050a090e090d0201050108031c0905150c0d0b1008071d0d1a0703060f09050411040f1d03160b0c0d09031806030c0806040c03090c06051210 69
    0x1841c14400b004d0482001c015010a4800c01d407442100150001c0c05550500701c11820074011709603c07400038001c5035001d5824200006150380f130000c221040c210311503105007403000c00e582e4144007a101d00030082e81c040c80b1b10291440800e40020010b40140108141d165440b003520310400c040d0382400e0b01061041c40c10141d8010429004080c6a52054140c909500e000e0460030561620450a403040d40c0c004040f0343c1004100011281c0d40388655000002d50705c00c0c0e0f41c072400c0417070a5404600460951b8080c10004109219407a04050740052040240070003903195603012404035041d80b00501c8005454001e41c407031513400c40e90f01107034404096010750b05c4c2070a03491360302f20005400100284661501d0001860084030b040950380020f08040e401e11200780b0b0380c00c0082000501140c15141d800c030072100011454000e00c45c90312006010745500c10700380da91008102c010020000b00c034040c981c5030500b0b1000580c1c1d000481002e8440d980380d050719203941c00e4040c01e01120081004290707135400300003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 843765035 1250 843763785 843763793
    0x4140402120c09180a09020906040b06040302061b03031314161206022a1e0a060b0102100f020a09060918020a02161202090603151807180504030806030a 67
    0x694440100c202c081c0d074829031440861074038070152014100f01c0580c3c809002201200341c000504560007107480041030303182c40c070400040b00c00000364594080400c002c10801418000054201c5041c280d5400640d400e52440c0c80303003103510031101d01c0017010424402c1010400207078103c1c0502400c0b0303001420f00e8120f41040002d500c405004010300050a00e00d24020003907150125130039812140b88000d402d1409881001030f410f640403400010b030160b00e07286504010445142d604c015680001884844002d4031040c0080c550325003080d0443c0580514151700100078050407039812503a0b071005907600b820303007001003107880765401110801040c0c034020803001e03014480402c1550265240160303a8a00d40c4402c1c2e1800e10074a20400c180b620300c440000380271011a00075901c0500a030368000c8070359106d03c20941c444030710054954416080f04085182a50003c104003c000322520446580316212401c00d4000b80001c1c08a41c50142c682082100305688040307542d400a1047e0014603030302503a80c3c0c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 843766285 1250 843765035 843765067
    0x1110318330117100b0310020d0203180607170a18140c100504030b0703150b0c06070e01020d21020c0616050708040e070504031a16020c100c0501090c060504140402 72
    0x40341341c5910790510038410342c0e0501000a42c01d880c078200315661441031101801035003040f9141c2a100f10540390030702d0021004500e4611034451540da064002880d0b8841401c0d0602c058200c4509554500a401c1d07504208000304564a01034090411881401c095080c50304c0c02000c2c160b8020070803009007482d001d40050940d0240ea40c081c0c919078607a03840d013804500515004c3c001400b440d2640c80001803480d600700c02401060116010b45e4110f5413048401d4405501000400740107038488000034030040c1c4650401c080070f030010205200c0140280600030140d800c80c2d6803c0a29810040900040b136800d050580140d1000f030502c0750038415561100412401070b4402d8240c036104a40c0084d0500e481507080701c3c003951f44003a4240203020940c40c0b200c048072003101e080c40d41c11042000007000e84d000040b01011108010002041003814404c212555a0140c40c02c0384c42e50341790051180050301601c0c1000c003400d901d40d00e03e901e4a15107104a20820504007403103000764410442070540310840c034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 843767535 1250 843766285 843766303
    0x14010801150b0c10052401090b09061b060903250f0b071211040602161412030d0c020109331a090108011d01110318330117 54
    0x1002d100e4032402101c84041c1016880c60700704140c0ca240604001000040805146407024035010354506500c40b440155980c2105014400103d141402400d02718035090008002c6851016229102a44450200c526025096a0446890300b01046119080c04102c0241c00d0301c00c0700c901c0d03800d901d01840c3c8602c045503217030b00800303441e081304080000d000d2409207154050036000d001c0c1c20411284170035101411034109001e088018000d45000703c0e1107100d00c10319982942c22407a04060201415020030400c002d8441c50403400340000c1c0500c1502c010944980341d04850b103500040b4401009150103110182c44201103050040b035090400840c0c0401348840f25407000c800000110485000042085584041040d80c3c2c040d40b0200080f85840041d0015040d40c0c100312818180c2d50000000345003071300c20b44480440e0940060001600c107002c5c1500b40038450303501005484444c4c2d02c2002c1e40c4a00448110822540384c60011418081102a10b2142c010403400510081c1c000940b6041900e1354150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 843768785 1250 843767535 843767549
    0xc0d080c0a0f0216030507060f030207051e01060b0c0c010f0f09050f01210f0e01020403030c06090804030519150b30070f08010b06161b0e04061401080115 68
    0x34200207400c46008000406407215244c104030145a541d00e0425a6101d540c0200000905092079050149000e030003a140640e0f80000900b00424111034500107400308044003070b0556407180400515145e40364000c0401c00130f1070000d8642106030400150500000c425910100500c07035510802c40e41d4011a1401134070b408031554200a046980101e4132039100b82151039039600341407418100300105501c9079002103402103090100a011654640c200c0c01540300180100d1241c000d90000118281d01c20140e0034070075161682040e03200c0d20303082d1400305c040c1d03280755510805415032401e0041042c01592115400c08007840502d0341000403c40d4200c1241c0088000d1380c801d140301c070780e07003040c0341c0000e40742070101c0d00700e4504a0b81d0741001d5031003410720712940741c55510f00502c009160800804603012104402c03200034519030b25940d412400080a0840403001c25141404101410156000b9000b14007411000c10845141c0c44000c0001c0410390024045030f141448400340303000c60300c1d002c0b000c0300c0131 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 843770035 1250 843768785 843768797
    0x2c10061d0a03080c030a03060503160605031902040b041d041101080a1d0109110406060e060c12070c061e0207051e030a0807210206040204020703120f020c0d080c0a 72
    0x111000c40d99501840d08010040d143c04180c01d250080004050700c07007012aa9410711081c1d0ba10710526845905c0b039100890040541d0030180001400341c0300a41c0c0065009421100f220601c640c820b00300c3e04250410034515800040822218400e100740364142c1030003c1c0081c40034102171342e8410152810440d800d041c85103000014960840310340c45108181c02040c19201d410301003c103068020041404116206440300c401000c0c0c60a007803080b4402d460603a00c5040061031020104110342e0803c03580e00185204807182c0c100b181032040003030720226218410380601c441c02e10304003078011002080c0100c000e2102d0b000c11000103a0000c2c0650403101d00381e03201e014028003108146000c00171081d20300d405100358500c0d8801c110740c100c01840c001e4001c03c540c0c108070f8030501d100039002103106117400059001001140c054034069000704100d034401d0515040701b0310300c03100030801c2c0c82072010f942032801c0e8007240c0c01103110810b000000607280a858014031500c0d20b25007551082c0200015981000307a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 843771285 1250 843770035 843770087
    0xa02060703060f30060e0f010516030e0a050109030f090b09032a220b180f0606070614010f120228080307050a02010f0c081209072c1006 60
    0x44015810105640040f15135550f440803418107401400710002000344611074400b01e9004503034103200351400784494400d4074154548402040300a40070320301d40c0c1d003410f01900c030034a03000070024420394001301d1080e10303003c24a00c010080038000e10055401034185520412000d04c00d55030215101046c820300c3d5200d009002450400000d00c5c1c607a14021a8104040c4184003089110039900386004441e0f0160520040d0f081c0b03410b01c0b8a000709004000c01c0a2034542c00304404000c4900b44913405400a00b545062800540f2010180c030f00ca80820b9000c1181c19006111348000001008046c0450138401d2423500016808260300017021300c889401a81c0d000e03a034055030640310b00d042c0010003400c07003200d499011508001d82ca511211b18200d020030120070324000d00c90b0280040b0012203030000002418041e41c500500440b4400406041003402804004500811110079100c1d00f9207030b0700010304081d0b010500a940000010780501c400000e260320801c00d1a03400b02900054180003140307203552031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 843772535 1250 843771285 843771329
    0xf0708010302220e101b090302100f050d0c0c1202010608190c030f0b01060801080d0507021e120307050111120103030f110d03050f2a1e030c0a02060703060f 69
    0x80140c5013031040c0c0c0942481c0200781032058011500c0d9021079092810351450003c000e0710382030501d120003500000041c100d0144940501440d20341c20803141040b516040e040d04100c4200c4800c490b0605c080703100301c0288800d004030642044044200ca00080042c14145840b065980c1c400505465400d102a0f00c40d0080000c1e01c0704c514010742e03014a01081d0b8060324945900f8800b000d000c3d400004851400000302c04000140d4185003240580300d061601c1a543c081c0006070481c03100c0d08015200c1c141c0c0702901038a503c0462001d11414070080d540386c00079440c0084c00d6904000c000c10b21004140321040d40802034441c100d04503070785070030400c8003801141400e660b9000351001e00382c10382c000c10808544164054020900c200201200b600c2d090341c40f103032031003071103100d1100740c0d40144000700c0da640001d040300e0010300c22001c1c0811410301d2600900d5440380306034411500c0c01456180454803240701a0104002e5400c000907090a101e83d5003001058080314105104441d08600310f0a00240c0e40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 843773785 1250 843772535 843772541
    0x180804150c0c0303021f06031a0a14040b0108015001081e19030e18090115050916030c121506020712030914040615080f070801030222 59
    0x2241c2c00b40106081c1a9a410065160001054031200840c4001014041e41440c1e1103098240d9900c100c030600065412009031182d90340007403135006d000e41d481d001c14100841158044e84258410b107521013840d81000707483c50030340390103054110551800d0701c1c110003a0b0f50881c2c2c1031000103000c0442c2e00010b0920303684901001100041c40c80e42d20343d407407001040c0e052002c2034280d0551548009214030580414481d42ea9201d81c1c0700f8519000e10768121140040d111349034074042a0402400c03101c868074180a4084860000d4580403c960754541d800651042ca5091602c0180030803100890340c2d2800b8515040b4020507c201242015507071200290f110340075011044c1820403000c800c005140800b200c0d001190058000c0f1000f61050b542c002840c5845d0782034003003100d6815522000154a00f0b501c0d03c1084100416003540a501c801c4041388281c4050b601000c010f009030381e201050708003a005212041c801a0108080003c500014405070f2602c01640d070300c40721000c0e034141041364020022401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 843775035 1250 843773785 843773807
    0x30b0d11060f0a0e090c1c0b0604080726030703050706090204020d060e1e0702030a1808060f01030b010807050d0b060d120306080708011b1404050d140118080415 71
    0x50040101d0f100e400f060b0700607a21105050300342d80300285515003e010250b40d0203a4503c0003803071462450620940d032016002404001001307482c0c40d007002d40f01e0000600300092500007031001503900600500c0d0060b40c0c0d441140ca0700100000c0c43c903052064074002e10510a21401030845502c540158045465950448402941250341000300e551160f0350300309020400c0d106154007001c0f10070b54484009410340c4280c05600d01b900258074000c00702e6000e4540800c1c9407640176100914110000d01c2c03071000e2000f288603403040060710086605528229024542c10b800c4404154081c0c0020f10403501c501800011040e0408038280850391400002010180c20050040800c0700e00d142215000340c0541003441174600c0301042c0c61180341c513003d1113400c13510171032248541903044a1840c00014043e0b280109040c5984000500d440d40315404660303103012206044603c0303c3d03003081d00040c3c0e40c400e1091002c00c60020700c0c50800101c0e29159581680254059070340502c2072072444a2109000701c0e06404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 843776285 1250 843775035 843775057
    0xc090b071a010312080603010507020616090902130302130209130e0f01140a0b0312120415091a22080901050d0513051c050307031d0a0f0201020706030b0d1106 70
    0xa070940c1c482ca009500c0c40e80c0c40703080703102180011004c5802880c042c05503034403a0300315038014407559a035103c0101200d0038440b100307014401205004110b0300500d0004005883c0040c01d40d04078a4510b00c1848840a0944030b2800704070b106100125442e0345906090201c079034010400b141400c81028103a01b80515220f2b19881503180c00380c5c9040d8403012642c031611403030751200104a001d111000f0316489881611002c0800081000302e04041c0e0f80c081d000c6900203000e4480e280c0b40d140903031000c100725600c003442500e480f10320f9207802c034002c0c8201d13103400c8e408021404140708040d54400140031100d9503180080c00081d002c2841c10840e4450f40589200002008043c0400c2c2071401c0e00c5004d0300724021094807a07001e80c1506015003205c1807200b002042c402e5903582e10b1599003e5048008201c0c0304280411851040c022050130b44041140d110514000c0e07440243e01c4e801380c800a0b140c85000da02030810b00d81041d21005041d2303915107030038104a0b0807000c1d41c504040e54100040b818440e40400003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 843777535 1250 843776285 843776333
    0x3060a0801020c100509011109060f1306051e04080307030c020f040c0804020312311802030702070f05030304030303020c0709020c061504020304020604140d1502090a090c090b07 78
    0xf8080c4074001040084e54400020800154036110710081c240c030700c0c081c420000c1000401c902981820000d00a1156441c003241d81410140000071961120081e0b62080c0000b65002c1340c528015030840e4002618035416502c66803600d03141070707a0540c03640581c0e030001c0c050081101c0300605644030806101c003040001001000351644120700034081d00b4041e6002d074041d2080d49801280c448000e0101c030040305c00089094481e00000c2c0c0044903c100b81e2841700f03240a200d440009680c0300b5888243c040001c01c1c0d10240c0ca910b4052802850940d0320b1303100e0300c040b075401502004144c40c0881150260380c0c06203030141c0c0e101c2c0700740c50461a1007003561065407000d1002862820b01c080104403940a05841d0325050160701550041000380e0105940c0a940620200001c0006884841407452140d03005085017049080580360583d240c2c096411190400340c0002c0da00d0300500d00031900c500641841003040158100c6440c0040400049024a02c0144400200784042c0100030802071892110b10f0340503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 843778785 1250 843777535 843777547
    0x1060c02030f0f070614030c090d080d051501030507080c030c07060605061306020d0e0a170109020310020a020d0207080d0e0316090902211b01030207150b0a0f031703060a080102 78
    0x4182c1e1613080344560000600011102000b40003800d0849020f401802c80c49420098503204000941128000441d040a410031038400240c002d405901d200380e5217006101c400382c410700000f5007940d00082c0520701308501c010070054400c1c450810b5030341108818042940b1f0b050f20f450700000808540e00720960200c400304900051a640d540903405440071582a540500842e8606860046403021625482031100201744084d07140f504502a1040d0090000704034000c0340c0d00030034202005412660030301b0f900010181c833056010040c00700300744201d10040204a140008a6440c4c2e03012046c403104001120584255a80e4208140c908000302c248140180c56550214031000f0044001304a0140c86034103240c0a0301d05074054282a02410715001c6c0c444032159528292460003000400c50515a00348905004900c44455110b05080c03021800924040c0d02000c00645d041180d00190b103c44080304240001120160b12032a000d81003a141070f00c0340c4400c1d000850031000c0d500445070f00e41c070100e40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 843780035 1250 843778785 843778813
    0x90b0a090603080921030405131e0522031407060e070b0304030215040302030901030c03060b210c0f120603100f0b0108012313020702040203090a050c01050a0801060c02030f 76
    0x80c542880b00b00c1e2035081710700002c0c100b402c04c0b0030054105005500144010801d50800300e40740444050740c5400010001303c4104050b0041100340300780c680c0b40782e8560401001d0050303070003110221248181c8541129050b90b03401010882044100021040e010410314204a01500b03e450f030f841c0040103039030341c041c0c0f29007103100e080d0030446080d40184a001d005000c036035034500003640107540542c06145480c5440005501034160f00a0301c44c20195030741c400040414100d0060315565408042100e0f04403000d1124600720cc10180c104220351038100804280308450310225080c0402100c0c0210741580c031740c00001d041101c00c2d020a0349940c05e180202120604a90010348180d1090326a40c0c074598a4400f85a00400c0e04024031905040d000403048442c5030030341e0803100041100402500c0e00341c00d0750201d026a0010346920b011799201041001c1000f03814440c1c000f100c8030030f1a02505001250380c0003402e1401c107100342c009208030f5440044c2591018000202c200800c40d0480d4104088002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 843781285 1250 843780035 843780037
    0x403080a0801050a0b030a091401021804201225080402041406150f041a13090b09010b251b0e0412030b03030d0c03020d1b020601090b0a09060308 64
    0x9080e0300050100c00001c5010b1410f404240203540f5504425030641d030f81c50b0f10030780060000f104143d8a5880085812805050034001048441501640003086604500902055881c1c0700705410301e5800004d0311003100d14440043c0d0b04114003044804a2540764103845034801c40000300d1042da06940041c0414030640c0000402c5c2c022442034504000e1080d03112880604000c05490711940844104e0100081030000c801400c040c3c3c1d00c030750015160a5565400c1e032500c1e4101030804002c64808134545c2e14200010f44890300a084508042c813400920200164020b001401107000c1c225020404c007061b2002c510070181c1030580d418031065503015908000c4100c2c5003103460500c00b10005d20002c00c0d40c1e007094003070b64000d541c412100d0000c4400c4210541c050300400000c250148010b201107001c203402c40c0205408200b15460060340d401c1c1d14111081600ca41000d08200d50040c0744c0c0001d41c20f03a00003246c5044a0528000103906c1020700300146207203030154850300515083c10004424850480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 843782535 1250 843781285 843781297
    0xa0b0105120c04140904020102060402091806090a030908030309030a050f0706050a06050a090b3a0c05010806011106041b090204060519030b100e0612090105090d020f070603020705030906040308 85
    0x101c071343d0002c244100800c00004402c50b070090050b00300d0030100300141044240350342c00400030b0480c0029038000c180d00501c4e08000321941400ba90000012405251b04404400054490b0300091031852400b02c40103640ca10035000c00c0c004010f0000b902e0703200d4080b070714160f0f00e034554032590511046c2040707000719018000a00a4074442c0da1118000130b0042c1d1580b140664012000d44281007030a004003000098804107410001601031551040c41250084200e01e00d07001e10599480140a0134100010401000108642c1c14410358101d4250303140400034440340d00a0f40000310048840201e542d004410b40d4950288580301c0c000714000c105103030020054072010102003031203141c12107240303001c03003c0c0c51681510b2034005505a226600152040e0584032500001800b109d1901c2c2d1003914144039208115403160781070755201c0520075880c0017402241a0301c1e016200815501d5190700e01151030303006074441c01c400d1503800614042000400e20603980001c200610711030310345130381c0d007804ea030150701c40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 843783785 1250 843782535 843782549
    0x4181806020d0c2a02040f0c02030301060201060b0708030f07020a06020f1806070c1214060a0504141627050130080711030307050f070f08010506090a0b0105120c04 72
    0x6400c2c0e44581c400c0c07100095126403904148003440b2a10f01300110190100816a041501c4e0703802c2e8280303c5454062515454541d500859880d0701d829002070860300c10385c200381c0c0003076004c1015201040345942a2034220440580018041d16203203401c3e8944184c0d01c1006222500100388198070440c268080d044200030101c1000149a5880c2040329034414014010400b000d001d4080c0a4031020710a540340c0c480c41074642d24540005080078504c4d0000c102c9001806c241c658041000b00100c03103e80040c0c0100c040010301a81d544bc010714000d028039801103504401011014403000d4858400c0c40c586448204002c0005507100c0c0e000041c47c50b02c491038038a501c1d91041004812142c011a0560b985410155150910b00c1503640d2060655a00a8259041c4401d202d0302c804182d050092005146080c8001c080092410340c00142e821580e610901d602c0c0d1400c420002c4948510751503680c400c2c226100061107900e0840142c3e124000d0307200c40b400010701d0b18100502415104010400d0300c0791 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 843785035 1250 843783785 843783791
    0x3050702150c031e090d110a0b04050a02010e0d020904020f01180f060318150203040c05130608010c021506090603010603080a030e01110a02371b050f0604181806020d 73
    0x113209040c680300c10a5844442d81d034440c0303031303a00000ca206c0c8070b0103802070420030f094030000b0f0150b45908100800640c2c00340c80c9034100002c8030046603040506002c03004800d54585041b8011500041c501c07400091010713000d540c40008100060b80b02d0301c14190010421102010711540700c11500003d11401c1c06003d010924105444010858003034660554035802819614030714442e50464004e900302420440f035841501c1c0c0c01103403943e240da2035414100764680c00040c00d00c1c94078841500791500049404290342040c01080e00461440720790643c494000d0b122482d40d80c94101c0820b0051030707079600c05000c420001c6420f01129905030085100031084000074014440510304903122481140210b60141e44100c50860b003c2c000b1422240021110242440c1d50702400014196905151f9000f180c4455103101401c01e5008400d40700f801414007070f110705002d400c05202107581442a4001c03603240c1c00750b1400c2c98480d15441c0d0080d0b106120391803008542c0b641c15182036406074000304016213056003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 843786285 1250 843785035 843785071
    0x91515051c170405101409041b020735100510060807090e010e060d0206030c1c02030106020d080a06050a060c03020d0f08060613080102040303110f120a03050702150c03 74
    0x98143c40507604c008103002c045a1050034155540710556454801c1082c00b402403500c035a0b50b5100d001d02c95241c03040904500003181d00c000303040c074144c4d402800c0881c01070a4150340e03040203c104540c104500203c4038511416000c4660f1424080c801b1103111107080408005507060303400c100800b00d41e1580c503040c290703440d401d5055417400300c1c0d03005481015003a0b10042002080d2402c42c1d98005602400355040a00140c001c1110750340102c58460860b00d00090b00312001c40c501d00000c1546c2010035045003907505016000b5101d0314888040d800300705017076020070960b4103a130b800301c0000c080060000c00c005a54200c0a071041c0344201d015000f500402c040341c3d03000c0380031756819034a8112954a5042599400b403c1040d03903080701601c50120b0303e4005020400100034401800a54080d841c0e1303e1109840d501214600814582d0700300f001e420030b03465910088411015148040304c04e040c04a12a562050101c0c0b40080071501aa241090001400910400280207500a03414034000c142c9000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 843787535 1250 843786285 843786323
    0x6031505060d0b04031704210507021c021306060f080c0a0c02120a0602042315160204090503031314010e150a0e0a0804090b04091515051c 61
    0x58000c40360a9000700d062010b0740001050114825072141c030038149a050740b1810480810701800442d41100c2242140c00e0b90740c01010846900c401c2c6400c10300d0914602440b0b5408201ea80d0341403010040d2445074220040115a25103200e09580380600c04100102c80d078955004080038840f14650303011660040224845214120031502040d6007511201c000740d14a03404e1000204400000d102e55001d5130194000080407400103000511a5805042d2200800d0b00340c0704411103ca5000c920807103040c0c800f421881240410786031140003e2401e0a02e001d0310f400403501402600c80014401c1c0000010046201c500204030301c122401907612501c000c40d401156030072101c0c902400c490b59031080700c0f5154481099600c0340d0b8051040000802d182c0160a5a1031400c0f2214104540080010a092002440310320030850179960480f418072100040303840311903c000401c405520419192042c18142e184110ba20600408018000c401100012017450800710251402100c3d000c40e2001181e06d10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 843788785 1250 843787535 843787541
    0x20a0306170a020108061f1112070c0e0403030f0204081510060c02061c140703200a050c0f0d0c0204050c04080c310e010b100504090b060418060315 65
    0xc095007001414080569001074507a20001005d159010285901c0e80511001c1088060000111521602e42c070b001101022803c20803a42c40405c40814140014404501c10a8441b811209089903421142d1201d0400b18050400c2c90304804043d4000103000802c2d1400198103140b6039110b80305115282c0f00d0010b06440078000744518400100b034000b0b100050324100d4000c0c003103140a031a44c0d036071444c1d48074044425581d1050b180d48030300d1a120100030840b0781500610340180c0c400e841c10715140c4c951296180980c0940c80001c800c00030007142140108404100410440c41c000301181d2158512610040100650040c228040d40c140030100d14904040002c1c0c4d07050300e46450182201001c118140042c1b9a07a10f0001d414940b5814000d40440345141848802d1404689005ca0342401d891025420b5862031440366000c0d07041e8005072040326520106450640d070322804003081c503029590002d80ca600072600300450141c01c15036a1806440598800000c40f131203084884e2203048604607283c22 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 843790035 1250 843788785 843788819
    0x510090c0e10050a03090b010801020306180403020d0e18180d0306030f0b1e160f0206062103090a09021914040306020d020403050d0e12030a0507060506031c03020a0306 74
    0x31200c2d07810002034041c00703030025110400080c0303400208481035031610340c11850203070700c5041d141e5400024818a0306014010381207880c840c041c801c0ca5400c060b680295a08003600c0c400c801c10003407014103042c80e520800000c001c0001503071001c84505000c400103003440320f02518180544645000e0350780290190181104603504240982100c1920b40c0b141c11101d0b80003001d48107918414403145641080802c9598000c0c20844a00a0107030200b9202501001104002d10151b500100402c0398079aa140004856240610202640111104210344c550f000b0082420380c444502500400c01110300d030b0203805207080c0c01004502507440d07040140c45400010481d007014210401003840030030056002003040204956005240c559607444260a0850b500ca420000600580e0210113070f01d030202d002041d582041c00550b10300564044081c04034030803264001e104948590015009640c140304646002044945240365400c511500070002d512810302c040103e45841404100c0b111a4851032070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 843791285 1250 843790035 843790039
    0x1302160515100305030f030a06081506010e0f0904030f091205060412031b03020c151e010807050612090f0718060e0417220902090103060506090307050d150510090c0e 73
    0x45490032070301071b01c0701c41c0c1d20060568003025141e0f8000581840c0800c29081542d50b003000161080c01d040c00010410b0100034a15445001a81038541031039031101040e0703410960609041c110b01420280a9407415880e0f40306000b03122014220000340300c004a1300910507481000035125a14207044240c3c22291110415803032102d40c88604048640070307034010b02c000301910048588045101607035582c1c04800311a003040411040750b21600c0c500300b5000350b50245c07110300c0c041c00e0242d0070540850440e0049072407901c80c0b112000081904801c00380b004481100c5c1c0780040e07d09403521101c160400c20208c0040c000c14601d0301d200001c09140c0b40c500180203e1f440410980311407040c400240803500040390621140c0705da81000188141e511200b0402000806409a02c86204200140441301207901007409004104800000c1d9640803d1460039110210740c041c10420850500d035203108541c4034040c90891a200922900c5c1d035409450008032825014203001e13040130160101da80d2190252195 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 843792535 1250 843791285 843791287
    0x303030b0d23031c0605040f0507020c22020d39110f060114030f060103020f0607030521011a0705070303050901410c030702130216051510030503 64
    0x81c074400e080484040e450320441200d041860044c00860140d40780c807140e11900c0d0392214100a07508090140078000c00185104202c40d00d061766010f5290b55212920307500c1a81c444810072420714818410140b8403801e40380854a4880d5024903200820748495003003c0040a035039a12240e41801c0c01420282c500c041c09081c21078a0480181c2d2080142054003050703010b034210b08490780b41d013000250700a10b141094100c1082004052509113501d42c2490070094016074010720240c0c807010715010744440c0030744d042c44d80d440c242e00b421507035401031151808007040c440c078604150240b0041d80390b040c3c5002d2000e6202c0d40e003041d112806c161180020003041ca410044c2d007007011901400180c603948006061050b14041d5200540282200020030f41c0e815814000d0f104400e813201ca0f0b04400c07405450181e0070314003810301e110b80e940c80c060740200a1060f048a6001ca4008210380c040d03a2524850f54014125401180742003602c1d044103003620118800c1000000d003580109803501c00849810a0142d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 843793785 1250 843792535 843792563
    0x20301091a0a0b12040309030605070c0204110f22050603040605010e0705030108060402040f1d0715020706090312050d1b030c08060a0501032705071404110414120d090303030b0d 78
    0x184d001044c0091042d001d010340e0b00e0000000c2200d5014482c80f031512075690500000240c410802200d1030b2046144540d1802e10008054200c00001c440c01c20441040d500e200c090100e2140540941d9508865085a804000c1c0401c211254012605a5440b6400703042240da03040d40454041c0001d01ca4102a0b500c049c1c04200581001c8d4031280d820043c0c1d00c80420040c0b0011254050450390059040c1c0561007030b4410015140b05843d0300714020064405040d21070b11746640105540c505000c043c1040c3c1c0c2c41d0300b15200c0c040c01202250b040c61601c0c0401d10440032a4103402003140c4040c01000d01080c1012003009000740720b801200c0c841c1500a146400031801c00004400401c41c00900d82c6242d03440300304001c3e41ca560f4400e29401248204020f2980c1e908081015400440c000c0485c1d0040d070501810080c5400d80d1000d4070251801d0621003151a062030000844814030316486a030395000c2c5018240c0034603401014941941d02a0303d05206c0c1004c83c0c402d000e0801421b500103003968038550b602d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 843795035 1250 843793785 843793807
    0x31a01050706020c010b041a0f030a02010f051312080423130903020309120a1e03020a1403190f140408060705161a040b0703141605040306020301091a0a0b 68
    0x5003624030144400010980c1d065801f04007120034040c01502d9183c03520940300e0032443d01d1018148108400d4010746181c800303a50000c0c020801e4242c2020a10078041040311503c0d5007500700c10014a2800180c4a8902c3d05007080d07481d41e4058003602134850454407424140110700c1040858401e809400540700d45e80120b4032400070104000101c04502003040f0b40006039803003c1a4141903022000540300049192a0240341780c001c611401e000404894500e001094011406100c025004400c0c016039580a40a081c21032140c10104081c0391190411010700d03d601c041c00801c0741c0f00c51303100d844420410141e0f581c1d031406288554500c1c0d034040c2c4001185503104e403000d020125001003a2140c10112587c1c0d550f03030b4050784c10082003960591420030051001f0340c160560094403504041180705820152060f1214005101201500c07416003a50b0041340f146041720000c6410440454481d61a80400c0b4058146a004190f1210aa40c0c4044103840c00320540c104482d109084035180110742c0320 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 843796285 1250 843795035 843795037
    0x307120e010909020c12130e242e0c0f0b040b0901060b09060708040b0412051b090a0c050f04030302030c0f1513060605180a050709080d0e240307031a0105070602 71
    0x54884d0307082d50390700307030009240c481101c200e8000e003642c1a0980e40e202420300300b00070300d084002c9020b1051410240c6a00b0048001c408504c880707031258403060588030611401c0d5032142e030320a070084c580401e03200b8035000e22268080737050261344148a071516a4072240107903400d03a03e0760f00583c031001c041048111603e1402c1401880c0d42d0344190b040505040c0c3d2030913500303d203811507800401510320344c040d10010420140182c0390040c040e00c14a5020140b01070215041000052940c5242951840b04510386030040041c4c50140d90040c0405544540740e1a0003074a0750000111231500c0e200d2400850a5401c02041c041441896942036003030a50720700601410454048405845180c2c2d10310001c101c644811003500c0495161000030006c41c10a19001800c58074020300d21020420b20010500c941d01d000301e4a010300c0152458084904044980010820724440540111140e076145010369030b420309901452144040f602c082109492021080403003082c50364103a800902c003000b4003000920958 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 843797535 1250 843796285 843796297
    0xb10031d0123150307030c03050d030218060a090b19020601051005031612020d0603031814040903020c190608010617190f090c1701020906090409050307120e010909020c12 75
    0x1100c0940c42d107803100f01003400d0103030b550001d0342c030200c90500a01c2440303401c201004100b05c443c5021407074140c201c400b00c03488154050440e4410000051740703024540c401c03e4124040c08201e814a07681c0c800344000200c141409541c503001600070700000060700e00d808d00720311114085503213640340717195504140340c2c0607142a40c0201042c4202e40424000d0044a8405481c5440c03140d8000642a400c40c02c000d090904802c0918002c40200c0c41d0074010084550f0382445660b0701030b40c0110318a5040d14081e42002d003641651500030100d1202c940d00e02e113840c0f00841c102c51880d00ea1501998942104a40407504e0b0304403103003160303008004540c00d00300311690140382a01c490000107645000c0c140c1d82040c0c074851f0030207440b800700320344080c03000707030908102d10761203a00c1400210702d02031a132800b064040c054a02103511855403000300b41c00f40070092048840f0706500490f0b40020713090f03580707024081c040c4a180352400510b00301c40114402e1700b584220b90010002e00010407005809013038220710341d0f002c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 843798785 1250 843797535 843797551
    0xb0f040203070f0801090b0603010b0102070504050a0906020705060610050703051e04151d03010b03060402060d020c03042c040f0f0312110405030114010308030414010b10031d0123 79
    0x307030780041d020f034032021098094184400040341003041ca090800c401580541000e1099140404107110303070784c002802001329a400c1e1030109855551007000340040101c9a00940f001c1e00001e01c40c41003003800304181b4400c103401c680780b2004801c070308012140b5000b41c0d040140810700400524588022840c0f00805081986508a1400391241c49001a2042c00680c042c00300340159502010a0310070710110f000c141d400c3d4000c00916400c4400290b403060b014101034001c410000300d006107602250102d507603510314070f81280d90303844d80e4056454980340c1b80c8038034100003184440000c0d84d04c0d465030710560062b070b00003403ca84108040c0d01c1720050300c014200d044051007040540da441c084450f0241c0d0810410f291003140c1c660340350405240c00d640403220340c0d1041c1d400314801400081c1801d82030300e40007604800190048031a4a008900504824294a40c868070103880c0202c102c1e8150051040d01262100c0d0780e5000d62030721411420398083c100340303d5409070b46000c06c1810f42d000400c2c1560094031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 843800035 1250 843798785 843798793
    0x31d12090a06031e18061109150a050f09040e0d080f0c0f0d180516050307080d1709120f03041b180e01020d090b040302120a050910030b10030e0d0306030b0f040203 72
    0x1150f41e80c21b00f1541e61a072140011180894001600e1508090448452030399405140c500681c9840c020503620503480c05000f82500800ea082068860707900c94074448034000101c840d1003540e80c10281c042c000407110044ca203441c103070006c1d0340401e8a5042d07030f90041803103101900780290026003c01400c04c00d0030140129030300e00c03084404a00300300100455030055908584a6905090a150400c1e6140d00003c041e58004000703030003019031040c0b0010300213484403e00091030300e51052260408011901400d060701001c41d4102c032003074010000314019072003a0301004007800c00150740000c14501c0d03c92540003400c0b095040364802c0c02038000030709002c81000014500001d4a0000044450044054403d03050b0003080000b09a010054001c030030b07690740c3c0324609005000740002d05500c00d1103140c500650b03a100030303106800e01a4202a40303210f80103080400c800c0800a00400601807011440032a00c944120040103600921441058a0300541d221030155981d80b15a100c0c0d004c0a08103e80500c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 843801285 1250 843800035 843800081
    0x19030903150b040603080309120c2508010e0d0e10020c010f1709060403030b011e0c06091a06011b02010905060f09060a080f10050907031d12090a06031e 67
    0x20742d44c89520040d6108401c040e45a0400c00115460840140c071081200c506c10007600200e0322000580305038010b01101d0300180c0540d00d484c4440112400d911810481d801c002030011464004580004982e000b0f83d10000c07003400e180d0030001c07c031000110400160f040b11450f01c009500c10b28411180142604108910b64050048103001c090110f49000254204800740401c159250080a030000e03c00d181ca0182c05800103240030280c0590200c075001d00c100d1910500420080f5046a44043d4000020008407402c04003400680c120032120035001440b030500e00400e0500c80111a01c000c0c0d01070307440c05032003418482031102d2075018000c1c07260f081c00e00703100c403007a6503640700b00401b03c0c0f400326540e440c440e0426050418546402034800a031030014494140510b0301c400c100194002018640400c1403a038100440c0c0141c000f8480115050142141c00000030200c10001c001950040d241c41d07030360950700c110443c22034001c61340001c001c0c25040341d441c00081598112200c0583c000400b501e501e1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 843802535 1250 843801285 843801289
    0xe0609030307080403120305040c090c0c0f14060912040e043e03070b030609060103060f0b0909011508070f0203090303071a1b0a0f1806080919030903150b 68
    0x500302c640708440e01e0100060034420000c0c0d148840c10340c00c4440c1403d010b9410700f9681e10303440701440c0c040c0c041d81d56039540c0356400340f0703101d1101d0f00200c0b900702100403d200420b08240c0b0300d5405281d5a0320191154034042450340d41c000800d4400e03a9041402a800c1900701800c0b51408040580166036102c100d070400210b0411a01d08040c3c800449a0756120001c1e1610801400c14000c10109200c0d4100000c00c014030b800c8101244c0d8000800c4494011595901005a00500d45900100642c42c01d02c800420303602000342c01018540360459208103181c1ea0b6031000300e40c0014003100c180c00200311002184101c1d00503600c00f44194114010b40e4140040200481c2c81c64108100580741d1400d44005440c18010101e03032950842a034074803080780ca10740c0d1103140d005031084000904c100890048843c0c211441084050010955007881e80da00c241da40c0e00052260100b903a1201c11802010607200034242c443c512071401c141c4c192610205a4995112040c130002c0040b000240d0944a0341d41100c55 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 843803785 1250 843802535 843802537
    0x1b1b0212060c03090f010e070509070513032604051f11100603120c0c05091e1f120c030303020a051b0109031407030804020607210e15070201050a0e06090303 69
    0x403503481d10320380d80b00d280482c08a03180141c11746104c4003c1c1d1502c511502100e4012480c002174132010369007a201d513101c010b011600e40c4985004241c0b220782d010004410800c2c0b484049403000080003542c40118a030700d501d0f046a10880c810180d100b510203580701414082071211404609450405103103450452235003030b08208804a9041e1900c0e62000c0510400240c3d4030324003100c402600d403c4a0201c525540d541d00001e1714000c07036120321000c4000500a440d55803080182070703000f00d5070020908000c5003003004101c07180070404072502d007100082180c3e42580b01010741745403c8071601d00314074034644060300258015540b180c01c000042000c491407a00c8010104001c41c800c0c0d000107854030a90800500d220441c00031403140860070003550740480d9026a16640050701103607100e0b6607440f41e00c1c01079181d912500c0d52000501442c5002e001c00b0381c100c450040714081c03e4840010f88e8401d06040603081c0b042202c020302150b018419420410b214407041c0c0e81000d0050b204910709000c1c1d40001c0e1031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 843805035 1250 843803785 843803791
    0x71401020c120f07060f05031311061206040b060304080708030a090c03150f1e021c0603080c070b0304120c020a050603010b0a11010203090a0f081218011b1b021206 72
    0x100d0f0701080b018800321004000240080c200703464140309100b004072005200d0700c03024003402c100010402000341844030501c08600049801082c0c1c0b0750350061810440010102121210b00c11481c000100249040c003000312881a5413000d1444d1410300603503a075054542025104000d4659100b1000000507560b041d104065401101d40362004019580b68030142e0320100700c0a03110b1401c2800440c0d4503502c1c515240c5281441203005a12801401703504403d00150300030607008941080c00000c28032403c04010480c07000701078190b6226a03210003480c8601d2005890080030b000c901c0044030032071407081192000c641c0c40240703859500da5581001803040e41080c0c05c0544d0500340042c01040e496040302414840e81182002541540b400201301d64580158500282c840390f12021036800304070445c0c003240d0305006601c10801080c2171504005221031852200d86034190b180034500040002c000001e000300c1600d0340d441001c0c910f10500c1c00000c90020380004c1340c2104103d20315041010003401250f00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 843806285 1250 843805035 843805069
    0x50706032405151605011a0a12030f11030d09080a030c0c05030f0c12030406020d050916030809010c05060f091c0c1e0813031211071401020c 62
    0xd40480698808510700031412101180803039200307010000350720341c00f1038a8880c25507060036a07201c00c00c1d00c070750030b48019074000c0c0100194078011103001080c41d40741105084500954640041070307101c0c0204070741040086006008134168510403030390310744180304101d00d031a05607069a040605049807401a581c1e008070803140300c800810fa042d12507500d0310458295405610340114501495164507440c0c1c8a2540c1511040b000082c1d0300041c035104000f400e0840180d00b8903195240f400d0300340800207411450480410303a00742004a454407a00199001141d000460285910391641d5503840403030703100302c041d5414000781880d0302020030414800d4a10600c0c180c1400c130304c00d03c2d0802c96241060010080316100780070040a50000540c00741c81e1900c3c4580c4000040f6200384920384081400c160a000208181c80008503402d00c0d5103245003180407680f00d40d445c1015441181000da0740042484c8031140d00340d2181d9005c000c980425821a80c940d0010700588a0886250010500c1350381c40c409460303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 843807535 1250 843806285 843806291
    0x30312160e030f0d3506061b030304151e0b0f0a03081c180807020307030221100219080604090219080c01020307020105121509090c0a1707031e05070603 67
    0xa80c290704204030341105062248140121085045c200711880310031611801e5110b0110000740094407107408840d01c800140d00c403505100d50104000f6640e0780100c038219401d440400c90350810001d5030045810b000501c0b1850440c2e085a000010004e0005072200b592008003070085030065280d0300c0f000c0c8080d41c002d1104d0381d03880641c003042c035090414060000324950314100c00904240305800f000600d044c2c0c00b64100740e5845507800007915001d003d40010f54020140058940d103e00500a44a0440098030a64000100d4640780804902622040202141e41303a00b50320151072182c3c801d551310000c01480064020883c1e00400c0d254616803140300b0007808020800e0042200c01c11494003410000d100543c6001c1e9a0b50000b40035015142c10040100c5030307180820665000c220580e0f080a45c081c12a01e45480c0002641e5039800c0121052802801010780c080340c42d0842d1442121146c1c104401041c08920b103030385000700c40345e1200f0b01c801010514402c020009909000010042510759004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 843808785 1250 843807535 843807553
    0x30705091f0905010804050f011a120a0809060c0f07060e0102060906100504020a0e19170703080415051b15060603090d051e0c07060905030312160e030f 67
    0x44103001c0d2860458041e242404200300e00d00c0e907401644803050b54021302e01044030340c0710b61401c6842c0800e0213042e00c055500703120b40c0350302841894080468a0b2022200c0e2508105001043d5854108084010b4601c6404005101319400e064000788150b0070301c101160403e940c0705900c00c0c00c22950b0341001000945581c012510f1b9a030402c0b4140d04261810080d28850402e604c03280c94550003882804e005540124041c1d415500501c9041035183c009000d00000d03061a019241c6821424050910100b60402d1010400d48000480c107040d203501c01300f2107151a003000c280c54181c41c10008503404001d020071000d40c100340b02c3ca20510400e400c010007420256056014086041001880103020f03000034000c00401c0c010000380c0c40c10b56541820802e580d04034182041c2507845c0700b212079115030000000c03c01a62400003400608032542a52911080c0b80c40301c0c101904c0b0305c6a51110485500000c020954469264408075000045820a000c2941e102800b003410036031040102c640e903403c01070034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 843810035 1250 843808785 843808789
    0x41104090501060915030f140a05091903170901180b040b06090408090910170604050d03050c071403070b0126120f030c0d050c04060f020106210201021203070509 71
    0x1c580c0540b0403410070380001801c00c12448030540034031010b00101502e8102c442a0410160310064002c82c100c4120f5240d8038220150102800c01569110600d1044001e400c3c00200c000f100812080d505a46440f030018090300c4000c3c1401c001b0f02500c215560b07a241c0e01c020604050a2040240e01c504a46c884520f4641012599401c000300540d0066242c1404c01000600090031100f0303860b0100c6403c4c115465025950700012a107401503014122211030710700d455440090a80d10880c0302e5412100302c42a148021400c1e108255500c0c2d04198040c07106100041022000c640c1c0240c208040b20700340181a00d03445107800c800c1c1e2000b940d51612a050b03d0b04651120741d0384605d1000744004040b00c80041040011620404400ba5403404022011800c420644c5040b24180d41e5015814800c50400c088070701b48a03889807140c41d002c41d44182d01c02003000e00602494040301d2460707104440d000f4840010310f012583c01c4004a045002d0b0301d602c0c2001d603417890302a43c003510880d0740d201c0e00e030528441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 843811285 1250 843810035 843810041
    0x90f0b06030a0c05042a110609010603080301050907030207020312180a0803041e120507050109240c020409050616090503030f03060d080408030d0b21100c090504110409 74
    0xd154040d8000000090100d406401d1030402c40b0400d0710002004143c0c3d2140c02240c95050b940c0e842003c07060b0550089055012030080f0314070701000f0075907485898140640703007226024403000300800c1050004214501e81032012690051540c20003518001607a0300003403c1c0700312015241840580032420301c400320105a10301c18041c0081c0d449501003401c120705550360340203500c1030412a180c0e03411643c0c44039845580302401042c10103000144003540d845c1090702c87c5d2260080c94001107041200041c0c0252601d01c021500c2e0003010804443c41136188120350400c10900c05a070419201e505890000b03800b040114400e044c1e8a0404800700d508101c000c181001c0c5034009072103a4810b00800c0094500e00b000c407a00f002d4120750101c03807000035241056290081d42d0107100c071800045596003140c80560020840504200d4005040f400140b2030308501c15400c08501d0002d0f841490094240e54055210b00701049450a0020145550b04001016103607180408261410045003c21035102a80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 843812535 1250 843811285 843811291
    0x1209100e27190e0a0b0a0b030a0503121018090305210703050106170117150117060a020f090d0206040b04060c290f070903060e0c01020f030306010f1110090f0b 70
    0x6400740304000740030030030f00d0340c6000303150015240040450108260b24003030340c8001c0c050007020302a110000c1107810059181d40104c035004022000c6203001602d490440038804090b1805649805001394202c003058006150a80c0100c062200410413071040388030081e800c4ca0010140b0040b9820352170300f4000102911410b131303c22020310840465031980414005c0c002d0707040d41c500e5014100320300c10380304e1868034207443c1c4040c60180090303c0700081100c4581060200f5001909400c455068850b84550012440394540c0040360720f00502000015182003040480d0440c0020500707400c094513506000103913801a4004008246546142d0f4200b085900c0c0b075030a019000c070500c0031808803807045400000c200410b454030380c142e200c001820440c040c000741c2011755040074040010320305524004d40d540c1c071129240d50140c450001070703c03c00080003086900c100c4040c2d50710307405241c8100041c3d070303002054014400c290090701901c420801e5240301c0d400e011402584a455681d0640c10409030300c3c8006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 843813785 1250 843812535 843812581
    0x1c120609021e210421050310061b110f100c03020610050904030c050a0c03140613261204060203010302011d060306010c0218090f1209100e27 62
    0x1072200c0d4805180400b41280550f05006185840b6035562900b84d150140c0e40308900041c002d001d031080c42c1254440080c500c650a00f410080445d40c07281011340f0300c054081c501089008900780d4007030009104042c032201c0307400058100f80760200a500024482550010614001001641140706240d030410005030002000d000040d11030381400c0100b81d102d81c00502c0a0b00784010041608100b100c00c0144014413600a0221005151a407800742041c03241c03a0042c00b1140300c0e400108034100080c0c503140745d801da4042e00507168800d288107200d03d51040d94a1008902d84103009100480003000c2105115600c94040140d49604603c0058510341d400d0f01142030f010001407001074151038610460340c0025003401c020075010540c0c07000540d00341c090241074003040b207840d003404101c0b9000030310020350704012003d482603141b020311110311030701442c591280c0c401c0d0316005c880020b0b805024144404000541740420040d0280400d481e0720000d620400c1907002087c0c10403030400c0b01108026060081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 843815035 1250 843813785 843813787
    0x6091c050313110a0b070807030f0e030705240c0106061103130603090609060c02070e0c120f0702010603140a020a090e0a03030b041b0809060105040c021c120609021e 73
    0x31161180c5403518082c40c00400306a409020a400c6640742000d840080c029074520680d40e14162804815603088080c00324003080500360b0340440b0134040d54000d02c0700e0340050001c01000741307440100007803601e1a44001190601c0d200030301d8060910b8030000c18400907480000b04406160143c0203142d940748160034a8541c00501c00e0a1410b82c255034030b0001c803607281c50045091203d034140301c4000d2a580c0c40051000303140c03401d9004410b80115411080b2030780d04810005903034810f0030300c0540c3c0c410401034800d44241030f070010b140c1920340c4400075080f41c540e200008805440c1d90320b04501204c40400020b503a030145c0031041c1149032201d0300720050000034406010070000032420030f5490800303031070040a241d200c1c2e0b18141292160340c4400a030b49600511240501d902000152030041c00b507684d02e0040c0192000400d09040c81d01034440701c0e4085030300a14400606111521483ca600709104042110f81a075255000b0b8440c0039910240981580059651a100303000c13a0400c68581801c5d24031b048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 843816285 1250 843815035 843815041
    0x501050a120c0b030a15030b0709060801050a1a070609140606061201060f0e060f090925080406060510050c0f010507050d0b0d1704080f011e0c0c020306091c0503 71
    0x60070315212007140d1000202ea07403079848100f0701170094099440c5a990080c00c40e0710010520050030715040c015519a102e000244d1b45542003251803000901441d9002141c1d96400c00035950f89109445952184200860804071075a5601e0259590010140c620089010a040c441030043c013000341c00c010100c621034603003c21050300c6108208148a844c0a105c45015605542805010a0036040c4002070190f40d681e019044166641c0e0886c00e111802460700340006020b0840c5502c130414190a1030301c0944006020340c01c100d83c200b00041013108c40c5a154680080c0325241e01c8124820000c0c207848640d260f084900a16242001140c3c4e101002c0c0e04060031f0040c025080703012900752907138859011644d0807150f404201d80120021005160407011801001c114a40c40007130000d41c0c1135042038540c14042e5460883c02d0f02c1196000b100d059000c400300c00e0b0066a594083c2c151740800f0300300f04000d8101500000d05206080f101c00d000780d003100c1103900caa105000d18260f4a480c050400d5801c3d82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 843817535 1250 843816285 843816293
    0x41b06050a0f0f0e04051008010b1c0209042315060108040b011a0c1603020411040e010b07170c0a1509050309040c0912050d02120304021315090f0501050a12 69
    0x14040311016014003c2294000101c00e2103010b10140c0d280010f070050245042044203007414903c648940d035030b1035207070855075134191406403070f02c0300390045580000103118119002c0060f1400043e000302d8171a02ca04183c4031301c241f590045d1034400c45080700603158891501c212288255002009a0f0402581c038007000300141c0c0b141c5d00c440c1580c15044903034888001c4408100b006201d541c0706c0340301500c50340707400038034a0303e00784460700039680300b590705002d06050010109814040c1d0301400c09400d030f6603001403008031494009001c003140950402c2e0000c404120301e802099210128410091700b12038103410078460f1040800054a0510904000200898940940724003d5040640c443e03900c9103021141c1c1d9200f24010705c00303003000c1260300365400a2460401d41c9c45040c800d03a54058001c0c1040d000c2814504020b0300e200d01c0d0080c04075144002c1c0f084907103000f01201c0d00b80003800f2541e000c011800c0101c070b20641c210b51180c4500000c103541040100074849440d680500000102000588001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 843818785 1250 843817535 843817547
    0x507050a05062b090c05120f0d0f0e040e010b091501020a02130608060708040b09011802120a0501020a120b0a30120906080f240402070b041b06050a 65
    0x480d01950080c81040c451210364100504403c03e052071060800803928180074580760004111032003100d401c0300c5c40007844601e81d101d5988805280071504070359181c0c3c9803540035030301e040340c000c501d40b801c921100203100005044860b56004911039079940c020700c0d030301802c0c19030365140c000305071913140030449040c640001d41d90000440b0090086158030481196070202c2d41162000e0480c05043d07507006d00d03103544001d203c1c800c210b40036a0391002150103c0c0c00c006040c071440d800d04510b807100d00400c100c542c092113254507804584102510801002001041084c405031864400d20356800b540540848188020f0310024400144030b017089680c20002ca41c1d07a00400c0302c051283c00c1200300c002140c01400c2850201819003e00410105035003080400e0744003076890142d5841d40c5801415440c0c2c0350814421410031100a020003172105444065107403401a1001c00c1c420040025280c0001a65a1041c035070041d9012a0700c0710045200b4880c001214040e1b1015001600e8018140680d0314401400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 843820035 1250 843818785 843818797
    0xc040b091b12010b091e090103030e0303190f1716030b0607050106030f02091302030d27031505011208030c03060f040c0c060e03090108040611160b040507050a0506 72
    0x903080d4034072000c1c1400d540e8402550381eaa4940c400a00c4150b07510950b007580c030303403181d40c0c403501c101d001d9025900b85c80c0c0c500030510225200034250076042c0c0c1c00c55505a500e0010241c4c0c080d031511081c491002140c0003640c2c41c0311000d1a0f80d071452360301c5449200190483e6941c038071000010351140200070030241c0c080d080748125100d0789004591680b222020541b03621482074060300c0ca508008010061091402d00307268050720075a60101c0315562124005040c41104100a50641100c035248200768444c4108455203043c15025803402000b20398410b102070140c1e4411260300e90a8501c2c4038000700188621401858103211040801c1401e0340d4004007440001d080120224000c00850200d8a40500c6041c0c00c9001810401100c000c9440203040c96904090031180d003800d0012400b810740b0044240c54080c181038451440c00d80b1036a03946000342c103c2a0074119100c034244103c01d540440c1c01c02c400022402240f071a541421700b420807604280582d005107002c0c2c40c210714208803a444450071114 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 843821285 1250 843820035 843820051
    0x12010c050d0b060c0304030605010303080c09130c020102091917010507200111070f0203070b09010e01032304030c03020601120f080901030b19080601150225050907030e0c040b09 78
    0x1045401c0800045044c02600d25910151001007000300410100303a000c64140ca0080c4c4070001e860b90354944007011803043e07140554000c0039480740904e401c900c9800411a4041c01d00016051981038001b2400140081031070349071041c03190380e08000003034460312103003a9242d0707050081c0820320b440703e0041d15402072022034001c000340324014030004200a500604000300001d2140e82e80e9211820115501c80300960141e11034000c01200081d0590301c00201c684800041c0c403500c4451040c0c10064005080d00f240301c4d640e1002c501e41580203039404d1581140701d10700c03a44601c0036102c10b0b81802480c0681c160040f44000d210807101501184010242c002040e0744078500a555604140040b0040d14800750617075000780354600083c01800c5080460410380700b80404640c0160b9031200c81d201015101c440b00000368010403029680701e10310407140c1204645440c070351100304c0e0342c480200d803d64104468260000c0d9580d14a00344a004c1070220f029000f00c1101d040c0104203a9100042e089000980400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 843822535 1250 843821285 843821291
    0x91f0203071119030210030e010c0302030a18020307060c0c03050708060403090603061d0903091f0f08010b0d0e032503030513030206160309020310020304121e0f05070203060702010b12010c050d 85
    0x2d40880c03083d040f4a240c45648c3d4002d0009208420015029400c203940d4851424107081da802421521a050004107e40003002020582e140010580701c100c007542d07081d1480800020f002c40030450800c00c0c41c0090421400504803841c2a013401484108d05030071180030541052401c20030031451031100b400c4016200005100c03900d44042080c075500c40e046400d5001b100c0c80e841e11032507030b01c9201000c1c02011161581d100745c3d4210041114114024024a0031142003802929a0b00d0b1055000300a01c507018000c0301d1800240b0b400110070040104181c0150b03080e45104401055494040c9a40203101c4101001040f101d590f406505c42c40010180100021581043c50403580b19400c10740c4000c1d00a1300b0340300c149441000c080041d5100720380c262000e0102c4d0364034040b110703c102c50448543d09402d114461403204400308440c1d0018a032403000410400341701c4000540e800b4815580201070340d80000550f00c200310184010040c45011400299240000c2a449990004202e030788107590880c0c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 843823785 1250 843822535 843822559
    0xb030112081308061306110a081f18060302362206091110140304030233070302031e1003080307050c07080307020f06091f02030711190302 61
    0x203511042443c0e106042900c260401d000e045014a103042400c10b0150005116203001e11014440d1442844401c0c0c002501c04400100080903032002140f441010445484036159100201036010b840d038a401c3c00d01c0b5588040420451500e03140310a0366095845201081c100d140070425283e02e10500240c1e04543c840780010b0f514241600205055101c2e00003003903800809050450003401d1282c811200003000c50816140751600f404105000d0032150340d040c030140c0401d400149180c02c050400c4055100d4108540008450310054010215159500000c0740120303008940b142a030190031003090500c100240400d0700d0310781868040200c4c0010300900b6941700c407218141c07030024950016010900100605c4030040c1d00000412f0b06400c554100d507080c43e1100c001e544c40b40308441c8025481154110943d00b07078200071001e8107002c0002012206070702c03024000d1017840c07401c40a00b400107030000601c5408100d008520b01c101c550050b101014001c9c135400303828090305424000648621503044031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 843825035 1250 843823785 843823807
    0x129090f0a170f011401120f03030b061c1a06031803040b031503120301060903062f03070f170f1b04060906171902030c070c12030305010b03011208 65
    0x8940c0200b001d4001c0c1410750300d03101405916452505140540c0794200301403903911810008850b8140c0361000c4020708034411a589642c0c0c002c040c0c1d4411010306490741c1101100355140400f6000711040100c240c5106c0b504144c290382210b10b0070b03e0014541094000e180d80d56110b03001074aa100b00115411180b42c050305601914500841e44558510b0b40000300300024940c840503030180d0081c059003142c1c41304103155840e4103a80030900031200001c80b800410030100d1001d401c2514508490081001c0003210f40d114014540c0d07002d01c0040d0710020020038070292583c48002185000403074501b0f460f00441042440d10078020107480a08229041e4010500207002001c5040d424a48113100541c0e0b140e8425018107070710101e100d10000301d0f200406d00707001e800000e00843d2103003030b0544900c03c201203000e125000079013000c1c01501c00d180040c07001c0c00005040d00029005000402e04849000090340740080030750b00140c001003003101c018030041003500d0486a030f1101c510703480410035842c1c3c807070816 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 843826285 1250 843825035 843825049
    0x1050f180408210f06100c0c090f14090a02040902120625030b011b03180f08010606050304080702010c150e1e0304080706030f09080d0e0f010507020c1c1202060129090f 74
    0x802303000c000740202c00242800d00c0d50321100c00f88840ea0010b100c5401c9a01c0042c252580403240d007010350f08020712010052402d6448403500d144000e1098a07000086034417140707444400c0300d10b000c030440107a080395128032a440d00715030082c0d11803500f0701c60414024002007017602d049280392001c001c8044036004142c0100d1000304008071503803089046541c1c641d400b403403041a80c42010f0f855468a0408258513103e401103d00c5244c0025090b46445000d034011079a035080440295034601d41600700100680715070090100303a015140c024003e10500002000612060000a261962003040b080101e0b6a000c07800074100c42d0700e41400100b00d18184d8104000d8160706000800e260340004801c4d0304ca41082c0d026601400c1443c0031070300d0301c0c0340d4445050300302c61095a0760405a8070210324842c45150088c10507655035010044061002c0e0309588810702c03d1030300202c2d01c0c05604150018400c181c3d904001c1e80c40307048201c46500d901030049120845910403440020700807000e1303403013544217038403000307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 843827535 1250 843826285 843826307
    0x12110405060a020d0f0f0c020603090a06050c1b30041a03071b02090a0e030d02130e0a0603030e062101060504050411030c0301050f180408210f0610 65
    0x240c80560b5510022000944642d8110030348408510704441e220143d0348203c071004407107141d60f22516028000781e000c1083d90303040101500c007039200b06c9030004001119405024029108444034585654460503080c254a240035120040d59102e030340344060031032415212800001d41d4114000c564051a61468414440c54000300240c1c10a41c90240c01c8101810085116a0303843c2e8440c010b0389156030800440c1d585c1c0341e0000e540300e0040c80c0843c030f003e600e45d48a0014041040112482e001c580c0f800d03a0143c0c3c0040c3d080741c840c14011300b020440c084200c0709003039000ca14410708100f600d046980180130303032032120b070558020758000c104c40d00103101c82d111025141c1e8400900d0745040d80e4940004019500600549005d075050088280d0018049415207010b1100301c2c6041c0c1c110303803c260604c00c00c013403c03220080d802180c15617080c03103625a03465524000d6008803800755171500441148500c42226441c0201300d10075007030030490f5005408a126400182c00c4410002a29007110100c40c070707003441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 843828785 1250 843827535 843827539
    0xe100509032203170d0513170c100612050f03122418151801030f060b060a0518010f0c170c0706180b03010806040f051f091a0712110405 60
    0x6040e0296400085070090300c05d0501c490400e00c002d680ba044021001804404028a280c460740958041d1841240c080d03c2c0c203d1000040308c0404000c03100362401d4031b00342d6112001003006c4000000a00c075007404400212909a0b00462926481910b00180041f0092142c6503601d29103a40450300d244188c55054600c90041c5440243c082c444550b00408005540c0c050040a0008240ca180e0400304001803842110106100302030f840e588500c1100510715030304880701580c420203000142d55800c0545128a243d5445548507105100362454468050b00741605101c0c5401100c040d05504c0210600402c2e408801074019a03c8818141181c2c054102038444600990101017002c581c4682503030041400d01c1e188191095640786e007070510344428020103074203410190019001c9440b44d200000018490000c132142107500031401e00500e0301100001c40c010392991110003e202c0c2c8200003000c050381480c41c02c07429060802c1c001d001915207492000c0944d440d9a0603600741490801918024400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 843830035 1250 843828785 843828803
    0x61c0e0715032a020a1e0606180c17060f0f03013e0912070302190302090907051c030e0a080d090608010b0706020f09040c030e100509032203 62
    0x30400c40500907003070302441070f0300868014810307880382c0d00d00407040802c8581e5038000c1c001900c041c0d110440981c8078001003500402c69040d00500044d082e106601c020500f01c41e40700f0104410041c3e160079135500c94200300810a16140e84041a4070030310700303d90080c004171045403009200b0008074212451048843d80e041d464080052000c01441c8000913910b04151000c81803809000448007100c00c0400b802c412107401800412024105020b158820030101d80441d2140c640e60303400035504900c0700090303040f00b20b0290010811810010306690300062804090180b8034140070120b146050000510071500300c081000c0000c0c075001d0396101d0340a5a010380682801d1340c031040150381d2032454070701e800000b5900000000315940300f070060301e040e0780306070304041e1400000e07840d20f0b406504070300c072520b800ca201045801075a680c1c601c034120703501203181c42c04606a4042444142000610402c4090050501c0100b02c03c2c000003004403510101c064500310003810380d80c134a105000d50290130040109003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 843831285 1250 843830035 843830069
    0x702180f060103110f031303020703060903031a180c0310092a090807050603040602120901060f0504020705030d230405010b130c0e0904030e130f0b061c0e07 69
    0x54003000492040500382c8091001540d00c0c10441c804d849095034002e01c0c0e07403040c0086260f010716040e0012206010b40b049800c2907449440f020104c691514013200800e07902c10700c00a288540301c03000c00c4105000c540c0701600000b03442c00e600041d40c000300103c84034100040020b210600000180014150b404401c1001120342d890700c444251441a07243d0a040400c480340002078401c10324002a90001c0014044c072a15140500c0342d143c2000c0c20854541e0303000e22a40f1345080c1c074880d0311441445d41c10300109620340703050890440041184c00950182e801006040c0101e0000000c031904401c60400008004141002004105e804400a00d030310005810900080c090150002ca651035400c84003141d4540b0305031018801c480311135107884007060000351a103042c0d28166690035845402814540c02c070010000c001210324400c0751041c941a60b58030703820b00410a2030b10803000310303520030b5800a183c0504503c3e901c1c0f91070705100624849075142c20b07524480040070700804d0010842d012001d10010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 843832535 1250 843831285 843831301
    0x40204090e030705070504060b12060333010b031605030a0f11220f060f020705120709060905071b03171003050105060d15021803150906070504050102070902070218 72
    0x40e2140f841a00d071841500c0d0049071616240c8904001c490252800618180244824524910b001019546c1c140145400203c6000ba01e00b00d000e1044070200c5408011500500b030101c1d9043d068000c15034240c0c01f80708200c0504039200d81d078090b00381d09081460312a668003102102034600c0e5901890704908094a004040014401805804001c41c01c0354000c414400075506000707d0754410019081c00d906800c1128038016800c15045054510640f4252921003001c11000810007610008035449128108000b01d424030074200030b04040038051101d414118402000c5a0114100390340c040c0ca281d2040d41050f000702d8100d0003008804010b540185851a1101060f1540e4030064406501303120009810b440c0001c100c41e0b0b010b034840300500e10f00100303000000007508980c0c80007946240740c2401030400ea50410001441811541c0410b209141400310300f818448082c2c070701c105214080c041440582c0e008035110090321101080140c0745d80550001491014420000c02504032450080c803c0740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 843833785 1250 843832535 843832537
    0x2030a121815050328090309150903171c0e010c0f030203091506040204080304180606080f0601050a12020a1d15030408090d080f041a1611040204090e03 67
    0x1074403900340c40c4034020340d0300e010300c0c1600a072081900c1c2c0098002c2000448907040d82900040d80c1340d02c4803c81115a01e41205d06049485206081d03010400100c2c040059641e42103090410001503d8541e00540c510f0761407e00c030003000d004400312148007090042c04900001484290500b2124081c040f44001d190550300801e144000800010721321204000498007a00842e0b0082003840e000740182c9030100381c906c00f051030107405c040e4420740810001804280c10006030014000c1c0c01c0001d480110b0141c003200c11600070b40d0241d000d220040c81044000d0b2100c0b440741c1d5100f142803c042c1e41d1119094412108180d100d10200e045a10104040486130303031004400b43d40c001400c0c4907000e40082d8504000c0800280f4201412080307081002400140c180d1001e4003103600d010300101540025a600d0350341390b400c8003217910512800482c04020004070044405540031050416a103000d5081c6003402807084c1c000001340442c03500101141664035594120350080400701400c100e104003a144094503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 843835035 1250 843833785 843833807
    0x30a0f1a0129210f010504181e170c0106090227061905190e0d0303051003020a09020406090503070f1a040b030f240f010c02030a12 58
    0x80c0d400c060440005081214404505903991110016880100c10b182050140100d101c4040b40d032030140030950808144541d00d450400e60481c1000d020700c0c00007404141c140050f13002c2481981040105c1424046401d00d9052884d00304180c0c84000034480c180c10703886501c0c5180103004801d072a11102c030590b4094080e240e645140070007031102035603500c2c055003030f80a070052600d0003482034074280400c600f011000010b01d40000d0030361820509814612100c8201c00b0072403002103000083e0402038a01d1003c40302c5052240b600745081001c911501064920310b40000060500d5070b100b002c40e000c00c08084107480119401072021802544400505010307400c28811b000200c0c100030004901c610300846d840040e41c1c2c100b43c0841a030383c070f040c08255a080c070000022078080320070040800e0450750b2800030743c49507400321580f00e01410500c5c040c0d00001580b141240d82c5e4007041c0c400d400d81b591101d0410320600c0003464154507481b02800044d0615440c984000c100d486090500b4040e42e0b0003400d4582 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 843836285 1250 843835035 843835043
    0x307030b0f1e0102070305061f0e01030c090902030f060a0221090d050a05041703040608090d1d010927050106020a0c03060507051c0f0606030e1e010b030a0f 69
    0x11a6041140510212034094030009600001e40c0b14824621080b05180c0c1107045030520440f42c91540da9140e81e401c01c6801d40d48206400031508550040c440381d411490014094008000c10300d42c550b8443d503951070228000e006503103441d4110300007555003c02817a51b010300100140c513481c0c1003040d0100000c1d400b0940141c0c0d84244840c00c40e11111007512898820610080035100309580c4110848a66022401280078882c0038400400d04848560b10700c80c01050060045642c0ca00f070407005011b1000003803050449500107210000c9055020320786810030000016002c05900c00e03c0e005907113000c2240c10150481240254201c0340184890039400380808204040201c0d980789c2904a8070783d03481d07490142564021100c06c10000d011503001315803066180c6091070032b0800c0580305110110308060300e90b008544500c0f42200740307072040c404c540040015080800201003450519a11034000001d4442640301164450403001402c1d00a41402ca9004041e10580d0090f894440b024096100e0300b51 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 843837535 1250 843836285 843836291
    0xa110d35030a050f0a060602070e070309140a21020a0321021c060b1e2109010e070b03130f0c0302060c0f071e120512031501020f07060507171e030703 66
    0x50301905c4280314410036a202503010b4942a030902c2d005100c07003500944220308041d0707a20040400701c1d84200a0f44029402d81028285d4500d0b2810801c44184103c08043c0d95200c0025a5903541500051912031207a4941040882c65000001411a0500c0503030324000407800080ea2068101140b81e0062a584108201700032198840f00017001c0c500494114000c000099200302e9103100601380a0414811050043c4441c00032026401a11000c01c2d10200318a079110921803200803014420300c009002840d41c91410340c0783c4100443c07800d90541c070001d404503003a8000310091040d4564808061071300039184982e661502e0700c034180c1c2c4400d00202c250881c000e050340400c0c0040905508845203109100010540342489100410309145160489440c840d401c0c658800c40d810364013851181241c08408110f050420001905000c400101d408058000c0b0500340101600312081d06c50080e0071500c048201d4241041e02d456910418400c410030004651403c12010700700401588903a0b003a035418 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 843838785 1250 843837535 843837541
    0x3010906031703010b0f13090617010c17010512010e0102040609061409060d0513210201450c0e012102030c090c0d09050a110d35030a050f 61
    0x1903082c3d00080c0241c0d0440c043c20000c110080400101422000c00b0800215048568440e0010221403c40c1e2008080c85140c0d0100301d043d100c00c0c426001030b450070f410034540b038018491f006c1c0071050b01401800d04c40d10203824200c50a0000f548001d1484d01d4441c000c41d45c1c0e9454080c003400901c4a4071036040040c500004401b10344030301e40107a440384a030103000c05003455031404050000d070034000d00b46501d403002c2c00640d20124207552601d620729150501c1c28010301541940c001c1c2902e214443c00c0c104c1e410702005440c400c2d07031956482d03008507244840110301c21101a034040c2031072985c024040c080001c03c4401088000b406804d56048905020008154020f00e21201680b4020b40c1703006507141e006084040000c1c10819000f5900080340840113181800c40b2a0010031511070b60401d403850b500c50145803041102400d684138203540200c1c1c21080449080e980d004500120300c810300c2c0c820340c107464000c100d1042444208020700340d03071550300c0d224603020080d800108021924913a080c243c00000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 843840035 1250 843838785 843838823
    0x907060f020a06201201090b060703021e070e0705120a110a0e0a1d0901050a0e030d0902060412050d02011a060a030b0d0203070e0a050a05070c020910030501020301090603 75
    0x80c09581102a030040c0c030030580e20741c950340010a503003c4c5124031301d00c030b031404414100038036001008854500c400808540d41071102c100210303800044201d005075820450701d40800d40005845001000d19800107043d4054400c0860405080d039018910359410740b0300b0311550a400101500c1030121201c1c1602c0daa644e0b0a02510a07170f42110323034070b841d048030070447d64060a00c00c00c8280000c541c00b03003000340203981d40d540d1001480c0011106880c000340071070a01c014413800380200303034001301104d409005c02079107207420b69100d00c01c5840e0780064554400359041103403520000e0f60002c0c0000303001044010b915080c0191952030844410006502c0c0c03580010b1486c17540c0e6030401501d400a41542d04000100105400a003001601564082d1440084000507a01000b001b4007030081405921001d081902420080da040503141c08802401e0008003e0f555902c18858080f06404541c0808140c5942c0c9213401100c0036500041d0480d4000000490f000c04a90440021284284110606291081c0c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 843841285 1250 843840035 843840047
    0x1104090b0d0c12110d320706020a03090510080609070c020d060204050414090706030c0210092a140f01120c021f020705070e04021504081b060724060905040803090706 73
    0x8070007040c0c06180d51b10715440242e02d10f000117003812900c50940700c2aa09498035031400b44d4039480b04005034000c546aa007015402450140144801e80e03460005480b04000503105007002008503004a038604000351010344106007040050750007812210b081052030031708030040c1d409130180310b0140707080821144940242c40481803080000038003a00b115404c2020480140000c901c0c05411482201d03105084400c6034450340d80c55a2244d1405954489022001e40d84c0451400008110b03c4a80100308070101c0c510701e144040700401c80e00751078100002001641c451071044032100d05a03241080360341c40281c0000302103503d282012010300c03500c40001076170030070b030301c681e000081c01d079045024100b0035140c81c00a010f42162000b400c0721940d45110020f041c098005500644081d8000c0d5000c1040c40c3c95500c00341192101529168580340594841c1050031401c103011100002c0d2a0b242e410640c041944030802801c55907a051060b030601d07080c106402d820503156a102d41c0120013002801c0360040d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 843842535 1250 843841285 843841309
    0xf081c0b012d0201140a060f0b0a020309010311120a140c07020a031223090f0406140118090f05090d08100608040203150a0504151104090b0d0c1211 65
    0x42c0203102050031520b03410060050300700044195034039803030f0356040e02c0c24001045202c2c1c0c01013200066203e1130700d1400440d2000507803000c0100760040105800305c96011007240e10410b020300b03000ca206800c08008440c14400d11182c15143c080b5001408021106508441d1118071110042c0e0801c0d00c0f0400d290f0720b28811500000d61003020000204002410031200f4074105410b428000001d956002c4040b40085904070740a690140000320124a440d0107071556040c8031007528104034007414420002d110050302d81d000f5041c81809000240d4858161041d440600700700c1806005d250b15030003100004d49000c0e1240c0c24680a40c6400650551040507124450a00072040302e0800e441d00e64140e1b40c1c650060070590f0035005880407405040f02c0c240c54140251060b42c4c0000707407890103040840d401c031640240202103a04203825003451282d50310a80d02541c007001400a01e50812000103449010508801002c4403a0301d00d0001e0781c507042e01000da02c1c480c000d081d0503010329003e01c00c00c6500d407807030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 843843785 1250 843842535 843842567
    0x408042103142d0d020f030703051b0a032d1e0203040209040305160813030b060103060609050f03030403140102031b04030c03060207030507050601080c0307060206010810090f081c0b01 81
    0x142070062285009a0319003400b0300000c50152504c00c0c103180d40000c2c2d904c0380e034040c40001c000000b0720400e65814400e1340d0341f0210303601c0c0b010505207405507480620302c14108002d003090b80b50088075104c10300e107640c0d031020900c0c2c102c24000c882c0d404942c0030f4013814060b03034940443c9000203c075002c8983c3c81e000720f9201c1e9074024282c90040d41d6075034060b94540c0000c07181d4240c2e200e0076411100020714190003400d040350811036500c5124590300d45502d240354010b00150405060040070000c483c1c1208000068810840f00d039182d03c503131417022034030358050340d1b1000e0104c403140c0c288c0c10281481075000314005c1c50180c903c00c9082550400c01301440c466440001c0c40e410000c2c00c1000400c4050f80503260040c0f0030300d8024a00191a120a880c0050a8100f00c2031a040041204c0092800308015001498180081c0541d50b00d4801da098490344040c0d0320031392040e141d41c00c0e5401c0010b060070b10000d0300da000c02c4071620740e41c00003904010552222500c1c4c51071460100c00380c0c4590b00450342ca0240c540c3d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 843845035 1250 843843785 843843817
    0x1111c0e0f06041e210606051c0b091920310207050607080f2202061e1801092301181203030504060c2105040804210314 53
    0x500703403138050070748803d4035990801c00c041c00011920000c0b121800845140c85c150300e1030100d0b828240740341145d15070303440940b241d14602040c3e0803d240c0c07102800c04183d00010712042665a00c0c0586003803140988803003121140f801244010841d6120f40514040b41c40640110715a02500a00841d0b0b4505140307048514418829002c03807000c0c04900f04000f072201c0b04050b0505145682c1c0341c0c903140042d82c145d8046000c5004100030f0300c4800c030310203502074000c405040594400b4821003040d08080c0c2c10190141e20009401001040c2c1c25000384050840b40600c2d0360b0300c1c885011350340ca118404a59840c000b0b4900a000a5402d50201c680104406044120980196100019079182c0c450b170014240250743c1400c006800c1800510044009000b5140803e40e45000d00c3d052045440009520081c0040d40c841000e8800c0c070303103041c607184c8a210100000c06488601b8065118010350b80300700c0d20080030103030710300c0142da941d19001540b912945441003040226040c2c2d00ba0340c0240b400c500c081003c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 843846285 1250 843845035 843845039
    0x1314180619110c1b0f0607080c01110412030f030504120309022d0a05030319110c0d14060a1b0f03020d02121608010605030606070201111c0e0f0604 65
    0x262401c420107031068441c90004982d66040b8080c10703681c02c0500c064045403c99054010380808842003007800500c00c0b074242c4240a0001e000600c54011075038003511030f18020442541c0d46030250f0000b40403003201058a52190350303c861900e110710b803403402180003034800240040c0180c001e00425008943c40030000044120152045004141d42c40c0305a0b8002030f100507051015103000c0e003003000e4440c0c1c0c000c8102c6030324030441031002c0c03459a68401406684200440103000103407149601c00305044d03240c51090318403403104052501d411b0702000c5502101e0b51a401041000303a074100c6160740c0f042420707070300d0702d40c1c0c2c070004441103500b02034088c0413542c0c0110541790810702c512060341c50013140e41401810814210901c400702c1e0040f4042c800c0e814864814815200000510000e880395940380550340b030341c107001d801004ea01002c0c0041e4001e0101160030740071603004480d80020940781508a407007040741594001e1140c45508241c60101c0c201c000798800a007090b51a20001d01c0d00504414038040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 843847535 1250 843846285 843846301
    0x30d020a0f1101051308010b0a0812090103051008030f04060813115b0e010c0215160c1d0417090909030904050106030501030f0f03020c13141806 64
    0x8100c81034443e041001c01c0008a07001c4140424210140c0b0f8a040000b030f08911900a008208200c0d0f00710800c2542301d6a1010805503d00d0125140100c0a280224503912a14015140c10003650004903450001280795191400c0400251048030a150342e24681d60702c840020001f00c1450440103400f40068141000756407c1003a106070150100718414488500b13220205441e5900300d081070000c110100d4106400460820350104025031703124206d12000d0b0349403501912644150b80703c6818131070612407100c103543ea00c01c0154002100070a41956450740c0402c2c1007141e5649a80c21901c032240308102042000c903903a2035401c40b81036041c0c0218207850340d481d02800340101420040a1002c1003040b074540340c550008090246032544000d41e2921400700400c801c3d514160420383c00c0600c2e050040021610080030304505176080705007202050141c0c10102c1c1040c003e01080342e00300000031544038100481341c3c02500d0110010003a884e83c1d446008408021102c10742404880354845808161a6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 843848785 1250 843847535 843847553
    0x10605221a130504170a300603030804020a080d050909060d050111030f0a0506090c0c010608010c0c060f060b03041b051f110109051e010b09010311030d020a0f 70
    0x35100014048012482400041e8a0b104451244001c0702d44900c144802c1004015184441d401c0d8500942d081c00d00d69000240281c03580131b16105440100702101030044444002c0310801c1481c91418000c6a8403403c014010441c15a4100e008911000c40001d000901040300311005e00c1d07543d542c0d132070984820100241001d01034103159000713100d070416400003a4240304041100c140785000d00c0c1c4a1030401c201c42c84102c0f00800d11801981410b08000c055914003c1c2154040d400326000c0d038503044408540c500401a64106090941c40c180740c141c001900f000f800e155580c420719062100300203d106040584a480c490303c002010140f0104002803008500c0c03000301044802800d14039961000090140d640e0101c0e41584060100c0b03d00c041c007640452407041d0407039490001d000d00f510503a155035032000b203c401c111904c1001e41c0c0c00481c1d42029040400c039038070000d20300809540c581c1840b1085000c44407147d4403900c10f0801c07040ba903d00103c0c0c45040307150020401c0ca840c13400c81d10392040c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 843850035 1250 843848785 843848801
    0xf1008030307120e010e0109020111010501050102150a090c080c030c330c060c03060f030d0c080c030c01050117010e0a0b01121505040f061107020d151107030c0501060522 75
    0x80740341c0342e404c00307194000240b044200c0705400d14000b10303426400e8000541006c503c800c020b03034640d0501e0014403035640c0000e03a88245005034041ca08190b0703120700c280c0005000604005020007008580060803417000103180452004c12020b46411004007410800f52050040e081d0042c00a105080c0b2042c1c45082c11010001489145c040c0c584a030b008250f80c100001191441c042ea040402844000c3c208107100c650740c010f05800912488046150140c610100c6110040c0245000111102400c1e0180144c0702e520340007500034080c95846444040b0300c0c10307203c81d504250358030f4070082c051000070000c1d0300b140c0c2640040016800340d080c03991507101c1102c1c0b00e2040e9012034034581d2012040f0800d03c1058452030042c0031681e880c4086182940a0318220030201441200c14007034000075942c2c0226080b0740a60000100d003c94640400e020044c10860101299600010a20f8005e15400084040117144a04000c0020740c0e21241001081141007500c40d0108204c0314258404401c26031143d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 843851285 1250 843850035 843850067
    0x106110f0c060d110c010f050112151a0a06020606031606051c0207020a1d0702071a0c010b090907030c080304030819030f06150e0306040503030f0c1903050f1008030307 74
    0x14614620210f001c01300e510040c20700d0400da640d5144044900841e20803240940400d51861303d800c041904d4481c01c00426401e003040381513035004400345016104c6980740320808041c3c41c0c2840c41d503035500080d44aa81c2114624024041c480100351101c1034409140c0580f6416103c2608100c40f0020502c03800419450b402c240300e50800c00000541d0721000c560b001480014981c101511860f800c1104003100904418195886040148200050541942c015140c502c40d1681c644600c110780e0790241c0401b2070000e820104c1641440000a40407460b07000b52400340c040c3d00c40c01903503165041c0c0d44c0c2c8154800900300038800d0200303564951011178a80d42c2c500d007a260200b5000c6103040e10300c08480a580c07207051450048902030103502c0d0031070014120040c2c12805031590385015102c158482c400285003400350389444002806401c4958156010b8100070722010b01c0c00f90840300e015005260544030301000304145030001d86000d160b40c105100352841900a5411510b40b101c09541136280003003014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 843852535 1250 843851285 843851291
    0x8070501020403230c03060108060a0b0f100302091e150d02091504050a0501030b0d11010210020d0b120a0f030e0a0801140402090f040b010e0c0d050a050106110f0c060d 74
    0x30200d84004001340c4c01c500c6408400c03003019035001c0748516200b031803075040e400394001500400802401149840c4d10466481c00440e400040030700180c4090010111241d01020003481071150300c0e41540a0000c0020595a6101c82c0d070b810005030b50b6445900144a9001c03c81020b4540c00400d11070150814442c0d0140c0503040c003003041c00089450803010541c0500000100b0100003078505104d40303600600013805c0402c107070318000c008078081003001070010b0b00e4040031980d203a8041e4800c0202a4619400d140e0031900c0d02c0b140d50b00030700038040301c44200344900c00d89018400c1080010a0071180e00c0c1d4401913494808a582e40c040d070300d0003040024550300800c040d200058601c020b0007940d4000d402111420190300e414030400c640001e01070035510003000c0b07046c104000913043d402c001d8103541002e07400280fa0340e00c0e00f601e0314841c890b03176010003482400d101c10302030086080d4100c0c50580f4501e84810741802d08506030a42c1c1ca0000c403600c00c40b540d1140e40c6040142c100381000300000c0c05185008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 843853785 1250 843852535 843852539
    0x120d0f09091b0206100f03080906070219050f040e0d180b1b060703110a030b030a02180717070903060b03160806070212040608010626100905060d0f080705010204 71
    0x510210b0b80c0d60000b0074850804800c00509059060050503800401030402c4404a030411090501041031800b002342480000101c04140366652015244400c0d40245035451030340c5800c240c945c4100d40c611443d4043c1081001040b45032900703005030106004010010034504210300c904942da241200d4040181c08042c180c04a1595011001411038405901d1400d44091b442d00c1010310788400100203100f09840d18201240381003103001110500d40549c40c011907074942100029003050302807100258131190352800034800c1600c0364a403070b100e00e82c0d0b40c4074620301d4000030f20f05c0044a0000ca4030034000a45144043c0000340c0103500091490300040c0c111551411322080c07400341c05c40c0540150034554000c2e020810090360400030035044440040145007020b1800e00040e11180e0f040c01100305005100040d40c000c8581c0a0001341c8180814090400c00c1c2020007203140103a410f409601c10040c203010001c3e0450400103000c95205502040c0091403522648078003020b60001c000440d501e5408100c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 843855035 1250 843853785 843853799
    0x6030b0c2d0c19030507030513050402031810090213020f09030604050c030708030403260d0c090504060504050613021e070b01052707050d020903011415120d0f09 71
    0x10080c0e4061106490340c0da1000b00c214000c0c9450400c40116101c046504400000242d00c90140c558650341070400c292103032a00354010300440d40a070401e0350058804000c001904030b0000040daa40b200440c03d80d02c0d405603000c0c058042da00c1201d8083c1d0841e000210603094408103034000d11180390700c83c801d14104040040082d0520205132402c1c0d5040d80031042034042e07882c003401084003c1859600452619103140d403800705299080811607000d001c1c9980344082500d942044903014404120100000000d140d8064600e001c07034000d69000394609000810079040610959000e54401000ea081580c1e800c1610f6003e03500c000c02e24480c840d200c18020b40541d030040040c1080910440c1d00c01d030300350305000a1150a40f580070302074111880d0800201c110540481020b030b0440d0b494a8815039405584407081c010380302e400c090507059031130036a03c01c60320004a420036000341443d000d69002540d004003000a1001603000a191075001340d511320004501408407030303c0081d0f8031704001c0b8295680b988 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 843856285 1250 843855035 843855097
    0x60f10050c120d052203051803100e0c060f070b0601020c09010806060102060a091104110f070b010812120f0a0f0603112d06030606041a0403120306030b0c 68
    0x402c0e624501041403007200c0b11501a550340684d004e000c0c04031510782e11440382c14140d03010318091300744040000d81403000f1a6003a0410182e081c0901111039264290354088010300c540ea400e60400d00031b00202950034a0481d00712000c0880e0303001c26a007040e140e5250f0345240c00c409031169040d8400c180c0920307020b40301d481d007090080c400c1e01e000e002c42d4034228001a06108009200b827200e00d00d0902c6440010301c0e0031000200c40341041e03800090020186008040038840c17008030031030012010461404104050018034141d900031402d80d01013a910b5414a1564003840c880600c40e080000c0c006404901101c5000c0d81c490a001c0c0d010404840401c1c0d09030440d0304580055a20403c0101c040b82582090054041205035052049102c01c0c60b0846000c1c901080400e1548101c0d0f00001244440c0d0300e08042d10007078046e0035590010446141c142d13030340c030354040d11007110407001c60000300c10300070f010f403054900326904032003080301d20b0b40d0f4016500110b500910342040700315108c03140000c4401c0614 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 843857535 1250 843856285 843856303
    0x70e01060504081603081210030618020f03030304020d08030703060918050c150307030207022101060302240a0807030e10021e0702030d26101d060f10050c 68
    0x40c450750741c0c03141041c060605000e45654500d01e50322241a04100003400602120000b9048036108055501d610805200f910901ea0000c0c0c045407c24401c0352581384445500528540708947c0007444008080070706031039000449019500040260320140407844550082d648031080f4640010019120108401180e040300e40c0703100410004030510040080030420146e41c00c03400c50b1f6030030400c062410040b1007484010144010150040740480440d1201064101e41c54294607c0101000289941d00d0013004507120030b91003442900a040b146c00312180b10500580e003001000303840d0580710041a548000060700340300070140c0d00d22144450351010700c03030310510700349851026030ba0b40c004c40c1c41030b2043d4800b03c40315a044402045100010394002510440c50303d020b0130400303080510003181c804008030060b400d61030380c5c15500c10040001440f00b1140103944402100016020780c801001c036245004903038103a0071601d200c41c203281d00c0c945080e02c1d40c50208146001807800100038401030500c0550 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 843858785 1250 843857535 843857537
    0x310080c1e0109080d051c090f03030f02040506030c0a02011b020606011b0503030405150c0901020a06050a233301120e120c0715050f1c0e0c0103270311070e0106 71
    0xc140840150100d0010ba4002680c1500901c8543e2468880227241c240ca55001001c0c1aa00d820070000c5007140d030140d60081400929140e180d14040801c0340d4250b10800005006500c2d11030311210300120340008458424580d030081600d0707511500156100703100000c040b4400500d06014100051040008501c59071064020b0180034011100d4406aa07801a058603c1e8040c1071101c203090fa6400600c4c00310041c1c0115003c9079586070b85030b10600400c4500a66020356030300862041070701c040f17144000c0c010312001c2101803a842400c07058403120040c03000400d4500c6031000700300d0750962003058041a0a400d10a0000d4801c84da40d00403403400e058403800340444200071400d210707040303010720001000302001d0307144a035031404e0720900400610400d50043c915010100b034000b55811000502e175000381c00084200300d801551841c1c0c40c0d0303942c12001402c1c0024248035000d607103141501041064001c26140b807658491003503070b056402d403120580010303c51083c6200080c8040d51029024028001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 843860035 1250 843858785 843858787
    0x301060513092001141b190b100315020d0b061914120105061c0c17100608070c02061201031b0b0a090501050c01150b0310080c1e0109080d05 62
    0x341e4a09200044110f212103910b1070702400d40085107980103e284443d00161240450341c44070014090b002c00d4440d001581c1581c8101d0b0100c116080a80d480c030300b80140155042070559580c101419164880f07800004c10b110008000d001150020390003400422240720300101c0e9070000e2501040e4160080b00c0007000781030810601c0100a03400c0300e01609075100103003905240084503d0b85184801043c403c0ea401703064000f8107031410326a4500f903c80c90f80c001c42800e01c5425079130a0b0080250f520039600440746040a80801c400040360398044040f03a4180e11001c0003039486690680d01d80c003201c8c800b0b03604a0003c010303061311280c0103500f4034065442580c2c00181d403c4800f0700002d5916142c0c00901020008001c1c01800075002640f100c1200c0007440c01310b584054228002c0e0160074692000d0810084a0704041b07400320003007014611400707005410901f055038428481c2d583d80e02d001c403050307049071840b00900885025076205010304e41c01814400011943c40c090319242a0542a9803c00a00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 843861285 1250 843860035 843860051
    0x20918061c0206071202030408100203100b18040515090f0405010b0a0f03120c120c200112021e030708060103050114010e210a0615050328020301060513 67
    0x5410031407240c103a00800c0e41000d540c1e10030303808100e4601c0303402005030003440c04145465603c3c0c400c008403000341540400b622603084200304024069041510401c0c02205e02e510040343c0d100c4e00344242c03074001100441d244418000301007480005e01018020b03a03c84c11102013411f0054903081d4040b070062000c860a00b4203842e06003045800c43e40c0580c22544100034041003041803082040d510410f80b0f4200900a044008410040d2078051040c3d000030001c003074104000c40c080e0b070407000d00e20009001e0100001c62401600d010050b11502e8030060707007c036032601d05094160900742e000d055000c1e40903080d9664980000354484d0150821101000000c40103410007100c0d59041c0038040c010100da40f2000082880e000018202c13041c10843c4070300401c51708241410741141c1c0b0307600f11006070000b0261860b07401641404000740019410003600c000420400051509000a121122281540e44072612000001200c00681c0d5450b80683c0c1c959215000440c40b0358491208000c105182d41000607804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 843862535 1250 843861285 843861289
    0x30c0111190c0507032901090506090109050106170c0f07050304172b02550f0606031703180109080f0a1806021509010903020d0e0402091806 62
    0x1280020407020860103405803000181d00107199000c2da0340c0218000100801d0704d216420a244003000c042c010300e4480d00000740850300760b00a501515090b15012900d81e03c400d0543d06684080c49803200055039180b090810501c5141419044020150881c2c50030f51001064801034000c0c14080c0c03415000000e0801c40040c1c100e103805041e000082c0540052210007201d0710304010107240000244032114403c14800f44280904584002c4089001000d01d000964080c2e0304440300075140043c40000038011502c114807458a00000c401e032740a241134034000d43e180c0d12060460340045900e6525801d0110014115204c00d504c9802c004204649901d0b01c070502100d407001541100c152030340b600d8000b201040e4410300315900c000020034503a40d141c1180b54111400d22540c845095941c2c510303c0c001c03074416404a111001042c010f61042050340f01c81c20030608907401c1c0c450090241c1d11413004d12046034003840399910101c400030001801e103012030380416040821280800c012081d40c0082180d14 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 843863785 1250 843862535 843862567
    0x8120a0b0112060b04050f010509100801090c1e145a090307121407051002191109130213020f040b1e0c150601050705060f09030c0111 59
    0x40d9180050601100f882c110503003130248110b001c3c1c2405101d06c020799500070f90054046400d501c0e00504043c038030300e078000001041c100c800c0c080c1e0201c560412207640d203020b01c04c42d1940102c40208000c01c2d2040401c400c240d844104501e14261000000e05c100741011005d420000b5002c14100c003108219511045010400504400e40303034100b2501c0340d1080c220501c5006404a072070400c82815650b40d40c0440000d181510640c0000da1810164400710f041204142035880c0300911001110701041d210000c01407002914509800181d0028400c0044007103a8210800d1060069000480300039555000c2122600c04540ba0452824102c08050460030a00d920040c4000d1485d011401d10742c404100d021b287c8902c4c40b450012503408160410705036003000c0039028860400a040f40d1b6010613104140e2161b05101c3d0300e02c0d00c184000009500ba5004e0400c54490b5a4400003400030b03950741c3d040f01c00060f0b40c00b4007001c0e032600c002e0103803514010302441800319400090034006e4444010081803800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 843865035 1250 843863785 843863807
    0x17120f0705030103030f080402060f1303060f021603050d0603140d020d09141504080d09030629130b060a09080c060c1c050f030f040b0a0507051608120a0b01 69
    0x1c1010070001040881c0c0e0011000c6c0b0301d0503041c90802030603103d500000300303240266a40c0c100b040b103001484102085c849c07400c90702141d11980c2e0174045043c5034005c80c001c80c010890b8040c1c40d11801414140068413880c002d240010b0b402c400001c85036180e460702c2c1701030340c11301000100d964000c032100c169403a010802001c440c1c0c55803610354251030401c0f41c03c21410b5000d965050182040c0b1038401107040401081d6000350070310004940f4111f070b16107030003060f50300c03203200580c2c0d440e24099101c0070041c9442c0e510188035100c0003400c4071035080314061040041013043d00400c5240e070350741d0b500d141e50354190041030120a141e44a40d881c50078211040c0c24033035628000d600c611001c1000c03a04603040400d054100760281c42800b810310402d00e50985907441001800107900200208110407800d55540b054001c80c0520400c41c0c095880c44c0c0441c0486a00b91040b80106906204141002c858482d4041626114104040c1004038a200c40c103c0f0110035a10601d0440e242c011030945560301581c0012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 843866285 1250 843865035 843865037
    0x609060f020a120605030c1003060b03090a14070b0405060315031015060908060a09051905010f05070305150f0307080f100e0303040309090b010504080f0a053717120f07 74
    0x104d61130b19001039038035220344a0a078058800c1d401764020346802907000c04020904052101d03500c0ca01204032645520b40c0450840306801d0821a00c407600e44001000d42c2621441145907182908000811191740c0000740800c00000344010101c401e620140000c6080c202c40c050040b80440c41c00072010900807083c0c118038100b001042c003c004800d8005407076900000c01080009040b1024103046043c240c806104000c004030f00940001003100540c442a054100ca400800c074549540b1021004d5410550f4500030641c18454a40150302d00780021030120000102191580d03070350b80031441d00308440003902201c181c001c1c500c9101665041e0040c016401448000b641c07079460070f642c0203000151140500d03070027141d0311682010540d018604880c00f51152104541403070010910341d66540c008108100d40c0c0e400790b000e1103100c41141400a401030701003403000072614200c4484003d8070088980003540e202c10030318607100610341504018400340100340131043c0170b032810b2907004020a4000d41604 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 843867535 1250 843866285 843866291
    0x50301150308180901060e0307090b2103041d10050609130207020123030a0f0605060f0f040906030f2105040915090606110c180f040609060f020a12 65
    0x90144995000203005a0760711001207601d500b80c084820800c48001c0f0000780d000712440f03001140c1180c01480340383c0d5a0f98100c08031403c407520f40b02c130501a50030f46000203402000074981205182e0380000f11840b0302e036260703040f030b8106036880111b441400c0155210140c5045081c00780601581d000440c103026000903241a807a000b40a000b080d01c0e0800403c900000c4c0384c0c04141030085a10401040c1c0003000540903000a03031003007140280a03948281d442c0c118580c50040c10040d42801400342c4011507000806060401c41d1064600038a81e118408081640300300300000b14048655100b43d402650140501c1c00701c04007949051698110f1041e9940e02005480314400c06555000e411141a901c1c21400802d20080940000c10000750b2170b003000755030f20b0400d40d000c03c0103903010140c0a0414050401ca9400d400110107010246840040c4060900d6498000812250980c101c240d000b52040ba0005089552034688400b210080701049603055000144481d190340d01ca802030440c2010f980d820 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 843868785 1250 843867535 843867551
    0x14030f0c0306010e04061119020607080606032e1409100308070f02060d11130b1204110d060f0f1d0709051803191419030908160605040b01050301 64
    0x10b0740d1010140300d020155101135000408001d15a0019058002a07501050702d400b01c44103107140c000120001d000040c801d00340040c003020b22464455004401c00740c2010b01c0c50f202c090103a207200107900d03410381c4210300b43c1e886901000c03440c0c3e013100d008040300081b10403078041031402c10090480240002c1c804000d0014188082542c0c2d5046a01181d480040c4c0418603043d4400316810740601001c00247c549001c0001c0c80c200c824800420605c82a026000080c98540004ca402c2d401000f500c0d80d5103541550001d0700081c41c1d0141107500c03d0006103543c5900c0110764900e0160362404a0b9503643c40c4d218029045080080c0c014940c0340032060680c42407082c8410300b400e59400310741c4078180090b43c0750404940101c0207a0742000e41e040300c903015250350b107000c01440c54000300442d5200d0000b500f1281d00d0a00510300c1b4054842c100c280381c9001100100000d001c07409045081c00940e00a041084250b665491510180c400707a03200c0e8130003164501c0d090521000d0600140d205134082e1b4100076039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 843870035 1250 843868785 843868789
    0xe010314061005040f23160906050d2c0708060f0c09150f07060203040b010902130311030c0604090e2503081b030c030c0c190e060d05060114030f0c 65
    0x610000d075070007a0780000b9081ca181c840080a00b004444004198140b0740c02c60820301c071000520351182d1810466107d03070090545e000c40d1444070b2445100e001640c280301caa20039040075008044101d0081c1942e12960b40c1130100e8910400c442c11002da81a4031440d010068164103111103907001402c841203110344d00c6d04190700c81d00c0c0d00c15440380314070680d98851102446600c40054540368134111f0081d80e02d4404503c2c0010080d070040e01d013511040c0c80c6000004450801e4002c030380d04400c8041103105103c1c40c3d555075a08800c403002500b40d16010303948126003d42c4a800181004201b0b8040108a040d0a840d1180c02c08810782c2c1e00c4000d440c000540d241c032644816003804100c0398402d203003550392900601d4805101450500c00c00c02e601001900510302c0718000003034031451345180d013500c110882400130000c8030510071108094a24256a04010504140801c10340c820750141590a0340d4605949460402000f40c000a040a0314151181d0b56410204015600f503140c904c02000a00c691b400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 843871285 1250 843870035 843870061
    0x507061a0603042a0f03060e01022805160803061c0c150e03010e070609060e03070501080c07211101051504090510090b010e0a05040c0302100c05070e01031406 70
    0x110140684840c000010101d400081c40301c1d0541220038140c0c24125100c04001c0315804c498030054400e40d0512a40088c2400d06208644111402888010442070048129450341c051a203052007404014482c090714103042c000c0025100b8454034801c0e560303182c043e00300b051001c0421460300e100e02185501e1000144041c1191054540c00e14841c2000443d0380d00844144c0c0191110700c3c2c055091120400202600058540540c0c0d20350300d8080896403071300b6007110550b43d4074186c660702d81d1000b4020059940109406034100001d0728100340b8090603a01e4210b0a070140c1880054104070a410310030420f035024400c00381c0048044002d0001e800c140074034080c600d11035580248501c9c0e4841c403e9040003001c000d0441600e401e0342d0240107604080c10103041d0750100344100c0c01c0100d481da000400490440c842c052059a02414603030b0110b00755024488130700da05550450074080c07203925a00c0410300401050f0018144600000d40715070541c9011307031407400301200081c4103034091028024414980c174 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 843872535 1250 843871285 843871291
    0x402090a05100f030510060501140904020f0d021902060a0b030a11010c0b0a06050f0406050306070f140408011d0604031b210f02010b010e0f1c0606060507061a0603 72
    0xc980400c0c01d0300d880352000c1c15402d0300d0303001c1d0342c3c0c211400710300100300500880c0d41001240907500420030b9a64420041d82d1b2002d150121040f0400c0c20003456804d8581540540310603444640d8071400e001049034080c007241c0c004a1001e604401541061040680c1001030650201d44040c05020304091807000c0780d034441202c0d40050000c031141d105072140d6440761110400d801d030402e104004a0510f602d10500500c1d07107002c4e06001c0d21a56a0b244a41e06060040d2411a20080c0013441a0303a5188411164050b40107041400c00c44150404031505400c04090b00141509100005d081c0007200000b45240c501078231010501d401610030070012941048440c1513246550b203034040203400d14a070600c044034622108030070205406003210315203548211079090b00d5000b500204000c0b05544010f480c110074140c0780030352150845000740114100001039031200d58039009410840d6034141e4869042e141035400c1180090404500c600a0103014026200c5550100601c660307101c00040126640744401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 843873785 1250 843872535 843872551
    0xc14030408070b130303140c03041104060b0c0705040f0e0a0201081e01060c050c0a0f09090c0e04030201240e01060309030c0605010303091a03060a17070b070317010e040209 76
    0x2200140034000120229500d85900600101c2180b4000000c003181c09038804081c0c00081c0b40954080c0004e00c0c980c64a40140071540c4e0580c2142c1d11a51170005812070a004283c00544500c000985102084003400e20103034a2005484080e0816050104803410240410300e11428103400801c008000304101e041240c080ca0070610741e540d004400722030490400e10030f40840b40d80c0740002a009501c0800789a8462040e02903c0540c4000c00411050a84500407a910161000750030004203540741c2c440e50455208440380d40600395100d4001e141984115402d034050303511525800c0c502c0421002d1a90b5100072500c45a200d9800e04200a04180050090000785550f41d8107000c10b01d4020300c2820092548290140119a100c1c0340042640101c0e20441405204140150b608408200d044c0c900c9083e02428a580c00342c508035144050300e41115211481d8007400c003020039400914401442120301a44940c60046040f1182100382041680a0096440007005200050755035a070180c3c1c000d500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 843875035 1250 843873785 843873787
    0x2403011e02030903070c18050601020624120a1a01080a03050406030b0607020306181c020a110411040803040f05090f040b04060e0706080a06080a020a0b0a090b1614010c14 75
    0x40300143c03031542c400d00d14042d05d1000100e000143c60b55114030106410059540103219517102c45006990320310b404da626280209602c2c40c143d4119854103043c00308030ba40242000d441a910780f0b040c5007003030101c8000760f850a000f041c14660402c1168030302da005290440080107000c200e03403002801d034004c40c0916020161107a40d851020350b1210142d440498005003501c6035810110188803c402c1105007054890041052100d802001c1041203080c0070308070380240c1a110078a0340e400c0c6490070f4054100c0d900c6507645a000401e0940034025002504e6032200660391107080c80302d50840d00704a41c0c8110b118920301e10411001692a928040c0c01985c040c8207200c1b142c07120710303001001c0c0c00d200300f841d0600d1080e520005525944051214000e42e00d280c1c00f003107095260340b2880e4070b400740400c0184d041600d1103410000c24568000801c660045031030125203c903120300c8204140d80c0550720301e1410485d5402c01d03005000c1c0b030703e50348042001020001c101284240b0000fa101c040000c40b0780c0058070f0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 843876285 1250 843875035 843875041
    0x30303011809020a1401141c20030f010303090b07031718030c0a031103041410030b0d0b01052706060d0f140906010e33092403011e0203 60
    0xc040d08442d8000b6801004201c01c0c2d074540050411141c03103541c0140c00103c02c0c11003441511440c070308035090000b400d0145024522540102000760001c2c1c0c245071000388190103000800d86111014500911030708085280b02e500d5410f000b002c410b940e0308806810780c010071100340000d4100b2500c610110303481c401c080c2241d0320103035205000300d60750b05040f240e0301000402815803031300400c4200126100351240c0142c116040c811594901541c01040110000d0038140e00702480c4c1103032074409003000d619000c00c04904200200d10707062040c110885a08100c280140a2450640102a10725002c0340c0b00e9074550211001c056410751014040d540600c800051200d581d10280d0844840440c100506003e192081d040c0c00389001c1d000c41c0c200400b030180400200d40e84080303010560103182c1d0460b0049003a0080c2c1e20f41e540c40c025480000b140b4100c69103110700f90b0745440018611030080308003003540040d004002141c2c0e00d80d500d10300d58826458456912480030080300041c041450031a001a140c2d9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 843877535 1250 843876285 843876329
    0x2130509180106030302010b120a1203021c09050715050901080c0f120f0a1b050405060322030f1d0105030412020106080610180207030819020d09030e180603030301 72
    0x2a441d8190300c95554280722021003419015000b000c00e074503041d65480d0020f14908401c3d0786880d0340c0d0742c0003410188801c0541203424407a0300a8800501c1c00c42404110021017403c01c4115502c00300c04862580000c00200042001c1c030703080300304040ca10704180d0301d04603c85000903c1c4100091000103217041c00f08880e40101105820f42c0d11944004a03c4d54407410070b40b43c1d18624107411204203062500b08050b5030070103440c1005c44110f000c0301e503c803c0c1c102410542041070b50b4000500340c0000c84401c00782d0201100c01002007140e02800303615800f151300320f1140010010251403c800400007036462800c021a684442125805508039014140040c0254822400350142c0e901c07860b602c1c4079500500510440061f0a102214010015564441c81130555042a4080c2c1440940814000c1000a4001140740d4580702034520b40c1c4801850301c452081100e04a82e4034500980004403800ca1140981c1803103c1c00780c0040700300200e500d10b20b01e4001c00003642c91205008001441e40d00c5070b108203c3c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 843878785 1250 843877535 843877561
    0x3033f0c0909310512070c140616080a030f050717060d05331314010e16030510050919061e020d05100612230906011802130509 56
    0x9110f0345407840943c0e407040c407402d400c215180c0c406640c28040d468420140d03c450034222a40203030706c0b054100499180100070105202d0150307603590003d50800040d00620301103800e4068151044403a19203801070003c0003000c4480b205a1080c00a190009200045070483c0c4005a52a0074200c110f10603550308001c0340c0010801e03000200103110b4404590600208070031100080b03e69001e200704045c454486010f00c00d407041d21300c00640701e021000030001c038400c14500e90030b914070700d000407404500c2420514a00301c14540e400c100c050f040081403080141c203200102c001003a40d501840307181041c8141d1030300c607418460f1680001c0051103051081000e141c000e41e4403440074007001044441e256160348081c1d80f100701210341440c98480002d400c504507000080640f0030304e650700c060111131110420b004080090340301c10300680c03060018403c00c1004001503c03075610000070307141039490400140c150710040407904a0321f50040c08510303031501c011180d07070040710402ca0350000c09881d005035a40075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 843880035 1250 843878785 843878821
    0xb04090503070c060237031e02010b01020f0106030206090607020a170606120105040b01180e030408250b07021005040305010e0a0b01060f02060a0b03033f0c0909 71
    0x5000218030941030010a8100350304440c0d5940a5845800d0500c0440c2d0038440d0041c4512a0100580108404c804602c1c070104031b85846414107100041003600500700400d0250702600c01070391a00d41c1204103590622844803c5080c1100a001081c00d41e400219a4000d440846024031004107108080d03584070201d8400410780c2c846850790a6903001d0031543c8840044131014064002c00a21681242052244134440ca03000906411180d091040108414000c1c0328400d40303d549a400c01c07600e119090001b440200040401080206800c40201410201003104482e02850080c1c003088a090540c00312940c4a504569038428203242c124192104c0c05950805012986030079240c402d60f03000095141a140e00601000000f03a80e141e1040390900d0800c0d1840005030015008142d00a100380c100710081000142500e040c180d40740c181c2103108024101c0303046d8500d4040f00b420032600800b200c0380c00804030903a002c8010303d095805076806205801005000d05c1d800c000184031142c04840c4185 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 843881285 1250 843880035 843880043
    0x2071a0306030c10080103381f060203070506010806012103020a0605071215081902030109021005130506090a0302090714040b090102101503120e030102040f1e05130b0409 75
    0x10f14544401c1c4010004d05c024041140c2c4140c2e824024080555014101200701e40c0320000c0703030040d000d41d05403c440f5403006410b400b2880c01d082141c141c00b0041c480b03800c0144c6001c3d4000c40d2148818100b0500d800c5060340701c044590010f40c01801082c01c11194602c80d0101c0c1d003413414003204203103412890466043c1020b0420791400b0b00b4031811680c410a84d001c40400c01209000f644103980002c0031100c981d1198591651090303440e016404a480294108140002c0000524000540101e44400e40096500000540000b0320b07035200032a80c401100500b00644c0c04a0900d0a03c80c040340c1540001e000c041c1c8a03082c00d00c002800144500300c0210310100309682c0548850b43c1d1040150b07541c004600582c094043c010305145045003510441e0000c001d80c440b0132080c64550740ba55440d42121000701c100f00300300850701000c039440c00d000410080140c200c244041910b44030620560103c1465588294081800100055600c0c03ca9400c10100e460800040e07009030000081c0003401d007190010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 843882535 1250 843881285 843881299
    0xa05092701021b0114071b080c030703081806010f03030c1b090606030c03110d0b0a0b160317041a06030a0f12080c1912180b1602071a0306030c 63
    0x100e101c4001c1000300058030f000350080c041c0c414044080769440e8012140900040c1030f003020364290000e44103858044c0790042c02060b18121142c2c9e04e441c1190303c107130340680c0450700d004140444a15142c00714402d8030445001340440e9410400f88410303012142c4009400c01501100c1d9509001c3c0c00c0802000141c0b50300f00b0103880329520442d920180405205100100f031900051020b041e001e03008140c0703022002d00203d860020b081d00c41c00c00504d0540c00321500320280600100e10b00d5590303001051062107003507260101505a140c01400e80f0030842c403510010300c462061000192051000c901079038007004205c1d01c19501c46010901d010203655010701005141c40046080c00440562500000740e1a5512005603850124981042c401c80381201c08280b000d41c140d243c2c00e481021042c03810fa40c4100c000c02d03144c0844102940901c90100c0603220b46046105021a03500c0d5000044010390840c0068800c1030b00d4801040041d00c24511402406900000000c500c3e40e01484600010b1500500034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 843883785 1250 843882535 843882547
    0xe0f191e0c0207052718070e0f0a0c1b021e0607030c120201020703020a1205040b0705100b0f06040905091905030307030f021c02090111060114010e0a0509270102 71
    0x943d0f403e041e10429000e00d0400303840c20a45244121040004002c0030364440c3c07a038844a8801d4906030745688040c4507405160408170b00c0340d40c1c103060306000b03146410030221241461103111040b1440b4030b00e44800d101508110180c440c005a411141a640441d00410720100103001a22890b01044000d6800440007500b001015084030780554101c1c005d03600e05040300072800d0b09900302c0c400e00b0409009680407800701c0c0c0000d00c0310116a19000140c1c40c141d4201075a43c0c3c14110301c0d410a40b421200c60708600107100f149001da1080712284c0c84d040700d2803001c4221100118815100758014510340544410000c1c6503a07800300003141019081e6040c070f060554a6040040d00c80d0001d0300d111340002d04220090220051500944000c03039000b032221440540d140448400941c4130b5148503042c08087e01129414020a1010360300030911094295003020300100010090095034145d0b520076a10000207110f1078490064960380200b10f24035682481e0410b038489100710010030300041c0c41d98000680 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 843884892 1107 843883785 843883787
    0x7050307030b0f041b141f0e0d020a080a0302030a090f0f060e1c082515050415020a1e1e030f06030515010e0f191e0c 52
    0x2814140c481184400601045c0c0ba5002403205070051417034100d14181540c1c0c2500558101105501c0c080c0d040c3c00c0906a9100751444a0141d074400c6464021502c0f061034410240c1141c07012190020001e16000359a030f44519101400110000d1000410458116a450503070705410421304499003404006c5800e5988219465800383c20905085824108680d4686940380144242d6aa07260150f11022001000c14031054040e8104400c0798081001401c882004113a814000310301a26181040c0c4609007582807042030709407000800802c0706810500341c10a242814003c0d07840c108014005403510082c0c0c031182410394100c1c040c0d0341c40184c0300b60f2000c445903081400004102d0788a8903150700d0091301380c148454000c2502c005009444c900c01c0d44590007801c5010110b100d00d001150310200d070707011401c50209603489001d104002c20040c240803009040c945420070100d220000c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 843705035 843884892 := by
  have h0 := BRFrame.cov_init 843705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 843705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 843705035 ≤ n) (h2 : n < 843884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
