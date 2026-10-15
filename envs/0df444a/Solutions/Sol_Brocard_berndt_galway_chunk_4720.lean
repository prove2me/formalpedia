-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4720
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:31:11.958986+00:00
-- url     : https://prove2.me/submissions/0145b255-3643-4343-b74d-b1127127f045

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 848741007 ≤ n < 848920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 848742257 1250 848741007 848741051
    0x281a0408030304021c0b0717060102010b01140a050408100204060306060801080c01140c19060510080a1b0f030602090a060801140d03030605121606020a0f03120b0d15 73
    0x103500950039a503d07982084448003a12803840f100540140c0f1743c038001400c4032410340c01181503440300941d9460f400000108044002e00607030443e07042002840769070360082d180180801c1c90384144e95883c1401d400984152242d9403080001d882281021550b40180d54003030f1007503c115035001c0c00001e6861004880c403203402e00448119030031840e80742407598000e80f48030001e0341d1024100c5081c001151181030604080086a00050803009504005c0140c81c3c407880307503c64020741100c2d01d0203040c002c0340c2c3e81c0c40c41010030052240055280341443c003405a0b0500c001400e102d1110304000f0740300d280880103034005a01081c06004015004960180502c0b4540d040c2e40c41c1d20030030702444105a04020400b04074800070307000d2503542e41c2c0119482c1c440d0301803555039000410003440004000d0f1024500d00c0007982c04142190844111800040e100071910078406405151840f8014102c54544004108120341e050344007031400003020410000c24013840220880d19010010070b140c01d28590901400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 848743507 1250 848742257 848742269
    0x9121b03070f060507020109050a060210050f0c040303050f0d06240203250c0306051302031e030910031b08040b060306060a1a090607060b210a02010c02281a04 70
    0x59007070030f0104510130809040110300502d4034461040d6a5404203461582c9604204016008007041c03c481c0140c03801402d4000c001030f0103540607454104102c0c4500d01480c0001030421600089032200a0070f1a4240c0742d2a000c101da04101e4681d03625051202c818585100c0c0060300380c100c81034001c1c64008000e45e0501142d00b100d42102202642d01007100c0c07207401c18101c510040f440c0c40031005c280c0903c105403040d00c912a401751903800300c0c0100743ca8200380708500250803004414001400301c0201c15039904890513107044000c2403000380141c0240860700549810966403480c0741035026400710207140a180a901d00002a80f13418081c15210340c01281c450345c000704180d004001700c0912454110302c012802c0e080c18100703003850000035000d502a450039501c0d280c5415042015107024240662069240c05011146440e0380c6a42900d44a83d0503020781800318043d03032481903480340c000313001c2c07110864a4440081d0f41d240000c2d0031001051f014488000c01220000140024070174202c0d415210 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 848744757 1250 848743507 848743529
    0xd0804020a12030c06050f071106090c19080a110f100c1502130807080d1d0904020604050d120f090302240408030a0306060323070804050309121b0307 66
    0xc1003401e4100801c0b00320b2012400c00070b01c000f80c41c001ca140c0703100d2607018145412071400e050900100c01000c1d0240448420b40c0c43d0010010711071581d00010303402e0300c00070003a03c800614080c3c56448060002c0541d0000c2014045d0460309420030000001d45034a080040724146884800c07002071241038042c0d800d00e407000c603480741882c5002c1242d014105c10b030021100c801600d4602e40f40e507455188451070380003480d6a8030030501803250900900c4110348810040c500031092040966010340e040302c0050f40365010700c41a40108003035445031402c076800f400000d40742c0c0c100c044c001c1c03920485041514040400080800418041043c42130000d9021207030000c12030302da41d002e140c0071205580e40600c03800036080002c1100050001e01403002d40114099030300d000602c240382810280030380f02103c00e5000ca00e9450311070f01c01c404201c40d946903041042440c000241d40e4452910501d507100b01e481455108501204640c04c00c5030004100080c110f81c0342010740d031240c0103000e0560b10352050040000b109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 848746007 1250 848744757 848744759
    0x30c090f0b030d14040503120418140114131e05060906010e0613032a06020601031707060603080c0f0c040902030c010809120712031523010e0301050a0c020d0804020a 73
    0x29104d20a50981c510f2030000341032074a0390b100d001034548142c3c1003d2603035011000c5010010050107003070100080380c1c01003041c010136404d0080c81010010500644000300319942490712107072540c0c40301c3c45108046900c00c00480504400032021414403000e604400b50078900003607181d04009140500032401a103443d03040b4084103040006581208100844000c0181000804a80d1070088405444200250400e00342c141115003803c0c45941d4102c0380940d4456001040060901c1040a6072198078a28841d26200c3d58a441d0028160690002e0407021001c00d92244136280465840c04c0d0015882c1150b9142d91440c05100949140001c080d60581090041143c10350045c0d0b055603002d040d0000352407028000500121664220100c20f49a42c0c0400d200c0000c2290940301390400040c290401c1440c0e2858070724802c280401b120380802030030b101d41e00c10b21070590088240b900441e03001002402245014081e1b0f20052030303140e82401c01846030442039414140144800d5000300e4002d4110b80000b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 848747257 1250 848746007 848746033
    0x10e01150e0a050609060c0d05070219030309030311010b120319020115090513051f0e060609071101020d0e01090308071d041e0c030b0108100e010e0402040b030304030c090f0b03 78
    0xc1d00007403040d54200d00100521f0a402070b052000410604c0c041d03c8258840b0841d0041c8002c800b140d080200c3c100341d0304081070001c41c0e000340005085070740c5481c200c4006001120028050030300350096035004046441119507420020000d040d1462502035200c01c1c0012040f001c030309890b400d02c4c8402e5442d8600c40306014001c20b40c1c00c4941d01058000f0140b000e0b44075a40c44030b280444e0b403441c9541a8800c40b00000b4010391a0180c0c00d095803010b00140424100200007640310b91018281d802802140104d006a001080d01981c680a039090740800400300b864400e01e028001684013100011021400904e449018210192041401c60320139a4143d038440d0500c00101500c942c01d20010b0020558101d1000c0355004012611000c4e50300030600c0c4081d040054894000545500c8a40e07594034828894255060380480c1190300801c00744500303448a00200e4003c00751a1440c540501000401000703209041c1000380886401c2e1200300a42c040c8060b4031000c682c0d02c140700c0395041d00045c0c02100c034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 848748507 1250 848747257 848747269
    0x5090402040209010e03060a0e07050103050103031725110d091d09160803120108011e0b1c0309150309020d0f11030d09050f1915020f0105010e01150e0a05 68
    0x3d041c10401d00b94052000081d141040484503c0031007621100c10641c2c1d00404d018000060000703090030b00165056980142500c800350900201c020031510024501001c140c105a0044c20031004160f05400310030802404001c1001d00c3ca1018465050140040e900c00ca4581c0c04891b4003c4140d07040d141000b60104545002810021241c400c030800c0000007114041028020003408008642e184089010051240e505900c0700d403580c3d00d01a0400e50b14030035130034003a415100d0000002101301d1240e001035050768400c2c80d4075100100601d001002c042e044100c40341034a104041c1c0030000c0c1000a8110203540c28031070029084404500c07a400018080d000051410b4840d4881002c00404080483d06e080c0d42c0042c0f9500007117440300700300043d040088039680c0c181c5065848104515030030211240301e0035103108181615000600c0303201400d00c03d102034002000c0980081c070195a6032030303413003074074403800e010300440f1250240d10301a00c2400303250980014840603090080b000e142c80d081080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 848749757 1250 848748507 848748517
    0x30f0307080c0c04020310081501180e07090905030301061724041e0b1315210f03022d100c03090b090604060b0a030807200409050a1506050904020402 66
    0x80501c10b1241580f8142e54500203184a2051000c1400046103003400b428640105252800544054100140594400f240c810102400c50050100e5030381030f840d059900d459071543c4a0302d45a8a005c4c110010018040b0085040f1342c81c0b0b503101c03201000354481c582c2401105a494110019801004219011110500d00040d010040000803162480c0402441c401401d10321080915641c1d002030040d482d1003440007207910650b007001c21504059080554a0181c54060301c290710041c000c00b100140403000c10f8041255201000b42c4060190740f070080e40c1d4011007071240c6a44d9060a100841c0b007007108044541943c65400108485008188804010140513903250101a19040b00740c0104051100590080104100812052030281000422140e1181180d071043d03845600400200c3d0318807003920000c581144922114105880103400070100c010001034005050010301c0e410b003d40032812581240c017494940000d41c6020f800c00c01100c2c0c0c1401000d501c001083e000c14050304107940900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 848751007 1250 848749757 848749777
    0x4060e1f12060c140d0501080d02030a090e06030a0c17061605120402030f0114060901050111060c182110060501021e150c0403060605030a11040513080a030b010905030f030708 77
    0x2844c00000d1002201259210040340d500440c0c4580041101c200200b001301031503000c520113903007400078041004000300c2440c82000300d024685004510365036010700c080d90100d58003080d00d208082c0d941580c035000b041d4030306007400c2a019034400140314203056860b4410b980100d694040c034005503502d00031420380004e0401e98040c4541944070220007824441c801c0b8580c4094088502403916000700310324040160486810821085a8100f94074000034420380c00c5055001c0d100d48800740c4501d560003095488122a074001c1031851480740030700c20144003030f00c2c41c0b00600075524001102d84c900700a170b585910030070707005911620b904c03001903c80070321010740a5400d00070b1b628010301062003e1034a03001941c2205000800040030000c0044a101d040d00500e03040e8060601a40aa01c800d900d00381c0c0c008850740107645400004400c1c503100c02c082103144c2d50204040e40c507607109400041c01014107440150110b0b1010001181078a0f002844031b2100b125240194502012540c426071a070304000404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 848752257 1250 848751007 848751017
    0x8010b0d0b19092a050628030f020d020c19020a0603090204021903050717010f060f0210060f062d05130e010e0402040c030506101d04060e1f12060c 65
    0xa9400200b40c4c41c0300f00c1000d100f10000c06403038100d040026802c002d0710b9000074400c4004005a105d00052080c420208594005182e100000820b00940282496120380014240300060848082c1059405072000c44010002c88007105440782032182e1386081b4034800f1303602c0a0410f01c10445c82e80300c1d411154959202420150401c04258505099200502c0e11140400d03125410096465030003180307e80105542001030b07074a0751401500903100446801080100310f04603500340c15081c0200405040c2c0c4c15158002c201c543d0752130542d0810000c19004800000703201c1038601c0c3c04561130b0841800c1c9082e2035a040c00c0b99100c18481650241d1010501d030300d03110400d8200142d59003c3e000c01d64000c001e003841d100554a080e204100032154182c020b2403d0502d484140311080e01d80c106d410720311882c40d003061048041418014100e1000000c51030346d201c0c0c100000850340b4544800664026590202c0d9948031440e41e0f180e00300990524022103000801264150021902c60780040080003154102 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 848753507 1250 848752257 848752271
    0x30e1201060e0907030b0718051c02090405060603160f052701080c1801060c1202010e03042312030313020a05040c0f0e010305060310050a0e1608010b0d0b19 69
    0x2980509200896002c40b16800981d010021b2000c1818034503880100343c07416800ea5204c55a011050a015005e4140510040c1040080200c0c1303211103009007940090240e48180303454030b44281d40d41c000311000d602a000703006110034260b500301441c0c0309884002d6403c2d50014140010311400580c602011035405000150300b041d600744a06540c1e010b00305150103000d0a00b080410300104036801400340e0000500500104501644010840c0000c0d60000f15159840c010b8041207002d4200c1250640c418040020001081c810703a00801c2a9650902c1010154014100801440c2038401251110a42040000500590041d5140c9000030300c0100740310140c0303072150085000c4440d403551440115950900000880c0d070040781065900809182c244000d10f041c4000c2521644024221400540c03110086a840c09458000581e0050880215002c441001310f04ca041c9002c3c62044226552914800da403e50602c5040c900b1042e8000081a800781c4034440060400c200e90b04490381d00540c1c40320 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 848754757 1250 848753507 848753519
    0xb1512071a040924050a1a0a11070f060206010b03040b010e0912030a0902090a09030e010e1201090b0412090b03070c03300b0103090b060d0f120507030e010309030e120106 75
    0x4158441406550501303600c4500300040c150b859409174215038490402088200102c20070384140d4005040c0c81c500312a11000c02c03003010340c0c03080d248040300c00c1980510100450286034441616045483e10b608664150340d0703d115400080c4016203016020004480050000e040300b0140540c0015203c0d0881c1d81d080301c24012941c40e500190340074802151541035503807e41c90711300c8900b41c1018084c44108004c10399a40c014180248640f040c1d03050002c4410440595600d036003c10030200d04a80003405552102c0c0752950503080d00301d40440b42002c00441c0d8020311481000740c101580c11105600e441e64440a81c00d03112500001c800300c0410120300300c2040d030240382d525042100d0320401340e0034803c0d0740031008180640c0c0040702054109485d007181c070008500c004a00c0d45c3c00007410f8581e00e51402550030880d00c5003901000240c4181c1900411440099004004140b0f09009940d00064201c821004409035000444060001600c54841403500d00c3d040c038282d00078162030000001d0707056441c1d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 848756007 1250 848754757 848754761
    0xd0e06220b1c06090209030d120f020d091a090d0c0f061404110f030613060b030a0302030703030612020d0213020c0a0830010e07030b0d0b1512071a0409 67
    0x500c0318000c4058418415440382c01078000d90b40a0140e000066041801d14030209646c1c86010007000c08000741501600c0c084030144d0300810a420403002d003990380342c01d4254682e0207488441000c451607180045445854014603030001c1c080c520f03d0002e40a81d04800f00110b40020f00100140c40c201c1d5401072000004e245445000c0c920510b007021161140b034141001c1d8005d030f519417521030042041528030071882e0390208102e58480100f020407640c1c140507040540007420401300c142d42500c210598817091540020150141038480da4040c0079503a1604225404d42141c03600094012a44148a0740107252a684c1d0001c6440d80050040c01c10b58103144491401301c90310010740b4140300015182945000807401c20721076035911103120041548445145018540501c141201c841c903510100e09140e119800c42c520030b40005100301c011a440f4104201d0303014041c1c443c00c42c1e045186003008064240910b00d40b24510f99100038200c4c0c1440c010020340ca8a94202050000007802c100c0800c09440c0388c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 848757257 1250 848756007 848756017
    0x120411040c030515010908100f0f05091e120405100e1005041a04080a081e04030803011d0714090a050612040b0a05101202011b080c0d0e06220b 63
    0x303030780d010030076013407043d0701180b0b005060498504114007100180700d4000001131008010700d00850014802486050410081c030510034054080b41c10b00c0c050166400d80002c42140044031103a44004201ca0006039644d070380e80863300401003a100784820003103403502c01211a000c01c034504141c12010074101c00608041a40103009011410204042c80350080f40f00d5000c28008036a141c0e0342c41c040c1030059032a501e4540c0000204244d00005007001000001340e2880c40104020560719140c0341c4a01d8240340640003409034948020082d41e40c50308040b01e40030208d008110684030304030507210880c035000d010382c048022030b17400c070120741c500044645402d0001c00c404c0800070780700d07821410140f800070303a101ea02510b0000c40a0410341030101300780407456104112508690a144821070171b01c0180c640c560031803040003021070000328060a2050800042c80c01c1c40f4510183c840030310400c001681d103030585498090308140180b006150442c08908400c440f00005054040c2c402d40d0b9980032940ca03400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 848758507 1250 848757257 848757281
    0x302037b10060e06070506041103030408120901110d0905120316050105180a0b0105060a140c0705030c062502010306051306032904060c050915041d0c12041104 70
    0x200441c20070920354006090504000304488081c64a081038580e181d0b00c683c06003001e496004070303a10704041a030b01007040310000c003000815110710307a1619584074842e8001d0040b40e03021483c0701407001c1c200d09000c00e40e5105141c054503240c98940c2448103200c1d000c1c140620202451100b044010303e80d910245c24420304034820000450703c0d25104081c40e03001551440002d095030302011010000800c900070040c1594819101207459046141c02214000d5454107406240c0e100041d65050840000c0b9124003519000c2d0101c03094200c40c10148a10380c45006040303065075003800b034000d4003502e0200070784079403900501d00424841d464000185ca038951031121540ca2642d82c000400800c001200c0c8150880c03d644441742804e020740c00f125011010040001708819690b03003410704140d0041e000e070746490f030002e00b03000782100c541442042c15500c41d008080c00c003034003404400c802400c21012180700312000006107050010020741c6200d0b031b0601401c01c50300500380d404c010990b51580e02c070316004415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 848759757 1250 848758507 848758531
    0x903232203020a080a0203031b070509190501210f0c05030303190506030307030f030209010917010c1e0203040e09010f0f0204090b040b0307060c0302037b 68
    0x1c61441000b03081c41007644a07136903d403c400101d2002d650301205413424011284c1c108504203425802d80350804030f00307412142e0301c80303a100140001d014400c814000440364245040059980700e01d50050640c85601d2602460192903a1400018501c0300d02c0440c1c0d07c1c8146503d82c021074407a40068155001102d00202c095212044015084141c1c09074640201003600a0751030070006403001481110751480d49001e05400188030540760340316409180061414121603030343c40040303881181c041c190f00001c2c01c0000341e81183c00c05c8480c100d800c1042811000750001e51400d0f280202c00441038800801c0c40c09955179036409241c003511180521060b0f0030107d0001a0b4031410a40e0348421500079480f95400b4501e00418401c0d103807030009840b400e0b5251402c203482403a004d45001c034610301c10b1010a41004100349000010303c0c980d41008109501c81488541002c00f404203d21103415032030756884a96141c194901001c1c102140c080600080068204000b10f05282c0303914503031076026070302d55502d05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 848761007 1250 848759757 848759759
    0x50721140105041e0503031b0909040501022d07120513090b0a1409041e050f0106031a0f0703111605060f010b070503040312020c0a060e100309032322 66
    0x814241e000c1503004c4442c901c0756550312400d413142a5030303010080100c07251101c000f030a190009007050554495020041c070581d45454507240590107074221a8080c0340082251204422a01d10780c44012510218045090b05001e03460304c1e0746410740300342022201404001c12a03a8952403030b10000700041c1281c450046a18980e40e800e004860005621000341c50324441301c5081e10342e86000040e608203421509688145490740c0c11084802d00609004040348500c804420340d010b4190003007002c03640603031610008503064085904600c4022100c50500814010000d0b00649c041c1d07006441d181e00a40e0414245080040000cc0c07207209030302c040e52a40c0c030410400440108980180e8054210051802d0604006079251980e0f40201e010082482e80c6a5540c011150310810400039505d030010500000c13140d4902001d0000c1601c2003041d806001c0c003005181c941e030b000340145030403030340c0c555100040b603c07581202113640101041b000c081d0910401200d0742006081480c41620000910107549003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 848762257 1250 848761007 848761013
    0x6050f2806020d090f0608070c0201051312110904081b07030803011701050601140d0e010b150d0b100c0201110c100e040510141e0d030801030b0a0905072114010504 72
    0x380704036845402d00c0e10407080d05100c1d0a50144803182c0188c50341c1041140c207581c520041e50076024003803801c00ba54014403c0061403151840c1c10100ca0390046800c88410321071101403101104088801801c105020010015800e400d40300391100f20345c50005903800d0540340c0d07590b640e07030b9402a440300007820881381d0000c0790b400c42842400e4109009003400d8070020120200340f00140103403291404001d580b001b000c00c404a003904002c0280d00e008103122600c61400304400626003044940903102403a1481d400c505013801461014060069100e0726010348403070307004460071040c01010203414062010a070001c0d0321080c0007506804159115400301c60184014001114001040840c1440c088a41006408005000260605030580d8400c2d41403920194800008007114441600031095121060038181e00c014464182c81c0305900c0e2894584640d4244070942d1540d113406029034210190400400c40f045e040c0302400001002060150b00c072545400c00b00c1808500318680d103035110000c020170 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 848763507 1250 848762257 848762267
    0x40f050111090909161503020f0a020319230f120403050307020f03120a0e19060516030b03060105060912010608010c020c03060f150d080d0c1206050f2806020d 70
    0xc000184c00040c4034000794516991145c504900c43c400752003c104c0280d000c100d2184d01201d0252078003d101c103645138404c11000b035482d40103c1c10350101d0f1034010101c80843c0c1c0305c3c1c00c0201c07030716070741c0350039110388501000c0d01d0840341c0d21980e40f9801d252810440c0ea4044e80c071f1144402c2c0f00d075029880752a1203140480000e800d0a5601072080c485030810481c140c0c10310f2005013044e400c44980800028002031a810003880c0c0003404507182d40781391a225101c0201301c1550040c91107050110f00180b10541c001c130040e02554211002c071a0f02d40c02c10700c018845814560060f24a550004091034190002e0700f684508490164025800390f0f510748450f400c0741341c0c0401802484001c103400134080b51a03d0382c0e40485211001d0000c5840c0001400c0054103540c0d0f44070604503090700180b0581d40d400c0c20003406030080c40300b441c1050100c1c0341e1051100d1541540e2040d601150000b8054000c8011940704100c3c0d4616100549820032143d0b03020401182d0700103625101a054580041039540c84480700608 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 848764757 1250 848763507 848763511
    0xf03090e070c1527081822150b070b010e07110706030b240310050a050303040302090604061d011e0f03110a0e070e040e070b0301030b040f0501110909 66
    0x3040c401c0079000a4001101c01980c0701050f4442c0e00b000400c1c1c0140070840e01c130b1030400e1448185801c60852007400703211403000106000e201c010110b0100305a448141f114410004d4150441d070500c00103d220b507100c95405c06940d001240360007808094035801c0ca803510740c000540540d510401c0100500581c81007040c220781000031420700035000ca1804c0700107030780c40c4040c1c01100105500d03840b0784409906e8015100003098216501d180d0042e09019047c1415042100c1c0c0110004083e00c1c001000d043c009180300507504003902461030300c2d00315000d002100c0b40107807400d90803503a0b0385000561071031240c803081e501d10403521104005502d0084411024203045a1036801c042c004001002034030700242001040340d41c801400103003c00010300140c0d012840746c4c06800c2d42d0308d83c0001c00405582c0420f910080315001c0f941008000c002603040c4d55070740100d0150101c4200100014004079401400040d400742c401c0e20748881141507036841a0030f581d041e540001c69020b0108606c080780c5440c00c03a145e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 848766007 1250 848764757 848764771
    0x90102040509130c120303091a06091f03050d09030308070e09060d02032406120f0c0f03160f0f1203090501050c0309120c180c030703020a03090f03090e 67
    0x5814642084000b491002015000c00082e0f603001c0d00b94010400f81c81d130824028142ca10352014508440d040c040d0103000307001005c03680c800c0040c0f1517241401070118070038054800548200801c5c1d03101807000e440500502c03c0c0882d03040703107200001b000901c1000f100300d0300700350340c1ea404100b43e1940c6070251065901801c2c000510000050758030701602c404c0119075204004507001a400800341c0040f90801440c1000b05856403440b040c003a00580d10480d07405e000b000140d41c021082c40001032400c0d2a1700b01c0219503085600310540160807481d26003200709000100900780c0c0c02d030072401a0a09032200035580241a031800000c010441e40c42009015401024100021000d03018a80d6000781006e03190f01400b810f215010072700404c40312040060b2013090001130301d64100e884104045541d620307400da00403440340c0003007411201440c04420590b80992260a4014113507180c1c1c1005a02030b4014903552810590344e015090301003100d144845078414085c1d11071043c0c03607003410303c1002100c400403c84 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 848767257 1250 848766007 848766011
    0x10b0c060f13080307030f02070b040507080115050405101707050307050d0209070c0618080306030610030209040b04050a0602040e04020f01051c09080f190206090a081207110d030b090901 82
    0xd0328501081e60202e01d9600024407503880c0e5801205030020141c03a02d1100d042440030134410204454044114040c500640031102c9543e80c60880c20f02362070044881c0301c0e4030a1075000030001e9041c150405034000980a2001400301e44030343c0707100c2884c2040d040702e401c1684003180800c12401e091210070058501079a920040c1c0c903e03034010400307504018140d0001c210540d01403074144402035101d000300b841c01d0107148074403120038100054036070426544c6034428052000446c0a07046400c0440c011264042c007000b460f9138482c1c841d4004440c1c0100141d409002e4048010005039851008001420300d814112440e030a080c01840b2219000d4400c0300d051050401c40301a1001c0e008184204400d1040d4001c60704000d985015550740c0120b89020070040740120328420201ea2001d45510030354407030381c200d683d19602c848609554034162240039203884000c10121444100c0702e01c905c0c1d806000ca0814210186201c501c0ea1314005000581900195442d8240c8800d40391018509030000d02a00007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 848768507 1250 848767257 848767261
    0x804110907090e19020a020102040f0504050112020d140d1e02011401121b0b031b040317032e05010207060810060c150203010f142409041103010b0c060f 67
    0x1070400040c5008200049100c0700010342c00050380e00c01001c0c0c01d015004c0954640c200100060301035041806184c0c4142003142010a060038203100d240d040b00e50120032068044595004d10205108018098403110b003420401d1001d054200850f40b004031040c2d861030905060440045c4400103001940c40031641030034030600c4031408048066054490014405808043c0d600c5c20140d50420360213940030070402e09000007249280c48000d580710b00c14009000480c608940540a107074811400000c080c009122068007440b9450350145a0050a614804042d0307642444544840048080280344c4441400024812544e050180b6070090805007007001d65401c1003120900c885000c0d01030719040129440080060146100241d20280b08456045560356140c0005400c04021405503c1261232102c540f25001e04100c0c2c3e09001a480c2d42c03036489000c103514500c402c540d90003601d03980d5016864802c1580c1034001400218000d0800c40049030f5500300c15880032b810300c10002c040c07420b002c0401003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 848769757 1250 848768507 848768521
    0x903031b0c100c05070605100501090501140307030203130204050a0b010f0207080a1515060903110d031706030c040c0806100807020a081309050106020a030305090718050c0708070308041109 83
    0x4045036602c08890011a42540340c4404581c240110b1501a0049007030000341b01c01985000c4070041680d0085c0d0300c19000e15207410041d240060085000f94880d4402c10020b40c00030300c039902440d0030a1000c1e8002d40e0b120582c0d00081c060398400d41e540307015503640d094401c03499a0080c070031403002c0b4403e0026103c200e01d821441601c580405902800c4000c5154001240084561101145407000641100b0312a140c00c0e00078546c04050000b154821808101021a480d125500d8038101e6456a00e0f0300f144002d0310001038203a54003a21954051141303081c82101d0f030341d47e8050000c82c020290b80307001031442c00301e0801c5051040ea0607101d05000049043c4008140d0100c0c07000c24003500a00e903580c0c0c42c66400340c0f030010f0002c02d40c002201546007000104006d0f40c0403d641c001c0b54002c0d50140029100e024150b500c0d482c0905c0b807401101c00b20510041019425081160300002e0b005116007070041030b48030400c443d0702c050001c4001a146004200801415051030031081310b040c1c60010350351034180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 848771007 1250 848769757 848769763
    0x1209020d03030209040c030b100e031603050616030212130c0e1e010b04030206071707061b0215090304051e0415150f08060108090f0a062f04030f050a0b0903031b0c 72
    0x2625403010010210341120307030bc0d1010801704850449406191281c2650307404c1c03094030b800050392042c00240e030054800b820070b482802580d4051100d16000f20b50707a181d0b204809180130440d0b8045980395820400001c2d6510440511841100740000e91401542c6072840d008d508c002c16045580300c240140010b01c090f17214001510050382c0d00850407000300d03007008038030030140c000e100d4018087c40c2400400d52079038907401c07030643c00014150202c13941d11078044c1950103c420201e9160403035a00500c0100090b161041c41039240410400d902071203a00900e02103002c1e90b20400301d020040000407020850004003501a032031200040c60065003140812900801c4544050a000d0400550b5000306001d2403003800001d222084c4070b402c9824000c403d15100003e480111a43c160860844920800540028100d9071000006012076883c043c115a40d912255401c00d1080d5800e1162070308030320015284161450040d502140150345a113003c00403001c51102c0e02001c450a1402402403440c074078400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 848772257 1250 848771007 848771029
    0xa090b040311040915090507090f0b091b0d0f050601020c030f0706030510090f0c020d0e03030714031309060302032406040e28050d0e010c031209020d03030209040c030b 74
    0x100c40201d504840e50401c489517800700c05080410901e021051300c10858001409130071070700c13a040700380613018955014104403181c8001040d006a074680000b02e00d10880c4c00e801d1150311f41f500b482800e003580002120201d406072019103a02c182d407a828454150b8041096040700a0102d00405403141d0072995140c80300f40f1841014103242e2114041022100c0f40c5840360060048144100560050481c1010180c4103525042c4054000e507200440d803540714002115598030098021840d2602ca50348000b465024400210600d000601074030184007540f1201a0040203a00804590b2034103500401d03040c102d26241e600382c21580e0000b440c4004000e10703d0b15911120131140040c0c1c1d90810500c2a00b00301c0310740d2100e0042c00c003200d0300d040510750203081004e01b0340c01001298002003510030144c8612000300c14103404034101304618030000c1d1061111442c103c802e1080480c0040203680403600b91011501c044000c01d40100b00c108240c18144500c00c060b00f0b0a140900c494080744010a02000346 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 848773507 1250 848772257 848772259
    0x8070323010207080f030406061707030f2604030c1410030c0908191103030328150f060e030c011d04060f0311010f05030712050405100f020a090b040311 67
    0x19401180210840a40c151241c0139040f00f03400381e03a007120070078141d440d510803181164040e14105000c2145500201c0780000c41040034000d08075541103855012101c11440b5044800e1810280c00760343c0b03000c5803400c0e10804188400e4454855040d803a00b1031006929810810241241c00c0740003050f550b4000c0717081c0313a50055060004000c50807071802c480c03e0303a440c3c110f10341602c1100c110041851070418044071180c041d00d00b800e100b0350b14902301074680c4001e0b5095500368062001d0500c1030b807020118100d03203550810000078020441c0f02c0c5a400c14040f42d10120160014000800c109500310b0312421110804901a041c3d074104400060710140c204061070001901c01240200d140d01e4551041010b02441e800441c4181c0c0d480c5096040e01f0301e1580c00600140e4102403606425020700c060f070313001e031320340780c480441000c4490b0030540140402801078440744556880710314081c003144a000e901138000302d0056900c5001c450003034030710904d075400440c25400c00c0000b000030501c0c91040341000b101c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 848774757 1250 848773507 848773553
    0x206071d0f0111010c08060f010302160219240f0c0b0106200304080109020103060506040e1b07080a0206010f060f08010b0a0e0a0b04140402030f0601030c03150f0f080703 75
    0x191540040342c010b140d104040f0000d40ca02808900b45603000850f187c8a0780017218141c4400200c80011816401029820001d411300d40c41c00c1401841c000c1c0145c9060031800342d8800c2d100c1d42c0c9055012002c40c109094525142d072910190071615800615081625140e091508031503c00381d6800215080c140708040070004080c41150406900440c0450603c6403401281d44468444156a00802c1d84a41c2240401d144c09400562400e0542c1980c080b56512038004602e41d64034090014070041001400c1040f1804008000001d0b00403c0540030f082c9107680104500d41c1031500028001c01542c01c99418080040d45240009034000e1b0369505480d407000841d6215410900c064030703982030503290294414401038010402c0f00171040a4000c607184041c2e01d02403010300e101804200d00c02030391109004289040016200d50090700146080030107840c0000703807061500d4100001a4881c0c10040e9214a08070b41001514041020749000e407031120041e00c039041c50340d0b55402c5507071004d075000e0120702 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 848776007 1250 848774757 848774779
    0x309061202030c07110102070909080d14090a082101030b0406140105150c0f0706111002190c03120e0d140f07031818021903090308190609020f0301060206071d 70
    0x1907c01c0c40101c00903c4a84018450f2200502d0a9015900180d03c2441d07070b685003414070f282614a4845590007604c0310b0020780303074582440d241c100f46030303001202c5850415808140c401255410441d0b00c5d00860041d6004012801d00e89402c100f0b66004030b0b80c0203d403091800050042c2d50b1039800302c040c0398805040d15903403501700801c2c0302e0a0030a8040700480d03900807860005459a000016034000b800324a040d03030000b0364246005003c034040c000315138035065100d40041c00b41900914040e20028000d003001c801c926890524201a5900076070a80c540da00300300801040d40d0340068156140d401d5122407a400d00320b51182c2c074202402109805000c1021441000a01c1d01000d04c14201402d40403c1500c1c500c1c0c1c10700401c1c40603601048110044002d620101d100c2d00b4481d02c251808194182e80d0404079485540c1248051550f507035064865a54070803000075444040c2c40100600c00b41d15032000c0d140e41c50004040c5c10404001c00300d40a00900480c03050036840c01098640d00810300321000c503031038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 848777257 1250 848776007 848776009
    0x2060f131401091a180307240f060602010b030c0d110d29010503031c020a11010e010f1409060103060f09052506050703090e0403030213030309061202030c0711 70
    0x1041c402554031490b0351902030300b9014400900b0b6090f21482444001183c591203c001642d83e803a2440c2501d4540d8005001e031100241210310203a5004040310808100c030301c41d00c7c05820866041015002c1c0c83d60751100b081080640a000f40fa40c0c492088001e054aa20340c2e00100306000d44608001303100300400e0f03816401030f40da4115171038281500420001b02c0314480382500390071008515034905e901c02540000140901e800011201d55040100500005000c91032080d40603411881007042404040004e254400100344554000754500384004100924000d00620407120200942000406100d0800c801030702c0014190341101e51140707000440c091074840c114010210403400030308c24022100c08040700606158942c00902150f0115550750381e6131403082d14540305190000740824109001002144081840d01d54028000d040141c90300c0c8018500044070900742c3c0007100402c0c5050030900a803940700c4001c00410030003400031403a40c1003c0c1a83c80150250540080070740112082201c0b50b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 848778507 1250 848777257 848777273
    0x9120f07080106050a09020c070b042c010302010e0f0a050613180501271e020d0f05100e09121c0e030702150a200f1006140d08041d1602060f13 63
    0x10700f1214200c5488030f855a420209841c0002003114104210290350b007833100c819407840c0d0480b513050b1203000703018000f401400b024480740b01c5080e81c0410514000a4691580002441e6510400900c04021410000100740d9101c0450305811070b546031100500540464010102001540782d6004800546194844015001c01c40f141a062100c0001c8400e074400706070040d01c8002848031090060440c0d584041044407806c0317034507580d803940c039000400035204a64521504191684169112141503401220055010340b143c2000c006040301d42110030b84442c0704021139100100c01644c6008030a400140a4050f00c48203c14440c400103044040a8026a0700c00d030001c4107480311000034507078a05510346821007500c0002c0c15004074809440751039030500c02e1009a95641e8801444d80400c102440505500d601d001ca03890b60042201046c000031448442c500c454200c18021528030f414089241429601c55280041d5405041400000207409594683c4920588802044802d060500f606 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 848779757 1250 848778507 848778509
    0x10f05071e030c060b0f0a14031e0a0512030702370302010606030f050606030109110c010e0a020a121a0c0d1103180f0309010c020609120f07080106050a09020c07 71
    0x4040031014110740200342c0c109800240b101c0c0074410800070318a00900b031000310800507507440e0340300400410a1043d031003242140001d590029045560809d05250005000400310480b100d442c0e000354120410802c0410080e90192031a200c81800e50400d00f0300030703580d40d0205800c42125070552449521001070102070810300c902c01e21343c0a195400070306010780240b616009410001f402c0140580c0701c0c51080c02101c1c02007501609003851680380000384001410b403156100e940481c204000040c0b030000340207110745c1503000b1b4050060320a09204104070351070181c1c0010005180080030b000400e0302828109480e4818000d021060369611141004a00c115410039082c5890000500050b150132000385100703902150b41a50303580740355407070b142d6598030407130070107050f9070042003042090351003a80c80c4103199101a040c6800c01c410140010000d404a13080841c0305d40c07128002a168010401c115030083ca4448000c01425061002041501440d4085c814890350002022201c0060070801d0030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 848781007 1250 848779757 848779793
    0x403080f250311060702031c0f1d0303070f080408070f08130b0c1b0a090f140c18190b0c07170d090603140f06220e0615010f0507 57
    0x101490900e0700c0d000d410f000f41010380f07101d50301c101d50010301414000000c42d104007801401409540c8002d81810f4003600800c1d2490700f80c0390b1036048542c84070980c000507804a80c4400061516031401100040542d40301868004c200a2400f0500c0049120715003181d9885400c860800390011a80c00c0c20300f1144555030034a0003030284e00000081040144000d001c3c52200f21007581e1035449999140d5105001c42e40d1400d134001030903c02006018030b1540315200f02810b50300081801c1341c005000081e850380c11035005881840024015111510b804880c0c401900c0803141042c4c0146200280c440d45102c0307016030000040d0020300040001000c00040c402007482c072410085001000001c0d039185c0d01000341c4200030070132642012a2140c041e000c0c280349072080000300340345603950b10040d07046e0040203480e041c0c00008070280b111000d40c440102e070840306801207000c03414040c0d801c40f50b454144020840d40c0000252500d60400340e0b40216809a4800546040d40d2141c00c03600300550321160b080c07012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 848782257 1250 848781007 848781067
    0x150603090c091503071401050316021c0c030e1f031d060106090513050c09010804060209100e120106080a0308091005090607030501060f091a040302061206040608030403080f 76
    0x4030203d5414001141c0685040c3c080e500f2081e558204200c030101050a49400b058041c40061041c11148140b03542c488003510460b1000100304140140031001350030b40c0b07000509841810400c2c035812860720640b041c010f55500301841c40d58030480c1c507210071601080c0101900d030b042041030180240b04681c1c02d80071103015280f1a594a4002400c070403a1032040d203011b014400c011102c5c00c8540d116030ba2140303402c0036030189810712075001154009001807045605903400c0c4404003482d1203120b00c0000a19030b80d2951031042c0f4120042100c00c40d44182244000da04081c07041c411140e02203090710f00b0341c0d8942441c11640d141c082209040c0145081c40306009840e14003000400c0c4000a400e900910789034074100404d0b600e41e80111001001010217201045c1800410001240030300c40f0211122400700c000f60030700340c0f0f0f0b0340012915404010706582102210003849403600d000e2007118000d2102800441c5814a1562102a80c0c00b230446107242800005c14251850850260045a206011044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 848783507 1250 848782257 848782261
    0x1006030b27010503010b0d0b2d07090e010b0702010e100302040e1501031107020d030818031b101e0e01151503060e0114120309030604031e0206150603090c09 69
    0x1080c451001c24828140f0035801d0404110f85030520511081c590394001c2014034840d40c030030540c22142000180c0301c4043e960582034801d076201d40044103c0c01a07220f607942ea803483e80381c240c0c26004480c1c1a000041501d00c100810750050ba00b00400c0f044c03e00e420b49071030f5000c0003a08002e9009000340d0340546254100f540030844580c031050179280c04403000341c03003c000072012605100e0440c051840020341007801340000c0b00c00300e8014610160300c03414102410850030341c004070071411900811010705842d541d40890b01d58000050010005d0424102820001e402400010a1402c4400448858140e64071145202c01c01e40a4001980c094040c030420342c100ca541d038496241d100301a1048500003458030601040303000b0302000c12412148441c1680c1fa8220304030b41000700d820041243c4800c0ea00c0100484c042c952410f100140c8920302a403140d085200b103240f200d400e9196129411001c54104204100f201c40c0c010382a240c0c04003080c3c1c2e407140c40341d692100007403616090100841d805840501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 848784757 1250 848783507 848783569
    0xc1b330903010606180618170c0a0f0f15080718230f09060112020f21042306130302190c0906230d02011b031e081006030b 54
    0x5103504054074901c01d001c0d440b40e44002c215000d5458243c0041401f9170b00303c040150140e01612404104031600035290482682000600203110952010300310724030001c010029001911508002001c1e01c0c0104840544243c60090441d10010070031414480c072181000c1e000e440240c1d0040c0501014081d8492101c0b4041542c2c451115400d025440b038503004035803a2960400c0624140180d606071200706d00310502c00c00910194002c41c005034180c40c420310415402000840186500c40d0f01050061924101414100400e5840d00d000b00400c20400c01c050aa02000094107580241c46090500949400e8541242441d460b03001030000f06840e0130120092000c0005504103c0f01460720030418680d0312212900301d140e00080444100c400003030107000c00e041540c2100e0015105241c90407005a07000300e000303517403200d040b0107400058600000412001ea81007070540450018204001249415071480c40600c1e2180540750415444803001ea01e43e0b03c41c4004118140c2807151301d0329807248604 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 848786007 1250 848784757 848784767
    0x602011521120306090c02010b0d020105180d08090306090f0606060901050c0303070908100b090a0b0607020901060c1b030807030f140a02010b150906070b19020c1b330903010606 78
    0x300460400c1460506c1d03081d0b9143c014410002c80100c09801c080014442d5001500c403504031003401c6558484000d0003102641d01c1c410452050f07841101110b8170b40b18084181458460024900b44955000e0120924074500c0000e0941c1c0c40041100c509603a000c083c0300403900782c01100d00c03014403481b011040c01031440c0c01401d2a01511011002c0704c0803042d0382440d0380b0682d880300c0340e01c1350032010480221b4100c0d8503070f4000070100c00000d4281880d00380c084d0301152601c6c1c82603000100040d00a48040c04008135400c00d8044004465051440681583c0b1a400d140c401c182c0010306000115884a024074024020000c00250b80a10301d0381302d05031200c002c0d020b40020301529101d034501c041d0740f5500d0740c03c02003a0380c071148010b01301c1c9090840315900c00c020314001410400c0080f0b142c12442c01c0343d5004e400109003401c01c1401610402192004e10246d198682d61407501c41e811540c1c540b41c03541012000590040300b4510306040040800c65100180d11070262030b42d403d9400d0100201d0425088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 848787257 1250 848786007 848786009
    0x40203040f03140a1b0602040b030405060703061d0c0912060c07210203090105070c05030a082116120e06090102040314060601050d051f080c0a0602011521120306 71
    0x203911030003142c4280c001070388041d1244483c00004101202c1c140c95449183c0c0100417007492140400500c0e00d0f45904601415400c21101210245c4c445c200b0000702a5040c090702c3d0060118030580c400d000040000458090b00c01042000b03c0c4a0116402c0d00540d203403100c4406c40700d0001d05454607410300d102c12a00c0e0f41c0c0008010f0f00c00e031683e03500c1c0382d0190b00301c060ac074580051564091404c10030240c004403102d84c0315200c1510710761013079a404201030790140400710a661041011503947c811624410603001c0901a04140d0413450720200b00d1004507540050068091034602a01c2e81ea00b0100400300400030090a18514883c55041041c50340301503000b807040e01e0141030a0350341710741c8103040140e03a40021101c82c1d001032001e0043d0041c15041c0d03084541c102244001840307081c20b4400a424141126a0001740390f80e1020700c1e081c000382000e991000c0504a10310084c0540781084d896150000346c58800d1400340352509000084034ac512843d0f0a211b6035011082036403a0540640060280ca03203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 848788507 1250 848787257 848787263
    0xa210f0c02010b090108250b121b0306010801062105013f2003030c150105040204050108010302120a08030a0e061e0403030e030912030418020705030423040203040f 72
    0xa40840f151991900b600c1d11812142514000c00e583e03605848400740e60f003003103c126603480c0e0091402180007054a40603044080c2113442128192411068a05682400d0070300c14182000c10010300030183d0303020b41414151074607401d007000d4003200304100c0091920034020b80e201c0640380c20000302d203040310b03000b03078030742c0320303071b050701d101c0c618422440201905242c0c410000b0704244900610200045d40400420300030074007040c25110b104030f0341021030304591081c144810507800403110b0f0030740c0c0c40030f4a04403400340070203440460409040c04000b80c5546018040a407040036000354048882c80b0800c030b18a41030350310014854490a045113840c0c090401c140910000740034110003e401a8031a400340664690400201c00c01c0c6e03140d903141900208402c1c1a001c106000030040c800d200e8551700488010f5800300700c011941d45140041c050300c003047c90024402c0031030041180300c02084000081c0c2e011349000403020040c0070062910318402024202089400c9400032040106205103c0c00c1c500400f80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 848789757 1250 848788507 848788511
    0x509070f0b0723070303030e0705180609090639130315091a09070e011e0e010501171302090415050a0e0615030c031e0d05040302060a210f0c0201 64
    0x690221081038180f03000c00f00d54a903034044d050810210b40310ba00180011240403058074251900c0d00040703200c0418541200b1342461b8050309204103030604110340b07548241c03060090105810650900d6046030004030030407140c0c080c998414200e03101d803d10500c000742650a209540d8414040310924002058442600e0900d82c11586100b0403800d402141e424941c0000c2c80000c1c40c629060018407040042e00d00c0c4014407030301e0400b080d010010003000340a01500c0300b5001c9006154924455480300c542c00800000ca0b41d14010002c070398101900d94141c910018212020f90746410084840c120f036004041c0d071100c6014207001c14001c011400b4000c00780304100501496554002c0001640d113036840c9110340754000300010368a28041c4040d0002e0101c018240c402c00220080024034021100c0240d800c8400b007201064000001000400c48030b05e451306045007081d01e5500084c1d060f004900317641c001c1c4030070f0541c81d0012000541d103c00c0381072100c0c00b0400109103502040402400b40b80c115402540c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 848791007 1250 848789757 848789783
    0x62101021812030304050601091d1b030708011e02031f150306090c0e0f030f0a0b060f010819021803031306021e0703020d0212062d15040509070f0b07 66
    0x40b5020045038459074003e0002d200903481e01003024010104041e085024441e50140026500800e01800026004c074070103401280340340d142014108182a400900c5130f031724203440040803103942d89002c0c02c0c50704030000c0180c0301e0f518800f150b50700c400c10b1019007030b00f03905a44010030001010b402d03610000c0400da404011198a64040d5402c41e04070801090101d2074403980c0340b44600e800900c0070031411010301a1034291610641c160b00d010001c0d201102c82c100c144040007001d050804000d51181c82c01d02c1c0c5581141042c00d50002c08103c00d410122186030002070032504100f4511910501c80405400c5035661181034103010442d14a40c05064014020480c20854103101090980c0315180604040c0403000c4c0b65608200400d40011022078200c3e035210178030700c1022014011584100c0380602800c0b42c1801e46074000007210842014280c828841c1ca051114080b885003402c60b2814058400082580756000850b1400200d5031014840880300140412464001c40292620354440e00204c5210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 848792257 1250 848791007 848791039
    0x607050301081c030f02070809130c080a090f0f0302031309051605030406151e09020a05030f0709050a0801060e0901020405090402060a03150e010e0708040302060621010218 76
    0x2511081c0b1a0240c01ea03c030742840002c0f05524002020302d40d000b8100000c0c8462074202c0f04c42a030f01300480555400c280483c0040050608056512011010071400c00c004e0010a02c00b0b00b0180c03001d09003504060390b603031001c03040010065801411070340000701c0481403a058903000355a540104005105001c10020000e07500c3c0c3d6a0288900803000803100009950382c400741180c0307035000208280e91058860100500464a10904c40302410341218400c507094032141c86100c82c0c0350564006684a0f20401542004540c0181569001086142d41414540700d41d8011a07107241c0f50341080b41d001c400098005048941540410b0032502c0700798101520740c0e502d107505800c03401244036641d007201c402c000160040c034059005185188650800107984c00e040d800414003020560003041102008900620802015070451680070009189c10104d0f45000e0350000e4803290003801440c021601c1410504103504ca006001000500d032000854580031f81440c8512000c840044890080401c1d04040442e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 848793507 1250 848792257 848792267
    0xa15030305030a020a09090609020a020d1403040b0c070b0705030105040c050f070303110d0c03051b0903070303030b011125060f020606010c060b03150a06090c0903021e0d03110607 79
    0x126601911501e040d50b40c1c90f0a002c01030341c00782c1c0e2128104101ca0718085084001c511031100600120700700140c0f510f104010107031914180141c85400d01041c40301c42440138a24000f02c80c3d219602800c0000e0949481845454500400100074000310085003045589607114010758105c40341114103100700382e013881003030f01d05102c0d11442c1404a0030420203040840e000e0740240302100c901c15000792500015442c48000c44248900030000282c555040c0b04101582100c1c81c0780400348042812302d00072000e0000f96484000384001070034981c8914032044e19a004502446c6801002e5040e102c000b0044ca850145500451880d00c8804244000105045100e24a4446214010780040a85888090042d5007410641600311601c40e00c076001e046481d1002d101d0000c004030903d0450049042580240003507a03450380100085918141c888402e00350321030b00c94412250151494101408210034160b02c9400b64580c07103410040c1d24184004040e884110310264080da1400c2d6a21a02d84203001c4030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 848794757 1250 848793507 848793509
    0x901050c0c03090d0519030201150b04050619030b04060f030c090203090d2d1101060503030f0423090c0304120f360b13050a0e0103081b150a15 63
    0x32540d100340310f400c84034280f032a4103507141d502440455150112640c2a008140841c40303084006075110098a0380c1005c2c11801e06028009100b4443e080509010204a01d03002e54486024002685000f001c600c500a5015181c400c5001e4010b11050b40c603075049541c034a40750b210884007190304100008202c150740c800c0e81e014081104c090158241e6003d0116455120042c0100e59083d2042001d40410781304c1490f800da4050755140d4600c451058180c69084a00e50341c030250081d0000c0140c201810714510880c0c094071610b42c840c00007100001c10314440b00810781585038206141d041030122000380c03840a1441a84a100580400341400204841c801c1c072405100c030108440048e4400c010030302c000c419071070709100540100840c0e50006124071045152380704500a40c00010b00070242000803041c01d029004c280c4203400b41503c0c04201c640c0030081403001502307a401c0031500140b00100e0081e24a0500b2a01c4200c62a915006441107050300c401d98008100c03600c0c00910141d40807a40c241c02c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 848796007 1250 848794757 848794777
    0x20a0e0601140d0b03010c090503150403020717010906020d0212070c080706050606120a0617060103080901030915110405010909050402030c0f010314010e1b0408190303060302180901050c 82
    0x10034001ca4002c080180d070408540e252039140c44040d0705035591002d20541050707040c2a551485030070300e040107060400401c00700320070101501c0070400002c40d4000601c01c0844505814500a000f0a18081c50040a9403040140404c1c00080c039101071807080d802510780b5040c8002c0d140ea4a07141c090059171248410a4003c000c00301c10b02070a400301e611231f448540e10920191900f850b104013006541d55825089400c0c030380c801e41c0d84074103200c0c00e00d04000403040d0f044044024007565045132103040030750045600090406469807100400c0180186080b4043c3c1100d15040c4010305240034402d403e034100703014050018202040004400c91203008981c0101d070050098a042c41d030040a0007060000e0740c1d2003c0c14141c4400d824081325000040740c90003005075102c0000242001981110f840c891071192044018040c04240700c1c0d42e42c04524400d100d49039810100c6447c1503442d054010b80042d0340301035070107803400e801c1d0114401c09070100740c070404070708000b04031694a1546510450250083c0c2c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 848797257 1250 848796007 848796017
    0x60906070c031403040201120f150902160b060604050d05060105030d1715010504080a0501050405060702071505031e0a0504030f111b120f0f0606040b130510170a020a0e0601 76
    0x54000c0f4020790021500301c1d0040c03400030703c40f40d816140801034500700d440d0031004581d40c00f600c3c442494240c0c00301b0050501c10400f0343c80e0a00100c882c19200e01c5250300074000305d02c1d0201003041c40d6513180845008010184c01005000c0403414415150312091003194002c1c0034940c0308140c0c2901c00c001d2462145900c40e079440d039a44a854803400300b40d00d48100035041c86070410001c501c1d40020404944041d1040c40040380700e203000d20b01542428406400402558031190050207242211551451040340c00c0c90020b449680742d003030240c0981a80c800341c1000c5404001032000c003c0c1d04d0381159200e40d0007900d600c00040c2c900502200d200385131401c0c803035007504050310521801e146490804000e400041c2a05400303c9a054154102070100c1c094250030703407001c034291424036018041540d0043e401c4504000340e0100d20003188900884901e0021415a9100080e44820305000344802074484107a551034010f01003001c0c1aa2490058020791003109030480c00a4403459003203529101c2c01044e0740d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 848798507 1250 848797257 848797277
    0x3040f03080c011d0304230a0e1b0a031a010c0804060c4701060f0807030207050a051006170703020111070305190c170a0803060f0909060906070c03 65
    0x1d00030301e5821100001205540300c8100340011400180408410340441c0003540d078551604644060140c0a8281e45000c103010002c0d408050f0742d0440c45808031032044020a00603641c00b03450308401a40403445c0c25081c01c6c042160b884e00c0b41d02d1703449100030290000141582c07014940c015130785100301003030003401b01e03904001c1406140e03c00d428003288140300d8a07540d0130f048640c600c5615000f940c200003041c002e64070509900300194140c030902c400060710840400c0c3d5410840001c1c0940389c45500c540c24403c036000402d413000d210760704841c1401d8102040c0c40001c586480c1c043d844040d4200810340032410b0030408903003541400c1c040d640b01ca0004c0014400c42d403950303005581307103040340e444900a80500c007400008500705101a03d0030303101c0b141d5041d404684501d0603011380d0006030030808800350b1248a601001d90005500060716030080629600ca80c2d560001410218142680c40d03000451038041c44080c94000500c103010704510380075140d40e9503804c00c1c21214843c1103c0d01400050031409 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 848799757 1250 848798507 848798513
    0x4020f0105040801050c13120804090c17040b010527011e0806010b0a090e0603060a05040c09090b06040c02060919060f11090a0501030b01120b03071a190203040f03 72
    0x684050900181001c50806035161141c908490007100d10342c02180c000994104910303101041c0b4406020101041803c0c0c10280c3c0780d8641728000c0f402514911aa6401c000c850640162206003462485240c44095442c00e0f28008034440400c2c03040c28010320011255103100f810a1a1056644070401c0c030400082c2e00e441e5010300d101c541603288020846c0000c1000c038060380e061000d140a0001701c0300d081da907000c02c01c20040070417076154440400e81d017009041c001680c0c2d0200c5d500f50401d040000200c1c942c1c54600700130311114640d0b40110151446c0c03004040400900e480450f20903041154100903040002806a07142c003011190303510b1903004040c2c00352407190780014110050b070041600050b0b1540409003141201ca4040042242940c00300d501e0f0050720300741070f0f4400074003820b10f014010300c07a0810020308251b40828152408075103d000d0401c00d03840420400008010540d148401e0304992001c443c81030303100845420305080d51692040c5228000000c0300c0071100300c0d900014007145191 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 848801007 1250 848799757 848799769
    0x41d2203050325090e07050310140433120206040e0403030f090b010302130606201510030b0f010302060729040302030a0f020c031002091c08180f03060402 68
    0x5020703983e681c00540040200a0740381e8900d04480140d40c07124007800d402e01c2601036410500405070020050100100000800c400c070f455400c0f2900b5090040903e0401c00004003d003001c0035124104000e005c03140c00301750003880c80468010071100300300c90352180c40c1d1071111101020a80040d402a500f00030421203518896106d136400f50103450006410135506581c2010f4803d004015261860084018000c0d0f1400044024922000364030802105190100c0a0155000350104602c00310030854040c40040d0240310004240200141da8049840c121400089070704841c00140d5225415000043c002e000441500b030603260010480c034105150f07a51045c0d0000f00180c0907080b5001c40351541000c03550701d103c0c00e41c00f0310b100342c01031900e41048080040c95510600d01e06800c542c08a4400b450719207000c100c0710078410300c01502580e00d440b00c40114070311541c4e0b1041a00c48692840640050200343c1001d001c000c007030203d4081c064000d032410011824001847c080d4146c20030760118006280c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 848802257 1250 848801007 848801011
    0x5040e070c140105010f03060b0607030f110a05160f0608010b0d0906020702060a02010b01022a040f0b0306070c03020c1017070905100908010608030f030f0c07020402041d22030503 79
    0x802c2c2c0701c6075100c0d581d0380050030340d0f8003a4070a16400c0718421041c001c000d00340c050702c5e8000d407050f20600e051443c0b40e1002088069050105810f00080c1190319090103001c2c040d412286400c8022200091980c8405c40e814030f040d03124010100c140c2c0c81002c00e0141c03007005e50504076104110074900707040c000c40302c11005000c419804c07078078190b08020203c0140c036000044c01304602c80c1d40001900700d9042c00064148094a1641c4e44c00940c0f142d00343c4203148180003114904441a580000c2c00341071504204010818818940e43c18441c4c0000c0001641d80420107410f11446035095400e15001c000034082030f1120b1400900118400d11040f40d03080007400a440e5011805160040e40359540c0c80208a806c03046440705000500002d80a2003a0102401150010418580154a0b0000c0502544103600011b040159210703540000f103544d00d100e0034107030385071590014001c40d0707143e5584584040030b10740c5000070280b00080383c0c00590303075145003200010817a800c0e010000113407140750b500701e07410b43c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 848803507 1250 848802257 848802263
    0x6080a150f03051506030609190203070e0108061b0306090622060b040e010f050f01050a1812140a170a17010e040203072c070c021002071505040e070c 66
    0x40e400591150106001c600075030248024054641c40881000303c0d9480051901e40682d01060500200402c00100e160110300e0285041688200900c0002d0400c0400c3d0300c04418110a000041010b200210b015401502e01802d01c400344010780989050302e02046840a90104a0300005012401c242c1010f003101d003200da084440b442441c05500c8122a00c513040342c00c0100d0042400e22030f4540d0714010b00e000d800201d01c1c541401c1e10700000541c100b000c034505241003000206010000718017601d02d82d00a220450a482c06a0b91109004a080094034805649041000c1001d0007543c0c0081510f40425400240000c4041ca0441a43c2840d80c00f5040b00400c015001c41d403081c9070034030f400390389000e4400500360414600b4a0f004241c946640c0b6080316800010800d0b0888141a185440801010b040d002c003000c0ea54410f1f00694440241c0c001c040d40004c0c0c03801000340610350100748642662519122130501c0118003400716036a0095014400e010131508012561080c0640200100c3c148 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 848804757 1250 848803507 848803541
    0x702060c060703051b040510230d0218090f010521030d0209040506060307050702040c090902191b230304050d050606210c0103051510180f06080a 64
    0xc0011015180c03090442d00702c4002070360f9800f40305440508203d040c008036808541c50781001d0502000a00c04510310a00b2024080989030b140340c40e1640d07840d14960341c418800240c1d159009030034031002a502c11010044598104241c59000386018106a80078540f0080c0c43c802c030b0781c2010144100380103c400780705014001c14030000f0400408100a108458101d140582c0f1804a01d051200303564020b04480d03c120801c0c8100130040d80d104003aa00f215804680c04144059201070640780e00340c168100c0c0c189075000041d48220700443e4070b01c9442c0819030380c0e1821f110690341e144601152614400c0100a440c450301a0301854213400c02c18407500158400b079a00d0701d030742e40e40025000300d003502c070449003600144100b02e02d41c43e124058245607d40600710305428614041155202c40c5c40481041c103169a64021075180000034079100241d80000c0c02e00c0100000104010f0038101d85c003200618003481c00d0038041003480080100340d0895402d901c0301001ca491700c180c0344014008030184d0307580ac52 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 848806007 1250 848804757 848804767
    0x20a2619020d0c0c02090702030c1903090f1d0601090819020f1903030201050a11070210021216021315290721021f0c0c0c151106090c06070206 63
    0x40c2c2072141070b0112100b80c54212000f4070a1041c4400407800401c2c1200759002400355890107900440d40281d0b043c0345c10000c0707030020a81c0c64244e0f12724510390001c0450f64008070001ca078001100d190307400c02e8054400721030440d070345410045035001d10324081c41020b60000e14240005800044840c00b955100030f020104059023480415205100b071071403049444103043c0100203040c0c082c4034140e04000000310a01034510b0aa600e841c0512401000078040c003200091002010301c01d0020710b00740c100c000000c9a50f1134010385480c01088844030203074071420321490521841c4840348201c2440c420080c004104040c6400842200e0208c0309030301030041c8030401614110288207400074084c4070b02c10b102000016201100440e610741c401400e000c00e55101c56004041d0701c0300305030303480c441800e25080840c0301d041e0020111107240d500007005043d00003403d80420038480c3c0703801c4200301c01c500303603100040b22542942240c3e4544080e11551080c4e0003c0c00301200500f0700d60001c1c0103460015101c1c601e01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 848807257 1250 848806007 848806027
    0x6040b2a01020307080121121808010b0102070807030c0902090612041b050607020a1a04050d060c030c05030c04060806010c0b04030c030e0105120604020711090109020a261902 77
    0x24001400440199500100700400690000c5c800c1e13001d8407101c1c0001c050078450b11100701490181040c0609141402c601c00400300b4800c1e98401440001c1503000307602540c1c0c400d051806001c0201c600e5015011b0340d4808600e241d000201e030340c11260814500035403540f80c50a000c009600005405400c51010403441c1816495804040e005911a848040c01003240758808134200d5120b803c854071804040211401503600d203005c40c4e041d1904105a1420281c2c2d0169550451003558420350300b240000078140f0a02c82e0301d620002c08562075031801e005545042100301d4980c070081300e2840302024140800d100e0280318500c0140d1010060400e80b00740540743c0c580e019900401c58003180002c803000281020103a0000c0107580c007410030300305142850144c000355910207100034102805036501003006802d000c2c00c1c814545501c48050241001d658441d1000da02030741c0240b8140001c1040800c68222a10100c603000d21740b907103414011406500d850901c885040300712040486000d809100308a11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 848808507 1250 848807257 848807317
    0x70302030304330f08061c140106300204020d0e032a0703140c060a0503090616080f19020d09050606060c070636081005010506040b 58
    0x16040202440d680c500e8100000c40c1c0d4000c0020641440c0303060076000d0f0600d603811851200c0e800d9a14100403100b0f54070900400c940007507410180c009007541c21802c0c801d101c100c18480d8000c1c0c40d813100a105541d01e55044203484142001d41b01e80d0300070f0020046290301820028442d1080c4003e0015250042c814510f1040d50580b000503801d581001030128400c80000109045428080c048640c0d011210030103c0d813100094440985012380c11040b156a501061160b81c5510800616040c2c032024100001440794100b01c03a4000148a04000315006203420309803400842c502e551000100c0e0707103182000500c0c4501520b0420143e03004081948d880d000c60019084003020280000359102d020305190b441c090b4081c04050007604100040070031400041540829034219080c003012100704c112029807c00a540780e08200559220f0349004c94807801c41c00c0000b00c40c880c0f0101c2d41030804001581c03040315001c0c440c2c9944040c0820007004140401d102a181d006a0700164210768642c0c03010441c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 848809757 1250 848808507 848808509
    0x606050a09060603150323252c0a111b0c1003050405061605070c081507031e180615031a0f04060f1d100501150c0f0203070302030304 59
    0x5100340e1580020b00c030140c4c0c5442052502c808400d0b121200c14a1900d0390000005d0300b20603201070011090325140004420812101803007400d240c2103058105800c40000034a54600a40c281d801580c00c000d4070521108600081f411462420f551454440000c10001014060500008400d05012030001a02510380f17102404403c0009050b0f42d84248007004922802410008241881d12040c040822000181a81c5c000507003801003030400b103c0074041c1d0f0310740079140c0020042100f14401040030900894049100d0f900d071031a4846a40b1a100150213440002110840240780c400004101c214540c01032014034008100490a01400c1d89401042d9100820500020440780e2405c100f0000caa0781c0d00401665807100032210740c1882001040c0041e800741c0050703c06900c5188210360203041c1e078440142640c0a980c0040000b8200c00310395164408003c0c2985018134203000050040100039a40c47d80e04180e5550311b01ca0085c90b5148455034401540a0b42c161041402c003000580701040100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 848811007 1250 848809757 848809769
    0x3020d1d180901050a1a0906030102160501060f150e21011a0a0f050108130201031805012a1b06060308042409060f120f020a21091e0606050a 62
    0xc900d10b0005480c0c1c0c03e44030090000b2001c0ca1914074020302064098034000d400c0c0b10111101065a1034141c0003a01a0191400000854402c0b040003000c100c815440303a401c0358100c101ca102c0d81c03a5640d03c03007001040b10301c104bd0041049600102001e140202186400c1c0b850301d0007980400106050f11421204041c20030100050504061480d40c90040c02c10320080401000510100b4149000203014160140060b05400128900c000c11680641c1200030705844001d01401124030300e06020740070308070802c3c406054001aa0090742c1600c1a10152000d0380c2040c1c07514240070f00381c45a04c00107149070714070a854560380d42002000080c0e002c1e00800c0142034080d0300403250f0075982c0c0c030384405c4046425902c0034410180d01c01c01420350481500141140039083c018400c24180c2e28801c050b01910b071200e900c2034800904000031940054000307415a5442c01e94031440c0e81c80024041c229840713001f01500c13030f810000d00c6980941c011132000381c000f4440e81000c1800e03a5a9404a00030f00e02c150061 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 848812257 1250 848811007 848811049
    0x60a090b16110f0d03080a02160b060103050a11090f041e06050a090e0d0305070203210a060b0c06010902030402010c0506070f320901020309131406010c03020d1d 71
    0x200c0500c0102c801c05520300500303c40210900300c0841c0083c14050061400805014020b400265102c055a05954140d9001c04013080306c1d010610b8003411000003201c5240c003007072518000c83e0785a500ca1084001141306c0305045460305d00760350100901d045005c2001030b400b035122284013440e40d0442e20101840100d5580200d40700d410304003004400304054101c8141d039490b0110b50303c100c040020f0340010030809801e0000c0c00d03480d5840201d0651080c40031003012120a080d05208003a8100c00040c403500c00f5400c01c120060726448203658505c00c0c0382c140d4120f644014010f00900c10300c0d500541e001403050402031860320b020355461341010022100103002c61003050903416038540054a10300c003c45a244a5402d00b04805182c41800034010b040c040e03980c0c404112196640d00800c01ca4108a0b0020705514200f512510890042c10b40c20103032511010140000c600a0350244110500726645a0003a00b503410111104840c2040740900b0f0906908460b408801c00b51184207500d2041c69800b882 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 848813507 1250 848812257 848812297
    0x3070b09210115050d050a1e060e0d030b0409210917030c0118031d03030408030d0b0f030a0b010306020c2b020607020d021f110a0203040f08120702060a090b 69
    0x203c40c14001079580b015006007407510b041d400051002c659018441d0b0f102c103410001240000f0741c80030402d82014002e008914240d554800104000f4600301e29511a5800b0b1000380104018081515059940100a03920855070700c009400042e074088280e0341a0702d801000980d4501c00c007072812803588078200040c3c100040c2c2804072070080c00b0700c054020000541d803c2602d442c0d94000e01c0d0440500c14031074a03c1020009520130758051003290014201070003165104c6c4501c0c1101c03402003c00402d014420018031015801600b00401c289541a42110404813a6886c54944201950280f01101c0850142c03500c41040f0304944203124007445561740751481a821103106c0686014000703131046041d50300456a81d03d050f5070014120f862002069900c001c8244200a1030000d407101c030501d0aa1000045031180d0042c1d4000060070031120f074101d42d03e580c15944c4d4102a125010032001d60f8091104012450150a02000a00040080d8074154412030342e1070a20035080d42000c000c1e0304840c1d084101c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 848814757 1250 848813507 848813531
    0xb030a0c06030b01140d02090f100e03210a1115010f062d03020d020412050c09012103030b030a020a09150504020405030d0323090d1205040203070b092101 68
    0xc070755081080e0a01700b4100da4000450024214010000070003001a00010309528580350b851104910320390290000c450b0000801014000c00310400206009205034264040030a8000341c54035108210700c403045281010f4031500301d400d01a0071840850511030380c08607100f1100841c3c4024001e00d0361280d58104a030600c040100552400c83c000c07030402d486d5071036100c060514a03010f010000c0350390400607600e044842d03008000e070107107a0003140000c218540307040a2003004945c80121f20011079040c0416070300c49130440020003403240080c000100c1040081c0019000e5072001150704030080803107102d60300e194000344a4500b02e82003000419192845e00e20b000c0ca0818198000d04011a070a6040908000c0403076a00e03180d600100302055141c00c10003050301c0c0340c070308607a548820f0300007510700c03e29000e2074070b5130b42c1c501b011201c100154807010b06002c1c1c3c00441c421180203a9004014182c058940303104003815801202000394031502110a50000d00001400003003102d21710030012501440c946 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 848816007 1250 848814757 848814761
    0x203071704050a12050c13150803120708070206040308180d0c03141e07110a120c050a06050a030e030f0408070e131a04150e0c030f0705010504090e010b030a0c0603 72
    0x1e8010702075011300100842c005400800c0800d921041503c0c001703500446468880054043c1c4844a05500c0b860600841c54031b8000c0018880c0044280c0c3c404413a480d10841110714a000312919401a0032400100700001e1203410460340010000400c80d4440070308480c86802c058903c061200401c3c0a0641101019001030f00108450b200d211040d00b0701440c0c8003441043c04660a48411318272000036242c0804c4043c80c5000000301c8090810032405032101410344081010040c150b440300485000028185001c000c00d0b016901d2a80e6814240004500141e01800c451100c4a015000c01c0c08004591003800010300024041d9400800e8007914005003844001d00c060f10b4405041494040403001c990404c1c900c0c0c0030b62148800d0800c0540d650b050004030410704000c02c1d03042c54200580c149035540c000030b1400741d40e00c1c11001c0d19024503040d1205039444090748109800301344180401c00100c11994403d00c00302490318004100314140c2c0b0000303801c00612640481d18849048014080c41c1d5140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 848817257 1250 848816007 848816009
    0xb150d0e0a08031e1b1b070918060b04050402061c0603020913021f020c01050c070f0e0f0601090e070c0302010e10020a0f210e010b12030a0f0305061f0203071704050a 73
    0x40c00100a03102181800c4031086d1140900c084410141d03109800c41c070343e000f0010b00c0d00503c600b260402181d5106604902d40f404010380030f0f03584a0800d1078120f00d030b18052003814051a80207080c649000a01035419405654000c003084103540c1d269000800b584500c00c0c184d110b07030280503032184007148a1042000d40340e200300b0304100042141d8007120b0429000940e112a040090a040383c0b10540c1c03030710462408000b90401e208035000d45130000784910007000b03581e0164070041c44250302550780c1001100c0f000581e106904520300000701148405004501100c4440d0191001080840c03120080764640b001e070800b440415940040c050030030f50381c05021101485c000e80340503000d8924181c0080c240102c400072500070f00d9a140400907003407009501801035040e0140440441c030705e070710000396100e42080d402e440c00320780040c1814418910074803850380300d030704000c06078454601090000e0000281d82d07d00c03d001d601c8100100f801080c0e21b90801210b034035085031410303600c50600d004c1c01038031400d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 848818507 1250 848817257 848817271
    0x110d09230406032d0f1e0503131a03100302010e0a050a12050f15010324150303080903040302010c0b100e0406090c050f0618060417010902040b150d0e0a08031e 70
    0x50780044e90f00003804a0741886a80c0d0b0400e44048505d0100740710507421601c510802001444005011107541c0403034031450003100c10004080f2142c1c01e2040000f201448116207507011005442c100f8001580604280c0034410750141c02104c00340e4071400402d5a00c1c80c103030440850301510640e2102001002c01141980d1111140600200010034034006051801800001c01000085020400418803410700d049000300d1800140030309000c0305243c049400040c0010f80006a015002554440303000044504407641a501c00d004899151291540e02d540580051480d440010b0000703088041003005600440c020403000800940d50700c1c3c4008400c0c0301380d0050340209180b41c0700d64900d69070726060724280c3d1125004c00034507202c2c0000007683c500c681d420840148564002042e0b000c101544810304c3c0c64800d54082146080b020b041000585071181c0d05807440c04100190164845603800419400510340119a4080559520512035401c01c48011702100018083d9484501480d0401601b01030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 848819757 1250 848818507 848818583
    0x31c0204060813110411070210030e0703081b06010b0c010e0c06030a0903090b1b07140307031509150e37170403050706110d0923040603 60
    0x1151060251440b50002c22441d21142000201403d00192282c0e40d0540300c4014820070060b001c0d031600c4c0341c8030b422010b03003030380102c0c44100300c40c92075806482030054407942580106405403544c1d84424030780e80040401c2445264410b1a2010b404007000b40a000c0d000e03108085450301811a140c900711b84207006101000d42c07003980031030495110b150844e90411f40424000ca030700c0c80d40c2c6c181030741d03408120b5000d5120b00400141c1e0464112061001100e101e44070030a440d0890750380c40840c207428282c004159030541040004000050042c900080d01c0089520b02084007085510707074a24880c03410005104494581d1105c200c2c0f0701d0148241a1820065201c05c11064014a0100d5045280404402050781d0184a04041c801660401555001ca41110360750b615200d26020f07494100302e00c40c4001107403d4084190b2200310201d041202180d1599a21007542d240c5004d000104089043e807066420f001c100042c126140c60040401642c00b07150100c0100202c9400d914840310389418000141c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 848821007 1250 848819757 848819759
    0xc010e071806051005030604020c1f0f15060503040c12061a0d1a060112050a0c0e030601080d20030711030c04020c03031801020f12070e06030c09040f0b12031c0204 72
    0xc4d0b601c1c51600b00c9440640703400d41e16552910007090092044500c4558227110780ca54611400b8100141081d1804e207006061110584404000c000e550000789100e801c1c0800342003d0203083d2085014561090255004054442e51240b4103081c009019038140d640507190172045200041d1f1014005481d0000c1d6401140e00d06030ba198124101d0b56407070b41d0f441444460022074102e80c4120b810081203ccc041a04020604080342000028610130703031014003042c1c401e1041419803401044081c1241d02c1200030700a0070349034210803074032820300701d03401e004aa448400c3e8401074a0100040d00b589880b4107080c49207013902100b0507240120000c003181c070079401001028520b02010082c0da801c4030510b080884000c419000d0039000e401124a005500000419840c04403e458a14180a9507180d12101107040000c020720415120441e840b49099a0420501d902401c040e40440000001d161001132500d150790006241741c4a40d07113500b85070360b00c0442c1004881c00207084d0365001c0051088214035103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 848822257 1250 848821007 848821009
    0x405150901121a060a170a0b0603041104150602010f0e0f0a03050f2107110a02060306220501090c03050112051f0915051806040b0c09060c010e07180605 67
    0x90300702c5002004074181c840f404596545a249424440548000d10b116120302c00d034a00207215200719044208005094004980800b03410711032100d04070300c0644564507684c0d880d11503007003641c0504d20282d002503031558643d000c0403d42001801901c081d5001090b48209204080c0030b03100482403201007074108400302c401100c000100340b4010743e03060500b6074a6014041c2481018050804076144084909045548902c481c180291140d010354a80f10f0481240245181d40d5030100c0b00000e40010040001c00c05920301100e00c0820030148a46030200d00707181031605019a11700b0303800030804075118280b200c003883e018003416024002d80c024640700225141c90741692000d2840f07008168403a144a40c4040407030540021500c1600050b003004050281440c00c4000c02e821038201d0b50990050702c60306080f0002042c224001c41c0c10640380d81b05600c54903071042c004d03849422140c1d4000390070403a1510101c028010291128060406020918a050514152848950851031a4520f01001031001e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 848823507 1250 848822257 848822267
    0x14090601060c1a07171005010c060b040b0d03020d0f1b030f0c0c0b1911070902030618041a01120b010902030c0409050a05060a0b1e0a02210405150901 66
    0x458075145400c000c44402418504000d01100300c0a030b0801c2d00f103e0802c80000d0704000c42c02d5889400b605c100105030307581d00d43d201c0c0d03101d07541c001c160000e4004101301d004148030760054064060001e10010300c0318101c0b0002426125072010031005a08039101d40200180c0240103038605942a0078100324034101d00310007034ac03d045070003801400e000e800c80718004501d01c1100c450000d540c1c00780035041da040d03d514091005400c00801d448500b08240c2102c4a103e10511040c1500503996000b008943e041c81c0c000b00c040d40004000c076410080564101c154944405c214600490045408160851070718815244a1a0580050003c42031042c0003000140100d0311081c1141c1600308010307283e481d82d01c41c9125500c00c41d4060030031039050800b4033024000c141d100764002c8030100c50704045250b03903a1540c0729070b00a00e4006408940012900920746080d60020710a0344210720503500608902d50345400b4200502002302c8480e600801c0500070350800b0f2283c070841d1040303441b1090030700441c4000209 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 848824757 1250 848823507 848823509
    0xa05041202010b090f0a061d091e0c09190f02030a06080607090e070c020d110901150e04150b040303020d020c0103060f15090f140316030224040806010b09010314090601 74
    0x1044862040001b101c2c858203604c204040d00361202d502c5501c0c2e2066404511070b4034141c49040c068001d00c010b0341090000b031040307103c01c0d40206c40075041400b0b02000300410124010921a45440e47c070315040400c038540d100c0e0050188007000c3c0141c4034180049020201c1c0c1c81038101e280103178000001d01100c160030981142c12207003c030025068a95801000312284409090025041074414050008000107541c0800c014201a9000b200c56a600e44808120942904a03000495004449003034941040e80014050507845506800c01035520f800b180580c0e8131980c02900140c200741c5900c080c4543c1070041284110b0b09180910140f4205640d031140c08c2e00d18030501c40e003c4070a0035140346260040c42c110008204031a0340703084899880588002c0c0200509602d4443e0040d00c0620104848801810007580e402500c0f0006859080c0f40c40800481d01c0440d40c4044001800002402c9104001c004c0c0030b805c00d100f429490b480c1c40d0001400f6a49800032002c0098203000c20800c00d4507000400d28 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 848826007 1250 848824757 848824771
    0x7050601080106050612090c0933131107020a06080405070b03190903031d061504090816080d0c020309040e011415044a0309010e040e03030a05041202010b09 69
    0x40c1607521004559423801d0902240302d40c0286080301001140c1958192458204003294006030080c0c901d020341400012203450826070107000c041a07586600c140340d0112a404c40592030042ca000510740000354515140e5004800146d4900104000c004051181e003000b000d00e51079072401c42c107000f10728401c01da800b07007449030410340d8074403881003807510942100554080c4071030071149488a4901460300c41c10704070b80d40c0b82078114518452015040c2031081e5240740c1d40200b05e01c5d040c11861002c550f01100c50410554043e5014000004501218412907031215055001199504541d80600c03051390011021140340d43d00d0074217040c110504070b410840e44800440d50b0142040c1049000030f004100402080c024811441548a119005010941e10f0103001e05c00c0c0031319441c05864058041d411550200b0a19001400442415402064080703d0b07000b006002107188083c0c1c001c503601e1a0006c950714074084c5e031200b05100070300600351704618565140344000d0010507010b401054003090054806 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 848827257 1250 848826007 848826037
    0x318031e080d0e0715020307050c0f0a0b0f031b040305060604090204020417031b01150b031e0c0a0f09060c08090a050307031b050d240b040c0302070506010801060506 73
    0x1001c21000c40c040702c1c0c0c90395490500b0012000512461961101c1c01c3c01480b0450141c3d1560100450001054940c0658071100038030145424000303004603050a10600d17a081080144003003a0340001c0c60143c41c1081820505685902d03185501c20008546245039840c002c07000c00c03050001c9080492a140d2005081e1070114400c801c501c0801c000b84500d5002070600071003101e0920103424080000c00c070031000302ea01401c0d03e03180817400c5801c898001e8821070141403080030412134103282202035a440000381e188180c4030b14042d00035a1421a007101c603c1d14034071001510b1550190000c60303112a084071417074400310030360030000302901640400034054a41c28000c9227000c0349994a4445e0806000050103036030300741d662032800314054403105417003242503100d00d030010400b400c0c0f40001c0c2c00c80c1a0801c0783e14002143c4241e1140f0a003101c0c1c00c3c0d5030702e1680c480303401800e5520b07203000741d980c0340c0700300d6034010381c2c4110074144070f400d00c001a045000d260341008002c02085d41c440d02074943c0c05180c00d4203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 848828507 1250 848827257 848827313
    0x1b12061415090d120504050a0f081c0c0f1a070309030e060c030c0703030216140a15021e060612030c06060f011e09090f02030f0a0e120412031803 64
    0x1d040d00c400b9410051495661881310b8443d00c1c0d011000c0c10490b10162a11212552203400000d055020b038040c840d000e0784480f000010444810b240c041c03032140141010034448819131100040e5100b05001a00c40f181000d1080101300700140103160301440501e01001810400e44d00109044604208039215650129000c0002c800030f00403039580c4c008007000c43c0c1c200c07a41c0789006901d03600c4185820300142d120b06c1c40043c0c65001401c141e400e1580c0140500d400c42d0074894100c0c00d8900315188841180704107440089180d100c0c09125060304407c60081003140b502c04200324082803081036500b425002440500d01c600b000284803034101d00211a07040222200382e0040315070002c0c603003001c3c00c0c0c038000d11803030304800b9040341050041d1021003005010513202d6038622001c0e80300607103407207401c0425000041c03018184d03035000840717100142094801026152b58005042d030403507007101d171031112042c404008260708a60a00201c80c035150820100510f582c990301c0b003030700e904100d0604214110071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 848829757 1250 848828507 848828509
    0x15040b1e0114090601020f07090203070302040914010e0907050f060c01110301060305040302070504060b090910120b061801150809030409061202040b01210902041b1206141509 77
    0x564a201440900d05400d40e955018081d0707100ca505002030250f007a400c04210fa5510204109021038120700c0144400ca1808a1410096100070301500403d0350038000410f08038500e00441120304070b145100c10b555414800340c8184a400541224843d5100c148104029161601c00c014101c2c0102c1e0307060f49420050944030b002d0240c010780400aa01e00100110b445501a4046070084c0e000380c0c02c98121603100e03c1031104840642c050a004410f00b4003005075245401c0c210254052103954161040c6035407101c070340f04040b100210484402c03241c007040180d12308000350341504110100360259000c2d403603c02d02040f640300710182081000780980000e888904e0800c2110024683c0d498100840c9070340e460fa16016080c00355080b8829400d21070100c909612036001000c451619a40c0c410b4410030201da4100104a0200d0480c1c10613103a030581020100020b60826920407142c1f50024203c04034103090b001c4a5184c0c00c590700f16100c0c50301074036150310342e40c5910700c180c00c8041c83c3c1c995580d4141c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 848831007 1250 848829757 848829781
    0xe06220209030613170f090d230109060e030708091201020c070b072603070f09051e150c060406020c1516030b09060d030f171609050315040b 62
    0x740075540c0600c140c205102d006210050f080c64a9401082040c03083c5243e520803601501c24403451101020041c0400b040d1440e00c050f107800c0c204d00c900031200380641003204002c0d51070502c0341c01d440142d40d903403070603410301c0564003e035122841588051880c0203150340d00c00945004404840d0700a411310300e84101e45600940c1120840d0310000c08441450356101e6541581343e1114000311840308020450180c54000c0c3d0a034000c00c400c102d08100d0030b46da200c0c04101c642c52040d517540820040b505074001410b4482c018100110320380324070180c01040c80a4103003c210354201b40c0800f0440001c204d41e60414601140c0d03150050303800040980d54403210b000e840d1420020707042403010401540144050034204221002518469403401d00400e1040c1080240200b02140d07000e8010f244041e00000080c40f0f1020355441548034100082140b0b0307000248100d200c1e08a500404404140d08c04044154002152000508003100140448a6a0f428094001d04003030001000300104401040c6031280754 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 848832257 1250 848831007 848831017
    0x70501151412060f19110720010c031b08030903090a2c15040e0c131e05100b030403030f1107081206031f02130b03040203120901050f070503070501060e062202 70
    0x8090144021406440841c44686c0b02c3d800c11074985080c00f280180c0040c41c240020300e15001612420302c00e6a07a82c400750350188040ccc9000040703550100c103244c005a00d15000d14003a40c40d5000450b1521030600900c008203035203030001703e9500d04022881203002c01c1000d001070504010040801252a151144c407606015041051752050034002a040341c0301002a01440c1c14004a0f20800030000c0010100c0403600d2409490503581c60b07180307000c1c282170403c0c0c1245070056a61141c000031503a0340c40703549030503401c151000c40000e5101d42c40c44112000b5409039003180d85400307520501e030266075511340e41684134081121462180d441e0006040356030610200d800741d0300c034000c1c400d006001103135810002e41c070070021002c041002c40c10100d046540b440c280c912950740500106030385504440d01000940000d100704e03041210410200c4801400c090140002c24884c0004545500b9a441c0036170035030301281c01c00d0f860500e121040060b240c0d96041c07114424223054000200b6818458500300103132042e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 848833507 1250 848832257 848832301
    0x5010603080a170105150a0e03250f240c0c0503010c05071b080a080d090206070f0b0a0504030504050d060b0630070e040c05070501151412060f 63
    0x101080401141d9080103c0301585543c1149080d1182e0701c0b1010451000392460f582e000440e8240310842841e4010001c05404074401000c0710b0002801503450411401d081261081200c0c4649013082000309100a05002d02401a9500894a03c6038449000d848040034020304018000d00720700c050100d182208409401c01034001e01c10481070300340c00351050303008100884021f01410340807022080e504000e001551003001c050310b40201d183e1070301d0000342c2080c240206526640c1100500581c1d034000282100b91040740a0486900d85040c007822040008154074090760130700d01080000307603100085030300741c0300c080341d2001d6400180e0030a0401001c02d000525045000012044040f02c8500385990b0481d00e11601c15016000c03020041c514510706a1382a00440d04610907100301d440c080d005900e441c0c03810300e031050030314599840b85802d4035201c4e840301c502c0c100d40c0c003018010703664040c203d0b405100f01500c921813411039042c81199105030003400c0000c000203c001094296030281c4000e05c20703201d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 848834757 1250 848833507 848833523
    0x3070c0b010b03070f02150a1104170d0e04090f0204021e07210f0c0f0f0501020a181a040e09030f0d0f180503030a0f0b10021b03060907060c05010603 66
    0xb85030b0000c142e06030310a071011004101c0c080171040754140b00003403800c0b8580c104403600e501e54403142d040c1e00141502c40c1550140a600303100200781a000602d03640c1c503180078030004080050385a000545141c10011019020300d051890450101f10740c200c03601c0341250f040c1e50041c3d59500011260542d141ca10f810818030101c00660b22050290a01c1e450f0040c45400c9010400b11b00c45403015200340c102c1400f03030000300b02000d0f41d00011075a0207020706800e0340604603450503100650303101401c907480061a000032550941840c00e010000b501d5010140232215204201d064801c00640c02a00407031090300c490090080c00200702040500680d040c803240d20301003980710a145e1034543c010b015413a00c1c5629851034416a0030050005ca80501c0a1580000c01b941c69602c030f40030090f028264119100e5507080c0c03204448411500c03103d10030001c803030382d60f8058102c144d181e2031382c00b040c50a101480383c403c1d80a0745c14858040c04c00b045800403103035641800e0000d1020707441c00ea40903040e2507101504000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 848836007 1250 848834757 848834759
    0xd060e01030203240c09151b0c0420091c0c081501030f06090f0213020408100b01020618120d0b040e0a0b01230a06020a02030609071a03070c0b01 64
    0x402618414180c03407084003a1520028030f80e200ca400809105040354288981d0700205480c03624610040110201c041c11050111307250341c2d00c1e010160311407441d000c801145114461500b05082c0f10020075aa41160140190040b680e100410a007042003102001a00010010720540d03c44100880140b03201a8007540d004c03007810b2942c0301c2ca10078801c0000a01900780706020409203040964141d961081908205610540f1808000c02c0d4000f0110f400c405c5d039026030800360b07541c0031a424a40d00d10303900141c0d40c1c0d42044152130030702005900d1400001d00306030784914207a8000c80d0300759220b5640c1508a055a645883e13181c03a240800282007034051002403641e83d40d034090b4100204603101aa010b120917180310070001e590341307541c140140016910340014009540301781c40c4588030740c009400ca229030159200000c0c1059500740e000c4400342c0d004502000850070144580c540c00f00c5054042c014071890080d8100305c407802ca050800c4c6040c03000000950032030041610b0110103400880c10031281d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 848837257 1250 848836007 848836019
    0xf090302010c0f0f050301170f07170f120f0319020a03141f170304050303160c050109030b04121407051b1009120f02060c030304030e0a03120e060d06 66
    0x34841e02182e100002c1c50076403c005054096020840c050b00e0070342ea00e910303603031130310100c000d00c000d02078807001840c025403c0e00e88201100f00309010260a100d503d554070f40c03003040300640c5400d03060360040c00d90742c20503000114107080b0401a6000100d058001719500c1d0b560014011500301304986111025102191080815070326501c41c4c0034499500c5a440015241c100840e0004401010740c3d04500105641c01c1c407903400200c59076204840c030070040720304094848000a0a41e041003078a00d01035202c0901000c180103480801074028442800e000301c50714203503100e10000c020000d10140c6109402146005002e01c5200b0181d0043d502c0b000b02d03071b2100340520f0f0094548190300d09000b490a00c040140d03c4510304025041c1d03001e1215114500503034500040b1202015078a08203841c401d041814403009070711110028010500400c000e1580c1c0d140030710b80079000320302e00050107000b0040301d0b03800e100181010640d4142d02001d0b0820880003174281c070004021344562600305091a080c12000152 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 848838507 1250 848837257 848837261
    0x14090115090312120b04090f060f1b022a06271e0906120c0d05030705060c0406260103031b08161401020918071e050d0c080105060d0e010f09030201 65
    0x12104510505100040050080005a9000c0d801c09006007030740407030342c00028415130320039403900019a2011885004013400004bd000100e41000d01507048403050765a10038121044002880c110044110451140c10114016000d06c1d582c02c141d02c6403240654a918540001420700c1e00310081000c0e10400132800d03000204a81100c40700d0240032250041403584ca8603800310100300e0082c000070100290880104024542d501c41d003035a0318002040303910045007090001922640c820300c140c5903984d00d0104001d040c00303000b0005410b140c66010b030794001403460410090440c4d4040c507080103580700900c1ca100840e0420320008010f060700083d03041c61078541c49100503401d40a02d40ca006001680c0c28031a00b40d02c90141000d621000081c801c04601e11141c9090b5000070f03052814001c4400e0700761400842040d0103000c100800c4001c91210030002241c005e0496896252410345165450000800c000740030390300f400100940c480328400540e10003540001d44200134400d0520200100c3d04000e40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 848839757 1250 848838507 848838527
    0x20f1b01030c0207032012060f0103050d0203070803010b090f1908120c030a210608060412020a030206060907031121310c0503010905060604050114090115090312 71
    0xc0828140303005180018000324100701125040140360880b0110031000a07030307030302900d401c1d02d80c8009248102074201c4030070049288990b4411413500e2a81d41107082c010326100b01c190090007190300400003103002400f040c068078111002c1107070b02d580b959400f100182848007011455074000d48441c91100c2d840d0940100d480c211071103001a1080d81045203c0f0030700074030601040140c00d82c000c1000d44400d911500f00c044030803c003824034000740300f81100900f00b55213031540480303c42e85c81081400180030041071a10704240c854001400a40c3c0269800303900e0300300c010700d014801c104040000700440e000c0c3d0805003451401c0614280e45003039030300219014101244081015018240001c2c100c4104040c82c030817441c048548224440d000000208002c120f0f1010841380720f0b255140004013605d0900031a00e00e244150043d00c0301e443d050341800100d0300305038002c201c8000f01640320a05078545407403043c191045980c004400340190102501d201038a9480289105412402190301c1c0360300440b818 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 848841007 1250 848839757 848839759
    0x81c1d091905060307030203030909070c020904050d0f110604060b010e0a06120516140306010314191406010f080603150c03010305120702010e060c0a0b01080c0102010f200703020f1b 80
    0x31441d200d03d014580d4848140c04020341603801080420103a2821070409940100c3c0c0d803901090800c00d543c0818116503054070211205c1e449680500c0d0b1483d04810b01455100e05850000180d0030441c003419940c4501800140c200d540c4c410ba0030070280d2144900050040c00948003140403552024014588055540c2c0620044c1c58800807900c1c01082070038542a0303900d04e56035031100c41c5a8180340c600c0c652000e840316050503540c0c0309400c5a034003a100400d109070060702084034136400500158050b00c14026131081c07a4044101000b010f41e0b0090039250b442001c602c0c0070314041d61400b02182ca8404801810341c0554450cc081144280840303000b981613a1065058491b002544521443e5500502000a0214505030040b140c5801c20801406501e48408110380c00013201c0e407180952071200381c10001c4070350810f42144019580901500c441c060318a030040180c101c0c030074064502106820708140d80e1460004410060510070030140b40f60030f0550042c1d90303a050444280d82c80520441c0611 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 848842257 1250 848841007 848841011
    0xc05040f08030f030414071505220b0d090303020706090605100f060f1101090b190b03030c030703030506121f055a01030c081c1d0919 59
    0x82002030000c01079030a001c141c0f02c15541182c94550710039211004440422855104600001130074000d0b20180d4040368100e5180c0d5a86c80c1c41000c0d00900000340015600005039102008000c2411041c04689084640d240300081d0042a171500300e001e440340c26400780200d030404074900c0511205070711039406024070900c03080d40c5643c0e0f01c800070088482c0b44200d0f40452910b80070f4030082ca001d08540d0000302291400020240e03079030790b00e85403c0c0c40f041e54100c8440011008440502c44588201d8107100e204900071800d001903403148075580e106041004042640310408110756482c1c01014060b5106800d050345e04001c0320300d080f100c0605041e8000b004440c01e000c00b14160755644c1e24071010000070070b2800c60100340b0010306404007503c88400f0100c2c0c8400c40541c21a00500181c90054081081450400651450400c1ca101d0a8240c01189884d008921924034640d460003000700c00c40140d080842c0301032030400d10084120300c0c0a4001d5000001c4004010f1955600501650000700407002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 848843507 1250 848842257 848842259
    0x30b041508010e0d050a030b120a0506090705060f042c04060c02011d0c190b121b1207030e011508030a020d14090904141e06011401090b07030905040c05040f 69
    0x111380e980b208020590049902002401d8509100c4e8000004509001d4100d41d00e03450321000880ca09000c501742601c55401420500000e210180400c1008050441c0c8160a158011240f082c0512030341c41030110b880c0b9500c8107880810101541c50f07624a44401044042d89030a09100c03001c0c003a1071000a006500c1c00076008410000383e4003410700316440f80c000301200d81d003070000d01c070482007000148070081c418550000740c2000000001c01e0a0f5444e026542d0441c14850280000c408041400d612400030500040100c03a02e88001550301521502e004190510b0403030600d80140340300f1501100410756003a0100314120000000c10300902182d003214560f200b02003044504801d0040501405403040080d40402e207008140550401d0050300303000056801c1c04000b80c58a0380090380080d00a8240c0310b01c0e03c0c0400d0601143d801401d1095000813145020000284891824004c8504005001c545082810310070000301c0003034100540108a6580b40a0001d001c0360000e21800341c1e00606604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 848844757 1250 848843507 848843531
    0x4110c0d02060c040b030a05090f030c0106030b060904052d06070c0317010501050d020a0219050a02030d0e03062712040533030402120a0b010609051903060b01030b04150801 76
    0xf007110f0844401035170090a680300c481a00c1c0c058840506841128803a14040c100705c01418401041905514000012041e10f145802081000010080c1d03200e842c0341c4082001040d0081003c265a0445103076a1440b041040e0001c40030450744054030106110f40c00c02c2028094000100000190098440c140d2110700c072161303505201024010240010400d00004051489039000380c100c00c4000c1c010f54050300002540c2e12840300340070381d00351402d601101c0e0742030541c141441458501c0358245000d04114030a000407a9451102405100d84603c59021548840905811400d10b03445000180c070403029a0012070706c034503000b50080a10070980280e40003030407480040b01d240300405000c141100521190000e4101e6000108103980000a02c07400d0700c515901403050100032842134461000550514400030301507007403900070b94043e5024403058428420950b002c401126030114010078640240e40048000c0e00150107210b03000b501700404e030798203489110000e20554584400801904103600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 848846007 1250 848844757 848844781
    0x4050913050a0b06040e01050a02030609070f02070e04030c05030a080603070807030c05090c070206031807090b03031902010b04090c15091208131a130e0c0a050904110c0d0206 77
    0x2401080c0b41c0c4204000c000081001101c0c1d90300c140300a000041d00c280b0030904070309558007200c40452040c1c0c000100034232840c003141c1e503a4002101d441c215000814140d400703560340360715019034600400d40c4000a000c2520800e0700c80c2816500000740c03a20b501840c10b001d08004400e8540621030f000e0042e000c950f0f0600001d030310b421281c00802100300384d4608400d100340703203a001d0b03ea110000390410800000da140d5100071406482d0805d0b44000200201303804a0800c04d2030382203800c081e07041c5000c0600540d0004203480b20400e01d2440d0b00628103101c541a8010b00c071308048580c0090902d2845400d0040d03902000080382d030f01e5403010107060076012040300c0d22036440c040c0840e03c4010001f41808508142c000c1d040541191190100c01611904011000f4829981400206800184030403104c2e03190940e04c402030210748581012401d20100850b086d00a417902d1000f08500480d0070702180e034079900220040300c4070810f42e5550b0781035648800c0d1610701132014803002d4030510700818640c103205 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 848847257 1250 848846007 848846041
    0x180f060a0f03020d0b0d0b1509100501030b010306150918051303110c091003052b03090c030c031416050a0b0d200316080408030403081008070308040509 67
    0x40e075a584510700301003900390000c0d044030020070a060ba841003031440351b4070341c0411212018011140441a80350041c4100180d80640084501a41911090080e034401e80120007042e03078000d0030086140c1c143d0500480c010034041d800300e10100300408084000d00c0c1c20102c1d40c3c080d01c01a030a0301181003041038040054801c02c0d21203194190020200402107842883c0f44030148040707c06464125403020300140504c280be4414040000300d521080080210801003481c0300c205058070000d107050b9241da403c0c0302e0070444180e14249611041250300b008034402416001d03550100d8000c2c1d0360303610f90074048140c000c0c01004080e544640c8402e41e64580660b0205005c559008050244580c1011282c0481e60084160302d800f09440c1e001080300280c0c1c26541180004a14000c2074403464046407480d0f00d0000f020300ba40511038000140f00104000d001101d80c02070709820038a10503101c14024880f001501c0d48002c80c03d000342c50020007040031140c002e108440003101d5072007507034481302210000c400d22 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 848848507 1250 848847257 848847277
    0x4110a030b0f0915220f06090b030a02120a06020f18090c0f0a200f0606010306120809060705030a02010606030507050a0f270902030f0f100b03040215180f06 69
    0x20341d40092901548000741c11300c0568042d0000d140c02c140e4a50030a0f214035103102c5212001c0c3c880441c0999450f161040a008040d07908041c0103030703050240880d4a030000600c01034040c0d19240c4807a0a03880c0100180034a4a41c44142159102203500704400301e500520301590f0040d1000311172002c0351505280083c0504c04010110746041d421220024465000250358014080041100320031600c03000e10300c6d462640860041c244c1e40301e0b298540c1e802c10000400d5075044c10b1510506101c00d4001070312030118554410b805075594041000056a18000c540008040d48070004090980c00d506402c45000c0721401d0300c0034411358840200c142c809024030031000e40045c4002c614540042d11405054404038000c24a40460046450307524580358102c0e000741104580000c00e00c48074460040c003441d8802c185000d03102484c101304100c07079680d43c014440c1a001c100007001050542d5542008012000c40856001d07503590300c252201140d0410150381188504178028540c403550610300c00721040009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 848849757 1250 848848507 848848519
    0x1a03150a05070e0d0503031e22050307080a050415080708070e0414070c05072c071704140f0109080a0f120e070e07090e070e06070204110a030b0f 64
    0x9900c26040d80149070040004042000030041c980e910b80301c01050107000380c05130000d59524509a41c0000d82030100b065034680f454454410410422008140b039105070174150502040711266080542c0746d8041c69001074802c0e04009812101550044c0050085845004007608181d0407000265403140e01100da500c0454204d0b0b0001c2c03a0716128141c0c2600c0c00200400c001804101030740c9011200b402101c03030601154040c50b07400103104c1d0400141b0010403080e42c40f14545003401202c84119800b2441008100d0a42004030b00428001c051103410204070300c400b09900d180c28184001d200d000b50010082c07901450b400e400d4041d2040c05800910f0ba0012603051605a01000403120503008000101c104a4400135000315402075024016001d0551b200410300356060040d018500b1201030f08020a21900100070447d445003c54a254003e80c0c0307080c00c00e280a51580495900d01c40c0703440007584549080341aa0412001001500d0300d0411075a041012906400c10b1201c10b24000001c2d0354424 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 848851007 1250 848849757 848849761
    0x3021b010203040303050306220506030106080f10360b0c0a09210614041b0e07030b0d140120040302060d05130f0302012703050a081b0d1a0315 63
    0xd01aa0080d600480080c0110300d00050781c00fa18142703002002c1c1e2080d140c03070f1540c2c18001585402d0203500090440c1c000603044141103400c20f180d0300c0c5403810b0010244c5854000041c1c0700c020b00010030140c1502465030081410f40511218820181c1920842d001c4e141500411000141728064420181c044e464070b144150400b01c1083e10000b141c4011000503070304201c1600095000d00901c941600c21200c00e081c03504241c903000c500c02ca203143d51102c2c18145003104000c134108025806d0381010203030800103601030754078003c2410900c003d5000b9060091200021502600c150300030104008142c07181c1e180012101304c1c4c1d00042c491840080c1d4401018480391040ca08264045500412107881440f00c99445544030303800c09444c10720990241c2d540e840d10744092016998207a005da0158001c8400b001101d94000e483d86c015110650200700c2c40300c00003a002c1880e14411036070207010a038400d80b203980310409207010741f121540024101c0143c0b070f0700000310306001900c0036080141c10411486c03a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 848852257 1250 848851007 848851013
    0xa0503040318050303070803010f14031002090a0e0106020d0e03030f041a0d2c24070c2301060f4208010302120f07050d020a0807090903021b0102030403 67
    0x103480121102e8030349640410780000c0e0781d61300704020841e00744907464090b141c5d89000b030a1101100c0d00e03407214402d52114000c3c0c3da0141d402042d8a101c0400351000140c89003201e01c0400c0c031250841d00700c188141003610021a440d0340004819014192507550703040c0f46245401415201e0181441c0b401d504a020f01042c48400c41c5044c04851200d540e660503410000e40201c1d02d02600d07000d0f40b05006c485030300038400e4804c03083d0801031184500e05400403d5101001c80e9142081c9207600703c514002d250460204104a10030030303101c0d82094102c8200c080b6203d403412401c850464549512a59618000001031122001e842090446150725640c00a00f0f144d003240c14103400840780300303003150b01511050030a5402d01050020400c03015070f0f80d400302c07581540305000c1d000e180e10018520684c00854428040d030300000e402e00c04d0b9501680c000484200c50b1002c12010203450708400e5035801034481c00314400c04241e0240c0a014041c1d0300b00c90741595080340707940040f40d0303a4410b40e006820800040c004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 848853507 1250 848852257 848852267
    0x306010501052d07021e060315030c10030b0f010c05030f03060102070b0c011b030504052a04050a0c2c0904030905030f0714060c100504050102310603020a05030403 72
    0x1c029550030003d0440640643e8040c004806080501c102003004240c2805604040c00d8049000c6400c07044e00400c0c0d1501c0000851722300000303010000e0b1000b540c0c05030103940c90034000f00c420120044e041c2e00100003509005400b4203100641300340105400003910440d90303c1200c0c501c20998100e0080c525101c1440980d84443d8002000c15056100d0322000203501c500d50801880201c520303034000622600041e042c9600170109200c10402c242c10a1305101c040f42d00810145a843e0510755903403d0740002400203283c4440040105901a15000400c005004c650b00201417004440d40d503800c0310354210821079003201c2c000301d20400d4108081000792160411003561a0454000c0c2410070082d0368450000b454250100c2d4803402c280c114000410242560f48500c824528040b00c0990402d000201d241c0d59800d14100c0d200403154540010a042c0030003981140d52421412050200ca880e0303c2030300803a2620040440b0360302000100001030200d202c0e100f03a9990707441a503a4a80b039600e440e241191 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 848854757 1250 848853507 848853517
    0xc090402040f0605150a0f03060501050901030e011d0a020916081b09150a08010b0412060506120102131409070806101205010f03060b0a050303070f08160312051005030601050105 78
    0x10382d19590340e10200d65030740c0d4111100f40311114407030003603039481c2d0340c88001340031058030101c1505040c14800c0a0295070f8100d001d032010858280f82c00154404c00300d18072805009144c141405010000030000345100003c00e042000c14000d0300d0190746500c65031864203004089030303c08000101c04d64045000c040850366000000e04044684c5401c002c00341f000125407040048001c071111303d0008460005540083e105401411003032580c40c141450410800110004008000c2496a544000402c107a03161040003080403a113138021900c8540d4a040030802c0500307401422884000d40d581d80d19103203480c000c1e4500c1043d50b96165a43c6849820902c005072400d080954180112580013043c400d50700c0c072a50b030090220f45807820183d4550305060044525110403079004410050041c01a5100081201c0c074160744000315020100c1c550400c03003480d00400004603800c0b00f107140184241a4400707040384031285445c2d4100855210803c05d1040c0050b10700c610382c0c05400c4400108034031341c01840548 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 848856007 1250 848854757 848854781
    0x103081e04030b0c03011707081e010207060f060e100807061d09070306061227050a050607180b032824060201140f0109090c081b040c020c09040204 65
    0xe401d2549a50700c91a2103241101e0f0201a401c020004000410440d82040030030694000079203907181c142500e0a40341ca600030b1302c02c002c50015000c41c1042d101c00754100c030156038008004201380581a40e007000580b86521400c41e40703180500104242c1d140007510301c800c4407503010062203007a1501c0c00035101c81c00110816048004420486680c0c0e4491440c1944905516680080c0c5981410406808511145252001d03030f460b00d038000e0005203040074644040803544a104115080c04d1500514103a81000c008209002d0701c0203000c5a150480d0b01c8414221070fa50350814116190303000032280340403c031907030240c07681c521407410f2840030441c0b060491b200b10020086401c446030841c40700c1c003000b02e402e4241881e8852604019151b428401c400310305080852241560800e920300d0070001c00180034840400340e030743c10940200102e142d96200181300c5031040da80043e0f04000c00e1000102c0010704180030300e00744a804500148046598149542c2c0200364404540341d50f02400000c01c5079000034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 848857257 1250 848856007 848856067
    0xb0a080a1b030f0c0e07050f0919080d1706120c04110d1e050c03040b0414010207060e01051602060105060711040e010912120c0c02102d0215010308 65
    0x100120f20412035880c00907000b0080d0400d4103160880c0400c140000034100c900300042404103030242c19019086440207201100c07a804465002504087d1010166010010500c200000608255004103807541d0350b80140d060240f0315a107100c1800034000e0745004101c941e0300101464951071800754400710500200005650404846030b40030400c46000c21802d030150001c4000c113015102403801426845007001c4505401c0d42070640e1040040c9074098001464503640c1d24100010203000d40c1680d00040d00144203201b000d000d4000103009110070741d03040e0348d00341c0303041d840402403400007a1481c100c40c0041d05151a1207599210141c40c403c003110034660003519000c11050001c400d00442042d40c5c003c404030340300021010300c054000c1c07500805030b0308001c1c06d05411011554100c800001555015030b000c00c505e00c0d85400c00c444803041000d0100c80c445a85444078400c00100000c00f83c21084c50302240c0c02e000030700a440c0d203034403001d12000304042c4040020b0312110122956900c5460600444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 848858507 1250 848857257 848857259
    0x91503021b0f01140619030209070203090604060c050c01020708030924070602040f23010e040e1b0a090501050d0210051e0306100819020306210708010b0a080a1b 71
    0x41241008140045025542c4d120420f8283c0c02600304030458001c9400c031411018030444407031855005c8254403020348255640070005074100d00034811a440844001c16080e030340d50b10780c4005041602c0b00c1105039003900c182c004440055000103030322815100314000850a0540303a004000202d074442500b0358100c41c00304132440d0710413184005040590b04c6513801503101c42c00c201c00d20794100c030f450340007000c0320780710008011230781c09260402c00c43c400c0207207410200d960615010901a040c0c0318202c241d03510540700d001441040760308900800200c00c0741d042881070ba5038041d60702510307402e001d0700d80e103d8000c041c1000140380c980c201403c84100e5043c0780d420311030f42c00f00200781e900004140715410b031000010000030f850f00d420310300004111400d040d1400e0030540205415000703403003000700700c5590000100704180d481c440c41500c94120841e002c810608180895034484150341316481700b035030a010340d0001a15003100c000f410749a101d40100701d0b2403940d8a0f03a0700f10304200d107098060660b010344 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 848859757 1250 848858507 848858557
    0x7110d0f060b0f0a09050619030308071b1a0f16080c1e0c030a0306090c0807120605031002070b0112081c110304030201140a02090a0506090f0603131209150302 70
    0x841d140c002c05c4d15140008081c540403061080e030201c4010600c900103122501400040c0d00301c62100e411000b64075081c5154135050707a2600c18050025000780401100c3d03550b41c081081d070744041d5446210000003a1010781c0300c5140311812103950b0030071040070950000003d051500920081d101c00d0141000080200031500c5020f83d40d0341c003041102e1040c2c0c0000825050064150040d007004042a000412005110307000080c18100094100e108100c100f04118083d0701c0303513800602c06000c0040507104c884010b141d5078802503000060403103117045541d00000d08101103a00241002d50880724203482c00540210280c0043e06240f4504a500e680310031003107048050070080d44c800c6100342c00014407041c2c6000f1716010210700806044005004018801607a101c0c820100e080310420384039941c41c3c2d0b044800040f020600c00003e240c11110120410000c0305000d451280c4031401220890750400e500f0000304d515901c01d000340d4101c014250303502c00d00588654010281c00100540b26144038000301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 848861007 1250 848859757 848859769
    0x121e100507111203040c231002100e0c06030402210a1a15011d0609062d120c03040f170c0111130303050310030807050307110d0f060b0f 60
    0x20396034a00040c200d40300b80d42404410411140d000314101426415480e10f0b5845814500c0da50084102582c108030580c8100844105011000b01004000481c0d6a0b0f1a1000070366036001c0d8195161003030b0800319225803c0c003020840c454900c00c0a40902c0c074541e9640c09004c0a00722201c408548042100e80c074180d202c4d000d0001c00d103070500c611241c841011802106005010f4040e1071002c0844070307000c041c0c980740e0700a8041402040f407100c1d0312130f2841000001136a01e004100019410030b00004040134500b454110141400070345000e81c11129500700300c0060140030304d0310100e074078002c1c54020602d1403109401859015101c0c110004180c1d10310350352540807150300c0d5900c2e03a20742800f047c004e0b0030003401c0c041c0c6c42c6048a00408182480b81011462076416054407001d81808030000100b8885c040145c1703d00d02442e0001d0409a85141034030303003d1f0340e0b80d00c0840c081c0c46100304410001a40e142c2031822000341904268640400c25042d2a08002450a800c1c400d0707000440071494406d03038441c0703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 848862257 1250 848861007 848861011
    0xc0a0f0c0b16230414040c0c0b0a09080c2125080c150a0e0f0c13021204030905010306051804020f061c0b030c03060103030f1809020d1a121e1005 64
    0x110b904c0d1130b20300e00b010000401d0f203c01c0003140b08504180300c940c0190b234024a2202c3d50750b00094441e8540d1100c0d480c400040030300c01e0003d0700e0030300001101d02c20312000160301c40d24115548a80c14204500d030211049501802c00d444034582c04018041e040220100d2881000364040c00d15585040140502c1c1d038941402c10802d0900c006030301c0e080003002d0b0118400c40001801d0f04001c4c0c42140368014003181c0350f00480881c0c5104101c0301c0076100f000d080d907a058800d0004155101306603400e00e402c024165640c14428280007904000740410700b8188007a0141e0504c85414000e0003039200d035420020b40c170641c400603a03000b0b8028800000c0c44141121480b0303150a51740c1c400100010b05000345800c0844070080f681c0640d214030b00400009a202540c0d00344007269180c88c003004d1a151316000c9150b90194040000c0074004a41c442c0d40d42c5e901c0d84418080c100a01d090901040342000380420300075101401d41180d00545600b41d21040003031514145007407208242d804644c5680c000d007040340c0302 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 848863507 1250 848862257 848862317
    0x717100c080703060e060607061e0603030c1403040608180f0714090f0402030327090a02040e0709060f0f0504030602030a05040510020702130914060c0a0f0c0b16 71
    0xa0240d10743d0544655000352460b407800a81c5881c0010202c2c00500c601c440060240790341e850304220b006c0045c002d07c401540c0c410340501605a0f28203000303110004545083d50601c0301c1c03000031843c4010000c12101141d8654691310466521101c00d1060241c00c1c8121004034010591807804c2030005001910107040d03107a503403180b01101d140034015a0720004110310000284c04080c400503a50000980704103010900350245400341408051070b03540d030342d400550340008002090101c3c100d0107030042d0083d160001c0c101c044503a2400c034115045c603050311400c80441c1380107003540c00d114426203d6110078887c5082c402c3c501507076030fa64002244c3c02200c4215401e5a284140000c0010502041c0502990140258140b60340b940005400c00e00c6102c071400c0b2155104440d004014002081a02c1c0b036501809540701c900d80390030015002d622107842640021061803c910300395020f50098803009070002e0846a2a070b8076a00701c102d084c3d10b5003002d00c040c45103940d0450542e4400d000d071941540300c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 848864757 1250 848863507 848863517
    0x6050306030102070507080d391a010303020a060e15061509120322060e2b0309050f01090b18030a0804030f151806050c09041a0307090e0717100c 64
    0x202e51507005103200c6272482485c00c2c0d928a0051540080b96000525100014110705980b21103241d241c01351103213020100c0c95002c2c80c080c0000105240d0003003211038110740111303030a00002600d0640c2544642002d4204044440c00301e01088072401d00b0210040c4000e90000c140c0e181c0003144000405004010944800300d91001030300407e207550075003200c00403017802e81aaa403ca0b0074540081c10301005a0b038003a0182c0c21200c0904e10440e0b4039039000c0c0118250300c8000010701014103000700703009168040d650080e51111500c1d80c081d4450300f0b145c0222801040c0300703400c01c48030700810503240600031141036142c0f0601c14040e0100304101c3c0208000d501c60703482683c01d4403407072804400403a600c00c601d81c60f085c40c00c07500e0500e103444910103411031948004005003e03600c40f521503101e40640364041d41c00c1882c041c21200048580b0860700700c80c02c1d08904880d07200380d44520344000d44003000c20342d0049030044841040555900d074180c01d0a0340c0711034103030760341440030b414140102d0703c2107805440014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 848866007 1250 848864757 848864773
    0x603030a030e102a030509071202030c1e04050601080603030d020d0608060702150c030424090c090c080a2703020c061227060c0d090c030602040e16090605030603010207050708 77
    0x301a42201c140c8902c0300d41406e024902e8641c005a8a4142c02c0c85400e11403126500700c001155020300c210035500e14014500030600040c260129900080742c000c030f074050344c540404079000e0340c014418180f01d900300800441c0341c40c44e51949076000c2e400c800e070000c202c01d44a41d4046031107202801b101c0e11940b51a4020b0000c108859911240f030a000b504c4d41c4a001d100700306100c0401e4098142c409001d8500c80c800b840c1081603400c00009254800c0301520040d8829408235030b02e40d60383c011444400140e65800c2060310360424032001c41d1401114885003010040100441c4061960749109650090050302c00e44502e81000c0740180d070000c490480030308441420804c0c001000820b00c00030030036005038443c060008174107032565518090450b0700800408684401080099000743c01d115038072040b110f0743c140c1e6030b2400c8806504103025403042c2a8140c000100f6030820003064142c0004142d8590044c03e182c44802e590a40c0054040ca4165400b001540d0200c0e40810000e8000d11020009000b41d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 848867257 1250 848866007 848866061
    0x140307050903070b55110703080c010f1a0904020a08030a031b0c050d11160b090901050612060603040317040b0402120a080306060927100e0603030a030e10 68
    0x2004060b51400094955507030901000700542d0040001c02403681d1045c0709a03100080a0343c80c400035091000c401d12a144001c001c105e03803100a01410f5045800034440c804011000500f07907880400320080f0119042c1b5201c040745001610260060b0010703200e01d001d103880741e1801c3e0440e44044c52040c0401d4881200e001341003410300a2441d02007103464840c410301e48550f281511001d1100c100303030410807042502424081b09101e82c0d890b8500b480c5030a03003000e43d01c40000705244c02c110100e910800c403400000501307003088800c4810b8211001c1c81041c40303a690208214160b040070704154200a25070011000302e010720307900c25020300d008080c1580c01d460a032040055030141000300d0909900203151840015070f178881501d420200440c0d102c0c2c2c0703407032a200226449500c0404c1070002a90f50030100002052420f0b80d030344c001c007040b40d11742d1a541d843e0440458903c00588145405500820071180790a200350b0240015031141c0e000c1e9890310140000000c25070b0781440710380300c0200c045080a200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 848868507 1250 848867257 848867317
    0x160506041412032e21060c05190305150405040b0402041b02032b060b04090501080d0503010b0a0903170c1506010f0c1502040e09010c140307050903070b 67
    0xc03020001902c0e032441c130706019240e4103e2a01c0090f07205488240c002c0d90f00b503d51040e450406440d4206160981c00d80140040201c00810607040d14002d10b00043c400a00d803180c000c03520b580b00881c1d1000b12121014000724000c10004110400c1003c64000d180c01c265901e001c0c260059000c1d04924510303003024010042102c1284c045000015204140804a15004000d40350f1081c00342421202c076490381d50002d070001d014101035498440c0b4201d400309903204450042e0058a1035001c00300801d85e20303009000d5851417a86001808a2824401003290326840802800807600038540550100c0d03482d130302c10007118200211810100400314007041440030030462030b1a2211400d55120142c1000000a000c4108040801c000c0010f50f80c4500300b441801c00712030300c090718a40740842d0b9480d81c0e90f85a0781741083c00d480c1c0c2080e03035007000001e10400d4400c1036a020388a007482d5000d895a10340c41802d607180c0c2c2c880d00e00a50940110440001c07020780d0103001d80016401c2d0750b030a1045c40880400084c1e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 848869757 1250 848868507 848868523
    0xb13140906010509011703041a03090f070b0d05181204050102240c032d060a08030a0915030b030610031103030406020706080709080105070c0b090c0112021605060414 73
    0x80c0650060004000780da135003812850468a010981526400850300002c1c203601c582c1d00320f0b401000609000701c0d03800325900c004520070781c0144281e40d1401840b01200b40c40c0c641030300c01c500544106004080b5501100c2d030005e60000c495128400c0c80b1140080703454280000b01c401040301210220301002696018065005c020740e204541010b400c4e20308032900781c0f546020b8001d492404c40800041c601040003c02e01100d01c0880303110205503003401410801448040302c010b0301030102c04400240664000040c0c401000721074440402c07060074150740b03690001140a07000100b40e111910361049840a001d100c2c0500c40700e0030080f800c541541400001c2c0030001c1031041c021f178010081004488d501287c1241078841cae500d0f014045464007001101e01090300c0c4c000d0307541c0b5441c05042c8903070603401c40303091841f807440345803000100c0da40d4180c01d50b100c130000405240810281d045491a6145541c010445014258194840c00e41c85e41c54041ca4803008441c11219190082e03145d00b04c101c01003207030107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 848871007 1250 848869757 848869771
    0x1090e070206160e130203070c0b09030901030f0b01020d0e01140705010e0c0102070321030b04050108100e011a12030c0105090a14010203070c1b0302030105090307030806030a03050412060b1314 85
    0x80e01d510440b50201780c0001001640201c072680c0800441c48083c42008003c06568100d041c240f0399080074070202d5180d9200c680414042483c080d0b2000c604001401889412001600503240d66500c240c0e060b60400120071000e41044814009088000204005080c005008000015000c0d480305035492601200a00ca2410342d80104410800500381c050136091000c40042199040ca18840003540a00a41015581c6c0310f400c00f00086020440001c04640d04042000c050280f42ca802d103105081310203c40407072a408203014229002410407048403010254204101d07840c001f20410050b0850720b055420450380e410a4403d42c040c8007044000300c20b005c400703100031132460401d200c024180d0310b45000b0081c520340503d015201c0640c1d44035191402180c01a0090140707240c001c03500ea80ba540000c508402040711070020944030b01b00050410a400d9050302c400d4605400e000106503039940c04078048a0f00b540702c102114640d201c040503d5090111b190000c075003981c4d86507180d003c0c94801402c41d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 848872257 1250 848871007 848871017
    0x3102032a0a080309030a080c120a0c03030b040501031203110d0c0f020d1416020d2411030402030601030605100f060f09092c0a06150302030616140901090e07020616 72
    0x105429034001c106c801c0c00c00d50108030f45680e0094240500e080c0905421040b41c10034001c01ca040d00399070001180a9400d10030fa8003007018080075400c0100310b450038007004c0c101c513018049080c40725000b40d014485030040582017a05250043e00d05038107071148000c081000ae4290242d080303101790104403040e00e0310340f68201620341908666201c0c2960145002c0341038001140344040d002d5448203108030318181e81001d4856840c030243e640d0b0360121042c00e096401c00038030340a0284121119101502c0c06a54001c0107000d50ba440d607100c0380042e00011f008082b00598103200000c1c102c40401c0d890005119030303251941400d86039007001d0400f84055002201c4142050a4051000d10242e0034a441c2e500c05640d08569005910600746056030a6000400841c40c01d28081003800104082c5011244210700b1a4943d07a5884042000d40384800e4000b00030400941c201c0c1544820a0702611000d603061400030b80c2290360340310541a0342e41c1580d2040241e0040c1041c03003158401c80e40e04c1b01350b0021500340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 848873507 1250 848872257 848872267
    0x1605090405030304033005010602070501091809031e02010b10050414090901021905090f030c01020a06050901090b01031103060a050c0403020105031902030115083102032a0a0803 78
    0x401d070b101c0c0310040004003000445186884180b100c080002c0c01d100f001071090940c20b00413000240141001c2c001c00300988544000040e043d07106205c82c0c4d083e9a00c2300c2d107503003203000d00c04508000303040548000c078144950705160301c480c03505072010b05c40c904210380d00114be035400720018007401e10b054503805020054204401e12180e98104100c1054041c20b6035140040d82c2c43c6034501d03009028195605074111001c81c0c41140582d8050098074200303400301d50700007072036091104050769001c12200c2513002d82c01051011011910a03484568024a100300105603020145c1c0d4642c0705c907000360800c41e9582e00a404107415400c0802c115548031405410030481420000002d0390306006502c0001c0c10420000005018000d032040e2607080c0c40d41c0c1442c15500c0f0350f1074805026203541c50008503c00920b40b14005010b0143c48181d51500d400410030010780141421441400f0441011041e6014842d901c2020500070312100904e8102c08a02d0078030010351a04401c200c41042c0b503030f021a03a50303482840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 848874757 1250 848873507 848873513
    0xb0306150c330126030d140610091a09030a03050a03050f0c18010903120509130b0a180905060a020c0c0102070509072604050706090e1618031416050904 67
    0x1030281504d00d905440307640d100c6241401440d8412842c90441e82d40400f03d4202c1b08064140c010a00d8900814500b002d0356031a0028800030145a014110004600c58801c11081c0002218513400400050481e032070003910101107890229600700440c0000d0000483c4a20503030305204542d0000318005070044c560a00440b4008540100312820119090402c0b0180302c5a000f81160b0009580c005a10300d00758a900c140a0126088882c50030b0103400e10300c0c002d181356000c61203400c05805004103010140e43c2429818420a00f144010505003071303440a81602086007003044502c2f0340141c0c5000369407a00c1c00002c09080c415004903960541d44244800c0c040c1c0e95910803007a900040a1410002800388212000d0703ca050245c2240f42090244040c041400000b0454000b81c0c4c4a64030f500384901da8405642003a200100c0320100030540b0084211051031003050000c81d05090070788600d082907142c2e00d9240012030401c1c2d03058660b503c4000404486100c4940c84030003040300300c3c5d0000301890591 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 848876007 1250 848874757 848874853
    0x6090b0115030c170705041205060106020f0303043203130501020c04180f05030702372105100e0a0b09120d0b0a09050901020706050117070b0306150c 66
    0x141d030451031201380f0010760124450b40c1510006e040c100381e00081e01ca81424555115002801000c2c01401400010700707410340c0000846c0c4c060f0740d1004680110313003a802c80c45008400300310f0411081c599220044d0f5000fa808101800d00348040e100d800c01c000346403900182c50801c040500500507810400030f41c0104001001c403a02c12034010100d0085107407103103030550944c0f1804000035400056104900e2601d0200c1c3d00740428088410041080703914500d001c0c08070a06244140d68111041e032070121817140c0c1d420b4980ca07646105d0011110f100010088040941e91121070520742c41d4402d214500501080313007102c0d900039140c0d5000d03010080380c1500c01303000742c8191a441c07000244c807407803a184262510b8101900404000c1000c1189080c80300d1010301030343c41240c00341c4440303050200201da5407400f005090a1001290010240d04d407a009080e00707590001450903130310005100140341e0001c480c1c00240f1f501d54000e03002d48094208c0c18a54100f00c840d0100d85034251144400016940401c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 848877257 1250 848876007 848876027
    0x21c02120a03110412050303040b010f033f02160e010627030b0703050405010e0c031b040b03030708040e07020c0312161401060501030b030c030c0f0d06090b0115030c 73
    0x1490b01042d19420781c1940f807034600c1182e000c84140d000301900704e01449808000345008611a001201869907284a9003050304ca00340009460540490480d001000107030f0000305440507444001c1085903948940c21241e040d0700018100540c12a06044403843c00005c2500080c082c61040d825065041c41c400a040040300700c0018007421805a6280442c200300400400039507000300008020320740f203003000f27028000030f45048540f036003803581d48030b280034000c40c0796200441c0c068014000c00b80307242c0039240603400c403403440c5800c19501c1600e5205a14180020b044490140642503a138900d0400c0c41c001610005100d0821500200404842a6008200c0341120b9008001c025140c19071400041443c2d0749005c0003d107070b2504245600c45840e81034001c0821250240c0701040f1036210002410b40302c900c0b868403154035401c0110140c1251904843e1800140c00142214417550741c03543e6200304507120440144d55050620b030040040101100007002082c140d4501440301c5591280064110525 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 848878507 1250 848877257 848877277
    0xf0608010b01230f040f060203191707080604061703070b06120d121e1509091e05010e06040503190504030b0a050c16110307050604080706210606021c0212 68
    0x3c00a4800e100c0c0c02000b00745d5024003844001500c135150381d801e02075941c1c0c0c81545100c0103074008500624000d4046e42040040c2222410114101d40e140f003c02c48000a00403d0140d110740e6a0502080c0c0004032540d01000c181c140c0f001f1543c4040d135040c0182003010080800b0300c25000d084140510002c003146210b41c04019040c89110303010b46500480113441c0807804024444027020301014082c156400010740c2c040c1c4006001841600c580803c02920841000909200c41c7c081c01c12443d680141144204c8500401c0001020b00d6092699410600e043d90709443c20380c8041010010328950080c803549408603801c065190a00c0c55a940e00e02d03040003400180c00555400c0040c400343c801030200c0c2c0a03000d122082c4110321416141516420907404849800381c40f13031882c0440c40703007446400c40d402d55a03440010030319189041c03004c0f13845c2600c2ca02c0300515061003540c0243c00e18000d01a14025100341d0b00a030801c00f5843304840041d0124200302001c43d80486000000820408d04682c00380389 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 848879757 1250 848878507 848878577
    0x60b030c13021c1b030606020601080718110f04033c030e1c0c0504050103030c02060a12021603020c010201090804140a0e15121605061c0f0608010b01 66
    0x354003524a01424a01446180e0604090744083c1c50f84a101001c2800700e1192000c000c2c06d43c551004a0b6510800d02610400398860721051091094901400500008030000030810380c0800140c5030315034001550554103e0404035050080200e1340040303083c03044000c004910200c101600500302c0b40f00c000e904008103c050b40e07603401854403030241000c8001014002c010701c0741c1011500e5640c112480c1040d5102001c6040200c0d0a18141c001c0604072509079842120042d501c0d000c2150540c004100031080c411050305c81000201140003030301032070884890806012420b0304003c2c0c2006400c0b08510f0441e49840e85410000d0603500907a010781c0c031864000d0300d4a03121280482e03904591a045030421a0070081004440c44c2030810202003203005a8194002043e4400340301e507507030402a24030042c0c0c4912070f0184038074140603000e800b40064002c1c1106e4458480070340e5070112100c20b00c0b030b00b5480743c5a042c1803150318404d00070007440c80d00a1900e8008070f640c580d180b01c43c00320780c20021841c883d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 848881007 1250 848879757 848879767
    0x1215190902090c09040b010801050619020f0a050d0e09040213150914041a0103030c0605130212010903140f0304061d2406151606020c0307030903060b030c1302 70
    0x42a00e61140800c1940901140350604005080440395004040000d10a0b03003008050507841d40701e891558101c401c017078212410100c0a100360040300700700c0121201148140442e10340201010000700010798003a402800301728041080040c10340008109450140c98400d040c8001a25246050305d6199542c000006031031000280c10131505030154003e01e612802c20307204443d03900c021070341c035401580f146c882421550101602a90301041c00d22001c0c0c08107141c1d1803d24003041c0305812195209034820399546100f03c1c2d43d80081c0010007000b441c88156991903810908254001c188003007443c10b682101400e1220304102004948070061008040780e484001d059a0308013450b4045100445020560fa040d405210040580c1008000c9010246448102140150811008040c00c24854448003480e2103d030550b07407032401060030b204a034402c2d030810070000406018800b60103030610070f956520031145542018002e0303a8041003c903129801011802c07045540f142c41c0ba10381040401e1000da141e03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 848882257 1250 848881007 848881051
    0x112140c0a030b10090c050f03092b08090105060a03020d1703090313090219031d0d030e0609010b100c0f0503040e22390909021215 58
    0x914003548058210a00110101c100300b5458000d600c81c1c1c440150607000c0c0c41e80c81401c5c0055481c41e4605401103039040103c581e107140d1007001544e000500e803044406084419107154403e0750510111060301480c2c45094143c0742c1d001e0328403500f152101000380a0341c1450300006d103046505100007481034145882c01020440c2000c6402d5450070300d140d815440e171a03d843d40f1501d80c0e1004812071440440c5100100e00c20746a417080e0380c220110b900c0d0a044140c494002500141214072420607041031421012800c480204070140c045640c5550218103001040d41e03262629001800080181e414081007804035103070950880f0b80c5803032500e011081e440031750030501d00200081c540500280000180400d09054048806008040d25810204503081c6010392003150013030100002c2001142e00112054403070480301145d4140c01d08034152950313900d0b500704072201248aa102144654680c0c40c05410b620f85001c403100c412601e080030b006095001c000450480c2e00041c03c11103104150b590f40020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 848883507 1250 848882257 848882263
    0x5011b030201180c030203060106030510150c0204050709091d10020a1b050c09060d0c0e1e16021203010e0601031107020d0b190608060c07050c0d0b0a1103011214 71
    0x24040c042d1403070084586513400c1880100c8100c0c08164001d00c284000003900501c28030902e840386503042c0c0e03055142ca0800d0b000b480d0644510040c84100806051003101503999031142c103011b42181d03154840c81a00d003c0000080e9000c41c08a500e4800098100702419900070800e45814070320f0446c011b0359540c420030706032048049805082c0103109000503280402c1400036045011007001c442d5034113203944000400c80c216507690701c003d240b8044007004003d000404140ca6070070a51150081d5203440d003014401815800c1281c124400021540300f0307446054042c13013165000c2e03440317a051074a5581425403074000307200044d214504040d13540041348100480c0c0c00646003017950041c00c09110421600b8600c440c0c0c4c00c1030701c8807840607110606070001c941c1603210b03490468919002411840e030701c0c1c01c00b49000c1d4008100a950768016442c103203203d561100000e1f203c0301e00c1071484801d1402d0081060040390410024107076240c10070070040c441c0c20303400380203400c440d680441c07402d04908244080d181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 848884757 1250 848883507 848883521
    0x5031b190603061a04030206090d060204170a0b0c0c03120709090501030602032415090d05030f07050c040501030c0e0402011106090a14070b0313050307150b0306090705011b030201 79
    0x903145100c9800450040d5150300404102c81e0341c00c0d4800f0041980888000c071620882c07100a6211004001049160030322160355400b40f80112030041c141907035810684004d4040d2141042e980d009002e11904101040c1c0c2c2c0c0d11342000b60001200d040504101c00e15076a4402c0403aa0280040c01c01c0005140b98411007801010f04860003085c0843d5a691400038043e41080da880840c40441c0f1780c1c000d411812100d030b154007024008084d008071a449d844400180d070301114015400c40b9030a242e801c0424800c000401142881c080c041796650b12506099040001c010403451195060400410125030002000e80079680c00e80710380ca5140c2c40d075200503940750103030ba0000c0700c00d40522803c0011406011403541c025601030003079800c00e401d080303102540324507440c061280c52060602c0860010f04c0d010070480d81c1584100c04803850000790f51030740b0403441c1c10f84011000341394903a60010010b041c14015503402c07442820040400901b0302d00041c1194202c40078800d8092241c0740c0104c2450b1003500411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 848886007 1250 848884757 848884789
    0xb0a1a0f03040804050d322a1008060a0617010303121b08060307080f030a20011a1804170306460807050f40020405031b 53
    0x501400e240c6c0c50190f4150003601f40195441d400a030608070348035403a03180340b403100003070102406100b5000302d0100c550201202050003a0f80700000c1d00359154450340e1851841580645400f520b5203000c1080040c0a10190020410030079140e10800c0c020b490503103440d041d00e5060401c40e001840c2c05241100a08620300c90841c0c1c0146158103040e03480c0c100c1003860103a501a416510010380f110003169035100100c4403d00264001c11000b814548148401c08040d40084040030100c030325400002d007510407101a01503030510704000c081d50761401520b02030301300c910303d80034443d10300c0c01e40c440c2000b8604004004040180c000005080d0340c3c2d0f804521507000e01d42180040a544a940000e010b01014030101c0345102b8440a01ca074074a14103034229001c48415400071f040030390800c800e1008401034000e020b9000101d03106011080240305a19154024404174005080c6218081646191201c11860b5891602c100824402a103020a810111086101c50080c2c10306103180440c2c05024804214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 848887257 1250 848886007 848886019
    0x4030b06010c0b0a090524041b0b030f0106080601140a0e15070303060510021c05070821060406140f040b120607080709080111070b070905040c030b0a1a0f0304080405 73
    0x48104413640d480280101d02500c2184c118450950404c001d0010508251808044207000140007072005c04203031550214106c00c0401150344c5803802d8140d504151030880c0803d10070780042c0308041d40071820650001003464112240b1b801c0801c154600d1150568140410200c0014032a003501c600c40404255032030310010300e40d50550350500500030031842c018244160400030107100c0042c4001803c200208200304201031880d020303401a105030307104402c1150440c01c00d10098602d01c0812200f464100d8003045021600d14115040208445490300074070350000000c4821055500e404425242180d0152030005d41300120340c000450540031442d04000b00c1c13048030100400a81d000c4041e03805184103840300001d964403020441e0988000b10b80c0400401000c0c01960085090407900c0342d08036855050080e1881d031a4408602560302c100b19080c08682c44080c038076110700b8020b10000040500c1d42c00320b8100026400c89180038800d078091a030107114084040340510030f186044500a000040030303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 848888507 1250 848887257 848887261
    0x1716050d020109050111071110030b0604030b07020f1c0c03020c0325090c1e050d0501031214040e0606070c090c03140c09010e01030e0c0d0c030507050d050304030b06010c0b 76
    0x340a4515003d0885a41d424017440304408015442541c00a992104540000902120601c1202d030341c240315400405071030712000070309510350074000c00156002d030780401428500103001034500000709200a641d5840080380000c101c000d1083d05003151040e240040702c10f030341403c04a00e40012564415414040c0344190552081c0082101c40c0c0c1046101020608a41d41c641c04011125000710312404076a6500907040c0381d03c462031400c02110303520304006051184006590341105e1098000b125400e804003a4041010b80007056110440c1c1403032103080c03625041c0450045241ca0145c4079a02a00004c80c0c00f0f0200b065501115000d005995400c00c0b8046a044005000d45807102c000504990101d000c1608506003204645100e803045c1c46800c45103000d1001100180800340400e4800d0040096590356591101e006c103140901803100c0f0361401c2c2c25810030a080070b8156201c207201310080c0b9201030001e0008800d407022241c024230814010b13a25580181e581501d42540184003080c0e04d42 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 848889757 1250 848888507 848888533
    0x51311040e1e10060b040614161e03081f120f08030a15050f0102060f060301060b21060a060f0f030f091a0106050a0c080309010f020c07091107171605 66
    0x264001110303007403c0080c00001e40c0c0c1c40c1e2092884c481c0d4058800045d1400981c0030a16007608c00130051400c1e6500e0302e4503a411507071642c098407103014801701c075a150400d4408082c19884104c40c0d400800c1040f000c01c00f002d082000380031b409124802d0b031842c00c1d0f04443c80d500740040c02c0d207140e8696401052407a900c0c5400316000000b00503046038404106040c900100d480d040c8503203030070f0700d0030011b80040282e5103540b01441e8181e0001481c1540c15901c03a0000304081454201602e101610607810001000c00c21541e114415001416203014204006003040070f550f100341d0181c070059841c14150308186110404070007400c5110341c5154038504007030104040001c80c0d2900c2da00030064105000c8541d0304c03000c04032018403031030503040b00040740140481e020030b400740011070b0024103520000411565601e1040700303a8000b6092011640c220320410045e400040c020803c2c401a2040514680f503103540da1000c1e208032507129100021408075590000c40514020034102d183c000044881c8a04012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 848891007 1250 848889757 848889763
    0x2090613030c0605030415020310081204230102070e0a0213030c08100e0c010e0a09090308040b0705030123240a0f020601031104023a051311040e1e 65
    0x48401c603030607030280d8030003e0281e2042c0c0c2500d0040b540070300c1e40089008401d2142008e9080075000920303c80e000e2030300044d81c80c001c12111614580d21041c998035685000c0d11084803100389070100503c80c2001c0e03103100482c1c0c0d010544130300b61141c1441e28039068503020107a00082c080e24143c07014118012801101344030890030f05000b02e4143c00110f80b4a03000501002c2d0aaa1101c10059404d81c450340c0c86000c83d60150f543e040b40b885000d840d50340741070b0781e4202c03c905030f4000100550218106200344800e000d001e01c0e00c00d41c003a601d0704016107154500701c0c00384141c064807919541601414188035a465860100c405145041200542244040417184507007a9200a01c2003020600600003010104d00105034541201c0d08032400e251500c0182c000d22020703510100014001846c12100400d4910f009030304a00600c6c000007130245210b500d141e4010440e0f034084c1c0b0360950711241384501800034166191480c200c080c01d50b0b000ca00c1040038100607240441c800030501200280180c042001c030400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 848892257 1250 848891007 848891009
    0x180a0c050435030c0c0f01020f060a0203060f010804030203040506070c0308032701090b0f040c050d03180f030b0402040e0309131b0804030f0f0e06040e0415060b04060c0602090613 79
    0x1d40c4103004241d50b00070025034a00ca9002c00c0f507071a400252640e4071600d00010741d1100c6139018010b5034501004007a08608000080300e0504034a5070210510074142003e0710f810340710075020b003440681400c19407801b80d501c0c0583c0c8600c0340b0132100050004200701002e03082d4001035600510750798880c207244000c115000d900038100140c260696403044444c1605001d82d4400c5078000703400340016120180c0f50100f014000b03000b655207d90f05138000807181c03941407030f40703400c4c5000380d07501100a6803040c403811608030185d204011030040c00d0710900118000900c0740390850707412540000c0d40c6000940030f90640c0541e0100a034404c512415803442801c1d03c2e041304010004540303031104507243c419415104400c00342c0c3d0141c0001e50134800b0403421800b414500d00340d18190b05112320094000e50001c0e440d640160007000c244a80c1c007081c00308200940d401c079020400250000d02100d4200700c1d149515006500c1400108001000c00c0c03018011203504039140504040e005550311000075180c50450940c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 848893507 1250 848892257 848892329
    0xc0602060f06060945162a021f210501060c140c0904080403050f0703170f1c0c02150609060906010509030d030509010b180a0c0504 58
    0x1c0010740b1403400d00121500070340014144001d80345698040d42c41485400310418000c0e41d8240750300b984035180c040c032142d030041090210700c42c4c0c0f41203079076075420001032600b00c01400070748401080900380c00c5210010208032201c4a42e0007085500015402c40c10003406a00c0e501080507100520b0307035114030a405036180110300c1c02042c0b00350b601c070181142d17401d1140c20005502c00704034900080b0b510012158410801e000c4840480c2d5620001e49500c4041e10215040c1900040400c208101440003050007a41c01019010302407030351b1206440b07011005000c4140035000203550f4550122071080d2040164030f802024102c80034860158000c01e082950440940f080c200c04149504070103070046e105441c040c041e514a61110400c3c0701c8100c030301078442418080f0a000e20030f69a2020030071680c03164901ea90100765070601c141c000342140c4068003c980168008402d030851500110306c2150080c0002900140c1804071070804c403580c0c0107031303004645071103500710b02c854401c82030801c04591080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 848894757 1250 848893507 848893531
    0x70c0609090c09030203030d15090e0105040605131511160812010b030c0f0706020906120609091222051c030813120f02010e07081b0102030304030215040f0c060206 72
    0x142c19007041d2054000c0b40700c020b5141d0310810100d9100f42180d00403501800200300c0b2201090349640c41041940c0c030b03030348c25140540e43d0340d42004280b05403805000d41101169162128038000f58035505807285031010800703a1a0344802616200090080c01c603541e29001190301c032003c920794980407159900c546144070100f20310200209030351400c80200c900548020101c07030310300402c54038102c89642002c0c8090381c0c0b043c0d00b80701828075500c500d0001d11000c5030b0308104503400d2402c4010000c1180e40a0110341d016889109058507004040d022100b543e00200440c6404458141c3c082d51004100d0300500d401c10200385e01d20340c1e000c651202540c07010340300e074840000d80d60b070301d8070300900c0c0000e401400b92815180f51501035070a40070302c1c40486034121301d100200c0c1001041c6040c903c1e181460307000129607400202004200000902d00050a0409201540c95400c141c1c40c02966030342095a4481100112808202044030012030841c0f0254030065203034200342c3d10540a515803404030780d1000444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 848896007 1250 848894757 848894771
    0x4150528203c0319090b0d0e070914090f0309150304020409020a08060f07050304030c1104090834030206160504030c151b02012f07030c0317030403020c0114070c060909 74
    0x503000e0014242500c2e50200c6e40ba0901e9200c49550010b0410340c00700c03500501800c9008254080036028a2007a15079840300612903081448440c0d28020124500c0381440e041801002c4c466074074450381e01d41c808915400c641e21781e200c60001400030041481d00940c001c0d00000002080078022521a10492010300c0701040356072100000e0320a0712040310003c00041e00f0115074000141c00d840c2204142501400004402f83c107540c4508031540301c03010850180807103d441d034030380c00340f41d504550340c0e400000790103000001e0030341d4065540c000280805d02a00301004000d00d174503118005440c002e40d00700c2c0c680c445007940d49100703140b401c102954100020b01031071050f120741d03400101220080c0354181c0d81d1041710b507447c001504008014090300480452000b40f0003140800c10003509d000740d4020510b00c0c00c868550314000703042404028521407074141c24020480803940101780c40380c010b8000e0078000c00d510000d000700403051007003d0008003000510080428106e40c0400b66600b0f650303d24000b04884 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 848897257 1250 848896007 848896057
    0xf0706091401052a0c0a0801150e070c0f030801050906030a1a0702030408010603120206060a080d120906090f0506060d0804150528203c03 61
    0x10004600410500d80a040d2900740554803c400403e603030b412210020780c080c60b1481e0380e00010b4414800d102007aa0048041e011140750880044000b802428000c010252140480a095585074455888000814800184068051000400903c0c0d00000104000e80140740192580030203021340e82c02107000d00001001810001080c15169800c511025030543d072607070781d003640380070700030110303011400203100005148009010f41e10196102c1e1076040d43c41c05280c3e00c0240303481d400402e901d114002c0c02004100c54007000c40e0010a0020768903001900300c17038900340030380a000c3c0351000401c858030703102103c03007800f0f030454900421510900550301251141410880c10211100003d00480c03c100010000d00302d026010744901c04241c1450740c20910f582501c25400b04c0e800c03081c0207001581c5000c05407021343c01059202d02201c41100d84038050f42080f00650b131440d04911801d40e400c0c0301d0701994080201400101c48004510782004e0069040400340c17600ca8101c50b088904641035106200f500b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 848898507 1250 848897257 848897267
    0xe030a0204090c080a082523210315041811010e1806120105150d14030304050d03110a05271306051809060408032a191d01050c011d0f0706 61
    0x18082d00440326403480e812140f0032358400d40100c11041090310458100143c81c05402200c4246850710010103074a81c607044d01da0282d1204001a918440c03480d0403d943c0c03110103c0c46517803040a0b0448010007003004031000584450f10340e20f00c10340d4086131400c20603040d401e960001d0751003000d0584940c1413040c03040511609940b03046c2c41c0090041020a941809810b01d0300f0341e40d440d40e009074044046a0981c5184500b9940140c40680e016080411001e0030f650301802014801180d1840f0709141900c0c10394024194010100e503426601213803a05070034510007541c1850015180100045418024105000014031280c03040728058084280b00c640180d000b1641c10b84580c4802d005482190307500d5450b244907520007040a4505080c00c00d0750180340703003120782d100700540c5820b280c1641d0307000c0011503100c51451911120304001500e0894108050780040005a08400782001d50f01c4542c4580301502400101c0d20b2041c4040c03810945e404585000140901c20101d120140c400c11030302c0d01000c0315 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 848899757 1250 848898507 848898577
    0x41403060408030a02070f02120f06010e090d110c03010c120c080405060c16080c012310091e0f0906060e040c061409090403020a050d0e030a0204090c080a08 69
    0x4102c418070003d00300c0c108603002000250b118042081e034484d403d03070002c1c6125000100c501d1280e40007000300d909000303081091070b01504010f01e031011f0610300945003941d1001c803407501c1410841c00310502103c5250401035100340d0b420040080c03001a185d031000500c20b43c0840c294238440c500b4814030310020350040b034480b40510381100c05404580d0b20b408450380740368001007124050f21a0792070140040394880003e03113841390b240703000854024140d40b000307541088a92100d02c207041001c4103028070759035a503402000f01c551804002c50756449585101c130220b461210a1014642041c00018882245510100210340305400401004c0d440f4050103000e0b00301150010184031005000b4000e40d40128401040304031070f01c59040c5001409000304883c02c1098400f01c2c056446840760100b04082800003030515491464018202140c0d04002503862940c00c8001c0e0245030380c2ca0810083c02103502c641c0c4003400ca080c00f156856005454a01004d92040365004846009030b19001e60318110165040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 848901007 1250 848899757 848899763
    0x2070510090b090f060d05100e061e01110a030806120a0206030f04080706060b181c03050304020d06061203140310090b040f05130303051f030b0901020c070b0414030604 74
    0x89403050034040d0541c840d0f4000ca02c40b039846201032120b0304069030b80d14020443e031004000089400c0c200032041c4402c45d10160000e00174400003004122840c0c41c1c009106500c0501c081012844030404001130790190080304525405010f441c407040300341034020881c8d500824003911419110355444642c81d031500c0c5c05100003948450b041000ca55910080380207190014000c680e010b10b0200707036584e808216042a4002d40a45c800851051001111304a02803180c00c42594140e602d6a929100026826921100101800b4004c004a0150b4a400384a81800c6070f000b18208410341c0c550302c00400d40c0460100440004040c6801d400103c000f442c140c034016520240c0510b00b4038100010328000d050320b511034a8000d955411540701c3c2458034000c0600074a94950040340c481140c0c10f0040c1903031030060081002c0f581581d80c400c0d0a100c46102081100c1e0460f4035007025072a4070200501901c140c0300c841c1c3d024400c4207800b1961241920041c03080383c0750301d0030414126a004080c9a1641400c680103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 848902257 1250 848901007 848901017
    0x90519051606050f031810090b060d0c0501050f0c0d02070807081f0e0102091906120504020d120504081c110c0916050c4207030906180f0302070510 65
    0x80302c908140e80207141c002c41d41082c8801075a1400c4c04052510b4019207000821603241c003104e0f010700403410507492b04075005541040381c26079180c0311104620a44c1c41032070304102000881000350980e041c15500d200c3c4c0110141c5600d20424500295104128011401c5c0742c002c040d400152500b0009045010780120a10082c241b2143c0b000c0c5d000901c0030002d100442e5400f000721103a240e40e4400d5540b01050302c0381018401e1802c10b8001410170701c050b50140311f0035181c0000c0c0300251b40ca00c5076107200303c1c6d4007510b00300709184520001c036014020f90340b050410b441342d0039203a030041d01d0405480390442d071190703110b100c1d048110862a03990000c03e590030750001c1109010038001128565021904070b02420864a0400c02e0000c0600e4200b64030240500d81080c2d0300001c0c000440c113a801c1540d5200160703481100480c9031050ba031501005003992090540c1ca000b2b480070059103401c0f807852090412120f0b900d161890a00001a0032145c000f00d0041c0203003000403c061410001010021403d0343e21 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 848903507 1250 848902257 848902267
    0x7050a020c190b03071808070503061308040f060309060506541e040b2a0d0209090108060712050a0f02040b0a110d050d020d09051905160605 62
    0x18056450019100b080e18a00c0c41c04000c5411030794100107500400495442c4030611111075440711541000741c0003030805030001c0d00104015a000968203401c051a140700100720503042c07801d402c1a2245030300ca12495103c4010000d0300942560000d1040c07400f41c0790a01080e601c0b00104040c01c4089081e001105e0400d8000030500c40820180d01c200801d08a880b003104480380401c1922564000c1600016130455420040c07000207031404589264600c01d500304060610b80d0310462000c10040c0070883d400350184080c0b020141170003c141c0c4248a5401140c6d0701c1e242d001040b00a0b61004211500480c101c100008140d00c001503220306c40c4d111075031010100c0c0e01c030740f03070100c040c00c0c001d03240101d55900c9445101d800030700d074801040241542c0000956642c01d00300040d20540300710040f05034903000704004c40035690300602120900081e604c0c3c0166142603035018500201128200684103201d41002c00380751924140303034655034038080c0c01140c081d00e82d000402042c8040c41e0050500007842800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 848904757 1250 848903507 848903509
    0x60a03030e010e210c0409080a08090c271003120e03030d0c0504080f0c010c0f0203010e010c03270512090109170601140103180b09031c0506040507050a020c 69
    0x106107409010149480c0390800841c80020740c201030311180d11084044006200741e4a05000c02c00f01d01949000d4405000c0d804258a600d54a4003840d0b9040c070031720a00742e0000740042000d011100d081440141000261416204aa2000c03100c001c00c0c030264030861008141100396507001c5d00c00304c0b81c0c030900c05400301c0d11542e030417201d9210f8011403079010312003845400295141d60044898034a0759a03203c645a526090502c3d20b40f062000c07140f070b00c40d04491010320259910248a02c100c5410100028640c451071021900600788101500841c1d442c1c4103d4000840c0d240d000302d607a00211040344021a44903207012403650281d20304c0101a9840810f112403400c3c5550047c00d604c85050400c00921540d030f110031010b80090600760300e0030b41c21500040c0824607081900d03007101c0e8000e2070104840c1d2403a003407800714011885000707400704074404002010401d04208603016803034201d0b04603400b4803841071207074098a0180c51103446103081c00c00180c0014404c10075181c4082c1e040d401030000d015500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 848906007 1250 848904757 848904767
    0x90506010b0f0405150a031503030f2609010504060606170a1503020a0602060f011205060703090606090c0e030c0301050f041e140c030708160b0c0a02030d0224060a0303 74
    0x8102c140c60100144000038099481d01402003803802c5035041140e4070500108010200d44545c00c07000c0e80d514040100b4030100e50b00ca07141c20b80320001400d01030402c00341312003464154080d00065540c441d9841041000d0b8078010b40050f800f0300c0c132980c801d0100d2074403240107031000302c2c404054612b412401710001e80c0e03010080c0c0049410b84a5803e40390040c0d0748a40125007481d43c20380080c0056071001060244061a1200d101d00500c21300c5441c2c1c810744c04a944440d01d424000d0f05190405032501200b03010b0207150b078804002440300d808100030b018801c0c0d202400d26403103049580d00c01d02a448010301e01e41418000c95100300070710050700106030740341d070f480d20703003a00303141000348212440024002c0001d42600d0f40b19601750461001441880000420145416025084412241c004440b03010354441c00070712400c00d48004a00c080d07150116451203524003a401500a9850712901c000400b00035004030b65482c0300e02d244c0c50300c3d0f0704002c0c2c0d541c0c24000d080c4042d40c90b03507080720b640e00081010902c00c0d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 848907257 1250 848906007 848906017
    0x7020907170a1b05070f0c03031d060a0903120306080d0207060206010806070e0607081608030a0f0b0609010c3012060302060f03040203010f06090509190c0302041e0e0303070e0301090506010b 84
    0x6d8110486102c510392906082c02c046500101c0104003c200031070b50b044d2030701c2400d14460200301c0d00c1520b40383c54200000c00b490418840144440381c400790501c105402900207502400b060021100f60340101c10000307544444521514001d03000d00c0d0004130b5218008682c02d4816512519005444a500c405000c0190311114040d80d0080085c480f0103104201055441406130168148a403603040010180d01280c003e02e0581c112246802068100d9480b60803d80701928400d00301807108640500380a50042200b06904906000207030350f0300504440811008030700c1106555450031481071190f4001242c02600019500110030300440e45541115001035078841d00c0a0000305207203003440b003007400391845030304104001038541040001c4004104505103001260800c400d090040d6500e59043e19601400040d005a48401151090b0395041031000040b001c640300800c900e041e200c030440c0d106c0d00107403802000500300c040d82c1c00c8903150501500c058150054082c258603468001082003039446 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 848908507 1250 848907257 848907263
    0x3080601170106020627060106110304031e03030606020712020607060b0d1202010b060403031403040302010212090604030219230f03040605040509010e090601091107020907170a1b0507 81
    0x11500710001d584103010003580c02050f05400400349800d140c2520100c805034075031811022840d05600310307030a030740001e8002e0460300e0506080c01d0050380a0101c90442c41941c001408a62904481e4138002885810420000c2d009940070085c4a0b00d0b5001262140054825642e080c40c440b00088094038100000f07000c2d1901c107001c00190b1742c1d242400315012203851801607030210b482c8020382d0192502801011a114403c55540f0314260070340da805482040f142480302115003010000804040c000d42c1140c0d003807920302015410902d01855100d50705c1c8002c6808500500954444494011000d6212100d19034840311842200c100800200da03010030710101d800070351040c1d200e0509442c1e02400200007a00059460350b603034500b0041481203004043e88818010444a41089803155020403582c0c150303075400002042c40d100120744081d0902844070082d600415074418000c0480e00410000500c0140c0c40120880b991003142c20300499030200c15408524800d80030200c0356034416401040c200d84 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 848909757 1250 848908507 848908517
    0x101a0d0b0307030b04060f140f060a08120f0c011103041b12020918010b061c14010602030910050f03010902030115021216082709011e0e0a09060c020c010e03031603080601 75
    0x340c10700482035021b0266027112102e1640350034031040303003400610304010340b00200040684180442e100a51813046a900050780303003000c00c26414104081d0059504a031800b151141c403030820341031208801d004240c03107243c00185032400107411300e00d03280c4030924640c000f010b284443d03541c071801402d110050045001c40b5541c1c2d182d400c2081c1c1c1c541c000307020002c09090ba078140c1081418012001c4607130301900d00d840d90b040d03840104102c0d48d00104803607410f201510340d40d03084020380780f041d40e04e4000c04000d010b4900002c030001c80d900942d030313019504a079014150001040110801aa1a05225400000080c03420000740c100e0300d94400c1c40800942c81906d48500c1d10381d061348005980d030aa03003070707070f501101902000144d81d1074054107450141085070301750800d140400340d000120418501c1000080c50303040300050020110303a44000e030310b05d030010024003401a0310302d0f0007501c070100c24040d503001c44d60303c128540c8182000003d0740c20042c0c401c9108121342200b0346040d15203510052000b0f0402c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 848911007 1250 848909757 848909771
    0x109091406040e1603050c1c171309020c010b130b01090e09030c06040606060807170106030b01030615111009020a050f15070b010f0e1608101a0d0b0307030b04060f 72
    0x2e01c0a80c2c8480045d400344000d031010520180400440d040c18241102688000d002c448000c2480b00149500e99425050fa265607016881c514101140e0941e01ca41e03640c82c4003041004180a042d08170001e4030000319001003421191000c0c0c0c01c07c5960800e40107001822601051001680380c7c02031640080c3e40724101c2e800d0030b4000ca160362509900b290304442d659165082000b20f10f810041454100d041c50070f1051041c602200c1008400505110f440c0826842d0302a4000740d0f406940400c2c0944542d508008451903140c0d000780c640c0c9113580b24100c02d4441e960525203098918850182021750080008104034504000c120250310701c046146e174000e110b80c00720352140d1078804c0100002445000c40c0b84941d0700d0420b19401080803941300b0102d6180c4002045a002802c2407000f100041900f025204e036250780d1045612182c2c180c004441c05112003040f4050100c4a074081c0c15080c180c0201801400785a4013030649807489484000c2104001401290000760260840c06c3c140c040548005691 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 848912257 1250 848911007 848911033
    0xa170609370521180a06170604110d1e0b01050f090301060b04120b0c03131209050613050f0d0c060c060e15151f0e01110d0e0109091406040e 62
    0x100492406020020000040b0441c6045861a0010440348200c3d40113503170318501348010f0301c22000710030300c60600543c14002030001e035940e0f1700004000c0500c2444a031200040c96426005142e080c052440d4261051003c1c4041d06250007a60301c4450103030345e0241044481040d404150300f00356211641552100320101b42e0307550300c02c0540020a04046542c1e80503006007800910048050300d2850301c11420003c10040d0100002900511a804400d000d1000078480e0100e509196503000190700510004002e220808118054000d0707400440d1043d440c18000010803d0118001d00c1c0101181a0680100a01d50080c041e00d01003500a10700403c0460b900c070200d508020500000d40360700100001030214851400000440c881000e6859240340508506041c5004214010318401c001402551401c43d91044040700f044030209030485d118150306a4003d000e0310014000103000820070780000840912500070100e10550f110300703000380da1b2039400500002d0802e00c80c0b103000510802c420f0201c0c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 848913507 1250 848912257 848912293
    0xc05120c120c15070809090c09130e0c0f1005031b160606060302030f040809040221041103060c0a2003030a09030813020a090b0a1706093705 62
    0x8003494007810503001640b040220650811440f16040a001c3c000c02c0000751003c402c4802c40d0004880030340166447e20f817000d000b8802d52106030b070800309140748543c5500e00b58008419007542031051b960583e000c01c050100455000c41c929601c000301c4904c220500e405200215048618040c28416511050300782156583c03004190400c0143d144051304148102c1d4841c100c05030419207801d501d1801c0c4210111444c42c006072002c5d010580001d01d0340360658441e411a010003071000c0c5106500c44e4040d2102181600486098646071300a01c0c07000010310b030100d4003d2180c481c0700c00c00741c181000b030541182c010400240c04110b1001c0300054402d1180c0c00c2018606c150011320000c030300b43c0440d240051a041d406080308000c6a60080010016551803400c1e000303451800800080d1091410300040c801c05055005c0c0c54240c001074121140030300081102d03489019000111440590580038201c0c1d0300720043c41c40310800c0342c4070103c0c0a04801401240112902a008075102c001c003407520081 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 848914757 1250 848913507 848913529
    0x120a11120103170f0901030e1609060806161b0f0c030809040b01050414041808070b0103110307050901050904061407020f10051018020d0515090f040c05120c 69
    0x20000410304010800c010300042e503146440d03a60310250341070141c0310031069214054800100e0516803200c20420100c001040b1084540300e00c3c02250f000d06075901070400007072507203024080c418000c2c080080c0d8100b0010300c04046c1c1100c696208a07260100980002c82d540001800700c2d5884400300301d80c0c001c2078401c18400c001d10301603c1441d5541818104002c12588000002414010240000c1000307452811031541094400c4d0303004500c1d0381030254600c020b075199240041c00d107a80401c01c5400d00080411090680c1e00c50003801000082410400d55102c8807817142d507910258580051120f8240f854046411034440c95003c22820040d10491620300c0301100c01000680c8404c644642c580d0040000000e0070345054002c0040d0304107540d117003618600c140260102e0f4000d07a00125550601e690480d1072003a040401080785003000d22242c0c2100c01280c40d02445400d400f03011031800c044042c2050300865100b18001c001a2a01090001e1100a41012200b0b80601c801001c22916400070b600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 848916007 1250 848914757 848914777
    0x40e09120f0309060633070f111003020c030f0708070510270b18030c011e0506030c01120c11070b090102121204020607080c0a030909060b0a05120a11 66
    0x10b5124680140c185150500042240e485411505c0400d0180c8001d050f6408107038240a110800014a0a0300911548a044c80050030728501d0200e40081c041c40303607030441c100007003160024480f200010040b0140e002e10b809076002c50b00704000c0d00c24034129a4000b0702c0824819a403042c1840f03e251241410f04100300e4400c1c080b2501c44030600c0300d2140050410a28002c081c10141c021503840d121405420b0008102405040c5503076040300c0841401c01c255880c8c60900802800741950102040c980c600d000000500d0050500c40824964900032640c0d11854406035103148c20940e02c403041001400d40c0f20305a9080c00301010796135255890912200700607001031480a5629074400000914010b246a41043d80e014188501c41c981c43c0440f1000d504582c0450b000e40e1030b02140d042112042c8035040d0f0030840340c410031b0408000c00d904120b640c01241c000309003c000780740d40d1300e0001120348140c440d46000500c081000b000c1d64641031a00c0d51708440807450000d00740d214105850601d80c0030001c42 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 848917257 1250 848916007 848916037
    0xd0605090c040501151d030c0a06050a020606010c051c0306440706050d0f050f060f040506030307170706020309100606020705010507020420030109091403030606040e0912 75
    0x11181c01e040c640942c60041c14031890000d03103440303030020042000124174109044521000c1c03000c4d0aa0354204103989035940000c04491036a6500c02d40600a40c0c030085d07a0344054040c500c0040c0c20741d0700a10000307071810f4010003e0149490b401d02440014403a00518409256a0746004106403c0b4000000d520120311202410301c44221092080040d80703055015014140d00c0c8c0140000e00e41c046003a400b11035540c1001602d50080998107805025404844100b031841c1130200600c480409000d02e0003000260395043c0e4603410b140a00007038490440b003454240d0b004100040c00581c0c070401d2090011400c01c4441d007401103a54822090307a20a60b00c00006902192064504240038400c8600920a44c0001c0009910300300018080c0c1c001c0c0000030348260340d502040c14291400c0d1041060360014036610071360b651b85806504006060a0074280c2c1c3c1c4134078441078046044400011680522001040356003024901110007032128030081509105000c0c3d0014003020102c180050800a000b400f03c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 848918507 1250 848917257 848917273
    0x10f05150a02010e01020d0b15040522020910260f01050609190303090608090610141c050d02010c050414040c021507080115170703051f0b031b03011508060d060509 72
    0x308505041d20b0742c82700301c4429003003000b0052a82e07184507c599842401e627140c0004480040790758004d000c0d83c01101d400c154000087d81525906c000301c0c07008a0715072043c190308808045054038040c48101d0740140002081001840341c0d2412001900750300710b00420309400b0060a919801b54103142ea482200842d01441092004680100310182e105030840001d04640c40c0548818020b404a480340220f450001114080c0948940002015035480c0c2010400000340034641340390b840032185030440042d440c10b100c0d600864801e03001c4408a5038882142e50504100b18104002001038003901000d52142001800c1701058041c10140b040b111a100c0c0c04180d854880b4499511540c01c10050410290080c2c07030042d02a04644aa0427110302d240000c1c00da0750f000d003012956000c2c1250031840000d00c5400246101c8060001c5104a414407405024001050b0441c40345000a000c0d18a12200440a00200b58428107003654081d40061080c0d60507100760311400100d4006644072036080d0040c0d12 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 848919757 1250 848918507 848918509
    0x7170a0c0b0c0606030307030804020906040e01020c07060e0402040e0f0606040f060c0c0b191107081005060307050f150a0e0604090209181306110c12040608010f05150a02010e01020d0b 81
    0x84001c0e444041940514500703241c523500180100b40c02440207100d9a0311901240d0940c131a940204441c682d000c000715601d6149401c05c0ba61440d941c40b40c0e0001802161000c4c609041c43d0094801321007541c000e84441d40c4582143e0054610f000701002c0c0c0008051000003580c03858003091070010701e145e880f101c5107401c0341c1c01c11a0010116410080c1c00b0007041100d44100c018004000048100c60310740200305100a41c3c03124100f4103503a001a580344a00c1c0000d182c0c110f031580c48140030385801c0341110076840e03036007040c050140304005080e035001c0c9050078640e5103980d821005203101ca00c1880c100070848403a4001598507040343d04200046a8007040ca580d80c1d0900c0e0040d5000c9008100c0303070015501c1c0280a04014525142005080945070348448103002c1154082e07a205100c102c0645440b004d03c40c402c0d15598110740b041000003001080001151000c281c050420b0700da024144104103145242d659000340d00a5803080c0441d9610090030384985e6007803001d0200d44610340313004034240c1641c034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 848920863 1106 848919757 848919763
    0xa020a1202010204090e01150b0a020a060504140f0606030606040c030b060a030516050415030504050a02150c1e031602011211090a061107170a0c0b0c 66
    0x8050020455010f4014100b503a0810700c2c10800512840011400d031604110014038102851400340880d660381002000c1003901d0b40102d4010400c540e8600c422110205c40c06d482401030b0100f6092444d1090094000300110f000041034181400c0c0b00103502c03400b010700010311076541c0b80000100240039800103807440300001c0a40da110700f00e02d2000760181404a0710300c2005800800c49405840c01f9006440c01c0c1c40200300f15041803580004260001e1001800070707940ca1144185002c01603413801d520341c2c0c1601d10b44040175200c0340e5030302501c4d02d0490034240c02a50314949841030b1106c0d41002040d14145d0610540e8001800c540e8001a070b41c1d00748010032401d40c103080818011070600000300170b00c0420001d4840142c59503640404a619010245a0003402d030010b4000704406000051620b40074405d01054078a001e03800d50320120100741d250302c841c0d80c058001c1080d1011503801c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 848741007 848920863 := by
  have h0 := BRFrame.cov_init 848741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 848741007 ≤ n) (h2 : n < 848920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
