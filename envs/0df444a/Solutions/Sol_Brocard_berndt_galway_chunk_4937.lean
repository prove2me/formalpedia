-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4937
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:13:05.925685+00:00
-- url     : https://prove2.me/submissions/852241da-c506-4473-b018-b7925730e267

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 887769784 ≤ n < 887949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 887771034 1250 887769784 887769791
    0x52502010918020705060606070f080c0c06070623151903140703051014040b2509090510052d060d02030105041802280e011511070b0d02090315010306 66
    0x1350b04000d86048006443c50b8807411041001c000003c0140710b0205920390701562468443d40440d0f40300b410a0707408511590098000201642000010b45c010348254134240501251003001ca100c80e40608000c03125201800107040b56a10b840c0fa0038083d01040c50341c01414160119265030b00c55205842008002c40154015802402041000e100004003059041c500700054034500030f412101c0300740680040e0010b420400071948034130700e000150b4070303065500f43d0038809041040001040882d00e0f10681001900d040042290000c2c141e0340f0208840009120892034442040c0070312091241040c1c0650818015407030008a071500800f508084d510503900580765803401041c001550844440c80080c00320801b0040b0040e030790000b07003e20612081c6601141584001e089043c1030300240c02c0120705543c0c8800004104096440843c04e045850380e81e189000351050301c2c03582e104018028000490303400d028001018510342e0107803003800c0000302164501841c22000c515444e400703800c241c446c2600e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 887772284 1250 887771034 887771047
    0x3110f340312080a150b28080106030c0e0303040303140403051207022707031107060e07050a0608010605160809121e0c01020a080306010915120c05250201091802 71
    0x4004485a034031030702e1044c1c14000501c1d10101e0038410801c5000e140b082c810b0100340d1524122107607c48421a900c0c801c0746c0c400c041e003624400390084000b48900000242010400c059040c81030030744813003003040940154203090540e9420340f24080786404080d0703071000c18000000455030421490781c0a15800426030342c0d81d2082e00512000c0e80c0700b800d4100c21a400c5021b968000e451244602e03522211a15000400d0841c4030282a07841c400e011014104508014548e0090000402c291003151310840f01070780481d90b101c1080c2c4a041092203540007084090020303008810700381070f05c406c88c3c40c4500311031403030010102d00040c1203926141090f00e00c6d0384002c0c1c0c1c2c620885520100962502201d06c02010000c00380720000390749040914004040c4503001c004118903901450300b81000c0c01c04003a8021080d001e280c00240110240410140c509081041d4100c24030700440880e0781103017802c0d200d42c0f40302428500c06008500c1c0301c0c40480c104441c03410000741d05003034107109141c06e40074054096070f03546 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 887773534 1250 887772284 887772287
    0xf07061809050402030312100f0801020301050315090604030e030a0609060209040c02120405010c060b120307050c0109030b0126030408071a09030c010c15051303110f340312 76
    0x4039500801181c034900814040036076000000e440c540f415aa50442082c0e4600c0000c981c1c0412aa01c01010f2480d403841c00b181d0740c003041d006907058603019000c9480031000b0041c8448444415554010346800c028040790100380300b1111164601d6000d0122039503041030b591404211100e11509444440c0e004c50021500d141a005902c3c00c011644010b140320b0030740d80c80f00c4d81c13380300f503205031414014a40030840c00c21890380c0201080d0f50b0003d00741150303100f950100c55100c2d032001c00221000d004003160810300c4d600811102c019690814850000c3c1d83c00c146a40201c161503820ba01c1c03500300780c94040c9076404400c20060004d4001403015245640c5001d08450490708088000e0a000c442805001c240c0d03100010707020550002460800000115428000c4440e00140c011551980c200002c0080024107450040300d00c500c032fa40c0341240c1e0f00c41254265203800c0782d000040005d8016488240c1012448413550400c0a010b04018681d0300b0b8800c00802c15000580c4200c3c4c0c0c020540e090320034000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 887774784 1250 887773534 887773577
    0x201090f11030c012d110f060106090608090705092212090b03011802091203040602060f01120c030204020a0905090f0603010c2a1703070c021306030b0610020f0706 72
    0x40e80a0804594603080441c1080c840b030031079600402c040080e000103014a82c80740180d54012110041558191f12a5030840e5813101805d01454001ca03039020000518103109030800d5129108000c050300e2042e00f080f0401841501c00b80020082041f070740349203181d22401d08400540383d84101c202031009000d10790b02401010380e40d07000d181500f5050004111b0012000c2068090500305c01e801a6135240d8503000801d40482404d103d60f65110210700030583c2600003410501910b071800c10002c0b26a80c40400403540019010000e00004910200304018246030b000b0304012030241c200940400c0c0c403840854101030045403c4040d29002d0028009141028801c4000700219031400494000083c440c50300f64a045551051082102030788540030f01501110300c6406105541105036a41001c403801041c400e55000180d104080491003802c0c500600d1055404807a84603881350310954400d01041041c21001003803001b54094142c9803449007109105a2000d41002e4981c0b404851a8542c0040311 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 887776034 1250 887774784 887774803
    0xb12060111010207150c051c0c2309130b10021507030203130b0402030715050319020412021c050d170603010b301c021203250201090f1103 61
    0x1d41e44104990004a101003144090101c0d215030003165440c0200011204e5103d0440c00035890016100345421900080e081000014410364880f0520b160f0494445422020701850310b08200c0100084445420f0050040540c2200c20000003480c1001c100441e156241c0d0342241401a00050b00040808600000168005680d0300d011400c42c03411200040c05400041c101902d1810f60100090440d901040310303001074440f001c45007680440c807101c0603006800030794000d0300d035200d1951081004a40340c4241c0c0d044814100c03444812840039020300845841c86074000782d00c0302d030580d0000c2c0403807070802503013841e0325183c4d40d420105915080082d51054000d000c0d41d01c203074108101d8012035610212020f200c80b5510001d00d0344500f0105c0c0e680d406841f8540d20301200e019001d6060f1a1200700c1d1794485d090300d015003d48452100c8204840300c42d100488a46941164218034038511541e2104410866500f078000056940e20320b4030390540c15040e10200b11b0b9041064550030546040074480d1420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 887777284 1250 887776034 887776067
    0xa090605030105180705090a0221041104090b07120e06010e0609010e060f0f01021507020606030f030c060129030103110a06030b0108060f04110403150606082e0b120601 74
    0x4c0d0007044154068494666120320b52052103000b0204496a42c1c550440c0c1c148040900480001c0442ca880e6130545c50781140c0c141c2c0c9501e605e64808000742001c0c014035a0b4150f121141e201280c0d240705080d40d003000e01c194a03601196a903d11909508400c01525001c0c1181c1a6021f02a03d001b0302006081d4070147c000ea200f00b12150180080c94542041184500c601180e04080f90004240102d00e0002640074101d5031700d03594020301558030b8020a81601504086d806e503002c03d4071a03850203640748140c844020059114030700411165006404500c04000d00d40008a05403c1c4100c100302036400a0700282d8803500250340380241e030310303021801200610281c102401403500c44400a0038900d0018021030040107095020b500681d21a0300290204058039465900c42c2d840b03051031400400c0591010341020701e803000110344680201030a52250281d80401e40404103100c1204088800407c04103280d922100c502041080c500c0d40038206c501e51800002c403552030004001040c4a540388100780 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 887778534 1250 887777284 887777311
    0xa0e0105250e2b0b0903090a0e070915050c0c0109030203190204111b01180f030315051c020a0e2719050304290a1d0a090605030105 58
    0x2010407806a5003421482a241090002058440c0200310480c80d140100d10444030420783c0fa00c2d00759a000c11034890280541c03500d500c80d0344c5512130542c1d07901c03e584910780d002d446220200310000000b40c1c2d165006106160043c051b9581d50b02c00113a41100c1c4111901058010641c901800750420031000007510900e46290802c2c5190046600c8000d903910112000200c183c0040c10343d01d59401c031f0a040b458405901e9660b65015840c0340304400039180030390095003080c144561506490b1162440f05400c0034000003102c405541c1a4001d00c3d03c001c83d6a0794140710703400042c40b69038000c158074803110701405c5034100490a104000040b10750f41c001c6800b6651000502c611401e41c01040703034444001e0aa9402035030490906a03240540361030b03c0400102c0e041780c410302008030101c003810032500301e44144e90720f0ac50f03102c0c881e103065a02d0075180c241140c0140320800390103109116031a03610350070812071068141040c003c0703141442983c02c5840703140c3d2107010810403030409104440d0b2040c00015000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 887779784 1250 887778534 887778571
    0x4170c1e100207050613060305130803180a02090c0304140d02250b03010f240f0c060b1201050106020c01020a0c0303050306031f0c030e03090a090507090e0a0e0105 72
    0x800001020506890052920700d6a014140c0d00801c68031015110060206450b9020703d80001e400c040c144c052075001130300303040100f13180c00728043e5041e2402d9402002e440c111f5a0702d13003a0a464400e590030414092007191000d42c050b84540c86628050004145800e999160a0602240303010082550070380d240e102c400b62001d116404104001e80079a03608802c01880503045118007601d07000d40000e40c5181001000044401542240508581010351101c43c4244681202001002e40d030040c60302066001d0079910003980f1424003450b1031440383c4d00c001210240e120214a200141401c0420300345c1d07440006001450b0104403144503c54244002d1159001e680e440c40000507051200500707110001c400f04d96643d0b000c0c4031035480f1103140c140e80d04207032201d02d42e84c4003d845480c1c00440802c1c038002c043c02107050080201c41d1070f001c025010450052a08540000400004141c1010040c00346000b04c0c208a0300300290f0f0254030b61800225045c03092100307050850724081d0004000d45900c0064 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 887781034 1250 887779784 887779819
    0x303030b060a0207270f09060608120d1d0a050115050d0c05121f02120705070809090402011e050d0e060402150c01060312030509060709050a0b09060d0204170c 70
    0x72803059500581140040c180c85080d104010301784001070100a030f0800d08151010146640401e50f550702805051140940e15005a80c03500001064518032000420902a013640b203500040603c030b605c54503681b00d40b00748103415170a0204131a01182e0070b945945582044d0365113185000003611007182c071925140d105035280608140580b24032401424400e001440d00d81d81030210802a00c56254641c0825880950794402540100c0000440e80d2084001c689007e200341c06a4170219807090383c0900d001e5040013009181100240300324100240c18801813091640b116003981c510303403140c4071140ca441140c2c1c18941610078074500c2180c89c1d80110100b0001da601c0c40f610000418803e09039030b81d1131158215440c054081d6400c0680640098080300d0703401581079200354801c4004405482603610341400413038414103140f0400f40d008581403414001d00603290001d2030420340081800b072800184107101410ba801c01d41c0b04a0040110700d0f1000010a400c1c0000d005500044403c4600110400700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 887782284 1250 887781034 887781043
    0x4090c1d06041d041b0f0e010b09010c02010c26090a1a0703050714030301030804030b091606110316061e0506180613150807060302040f091806090506010303030b060a02 74
    0x52241d034861204004c01d05200303070443c10702020203441c4800b071030003501e85202003241002d0b8441e002502c0c040c4400012120b070640180c2d030082038143d54403e240e40c1e403900110b81d03056a9150544a91841140b603c080744100030180f200b41504405031a140c54849003040304000c0f00ea8170441840c102c0d12003141407540c10008803180079a25003030154a074074840c14000589010070407244040e120000020090001480150084a10a06a0b0301c2e6907502c1c00c980313a480d20700c1c44e036012400070f502d041306019640c005c4140314414206202142d04205052043c4c03682451000c109a81300750f80e51205495001040489240602d98181e00780540c0c1048004248800d082072007051582240b00e0104040d13075030308050065561480c0006002000e951000d40032103e0a6101b9500c82d4801c42200040c404e01900a03981190a0f0102c0c843c2114940416080900000058602440481c1d28020000740e41c91140001442c01000280b03225030441c42c014044901d60010f2501c54041404540580b950015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 887783534 1250 887782284 887782319
    0x1d1b01090e270a0818040b0a0e070e0d2604060512071724010c030207330201050717160c140a1407121e03020304090c1d0604 55
    0x1882d605102c00c0707007401100850350800d99840207000d005120800c1c00b40120203032414002c14000143c40f03454040030401151016500240c03c901030070030400c600ca00308a041c42d880060341c2802000d40400c68001000c00b50b00c06000c940c0c40314542030440002c0f80d0b00d5164803581c1c4002d8a1640f900e400d2000c0940940980c0b04001c003020407450010703000c140300342715a00d901c11820000c900701e0301f000c003d03070900300100c2504c0c02e160000314801c2d00b9142d1310441c058201c25406801a0440741e040c0424404280060a0340301a04481d20401c1c2c4112440002c1c00301c0340c20915400011141880301d00140150954862410006110b80502c500100d00d42e869240600303181c20035810343c000e0381c17600524886085a50040302e0060644603014401d0540c221188041120140d80710710f03485480c80801c0040020002d80484403400002100580c05d042e8009a14002d00442c1c0c10030382d4818007070044c0c56101011000180b9488251202c15160000d071101c03c950403034140d070a040c1003510000240401d023 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 887784784 1250 887783534 887783551
    0x819060e060c070623040b060306060a0b09010e0d0c180f020403020f0906031218090f22170a09050310060e1b12090105090d02010606020a02010f031d1b01090e 70
    0x100c000d140e8030701501c49840b045602c3c3d0700501c1154505420601c01411040b1546400ae024510018016190480b0400300f0350315000120f034102a451383c011540a500081a2900020307170340814404140d80324100c4000303140490101024030420f60000d000d481858900642c554018041031006a8690b407500da0031a4043d2280740340e90f6a8034000929103400b41030284070020000500400508104000c1250070000b903c1700107854460406c0c10803140c038210fa043c4021000340c06400020442c0e03200030400030740501c1407045424188010340b0490752004c80100085100e0f0001045941014003010000c00c1c1001e908119551415080005002e0010310300f0660310410044500c40b5880d800a81b035600d1907000d881c010602e0446000c900900f41074031002594400c1e07001d4601d40502c14058101652515406412440042d500540300511f1140d8092305054403800d2041d071381daa00700b0074000d40010160081105291084c039079028124402c0c44c3c0740c1000035208050201d207518841241e00b1401c503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 887786034 1250 887784784 887784791
    0x51303030c030228022e0c0215070f0314040506010b090102071802091519030906020f070c2d0e0601020a02060d02070b1510030f060819060e060c0706 66
    0x1c00300308a0003072080103c041625200b84048000140402581a41e502d94940860b8880c6d00301c49141c0d002d45a1101440e14004010110940f5848403070700203c90384841401280c0003220741c140703090b40703500301210020001072000c52118041d41d814011107503801800031110800307040540b5032503140c41c01401080c5030301c0740002d4291816442000038100a08404000c2d00354001a1801680a58030a52a2078440c41c0c6201c035030a0b00644400c100ca400220020100d031075980010000c0c0c0c081c00700d500e0282c504507400c1c804e08007003c65940003007000c0c1d80320f000400811814260380f40110480f50041004809a411995071201500a034500c00d8495422250100d5512480100d181c0b4905a00094109201082d81c0c22031540d00d8000d01800c6108204100c16961008184141d4012211a05600c100ba103000c4850b818020350001566900d5200d003c0303000c681b20302e903841c43d100c810303403603c003480450140080c14004144076065816100f0000f038259030a01c1440980640942c0038040c1110340d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 887787284 1250 887786034 887786051
    0x1e0b040c0e1e03330601050a09032a080a0c060f1211090a030b10210204090606030803090a021801082812080a0b0301050c0319021c1b0305130303 64
    0x408002410088508205500405000d044c052401040c051003107614200d603803010a80940c01241651070301d400556030101c07024603607103030105c00302810744400b00f2a00c0701c0c050600e101c407056010000030b0107403d8010424a1000e00d00004054030301e07444034041210f54516124820b901001007039031080101804140d04a6010300e0210510404042c294080d0100400208000c030381c3c0340c0e076442420110401c602050b076503080798000d852003291403021685a1400d090051a05030b001c441981e00a520000c0e4080d203994421200c0c3c0d00544840da003507801000350204520781600e1032000343c154161404c08a51500c0c01c040c3c0d480c403c03540403034144010a03140070918030040c5612030700b041e041800506a07d2030914040e001d0030703060b9010540641048640c0350103060500910f405015141d1603d440c540d0340c3c1040710301c507090400740135000c42d400300124031800e1041e005202c3c0541041000154000601d050941100c0c203a030342d0002818240740030001072160900ca5604812703010301b804034070341c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 887788534 1250 887787284 887787289
    0x1050301120809040903030605030d02060c0403030305130501060902180607080904090f080a0305070f050712080c070803240904031b020f090f0901050a11030412031e0b040c0e1e 78
    0x22a04540c2d04070717161200203424103915070011002c50f0b00680030303684906150380c400c0340c441c50105e5807000d4180c010071080001a101e0381c01160f010b80e01490400110141d0340c1c8803805c1d9070055225221245d0041444090031014000e4255000011210f0354a8100240e99140c03550103034500041c0319540d19490b11b4107004908240c1c4104591240005503100c4441002030020402540c5450004840040511056016004484505804c2a0804c0c22b88940380c00446e846d80b0001e04422440400b0b108040004447c00040cdd4001d00011244220718480f2100400580d201d10815600c20074807001440003094124040d92449010740e40300c110040058004030f4405080030071680c0e0451001e004011402d20240401350041d0a201c009101940310100d18200780d9071800346240d0800c0081010030001402c00c1340448131170b486410041903c102d034408040d1101c0740e008049140f980c0f1040a5002440d2038420024211001e041c8803000100c408007090020200c24a114070080c2d401c0c0404503180e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 887789784 1250 887788534 887788537
    0xc120f02010f230408090d050a0302100203060f0d021c08040e0601030c080109020310150201050711030a0914121e011b050f0c010b040e0109030912120507060e01060f03020306060f010503011208 85
    0x2050241c411f0420703880301c0c40c000b075888040038021707001030007440350003403401301c15008807801010300505d0403100c9400a02048010030b1407880807030f0b00200306074085001c40c00c007086441c04a801880348584851501039902c604800007000c2c80e04140c98440c001d01c0590700000410705482400d030b40141c680d81c81c1521a0301c9003001d500100b0007200c2c60030700c01034030560540009101d010a0350702c0e21101e20006400f1645d900a03032101c10081203c8400074002c54401d000c42d8441c146008046400d440c091801050522010b10310200f40c0b548490481d03070380c44009003d034a0b10180404d10b664209d19104100600078050840910b07880304000410040100e000d400c01309445100620070030100b030078001800c2c000c1c4462002200070841803003000801400816a04140f140c02c051074201c07481004070b0440341680406400c41c0c80d070303548010a01505000b4421540981001100805c046055004240c50810010500f91155400030390b200c0050f41d205056904448500c590071100941c9890807018a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 887791034 1250 887789784 887789797
    0x50d032028050d0f020c19022d040608010509210f090d02040e061009050105180403020a05060718080615130204050622050102060106020c010e010c120f02010f230408 73
    0x2803c00204444d0076040d640240b0400610b0011a128680302c031011141503000103401a52040030369003144076107001c2d841034041d0561054100404c603840c40001400302c030502e0300b00309c0c040d82d035076000c110600c40c04108400c813015401600c0c00503c500403040ca0030907c9038805052140ca000702d4002419261030810b81c000550041041c4034003201c400d10140d0303075481111802c401c80c80a40d40001d1541c014414207040e6040500070060500c0701603048000c2d46000b400032421841204180e1000c18024071004dc01004103030342c0c2181480762019a0143c3d484603401404850300100203200b1075204480c0c64945241c000d81d8002200c400d0300c14110b0090085034003858222000082da040000b207140141c3c1092007204146150407a111801203075114400d000c0c1e5400340e40b20700e12452103980218080c200c0d4240514200303104429980d5956885c95034001c002021a608103041d05e40a9021f009410015500c00801c10644e01809041d8115020411a001a081e0383e03c0210f002d002c01a81181c02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 887792284 1250 887791034 887791057
    0xc0507080c06060a0b070c0905100302060408030409050a06150c03050d0e0717010b01021b0f04020406020a050706141b01060801020301060513360603050d03202805 72
    0x300d6128208006803156000c036200391040541c0300c4c004c00c2d504555410358842c00d80100c030b0342001a080c2080b00000b80f802a10140520418810000050362000300074006480c0d0b4034040c6403941e00c0e0451b0a4203170750300602700204a07810800d0601c80e91845911040768440039103045010304400303040558051140c610310201d140d0070008044d4500c68000303030140454540300000d500480c605050705080351a01404140160000b07144003200c41d403075000840c16214001c10455607640000001002c0360310590241c40036802400d43e40b001d2010500584000344a2814030303007611401000348520a2065043c4010612103440b0104c10382c50003580072801826221000310754958413060003401c0794006071010284240d11a1010907085d03041007681c5143c0c580c100b11390511400004103211720301c6400c90302e035601da6542d40e800000b1038000c00c50082005519140010715000c050554a045090682e40c0e05240900b040b00002d2807426410840f01203040f08101004000620012601807152104002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 887793534 1250 887792284 887792287
    0xb0105152a0706180b12062e0306061205061003020a0215040f02122e15060e3613080403060501060f0315091505040906060f0806090703060c050708 65
    0x355194008000f420310413180545a0442d43d504d4040700d4591080c00341d410a00d4402001044d01814420009480300d2402c9610240070060000098081e4643c0900040081e0f1522010012142c11002d50183e4030401c0d0400d20061810002158071002180244801c141c0d0002d40800114030910080d00d143c3d4a51000344010306140c209600c09074049202a80f1a0340540890120010f000940c09009290076038010218180038407541040003e280d4a04c1d183c40d02e030380c1180709521443d00b0038400b802e110b44075209100c00c60000d02100010882565010712050210814800c5940a0316248140b2000d0360001c91341c0d90f100c108000581c0740000504c400c0010501004020f1342c1c2d045541030f189642c1e06c0540540c2d0011003103060b54400c03036142c41d084180b00010711105074207411070408044450354801c4001d86d40c41c003050407501e88070b0050310829500c801c2031101900b81e182a100620301c407001032402d400c1081d13091b0f407a40b0b25444014800d03a924040703141e0b00e900880640b0480c2d5000035096 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 887794784 1250 887793534 887793539
    0xe010f021b2d031507020a03050d060e07030e1006030b0402061b0604050c0f0d0305070605071b150f060612090c031a07030506150d0e0c06040f030b0105152a07 70
    0x3485042042ca40c00d2080c010081008a06424500b007144501c55940c006c164690158a0682c1c1c05c0d40132040f1031400580354513011440d1058014514041d124a0380e001890f41c0b50003000c2410020201c030801c24141c204403003080032555110070660410b03012100d40760703210b100b250ba079a1107540319a022145802030b6001c010512002080005032a08103460340c00c026441d5000300100300004502c02404940c00b8030480300400c1c0740e81c0c0724030f80c0b02c0345a04242d2000502252070781608000c111080300c4c212175a0500038a0103180d40500c0000d80b010b100c09205440c11b041c4003501030307241c405134881c00075542c0c00d0000a00902c0401840256044004556003a00420944030b00c038008030b0744403000c2814180801c84908100c080c0700070700100c1d200c80c00d08042c03040c0324a0000d411040c04012582c400c280300c4c0922550b071000284001e100c02d4002c00c100307a14510301001c6004050b8040c910031086800e02da080e000300401141c3d01850050400041c017405400c0e603401203544280c15500c14072966002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 887796034 1250 887794784 887794849
    0x418020909070221160f020d06150303120b0906010c08250b09210a1e090317030106020a171309060603110f0702011b05011b0e010f021b 60
    0x405902c0c038200481d942540e500c1c4800d0302c801d889200c2508240c45003007509800420342008106c0001440104100c91036482a10b03030100b034a400a4405c04211041b03401003007095003010040703000081000c0280240604000081c0411038010207550500803255200c03010010040211107503407030f42d0401002e441c04c1303050010240701d020b0002211000203d60104502100c0024200000000e24910340196035403281501c410ba0080d03403040c0c0500c003000080d00b1516078491049801916190340e501006461800c4c421407001084004034101041080180302c40f0350b0100d86007078130070380000c0c082c001d4428808011150f4443c040104c2c055070300700f01020070050182e0300312400301c3d151a60103100c15100806903882501c10592010301c44035040025100550154180100d45101e80401803405000c64544509454040340401004007c0c0800300620300e400c04000d0203080000c6c07a206210144184020b952050382d001c2240068403141d0300403100750b54030f9440212110b0310520450080b40c00005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 887797284 1250 887796034 887796043
    0x601140c030309070312021c11100f0e011b0f0804030e03100b0a1e05040e0f1903170c0d0b0f0d0f0c05060c03040303030e03161112070b04180209090702 67
    0x811038004000e251000005403001800c04140311001d0b14603010310790108e0017560005955210740f0014041d1080740185026140706d44040c107280c0300008502500300781c01c010708440c0d154000090224044039400039055100056500d0801c490500f60215200d505082c2c41115400403903070342c50300c03403c0d801c83c84980050b00240480780701034039a160200e85480108013650404102140c2d040582c03071007000315240c590491400300126a0542e80d40d444498505410b11800b40154503072002021241001c050f070081180c0c40740c0100003034011650070705201003101885000b07805a0f070304c0c0e140c14844040303a4420281c80c0f0042002040c00e8000c03041c0e4a4415583e48510344140c481000c070500000b211309081007100c0990081401031494681183e9050740100159213108000384818007066540e0b25480321010796141c001e020100004201004003c00c21004281880740c40d04112410090b20b0444000d0710143c404440e18880c540d496906000c000b4015202c0041c1e10000c840c0921400e42d1b004034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 887798534 1250 887797284 887797289
    0x801060e031e0d1e0f0c0609060c08150405010303120f06050a1503050c0c1f0f050c072618010c020a030c1802040803030a0207060e06010b0c0c040509060601140c03030907 75
    0x864058005002c04c1c0c04110180041c0384080200d00c0c108071110400780300302e0308954401d100341c40002e418132050715040102d8488511800101e0240014800d20740c00b17050012900041c200c90a200039811650018030703000f082e054241c0c001c2d032108148210403d01da0425009018003600c030744c0350700d99105490b400014558844001192501c400300341718821600c21103c034807880800816141010842d5040c0c0d120f00c001d0380c15241a80c6105108035035403140a140d0180216000450f151031071b0b0b00389070040241546c01c3d0b4021340a44480460702200000039105244681014429014100c6005890805480c1c000a610104001c00071080014014289050360890140c3c01104e600e400c0c0c0704022485580281c2255600500000d11554126001040349a03c00c0401050142c41000e806183c00820303048080b034030102080511102c20300700b040349a4140c0844d014000360824038800c0f030711040c000c3d000030304000d0320411180801d1200000c585062a480045940d60719001da8400d03151040750 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 887799784 1250 887798534 887798537
    0x3100218030106120f1703091605010203120103020616020402070602071b1208030a24060e150d270b0103032d2f0309040605040c0801060e031e0d 64
    0x1103502828101441804240c03034900308402d44020560300c41180d2070980100c11111410030350004540d040c03010f409107004600703150027050060140d940e45810b44900e500030904560050025001c0010340c00c140604494040d1a6141d90341050258030400c4103a01d0030194200c3e000040d51410030400c3d90041201ea800303518802d40000301d098101c81c490050380315100ba540040c003d404041443d01c401103402050002001449107084501060030226107184c84660a0380d0318130030400c0f1604170311080382007130080361024000808440b9100c41d900a40a007020305594070313111041000c40d9110001d030f00b40c1c400402032418610600c0c0c11181c4020034007007180040d1a000300c0ca08040d00f005401e0310010002102e4003c1640401001c80d840640b0341c2100da003042c0c840000100890280702e801e030920064001465071800d4000500003903842c2e0781e020034041d40c64075690f02000780e40090444e0644030107180245002c0b50440010346000c40d0301d000c4980c60036240c0e401c1d00c50a0710009000700180d026 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 887801034 1250 887799784 887799817
    0x120b04020f040b01140a0c29060108070c0f020f0406080a030e06030c03010623030705120108030711090a0f051939140307020d120902030a020904050c031002 69
    0x180060105540c3c10340d01050100700340c8400d10080c91580d02c094000c045035442c1203240c112141d25216200a0303100d51036000b1101c02c0d80390151400810f80704d194028420308200c2494148840010203000003c03002401c0801d41c80c1c0008115070318126000c0001600420a00c1504e031505c56103600c518842904901003004c00b000343d010341c00d03c0010749200340003204000d8216840c01c10309407034103811400b45111080d0070810201c104c0124101450040e0a0350b61440d4640710403c401190250043e0850303c0280e100740541c0700000c468030f01c120400364080e5403002503511120100805080c07944051301c0710505000c00c1241480e102520501810302c0c0850a0000306030240418140f05a070f0b124643c00340c40c09030041070094480d405650f02841d031070b00d8801c054420300140248244c0041d51500c00680104c0c109074045544110400d1701440c1c10441040400801d900003170303484540060080c01400c0b2500003e090007000d01c050488101c0c0a401ea030400b03040004071800a501441900800e80344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 887802284 1250 887801034 887801059
    0x1c02070f081614040912020303010501110604020901030809060c0d0c0605010902070507032a0305010605010207170d1808030a0f0801140117180703110112050c030a0c0306120b0402 79
    0x1500212602040d411402c540b03007050072160840c2c02ca03000c05600141c940740d07500005003407184e02002140304c9901545d100d50421000609406142541c1d2045500c0b2105220143c1e84881c031150440e03900c01c60441c3d40b9025403020544901440181400300d00580031154030076900b040410350030b01c0c445c0a0401a0341e8035100031008a00503407a029100d544043c405000040301400e43d031140c1080940800c3e000c0103070915010311105160000c4440b03035101d00007004103503010045c01014090000100e01d0540340700c40800d55070036040580d0305c00c000555400d20070001043c1640805800c04005882c0c0d1080000030241200c1240c010a4001914140000884681524060030f18420596070800c501840c02e0b204900c541010740814142d105641035400580c000300801d0300154801e1018807840315039100050100c5081c8000c060b00c8900b00801c01038405d4403d021607034440b400c142d00080071a081c206c200c00401036504541c04114070b40e46814140419182d40758030880c400ca42001e803418 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 887803534 1250 887802284 887802299
    0x30b0a0c030504030e01080c040b040b07020a05010c0317060f0a030506070f0f0212091f02061b040608191b090503070503011401030b13170711010c11121c02070f 71
    0x2c404075030144c0050319407494001558420400b0b15044204900e24500b030540f16030b0b02c81c030540e00560108412150000c0c4142c11400e150300c4030002440c0c09d003058a08200c00b07032405080a02c1d0300302e0088203604080000b4146540e041155122610054040303204540c81c0e103826075407150147d45200108042e24074420400d44181500126910154080c1180b14002c0003881000d420a80b401644141c240c0031400c410852010421b960b690070758018241c0b82406c8034400d851843c031043c2c920460504120610410786c000c0500d9030485500030411955450445480300107201c0e0401c41d01d002140b40691a400c02d80c800011400da800c00c500b611582a6503408160882c0d0040c4807504130180344000403c0800d021320303d103035404411106508401123040d910781e10103218421415a20303000c04104a000c0c000182c1390841c1c480c0702802c0c680c1440b0030303a4441d51405609403941510032200340f03031243c170801018011580260703002d2801d61800c02d0803030000380d00c941c060f00a036291444480d40005120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 887804784 1250 887803534 887803541
    0xe15180402060a030e01020d0e03040312030e0606150c0a2001020604150b01050d111e0703020715020316080a020124050f012a20031002090409020a030b0a0c03 70
    0x50381e0040040785400011003042d800b83c102ca9054185c1d40d5400c0c05013440c2078040c0d0240f0301c1800c2c0384101a6580301d05501d0f00c10b26224030300ca4288101858440d0705016032030001003040e0800c1d0200d03007251082c2d0a00044113420303c43d0344442c1195005142c00f90007040501c101c46901d071402c000440100b005030200480c0e4171703402214060810b02420000c0e102c0394081c0c1d880101540d030189443e61505030300783c0c4940141e0304800144030102c000040c00d094504032507c00d00c41503031200c80b002e07890a51030703072002903840046010b54060840c2420503520594000c000300d031700d28102400401184500c900b440ca8840c1c10040c6000050b50a1412107030105100d00e26041a0140141c120345101c3d00340024018003010340e210300b906000840c0c01e8000000890603080703000f50446032030158100814507000c080365401c1c0c075140070700031541502600079550110f501e443d40c000ca00401070711000d1540000d8080c20000d40c1c080e41082d1104008401d00c08122101c42c0f0030710103003c1c14440c144003a60120101c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 887806034 1250 887804784 887804791
    0xe04021c0c15050a0c061505061c15031a06011e052208120c01060905131109100605130e010803030f070f0f050724090b060a0605041206060e1518 64
    0x10f112411405c00049036680200310307005500048030200740d21100407a1442d402105c0b62200003442c940c2041070104d05010340440401441c400c0f03c521403843e0745407940a01c0d40030402c4000c40000740000c07404c0c5d1040d1016068a14001542d41d13500d6502c2d100071784168000052521070070000740c0789020072040c1908100444850400900a0440803442150744c1e400481c0900025500c034040007906c0803441c003e80d40901c400c440e640c50484100e00d091602c911842e12480d02501d503141c10480c51001046904046a1140c02e0140c1e841c1740c601503184075600300d83c00c0040311140c140b0011a10382d800101075803203010b0952008080fa140c20b00141c1382008552104000513102c840411446070ec5a4094900580300d05081d001420302038803807280e1065103211480c52181da408501c018007000c107842036040102035500c00d10359070800c04014240d11450081c54010043d99505408004640e1b011034010142d0901c40f14041c105500030543c59104119054484c1c400c440c0e0404080320207032a070f41d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 887807284 1250 887806034 887806037
    0x51015091815020c06181e0309010f020c0901060f18081c0314010b090114040e04060c110307080409050c09090a0b0d0c18060f0b040e04021c0c15050a 66
    0x85800e06680c8011500d10459514186070380c0a006a135480042004001e014215011104c0304100200b05614030b030003090184d0524080240164032140003000c41200d48040013803074101650141c900080e443c1c81142c201b1150802c203200000641c2c141d2100c0040031441c0182c1d1161201c2407030380881c0250301c10b54011000d00b504081542e51107680242000c0040701203509000ca01d014445c11400c4030202e00340c0c4481c42980f00042c3d031040795070340101c00794003031100101103900345030030940780091031080207000408035a554400050781038051000760178440c280308212507403400a80307040c4d03280350410f204e1107031264140004038046a6030b0900b55072071101e01904403462a0344607203610000d07048070405203400075100101396012400390100c05002d40490f0816070000ca144100c00e1045030380035404400110707200b100078440e1090810446d07040b5011301c17600b03400c030f51035600000310140d000b04e03220f15072060980c5d0f0f00300130000d10340014002c035050300d43c016100c1c4003800350940d40d520441c8181c20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 887808534 1250 887807284 887807321
    0x105070809280c09090c03021513051c051204150e03030306011202160501090218010b04060f05280e03010515150d15090509070e1602010905101509 65
    0xb850480c000e2400b603180514030302040303030313a9480721841180d508070300913030721400e46900c18401d50034000301e40141d07442d07a0f40a642c5001c1c00d46101456000c0c1c04d00986104800b4610f4609100500405091006801c0415078003990004004040c40740d006100343e0054600002031105414000c60a8555001020b00590b26580c0c8600044649030a170418411010707030300b40156110322801c20218684217220b04d00006099005004200104080989040c1d00392034032801400000b29000684085800340e0500c0c15a43d6031103401a101406004000d000800c0c1c1d00c0c014030a64801c2d030004d030755980c0345516515181a12041850f090f00c40486003405500342d40601000c440c1855002801002120b00c00d240c180580528000d0030f482030810002c040c045512024002c841c040d1081e107401040d100300500b410303403030301c0c0b070720003240c00b0051541109480d4000d0020900d4000e40250403403607400000d41c3c4c030b2580f0b01c9403000300520311070552001035419000086000d09076440350990b070840d543e0004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 887809784 1250 887808534 887808583
    0x1005030a0e15101a0405030c010c053c010c1e0306090f06080609010c0e060304020316031b0b0906090409050712060c12090f0212070b0c0105070809 65
    0x80014008801c0075000c80d02c074902940c101c1c42c48018180f03009842d10402420800e242140d007034020500389000040b6020200300400141d40c000416906018080c2004659841d41e0b08005052a004610750f01009030345818000a04856604001002445001741841208840340351400c0f80c41020014020640d4410400000c41f00750f090100c0a480c0d51401054450b11b40320400250380c070725556003604d952241d038244091507081c008035600c04c40910007004215020030006140b180c1d202007ca00449000010800b551024042c040380e2410540c41803d01c26683d00e000d000c184651241610407105948003c12005015000c4a05403030b401020103007010714140801008040d201c1d411240303840354000025040c40c88240000c851800340303400260403004034502407e844540700c04403c040e464092800c000421030020170035050740648038044006403000d01ca41c84c20031540c011442e204000f08411542c80c405400840c400d280303d80c1d60f0100787e2910078040741d982c0c00600b001d00f200200c98018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 887811034 1250 887809784 887809801
    0x80402090402010809071e03061409070905040807050a030f0207060e4903080601030203011214071a040302040c0f140f090a0e1b03010f0314120a080f06100503 70
    0x1d07a81c208104400741d40c1007c2c0c2c0c0e5800400f540b400384c0b90038a02e840300d2040c10403d001e1644503e1400452180c002d03003891410070400e44c2c66480303a001d9071703890550303d0012905128200341138a6410303601108680d407290860070007034913a41039034030000c00500c201d404c0482c520344112003c400c03418000e0554401d855400b142003155464202c4500d05084d005c80c540307418101c0008030301c198214042422a0540828200200120002443c1605040c010401044284442d00c0d8208400c1c0e04104041c103940903201e14542012040e5100844944400030500e01e0a10002c0050080340e200f141e04114014a24034184c41200203c6001401305010480040081c060f0100805c0074550a500007450000d82400103540f0441079049980850408410800c0d1200000e0444070440c5440503003a00395850118109148032490000800785580794102d983e100004001c51400111051020740d100c03d44e454009013800c000b00c600d05a49596070010850504143c8804a50007415682301031a65075907020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 887812284 1250 887811034 887811047
    0x4060311040e3d05010b19080105090c0a1404231806240a053a09030201140c0a080a0e07150c120504080f07050609040b060f0d0903080708040209040201 67
    0x203501220a00b250311000708690343d032007010301030211000b546895401030000700950325075580b61038042c031035141d006102d165101c0780c00952207842003501660380c0001a504550491203100452001d540c040380104042c007440c0342c0c0d49400d40d00c0c01455029074800c8002c00c116039201c03400d00103108640901244031030a0100800c0a021510019880c107804000e810a14942c40504540b00140012801441d045800c81c0004091030000d501064910400100c55207058a1414408801030703a5248000400d4001c0d0482c403610319099888561924145c150f02c040e43e40507003214030002c2c10103400220a10820300c202410b414010005001840c10b1050821100101c0c684202c248044007000707800050340350242602100302e9a4409848070b24202c0a03d25090100316803514607040b00c00700340301c0341e2645d1044e900c1020040320301048103d005d0001c02c280d882054203110041d000000d02004c52740e0350346c200d20a00d500c6a40c40745030036130301c991040301e002c0000c0c0c88c020760020004002c40c026603c1284c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 887813534 1250 887812284 887812363
    0xe0a030f0f170a02011505220c0e09090309010314040c03150f0504050c01080c070506150a1814060405040b04060903050d0f140705040305150a090204060311040e 71
    0x10340c2c48440c2d611106032140d03800450303507000140c0d11805d03903001810308441d03114002c2105440104003804041c4816009005454007420707090768841600115074480c554880c0030442c003070800c0c40d40e4100a0b02c80340c0c4a41c08003030311a022900b44100d200c0001101b191541c80b483d000344c201d45400b0308580d2111520700c1007a4550f8030f89526643c011200c00c029100320350040e4458401025407048910025040810060003030704080c1044c8170802c08124040360860340002000d6044940d442c1c6140011400c000541046138030780c92111381c010a000312a804017554480000c0c0c032250300d51b18141040181c1c0d8045400920079114200840c001400e1904194225032082c2012420102e400e25100111003450031001e96136a01c40300180440c0051424030398121075985010740c5018251f44849684940343d44200e40707514440000900081040ea0002c038a46600504c02e10070f0558904000e11101007484445205515000c0d03500b06440000842a062408494031400c42c03440c4d0583c840d8a0134841c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 887814784 1250 887813534 887813543
    0xe1b030403030f0b06030c130e0c1b070e070207030b0a06060f0f0c08031306051b040509040f051b0906030c0a0902071506060804140a050601031e1a070e0a030f0f 71
    0x2c200744415640d174a000f840c40788400c000417a84400070240d900b0440b036010750100b05825100c005100109070f4103402c031079103c0c2892006050140c100e8519a260030351540c01100c0c411102020b10900681c041050400c03a07005040ca40c40d0754071400c400000f1940f02c5e10888010a01100c090005d15002d03203020408403c0c1800c11190089240c0c4500c0e180c0c0e0b100300c41d07541c4c044c040c01015108006161041d5900407080c00c1e08102742c0d0350ba914594040c3d21890003011b02c24014100010100988404060300703180d400710503500f50036400501181c4102100c1c1003107120300c0c000070008446041c0010060781100700100704030340c5c41c1d14000c4c14500075030080c0000d40c0c8d801194007c21525000b6409044021700060359028801d1078141801c030301c00d00c0b5122110300d00f9084105464081000003030202e055940082142025044058a0f140d03442561640107081c81c080c5685e542d44440d44407451781c4a01660340310840000a031000f003001040c10740c00020300c6100458400000f140307030001d18047c420311a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 887816034 1250 887814784 887814791
    0x62505070312020c0f0d020706030605061b07030614070801080c01120b04060308041509121a130209040f0c06030207081b190b1b04050d11030c190e1b030403030f 71
    0x80844e5810204101c01095156110303541032440f040d4104210310080c50185000c02c11a410b14001031040d12512402c9603100f041084494010340c0e06019000c002c50744604200540044281c610303807803110844000c004114050700003e80388a0208150601110507920400b5056041001c140100300d030b421090f030010798030b00000c030010f50302000800c050011132401080c40f80080c50000c144034a19084003a00c8244841d41600040c110030b080c03d10300c1850380f2842515515500c001094065641c40030754484001d5081c031080c440d0201d400040715001300c41c085150b6031280300650070b900c5443c4c401842110308002030b4100d1071124500c801b801c050902074840e01d0038242200325810f000c003c2d080d600b4215840c1440b012070700c2d03400041a685206280c040c2014600f0000802d02d061414001d040f01c10302601a000a550501c4100300c20b8100401046c620300d88400810003d00c4079010303c08402d44204042040304103005540010084c580745400e1075a580c541d0200d0240440c42c024140751502c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 887817284 1250 887816034 887816047
    0x60409110307090906060803041805040f0c0e0402030c060a02250f0e09012a05090406050402040602030405031006030209010317251208010302012a0c0806250507031202 74
    0x1400e20840c002002602004078132440241842d20849005030301c070b07864a03841004100242d2210030800e108038100361000007403070790701c13130404c1d442c03028cc00c0100800b1742c2d0300d0f846c0200d400c111003640940114000d908691400460301c0030712a6510402d440b0001691203c0c000d01c0c000325400d03108801c00040c05604100d13160b43c1d080c0713034042030550b130b002604540d00d00c1c820000c2d1150244580b101d14600e100b924546c1101c401d84030a00d0307402d442030308010400e0016511200c1d440e180c112400400d0042d01c1159590f40c1ca440017522500180200ea100f4095021561030007100c90081600741e91700100300741003607483e40c0d40d03181e44400646424241c800d81480300c1e1240d8400b90f08815685001c0c69090000e080003440c00b24026000c0d490250300303104600006102503681300c49201d4600804002d2a004481d000103c103603040b2000340010100d180251010800020100c0c0590089c44411015860800690300c3c00d00010301c889441170001e242409900c0200e44205690504007031000001840c108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 887818534 1250 887817284 887817289
    0x1809150b1207080c040303211d0705010e010513120f060219080a0c090b0d020c19020a051f0c141e100b0604050f0a050306040f020a1401020606040911 66
    0x1080300c0031900030502441e04120005411020702c60740004489540c038502801e55502600e103442c000680d800710340040240c82d0038020198400f07150b110f000204a403084c030008400590314140d40c011680001d4404050f401d542d400b9030259040b00500d0021911281d0910030b0318540306120020940e00803441e0011300000c0765980c80200415600f9280e0100521405080604401d60203820040c14500d4991311006055000148505682c5504070056a4980550804003c2c3c0142203228407113001c4d41ca8003d8500c0f0280144a0100d4801d030b4110b01c3c0e6582e1103041110681c04505181442c0c1c820503441a2a24031800c0400708491042030100281c1c0242c0580610b89252000111243c1140110344040000c0400002c1d0040740c5605043c002e905140c00400c49074003852060340c1c02500c200368200c40a40e90b251008018200280441e8051320306400c05003041000000141d026000b03144022a4401c0c0944030003954841c1a001804507440b4002030000a01400405642810901c01480c3c0240d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 887819784 1250 887818534 887818537
    0x5030d0911190504060e0402030307030f020c060d020c101103310807140c01020a0803060d06140711070e1932101401080c0d020f04090c1809150b 64
    0x2c9000380b075459081c00e10007404121411604200074007181c80c010000165400400c03190f00591600e070a000e5268400400c0e4580104000700035440714020540003111200c550180001044070800c845146001301104801c03100c2c0901108490300013000050700e84000f208841c1000800f6040c0c10a0401080e11038007603020040804076041d55000812109000c00c0000c680070941049000e06420118000083c0d51108224401444203a010000880e42d9135590014013580342c10601c18000c030901044c0e40c0c403415200320307200350108041004c1545140c100203030b24010b80d0340c0003c60711107903100d085401ca031084681034414489500e03012500c3d9142085440400240c0c4003140403d00392040c0c0c3e42e0b072440301900130018112409146020011a10300004059400c002801c2c01d081c107880703026030354181d031048101031212203000080c0c4007c042040c400074822161218810048418250300840e42011291440d0a001920360f8040c04060595840b00f000c100003200e1801d041c0303550702401c5869 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 887821034 1250 887819784 887819809
    0x90504060e0105030c011d0f010e040501030f03021c1409030f07060302042c01030206070206070b10090f0c0905130209042c0d021023090703050f0a05030d0911 70
    0x61140707000041080d41020403840e20002002d08004802e0050a0804565480301d0300c00d4911907140411101c1440e40035444800c03030b52201400901456850742410601004c04030811001841568000f490400e480c00401320300358400e40e04c0f003011040d415109010b9800180301c00f6803600034024014100c0750100300c01070040c840e6031805601d4a1401100b03c01c4031742c0401c0d4001e6807180c0c03005c2c040c0d4408007416817141580e80c11110262131b244c09001040150140c003070024510403a04042c05000c08919051008035a5001414002c08030100c860000b80c03905109018041042c400043c4800d1401003100b044c0b150391080c00508003481180000c003902c00138241c10000c008a5410211f082058a070800421507151000b0300003003d01c003034001d40d11984042004e904607924800710506500510204e00c240e150307400300300c07054201000b169403145164401200c0c00d10408a03545052903010480802c803070380040c095414030440402135006007400d800110340013441c005030040c0d0382d40c0f0041c04411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 887822284 1250 887821034 887821049
    0x315060d2309030702010c02150f0a0215101203080402041112180601050d0609020f041b080a0507270b070f0c120c032301180515040302071509050406 66
    0x14114205110100310403014100080743c0e0800c0050102503604403d800d02c03182e5040c0c0f44107800f580c0e17000b03c56039240a500003040b040f00c000280a2502a800180b000c030766481031108500769150742583c542648818031402c2c0104a41800da4070109001e4000d2980c003600107000424020859044441141e014101d280c072a03800050038041d80d0b59203200901c3e003910f40b0300010040b95040c14002400f045500d10010070f0581c0f0780002c2003c40d264005c9031001c550011b04140920740740f00001e4083e12880845810000700c400000031500b075018040e80780250481d4440640004070241030040710540c00803400d000b030f1039000c40092110600c07001000d00e80d001c1d41c40455403104a182c0780e4031102083d071005140510f854052070114407a4454181142e80c00245424240000885a1903c0d8116800700b250b552a1018044060903085601c10501c1d10070002e80300c603d0f028a4110b10480810b80e0040c00503400b41a0038440c200000f042c00342e900c2c8050502c01c00c901d558a002400782d8906401684 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 887823534 1250 887822284 887822321
    0x524091e0106031d1605060c0109020a0b0702090610090603020f070b071e050a0509010c02180a1b110a0f0c03050d0302070c0b09150a17100302010e010f02030315060d 73
    0x2d002c169446440303c82e113081c0b40d01a01ea03d0f50328561141041a039401401c1c0710f800006410b02450500354004140240e02074075200800b5070314005000140c00c1080140c0c019003425000580ca4035120f010009025440d8651410b05818501d00310005e422049a066003c0c104200901c041114480180e04c507901c0760345c0303140300b0911015075001c5140701e07603190f0070912a0500520315181d03005003e41d12030080a20300f14082280030700001d500740c41c01070b0042034042021750501070842d0311a04181601540c0c1c8415000c0700c0c01d540c804840c0281c0d0750b2550041c90700480c031104001100c0c40075001d0554003074005080d8194498948500b4209200480004030394002045004c01c04200c03612401441c0d0024918186801074000c180411344041e42140201e00000e0980c0c40d00d40907a0f0400e0b007004503040c241000b80703000304c04074a9000860006034041100f14840d09071a40c4126040040d040e6030358065410340e2a0b44c58503040d92240c45010300c1c1c0c402028840f01011500520861126440880215 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 887824784 1250 887823534 887823551
    0xb0d1101030c0c0f0308060406090203150f0307051804020f03030c0102090a05040b0f1002030f0d020d150308120405071508070806060f04030b0a0213080a060524091e010603 76
    0x140807161025100002d000f900d00d41400031900c2810600e040341e4142c04e0082440d5a80000200146016007110707000ca8408000e01422100c1f42c410105800016034104200800c0402090f589003046c0c4a06603004243e00d20501c03907102650300082e0030610290a407107000f090000000d0440c0c20a2405602d035a5004c81d1181440c0380c0890103000524040d10108586602132020a00c00700101c140b5600a0700401409241c0318130030403c40e84070380351031000c46489070f0240c40848060362103c0d0904074001c0c100895a03031002d408406510449500c00402807805441d0300c04050040381c001d105030f4a41c0144140011080034401016501c0036641d51261038030301e441074001c0d200c2c4401a003450b006000c117002061442030310f40201c0701580e811003032410095a910844501078898200384d0119070340c07020f038002125440083d001700745501c00c134814080c83d560010850101d805407038218240d1900508480c9860400054140d00950441c40e1000c2c90110080840300700c54007a400000000e5548100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 887826034 1250 887824784 887824787
    0x6050a090905041709130614040e01140403180504050a060e0906010303020303180c061b1b0f010302090f1e0414101e0f030c0e06030a0507180b0d1101 66
    0x10100039000c40750042101d410a615403c04481008403200b14000c4c001071030741c1103956032003174036410030002d070000b8018942c84d50030541003000000081e0307006508000414807203980600a0030407444001c600003079250f449490484001c4903000e60040c85402400000c03e081c0c507070f4050240300c1e81c403c100104a040c0f419504160780310009041403120b0b0400c1005000081d400b20442e60052015a2214104074a40904a003415110420250b2154001810641405140032100c4160b4020380544401e40070187c00d804180202004aa80c40800078840c4c10031503000f41e014002c1d03484003800380c1c0310032a03400300805d213a00034070089510002c400310b4170030381189068041c000c0402a41c1c107603182c05040c4030207000800c0c4641c0c0900c140c0000303440d0320501007440c1200e044000f0f1003840b800200041d52400c0c2110300c903c043c00b0314201000f03034070300142042c180081e5212445510400038541d003490141d854040215044049100c41d864405986855a950b1102e00034240600d01031141445c56100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 887827284 1250 887826034 887826047
    0x70c02120a020a0302060c160e090c090705120a0f0f06080c1905100309020d1b150c140f0f030315010e0607080f07080301030f033213090606050a 64
    0x400540d1603015040300c00c0180c481d20900c000300d0f0f506a03030158468034a03030300817400c00c42d540035400707080005000001140c166122005d40928000c00603505070450f00c03018888100c070300301d5014000c550b041024007941c120541c4070550000740303c1000998183e14028680546e0101750702081d07a2502c07400140a801c4080c8080c40f4040c2080740c4e0464005840d5032501c5442105d485003e01c259a010701d4068128025000300419647c010000903500701c213440c0145517940c91a9107012020303020304012809400da40a0a01c5007100d60700c90807031115203540c48015a02000b05100c110b4002c040701c0d600020000c10404a04180c80c401441d104d2502100e620080c0c0d0380c0810302c60410100e0701c0403104944540b0100c2d0880f5030410f040031f64503e08020590f6880c420b852005080c0030b0004000400d005241c8500c01c8290b00c82c0da02c6c0011025030b0318121000ca40721070900300a01038004016200c0000a000800c1d1490940c0b09158589a8030a0840115a5a6800b81d0040340c40000d540e06000d60118 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 887828534 1250 887827284 887827309
    0xb040b0109051303030e0a02030102070c1404090f022116060305060618010c06021c02030603010b090c0306010e0307032a1d04020d08130f150201140705071703070c02 73
    0x7103041180740340104580800c207003003990150905540340801c801190050100c8884560090005c2d581ca00c070500d050141e8507818410442641189401c64001d440c00340510340c0c125800595070840142c0940030004840c40340005203c90401c0605c8030740d0b4081003400304a01d4049a40103032252145002d1000d0103891009107024070500080248105a8071800c5992944410a20348215840958a0a007000b07210318001d102201c201c06064104c0810550010362003100194000e01640c40740da024044a1003050b9603c00000394148002002380d4401c50302c004084130010116200c0d01c2c2c0d01e40b10007100700c14180d0645070050300020261040c07811134a07004c00400d403184501482400400d0601000c01000c3e000922030303000404c0c1e50051103174040503944c007c8034407581509410340e80c0d0042110210740340300e4043c0704070f107100c08058240d0041c071078070aa130000915140905e50b41d4513001c4440303500444046440c540164002841c40d1502030145100e0761507034030ba035020b551503801004005807840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 887829784 1250 887828534 887828549
    0x9110903010f0c0e030703080409110c2a030c1e03070e04150c1701061d040e070f06031e0504020411031608061f1416030e090907060c0305030c090a030b040b01 70
    0x40c06c10800102ca4904450854001a40c001546005017018a4039813090000e82c01b2503110b0341881302d4000540da161681d0000441c0091004c1c00702003000d154803140c00c0b00c81642c1c010310450403a180050f040d20300e0840e00350300809071442c40d40c03141e08040341904140d0f010340d9845210800303a13040342428070500c4000c038924280b02e0030945030012a4020050f050003410704004060920036444030824001e0401700b01700270410711902888500d0300c0d5492a03903102c1c84080d80d43d00d840000302c8034040c0c40740b4284010b00d902c8020340b40b00c00c09107000c040c00f4042c0c4201d07082903450300c840390b00c0b030076103030255001d0b8540b26102150fa0300030043c020140074001e0007291203615400d0000b82c6100f039110144505144030704200406221042154805016100c10045d00030310545144013003507406507181c034089004403910100c0e5120405c0b1a0380c1c0740c4441c0502c802245031161f690300881c2c000d9000e035901611184149160021810208400244540c0200c811030100e80c1440100070b6400242409000340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 887831034 1250 887829784 887829793
    0x1c08060306060d0510090501110a020102120105060c030a0e0d0606080a03110118062a091e050607030804080c120405040e010e1b01030905030c0d1103030105030709110903010f0c0e03 80
    0x160300c039183c45010404403610170b2540c6001b004200310b000e400890500d03189200c195200d250840000c0c0c040e6011403102e900943e40f00001040902d4500240c0703840070350f020300940c1404205107040d0380826440410641c4400185544400104180a44009030103102c0192001a00034038025041c0100307280b101883d0703410010207111484c0c0c0d046a06401542006010403400c29060aa0b8400341079a81140f104014014903480e482c5c0e000704418041b108850344007150242c8400705d08815013290702609500c20010009180882c1c4249a07691300315014000446c640004100050700d06940080076445450010604212528191140040085030303203000703214408504401c1c0d0740301d0558101d516000c09082c003001c1c000e644282d06c10042503600800316956072014480d0356584001c0f80100800003481d03440520040d540120503203040b200003030003c000c524140209140680100c80c0034450384141800980110796090062284200c49500300180206850358010425031103034100d180a41c0c031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 887832284 1250 887831034 887831059
    0x10602010b0a1d040f060e0d18050d0b04080f0f0a03060e130c17011e0614030d0e0108150607111309080304080309160e06042712021c0806030606 64
    0x2c4a2603e582c1c030650003442c0c041c3c07002c0c941c6048401884031700c142c00442d1081180500350660401034511042c000701a04c0c410321650766042180780e024949005090792409008100094460000780002c1c0403009061800c10551804c0101d184d00f02e0405400003a44405040000480d0340a00030341080c0c40c8110501881002d8aa0218648003845103c08036440700a4025800034207500c15138101703c941d42184020b48842410300040c00290048092425000e11050428500001c549100c040d1a803216a15519228019610442c0c0181406182c1c2d0042241100c5691114003d004840c482c00540e5111629a001d1180c0e02c0f0108010b043c0692a1400c2d82010403a81e80076640c0c8280d000c44540d03502e83d0745c0e03411181410340c042c40480c1002ca18110100d650031600b48924401ca000b0343e0f04010392828280c0074502100518601420650340ca07103950041002c8100e0480c1070030484c012034200004041c1502d2262032401107600000e50781005101c1580340031f01045400c1401100c08410b84030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 887833534 1250 887832284 887832329
    0x1502030f0f240a0f030f12030902030d0807050403120f0216080a0f0c03060212160507120c061401082433130c08090a081b15010602010b0a 61
    0x440003030070603403068040454100b03594807a56400b02401c541a80c0c00401c560302e18100382080090402203e240115101d102c000300d1091003195205500180144250008140142c91121000d05004200081000040082083c400d26480030006e07a41c0d0b0100b40089020009080019640100c90518401c61040154100006546100d02c0d001945c040320f607402441d2803540c034451079000524041c0080b65841002c20003003c860301c0703408030004820850000300800c0b6110300c07444400800350350b441310f09000c0013807245082e105007078030030b100c002082c00b4500750840030480c099105107480d610407070700c003020920301c8200e604800680070154401e5003041061a41c0c510301d60024041200041420798201780c2e03c0941d00c4413000005001c003548514020003940c044e11000c00c0c940003180701c035008110020400100308201c03a821032441820945d5030340348480b004900300314560a6104041407102401b4509040720700800d510b0300000313a4800740400b071016030b06c81359002e0407084550113402000e62 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 887834784 1250 887833534 887833561
    0x60f0915030b0d050a0803011e1a1809090616030204081203130c0b091f020c190801060b0c060705040f090b0604091d07080307080f09010c1502030f0f 66
    0xc0c4039905001c41c801003801c002c140401c00c43c98002c4e1042c40740c0040d4a06100001d00114142c5078440c40001d102450303000f800490061a00c100347d440380a2002c440002c034400b41c050980b5a070091465180a062078001a80c41d050030b40e1b510381c094000d082400703c840c000070302452074410700d402d05600701447c0502c06600d4403046c0c25541c40ca50000000200c1300442c4801e6440703280c1c4d00003032070f10144d41c031401c844107030340c00c00322036036014072060007110700d403e584002030030002802a80104074255080c014445203141509042025603901c55001c14041c000703008840144c2154003240d510382c05136101140c41d10340090169014440100418882200d90706640e0701664000907012400001400202d40c0b00c3c07165900189100d031400385a0390b4400d07071000014031200400001c440c0115213402c0b03600c0c0c03680b0400100400d4984204204001c3c03210800c0a0403103450141050310280407180c4604440a04202103500c10a40c000100102c1c0102d10518a401440c079007041240c924100e64088080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 887836034 1250 887834784 887834819
    0x40c230609091305070602010204060e01091206090309080d0c050d110a12140415171e0a02040801020301030b101e180f0606020c030f0606090402060c0f01090b01060f09 74
    0x1551040001490f0740e1400c40c503103103849038440b04a9042d2035851800a000790414010755001030402415030941e9032040c801d8008ac1e601944958002c1c0211740e4690005103501e081c100c003400580703403001400840c140b004004946071501da60305058040c4c60302c241045801c03001d01e800c0c4035aa180c81d45400c0e46c00902900e1140d4014200f0451841601003a9007030b00e03404601202c0c0d0348d80090041080d96201d615800d021603d80c0b82c0c43d10b94251103003001e520000840b070407890100503071507403424480c545860a8200030320143c010b00c0c3c951103c4d0160300303a034401d81050700e0700149042070045c8501e070f1100c104000c100b000650170b07814003c01d4041441088a12031f01004480c1001d4200150145038070004c589021140c04005556645070080d40382c8000141c4e4900c603010b5440c52128810b40464018898400181610074a03582d075807c1202c550000084c140c0244a000c00c9841c0a601c04d21a40305864003900480e2800d600d00000241480c0c1d008400d541080903610b810800348040d40d80c43c058 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 887837284 1250 887836034 887836039
    0x406121118060319020403120f0207030510020f09040f020301170d020c040e010f05090d0306140f01050717040b121302010804061d060c1e030c04151403040c230609 72
    0x40c1c91300d80100b01d078141d000d42818151410b10001e40041008025202812001000d8a401402a03000d850907625a41d080c8405031003604009000486400a5802040003d00088078107041c18029030200302165500b0704d5803811642c3c0000140300402420140c50802680f40c1c004103036280f00c00b0b00c02500d4104641c2031a00654036130b03402c400504001e40110310f589810041c1000503240454029954010035100d03980840d240400201c1d03001c203114410860900060485c6180035140740044032035902c01001500c2c0700e0740d0103080d00c4520326010000c20051451aa1243c0c48007003540a10b1003940300900a0b00740070343c41c000340a0060340c000c10041d0b0700c240c0190300083c10b50841100141c0141d5161a4a00e250154804001095078618043c000d02007588040c15003040300704110f00139500c81903595203604030701400308100d0702c0c00e12607282c1100386452420b0039144c4812002010300d07801c10750b800c54984801c0c140910034594911070704a8215180ca0b03030034081025907000301c0c245116400c030060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 887838534 1250 887837284 887837287
    0x153009020103090618021507030801030f03110d020609150105030a320f07050d0b010306200333150309031b060405070f0302090106030c0e06040612111806 68
    0x3903a009500c049071507038001c00240100300c505c40e40340c0502800c6000c200d20070010702e2200d2400324510402d41d095103a1644919405908545070317a03803540e0a0a20483c00c0044020800074030f80003d1100070f0030034502c0d030010302450a00700703c2c0c14103150035000802028030740000104a42d90b80004c902e0840d5411010081c81900700e101d46c45000e008400c14207491906041e044c4040c407900081d60034400c40188140e071a11074561081002913806a400507003101045001407010560f0340c0d0101c6228504d111700c400022020010144035900110740d0481c070343c00c1c60180c107015450001000304201c865816448c010300d050100240600d24020b01c95058507070007000081d541c010800031a21800003000d20b0300004000652995a9010210f808681d40d000d696000200c5802101c6051305aa070700070494142c036820032034110300800b20200a0310401c10f92100094154482d107005001a0003150703a6105181d07a0300c40400203170743c5248101c44020400700000c0c103902c0c0580c458a401510211a80d0703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 887839784 1250 887838534 887838551
    0x90411100309061e150509061207050d08040602060f1006050702030309030a0b01080d081306230f09010c02070803090f010210020f03040b1f060e03030c06011530 71
    0x21001019000402802503281003084000c92145842c040c6580da04c040c401d100c1040c0c0b800f040b4030b5000e030714030a25800007400d1010481c186070808101d00b00310090303803ca0f14041c2d510f60002d02143d134100d034144e5060310300140074054103905000480d401003181e00d010300b85081082d1001c0342165603114020402102040500441d50140111140204000d04039166a42e25050a000b410004e1048807528800c080c0955000c902907540d5074030400d00c03248681e410082d2911010301510a0005114106c0c0c1510150b5991604031074842e0301480080340814628945010b4041c02c55209800480c29580408400c06c01d2000c00411150b55500660f900c0145120200050386003010004440383c0050000c92a1030400754a44055807080f401102d2990058071078049011245070303074000600c9401681d00e8103003c0340d4003894500c0701d034010107000c8a1424801d0440b03541000c0f020707000b0000a01500f84d552040f50340c030408400103c841840b09000361100e03101107080d03c002410452407015103440d0740d07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 887841034 1250 887839784 887839787
    0xa140f0c090103060b04080c101d0904150914010506012a11090405011a010c080d110f0c070807140102030304063c050f011202121c090e0609041110 65
    0x1044c01401c1903d18142c46649a0240586a14801a41c2d81c068010840c1000b0b4a40c0b041c1c8100451144d0069880d00e80071084040c894a4000244213403002150440e0503502e070706142c0300b0600c00c00d0044c2c0e0303030580b404800b81d003407420f41d000038010343d0400800480c0c40b841c15642d850390b04c40e1000c3c085010340c480001ca24050b210441d84502090344100d24000700800e100040d000034072000c41e481c0d2900320a9040c00015074107800501c4000d081d1110600c130300803013100168466241c0302e80003002142050071640329100c8035403103d4003003e0550880ca42c1080b5003001000064003074031595101800301c4000800003941c900000b4000f403c0c841c1c5a8400386401d821031140034a011402e64071418040910104c2c00c1581e42c03410030303084142403070500018040020700a52505988000503100b1400f6126001c1107040c00f600c06d03250700d003030188001c2d0b280e00000248034a90f080b681c989400c551503203017074101100301e08001d10072809000307070108200000344400b8550102e40c0049030f11810368841f0020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 887842284 1250 887841034 887841041
    0x2607030506190e06030a06090b011d07050f0c010b190504140106020a020613120303020304150b060a050f04051801060801080307080406110f01060303030501180e06011a0f070b0a140f0c090103 84
    0x15041e545070403404030a09c000510f52505844005060101c4205072410000000d03000303c074a000081c005101204407200c00f280141030301d030003070700010440516041c005000005805c0c62801210104102086142080c0c019000c0c86103030306a8810456140200194407440360b0720700244100400184500e15003103404141d0b0281691848030030000745d007850060020362066409441c0001942040030504c030706402030742d01c450005842d0b02d08046100c80c082c1e44a070071104105c01d2078030040c080072030251500c2d12040855001c500840b0030b030394588070028080350343c1a00030f03008541040041901181e55001114215840b915103400c60402c0d10b2012801c04110504e5141c055090043c00000d0561540125050310710482600640b261f40c4881c4104a07203d03c8020319198012400400403655580b03c04031810485824840c13038100f845001d04010b41c05402c003180d8070360144040c000b04071451300c507281982960901c0d03480c007401c0410003002c415400078104442040b0005c1c920000d03912170741 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 887843534 1250 887842284 887842303
    0x105090711030409180c050306040c0e090c0d05030414010c0f080f040b1c11090102060c0903010204030804061e0c020607060e121b0c010201020f0a05030402012607030506190e0603 79
    0x681001705810024640c500c0070351400c0f003031710a400038000100e841d01d008580713240590b038441801c1000c90b103804552400d403c03005003900c0d44e50040b4224100180c0f184c50202030450b01c2000956540c50500d10032442002060202c141080000c2003642c0000344107180407812540c00c18130311a142c441902c0c101c42c07a441140c020780c50100000c2502c0440c072400c48030b039150784210510140042c0440400e50261800f4144505005900c00c0c1d001c908000041c80003001003000c06000589025102c0d144c10145d0b512035030003c000100b030803191000710a4461002140c01c1000d2a1480c0d0155450b00001d07000d0048003800b07000c41e69158072085403103408210a450391002000131588920801803000321510700d044018800c0e0143d0915080c0c190701c1031084507010400241d040c0d04041040700102d6690f00010412030500c5000f10900192152110180310100444040f1540e10703c2e201000400f5698042c00b071900805066004540e1010f5040c840820ba8005a10401c56940d60313000007840e045420 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 887844784 1250 887843534 887843549
    0xc120b040b1512010b18010c0f0b0c040608070302030c0a0e040b150a020616091a0d0203040809040e070b0a030c17040c08060c0421030c1a01140901050907110304 71
    0x4a44090015480c50090406010b10042c3d00040341c1e607520b184880d620a10801070024410740941002c158005c01100d050b85000e5072420400c1e2043d0781d5141c04d0b01c2c906031504450054003150402000d40c1c00040113611106c545025402e50508007046409402440d200302e080c42100001040c0a417200e6002c104003950083c2046850b40d00454000000d6202c3e03030900c8018010741e80082c081c0c003040c5401542d01c1c50a42e4414201900d002032401d1611001490f9020308401005201c04240710313400a1802503005140780d40c0d4401441081004403809000300344650342050004111030402d0b072040e1a8100403500303001c1680d03107000a0441e004c45103001056038811085d01807200303002001082300300344d8001c0021900350303440d081c015003180c1c090f0384540c00800b0000200660a07105a40007040401e1103400c080400e917440d907075581e619040051a41c506800a40c0c01005004070510789980e0854003992a607020394100b002140d0b040000412440c140400210307100340c60641007085400a0040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 887846034 1250 887844784 887844799
    0x8031e0915040f060507110904050f030f04060306150804110a09020d020306090c0705030403020f1f030c0f0314010b161e0204050c181302160b0603060702010c120b040b 74
    0x7159001c00300d80e0440d01800c08031100410020035414003840440b10b1043d00000c4044040d103103e0104520020002c0084031140102c0c4681002c81608001030501c6290000381300b511182404001021070b040c03039008126210701c2c510201c0d40c0ba504001c09a0300207070002c07200501d10346108081100881d040d48200b22841c40007505800c07841583d0b02641c010002102c814255841d50701d0042c1d03d5000304c040150190300104000c1005140c0001081024080540000043d2002c0c012004c1042c140030036071404640c03211569164941d0040720a07440d0846030504104840f200c0c1d5110556090502807100c2e180702c00181102c889407144000102c040d440186001c0012a010f0241c00d011032815080380140d007008003260300c1c8214481554810203441030460510040d036410018580c414507203200c0019400c11180d2141c030190021340c40c2060140c3c0140203a41010000c2c14541031004081c1d1086900d85449401c01641c0158018102c0d08200c4010a440c404100020000c1c01140545948501c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 887847284 1250 887846034 887846059
    0x90d06180b040b01050d05120a0c140a11061603081003051c020607051204020609040605030708030a14030702120c0723100305040312110c0a080705070f08031e09 71
    0x40414041d40708910035400c035405a41d8580a22010807001c000c01080754100c04034015840318144c01a002c102514940f84840d44003d440b11001001300d1540603d00d500890704040a02c49503000d11000d4960641e041c1e03251224030390f11000154140f48000b010003e64402245d1106210b00461001c0c680000c142d4401c80100113400b00d80f4441410007101500503480000c02c042d0055098483d40ea00c2c0e94104030855817642d08101c110b5004140303450740030703640d0070010404d91800c0064030042c000b030300000c5a8400b1107000141002074000301240d112a400c10800c405039601085030b0001c0701f007070070005403035080e040303806070410445402c9018071250758502e10700d141d08215440002440180c50b00800b000c81da00007201540d104403009004940c00424078400807681d030f4840384c0d2051b81d030540c441c101603540070f1550510070400800e0f140342c030000ca580c2c814040d007409001c000b86101401c050799145840c19045d228000d03041c0c40c42088110905005a02d450703042180c100b088010100c1240c6138 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 887848534 1250 887847284 887847293
    0x9030b0c070203070611030f0f1308011e0b100804031202032805150118030b04050105060a0f03051b01050405100903260313110901030b09010b09040305090d0618 71
    0xc01070001030303101c4d1141080c001203260003840380c0400e612940024510309801012018000c0c0d1181040440543c0100640030201d4840f5800d00e01915910002240074282c0708201103040000c03420f211203051400000200d02c0d80c801c40e030a94808140e080c548115034440c1025601580b9901c0010041030000041162030080e503912013403809801d140d42030746101802d082000703c80b0100c50a03d07110171410280307405503000340ca210109500c0b50441207840f91b2240c1d205070303850f4001e0300e0496103a0344610600c200c074504a81c0ba44060200d240c12400b40610315102d5907035845034440c80c0401c2081101c00c0020f281d20610440f0040c0402600440120f000004e0040803c4a18032007600d5520a4184c0e40081844902c0c07000201c800c1142180e04585480540403c5030380900c004481e043c0e135440b6a00d00396101d040c001802180140c4070003496180c508112401c2d520b40c00702051140c2260b00c2000006074100041d540038072801c1c1c4501011915501d4020010324000040040744c0c001540c1c03040402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 887849784 1250 887848534 887848537
    0x60203060102011103041e05120d1a06162901180506190303121b0504030311070e1315050c0901030b03010b0102030f03150d060f15030201120b0109030b0c 68
    0x1080300303038004c1041e20b041d00703980300744d500090701d00500b002c2c00c680b10003c0d05548100c414070624095010b444202000d1015030006600c00c80f400d4242c291280901011404220242142c0d402d054071910304c2c040000c13143c10803141c9400001451140c0c45584d91412401c9001c0444124010180701540c1e07585850064001d803400303604002e8140d003400c0002e0361900b000f19200c2e1a0810a28030301070100d003560b400342d601c015440380c1d2110650344d40c00070540c0e01003003508240310b540340ca8903055526811410014a581d2950120344595441000d0800a0b445a02845035010f039000c0a00880c00d089490300500c0c4101411038a032225007070100b80404151100020030f6140d030240c80400c5401c5c5444141030903a4001d0101502680090007e0580c03907842e640116409101080c15505d4501c40c500014010601c07044241e82d91a590740000e54a0460751003548148441c41d40c0b1051800d00c3d503800280004003130300c0902582c0380c42e4801160741e0f034000c008800145074403811051441ca4004550910b5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 887851034 1250 887849784 887849791
    0xe090304080712122a060e0601290703021c050705060a02040f090618051305061f06110d0e040906060b0d0b0603010b1914071b0b160f020301021204060203 68
    0x80c0b03551441d072620114010600c104404008140340340101500780c0110910031724990081e0381140d118a0004401d10701800020b010301402c2010303803c400ca17092102c081e402ca16502c0801480703070030407040002c0307600090f40c4140042051600b4003000e1070f50608540034020103d00610074480c0d0800e0280301c0200e81c010b4001e440d90301103000314190743c1e62103020580709a4803482d04005020301401050f41550f4102c5540700c20321982c200500081550b0b207514101007210015448142815440780090705e40101c500200b0040c98650560590001200d07129000603d19009110318129240c0c001d840b01d401c4040420f4010740b04120b038968a06170700401d64042c018032013100e8a07040541d00540b514000783c1c2c0c1641c2c5103a0305582400d43d42103405c9806151447c0728001d001e000e07001595940500341c01440008d1284141417081c21000b0440480f0f2070041c1c12602c1c0484040c094001d020101c0c4c81502120340c0c1104441e0450142e6001080c0203211721841400407400c9802080144a06600150301 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 887852284 1250 887851034 887851043
    0xa1d0d02130c030b010c020d020906010507051903080a091109271c05040e0a0b0406170c10090501020c0d1b03050d02060606070807080703090530030301030203070e090304080712 78
    0xc11004001186c0301807000000a42c010701c07500303895000d42040c107030b0345900901c181040c505c0e101d40c03074854616000080c00740808041d610842401056170100da6260007100c825000c1c081200140c0e902240c000130307240c1550181542c000060803140140c0f640354060280202240039541c00c00c942c00c4d48480114254500031500360076a646014130406c02c686c11148036400011054a411890902418001d02d541e03170b00075103074000840c00ba041844150b01214825004040d00b1103a803050254003459021400e041c071140c03110070030607131342c010403030803040d030030488079861011601d14209510001703144403801443d220003000305c108500002e020f42000c1a680803903065a4400d010800346200e00a4000e241c2201440400c0c0040c8030341014203585840790901c5a4543d4480022516402c105000c0080504281c466444040b141d0300d100f06500f01403401035031031507045802080d940c2e512449545810010600000e02140c400e00c1507402400c10b660943d84010358548407640441400b00007644c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 887853534 1250 887852284 887852291
    0xb0f1b0a140c0901170309060c120418050f060f04091b03030207030302070803090a06030f200913020414011b0f03081902031e070504050909011406060a1d0d02130c03 73
    0x41d1840d0441205d00300703410410001e520b42074410f003c0c48843c1d040074039800010301c94500c8480e9444160800b4001030401040c1072422214102480e4051b10000303481c41034403105000034840c16441d40d44c0801c1c2061026900404e40282502d0112075001c2c10015480549104101c0402050340c04160101101d000b60b007143d4120b5120304401e07440380304004070113a0180c4080000c124882c081c1c0c0250b1a03810480200081203540d40c850800c4402440c0040d8420f00340015490016107440e0780c001c4005112850110f08050911403110f40c00000c406e25030f8140002103c0b80c1c100b41c42039440c2c6140550740314469039141c50307161501600441c02907445007041c80c21244603441e803140601c2901e02c120b04000001d0380d01c4640741403028040401a1410007001020000440c403625010700c01c5000707a100000002e100081c10301040d00020028003058400c10082100254482d070028020846054203c1101141c9005000041c555220120000d4000d0401d82880d1000c0c1a6075001e000040140e84060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 887854784 1250 887853534 887853539
    0xa0807031106030709050d030504090c08040201091d130c1a09040b0906060904090507150903120507031215090905011a09011d090a080f0406090b0f1b0a140c0901 71
    0x4501c42c08101d030f404e000566240c1040045240c02c4172440340c0c440c02414400c1c903041e01c403444413007a150400c0072280400c00b840c05000c21541d00c046454010f00a1145099040b00c024014071000d1101400404400007080000b80c20300c06040300420042c0000f850155240041c18041106038200b0104981308614040b102985030811001551151000800c03140c0341034140c800300b10045c94020820b961070300c9281c0021400c070742d4200f85030840c1406d41d11401c0b440c3d0300c0c3d490321810f0368010200900030030005121040000380c01450031075080c50b803004086201c4003c0c2c14805a1402c850307000c1c1212906100c03a4409208066001070418481e0009904416050000380000d60f4420300c983c0341035460307402e0b5002c10b00c070b00040314942080441303040c0ca20011285e12b58a8070368205c0040c500c6013440014040060940014404000700400c1350032031300b08040f12010b1420b070302030054082e008031413080d20a00b01034010b00500313140641c01303c04040301c1409014059070703411012000038000c50360403001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 887856034 1250 887854784 887854789
    0x607030b0f010504030807110909070f08030f032a0d1d0c010815210105010f0e1e0a1401091b030203090a031b050a050c01120e100506010903020a08070311 68
    0x41e07010320300103845461078580f950fa00d011496101e0a81074600880c14401e8124642c0e4590305180030b00c0e00c0e600209412410018040504441a03100004540c01002940c0d02c800b107101c1581ea10120442003403a0300002c25001c1c8541c1c0303044121a80315a040001c01d50f1411155030300031007e005110b61032080d200c0300342d82c5c103a47c0c1c2d40810900a020950180c0054032505008003169800980600f290041628088101e8480d81c4080040a8182d46480c0184112014194880010402201c880c686800c000691000d1050070745003110010b0880000540d80b00a21b4000c5141084011000075141d80e5508080004201400c6401d82516140c041490001d204c0c0c003d5034041c148200203040380ca08555000d450a80f10f00d09280c0c0440421800ca40c0030810921059080341e0203000034041c42504070000400c2c12401c0c6001441d4640b41c920903c5495000040500c1d40f06040c000c0043e185e00c070040140d0350401194002035002802c2040410491000b050400441c1c1c40740d401d40080c4002c5504 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 887857284 1250 887856034 887856049
    0x60117122215080a050c090a0806090f0a0b0109020d0209030610030203010605061e0702031c0c111c171312110d0210210e0d0e1009091d07080607030b 66
    0x11101c00a1441004070746180313100c0d4801c0d81c00040e40c614051401010f4804948040074550100c10030350000c6040104042041c0848108080e108000c0c0048041a640380c101303001041c00340c20102507021070309030501c1e01103a044440510008080381c0c15440c00f110300468034aa40e0104074029420040002400d040a10a40d008100c3d85e00c10004102034402d006400b60308100c009a91510550f10740740c1c4004000241081d40b0507070350380d402c012a056070500120035000c103906a0b0003010b03000113440d20101d0700c0380c80b00266544450044001c28048074019a1805190148040c2e450000d04c0028140c41204120300305c03502c6001c611075000544000c0042c0c8405010000e900441141d084000d0548103d00901c62511111000350440300c00c2d49c6d0303ca003101c00031030035808554440a801c8100342e800238980c600c4024122081004407908240090040c3c50780c0c8100380020381c0b600d0a10958801c94040c18808181d48811a200980d42c2c0c15429603800003038584c40c022a29005001c5000d041618 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 887858534 1250 887857284 887857319
    0xf0e04060e0f030906070c05220b060702130f091407030c090b01140a030f020403110108094917011202010c030813060e010501090f09050601171222 65
    0x1450800a000d8144042d42e0300c0f00d1822103c00d0b07581f47c008282a580c0307a5030314000000e02424040c4458940050104a400c0802202e201ba1802d00540e4016a148100c001040800790740208500d94414101d50260440f0712005001c803590340808800020005001004c9074000d0241d04c00c0300355129038200440b005004140c0c0014501c5084540f01000e040041101c0391141c030380010010221880001260016042200d60304d00b605c9029689688c4064525042420304000d000700c0080307007041100c408040c00c80c16160817000120000c01080003030b035402d00726039034158656006a40c010001d00c07056003a510b40340345040364400403404031104800400f50340e0381a12180c00d0703440c6a0728241e4a40c0c03001000441c040400c40900400500715000d2020200381c8600080781d0741d414a02000180e0316030b62000d4480d1031805035038401003400065000c1c1107d002034000044428a001e07090b06004052011100910000030303900051018a0090741c6101c400400c100251781d1182c440c03808115225 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 887859784 1250 887858534 887858563
    0xd120314161815120c02010507270b0c031209030a020a0312060314070e0a0e100f090209100e0a0c17060103020c0f0102130b0301081b01090f0e04060e 66
    0x68894440390080b492800116201d60400440a64800000720b0304003269204070001160741075032014080d028050480b10880e680001e100750310741100c00520002c08016814200c4440303143c000000704444802402070001c04003141e66417001d0180c90740d170382c0c1c1c003d01d5281000c1c5030310000200b01305030110a40f00120b1440d40030780350340740c0c15850843d414004464800325031541c03041d0010001d521300c10840b840305001005030400c0b178600380180c000e01c1002171038903000c0c50a140704410b04001c0401c00b0403407070580034400202200420b803031200410401c00025000201c600a125000728480b800e1405c0758928980141e00d5070369186c0040680f01d1041c07101c030200e01c4402c00b4448030700540e50703c5580a6018500103007000401120f6a2415005285800c81a54001140e03800b81400125001c0500b0700690618615451300c0c003081d6942403004c221201140d44414950641e03071003002048000d02000040c0340440b5150b10300c0340c040d000d0640d8209c0c1e602e071410030703004000c44000c100052082c034076 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 887861034 1250 887859784 887859811
    0x150c0b090102090306150102070e090a031e120e030702091311040b01090909030210050c04050118121502090607140c0924030a050303150a090501030b0106110a020d120314 75
    0x40001100d0003040100031103040d40100000070500300044201c04bc410402d80380149540d0000d8100585060340000c0c0c80e520030261001400510794015040b4216405007a00c005001a0080507250440c01a070000070340c0a0216002e024080010b4a841c1c0d01c0d0500a041b80250318204504100884008080190110350099000c2000328802c0d0700000d4054001e0040e1500000742010500458030100d4602c0040e54021134140513030f5901c50454105420744014500c105801c054000712215603001c03000b88140c000841d2a5051035964060b01d07444076010b0f006c01e80303c180d14a40000b41d10404040c00c1843d12a41d6400b0880d882c1400b0524041da5480d6021840040d40560403030000465070340c000d4251150100c4000000c000300000c5118a00682454140c0d0402d0002c00043d48550ba000502450030280148045101a140141101c2c1d141c1822000c01c101810300d107040424500c40a548145250716000034011003003070260110380ba0b03503802c1110b0561035101129850003504d511900014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 887862284 1250 887861034 887861041
    0x1030b0405010e010509031e030c0d022802010f0f200a030b061201051206041a070e0603040f060f1a0d031e050d061502060601120204150c0b090102090306 68
    0x56509960410701680011581d00c2d80740e85401e003074420540340104143c0c00083c030989103040c0501c0300700307004884508403851030400c074100380070a00640035a03081850b400200e0f075500301e042c203038021072107695030002e040780c076035840d030083d00030300d51505d00c40032041c140124000e0240291141983c9003c64021000742c1c40c03e04012191141c111840700b40c02d041ea28410089240c0e101409058040020400403980d98100814080800c2945408008a5000300203020014450b85005010b00303000c0d28249800d540d40010480c5c40034480c0c0b01c10758000c1d1000041c4801d1000360307040402d840f4000e110520100b48210f42c0c80046802510000d080601213030071008807440c000400030324840c041d103018030035140d071401710076558100c2109000200e1400100c401340110240550401010035010001d58040d801002a4940e440100140c0c10070504a01e5420045860743c10f450191803034900900c590840b0240181200c848c04405030390741c0e114036000a101c003405008844100c040640079024549 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 887863534 1250 887862284 887862293
    0x6051c0f0302070915050a0602060f0718050d05031801140409020f040302100f1b02090105060306030a0611070309050d03200708010906022701020c0120010c02210a080103 75
    0x1000540d00310110301600301e002429450720700404080e0089040021103003894101004002d1100d58880002d44d0082d8080007280e0101c3d10070103600c0111030400c1242d10f058250f0340400c2001303d4012550004c40ca0b41314400740000000548131010011855151302080324005480500c10080c000c002280c04101c140709500d1150003604110503070050842c01c7c00c0e12070780052100404481c10400050044a1001d0029482540c403a04010301449002418078107401056805005001e0b0a015080020208640b034804100c82c5100c1a005070040018400100511200d44c3c095202517001501108010440e407a10341e5246c41e0341d99242e228440074000514450829882202c41d01e1040d00402b01c0005d550b100c01e00400560030302c01d00005913140c841941c41841c504801082410040e044112906076980000389c524800c0e1090038455500c8096800710b18075410301003402c0c036155007006980c2d0320280c0c0004034190007600080c0303e02208000c00f0f0100340c260241e40d0030b000014010307500400114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 887864784 1250 887863534 887863553
    0x6251814010903150b180f070f0e2d090c030f0903040806040516080102031006120902030114010e010e07050d0f02090315010f0807141315061206051c 66
    0x114041c100b4400156a94840c0240101a2500c0d00d013a141c035003581d0b440c6441c240107903555601d0400600307003040c100b0070024562040018283c4e010701034481007101946014003000201154000c3c981040d42210481a100b0b0003404520b41e9954200c03148070b65011b2818001491060303c24805441c1142c1e07922180419607035000c1c1041d00540001c01c000f00d001c14043c03100c00d11a5000f00010200448500d100f0034040c551b546c003640150b40706005200180d05005910411101c02d468074000e800081306c603220092540300740003507056203000e821007a049107803814241280d41a20351388a060b81c1e2000409941081101c104001480070440d0107040440799020031015095001700504001280d0046880c142140c1e2891a4804c2d900b00104944130118446074007600550740600100b5160a1b074040540450000b4184940c41e0810301c482240030940c4061014041c07114000c0301141d841401400c030603d1110b80b00703142820180c0114213420141c1000d20b802c0010780050791500c089485070780d080d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 887866034 1250 887864784 887864819
    0xa050c040305070e1b0c0c09150301020403140d020c090f040318090902030c041a0d050309040203131a06010c020103241503050a0b0607080c0f062518 66
    0x1120824403010011400c2046107901a00c4052542c400c1800d10039940348145411010807204410300300890402c4080c00310707810700d401e0b000f80c5041c2e0031515a070420003540000c0300c46903a01584046000020300c0302e50b02c810103014155000707590006c940b0480c101c1e210460104410b4000c44024041441c9540d003104259109000b850810882a103a00d0503540720741841d801007051589815401081d03140901c420b000880e0101d50401014000c40105082d0b4006000707c2407181560b228940d0a00a00740111480d41500420455032840e20140e4414003000d80503090310402c0306a91800b408240326242c45014a8050f1501e8080c1092980114050b1000e0480c05030117502160400e8141c0c0391031406903026210901e5070020b1803245110003070403524020144c212032030400305450071680700d020407124425004408959150820b110040c40d1040c40300341c00314239104101c00c0122a2500512240701da400002c2803411603d0f07a09822140e1814402940ba040100140c0030400880a02c003030245 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 887867284 1250 887866034 887866051
    0xd050718180f0203060603011a0f191d0f04080301030803041401050106110d0801050603060d0c0b04090902040b1f0e030a0828080c1207032405030d0c0b0a05 69
    0x10704196614160014419080d41260405030032020441180307024000d0f079600c5001075000304503040a46d5560030000c2c2c0302c42c20341e60049591f1a60301020303840d038400c03007072900c1c01a600d0b891110390b80d03694507140c140382c005001c8034503401d036001b194a225201e04180d0042da00030080380d08590031911508007642c00513108440200310600c0c0c03600c11580a00466000388601d80320840100c0481e50020704103800c0c03a4038001000310b00710041c0038036039a140580e40c00000c03c0c3c0d5024042040c1e031030704216541003600a4642e0340070102c7d000910350225007056074881d109a078140800201d40301444400403d904088012107200100340001c144213075281d03860340e5402002c0711110040b5855801840e840103c00c041e0901460361603c140003050740e141c1d07614098510b8507610629100207400c4540c044c0108854402c42140d000c01d80c0c252090300000c0360010703d24803c1c8003803041c000c08540caa609501c80d00f0702900400307001c11451030007a00314000c003d420810040a981d2140c4451005100c010104032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 887868534 1250 887867284 887867291
    0x803040303121802130e0f0c0d0f0f0503031906051516021c150b010809030403030810170a0201030e030306060f0d020706020a0c050c031207060203250e0f0d050718 72
    0x1004d0794595004020950750000f0025048000004140c1083c41c4910320100ea58000c001c6500d880c0c413103510b41800701c4d810911801c1d031070400d13240050400881502c080c01c644000b206208125024440396110440f203158208005a5603500b40b0003003207100140d103030b020300041c0700c03200d2411341c0b00345200c0d52544014103402150581d20f0300202101303d14401503600f5243c485243c10503010500c21544800070900740007020346000b08216640e0301c00d90000030304203c2d5000206d45400d014031780c0040a00000310100c01e510114000307680ea00c07041d100303003a0300103403e150600360076540c04800c49010300d501621941c0342002d544039018440c2d01a003c5030804550810140300442c00030b00c0a0003142c222581c03083c4146585080c40c0786010413074a43c40307110342c01801c607100c030303540d254003c0381c000348e502140158990360f07443c20940d1802c600041040940e80783c500b10799030080d0701030743d031000c01002121004032900b64407041c01860180745d20002d0555005540502c910340d140c10b204220641d40e00e0010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 887869784 1250 887868534 887868581
    0x50616020a06050706050a061a1c0908090301201b0705090a050f0f09060423071e0f15080c27010807020a0201170709030b040b10080304030312 63
    0x207030408026030b00210000700c011400ca0100000e0f8060140c024008810500c0714909040301e86000d0041b003000b00d4210034000880c2c0d404150030030780103010111006070070418140d983c104015294072224140f4441d5190101e401d801c5480022600781080500311080c5c1861340300a071001c80c1e413100f584103a0b407920039542c00007103942c0c441800c144200c2c030304075003c58141008442c28620901c0a000c54211601038070030007010700340005040345d0168008400e01400d007400ca01c2c4040d13450100700c0403203660055240c040360b207100001411412400e4110400c0c0d0655603005054010606801030ba12000030b10904105001d01c04d40a0030382161b0350400d040e203001c070119030602d1401d1044072412400c1d0004d500d021035035a00002c0003035000b04a40080c2c0032081c00c1d540020001200100925000420480401e80851240314404003440d070115a592060409042411500c0801c441c0c030b03107603604011008200c5002c0031094908882cbc2c16183d56182d00a40480d00000d817012440c401c01c24014003104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 887871034 1250 887869784 887869789
    0x17032d0925170d0f050301060c06020d0b090403020d08091207020d050c03100902130507080a05090c031501051507020d14012717040b0418020c15010f0501030c0905061602 75
    0xc0038808014140203000781410844060030803070075131203071406202041c00100443c5822075070724400a58020b10050703880f4a0664102d00a0588440c41c54004200b081003100301900006c102c092440c03d900c80c0c001035500d000d15141c0c3d406058030f540b500d04805000100041c02c0a80c61400350f00d00c11025286440344d080003080c075108000c8038908465817219140c00a500702080c840c000c40912501c103202511b0150000707401d400e07000d40107a01d519520390004400000905c9010a024401420340b141c400007420564180034003030107a40e21403200300e9011000400305101312112a513015000606034415900c50b0340300b040d42508507500554944401001c0502c501d481c000b07a80c00c25541d00e005040c480d04080701c1100c0280c400210010041009000320181c01d01560101d80504808a10718100c45614002a01540e4240481842502094000c4080c1c40074900e05a0305280c884249144d81c40004400b512a0b8000d03010104500c41014000d5081400003040002e082c0000844010700c81d502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 887872284 1250 887871034 887871059
    0x6041205031306030c0818010908040b07150c0f0c050a0210120b04201c050109061d060108040f030e0901061805062517032d0925 57
    0x404480c03a8000203010070203215980c005001400d410700c0c1c1001040ba0761039003c4c140c81d00140c50f02e00b089143c8104412a18070940128522030f61024542c1e071107560300c5945031016003107202c084403081440d03510030180701150300c2400c0121085680380000d4042c000310607101015a9102616036010711480440540c032131107400d4009010325a9060031100c06c5861400407102c2c0020242d03c0b4604055108544074030b80744c00d140c1c0912001100030b9071010f06000500340c07a0100340c000025182401c0002502c450207501c6801220303c3c80d00b80c0c0701c1c004803000e801d0b80c1303488046074024042841417001c1000700307014940604045100b42029820303c02c842000401c031601c26400400090390581d03a10a000c4101c880700e50041c10155145410501c0c0038084140f02c3c201c100030700c0d0b03030301601000741400d02503040e03590030b01010310841c0c45a403401c000440c01011b61801d540040400c0e0100d010b01c060030b501381d9010340701e0009180503014600c9400907801c05140d405c0c0e0800d50050b82c500010805101520 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 887873534 1250 887872284 887872319
    0x3020c03041d04110d1121010504080c12070b0c07030c0209090d0207060c020603150a1a0a1b0203030d091b0915050a18020d0f0c0e12011808090604 65
    0x9000002c0d0300d0280780c4080c4280b503811005020b05c240210500016540165410280c9022200040c85454040d41e0100714006100002c01d07660900f4180700a2000703500051210040c00e4081d141d000403075078600d52a074070804000401803a80c010024000c01a05c80251039920f20034074080c4000c0c2d140c1c0d00040c2280300c098a05401940003117861042c2a03404001c03100c000c000a081c8080e1003002900080d25600005290004820324240d4402003541c2d0986920040e0061100901034014504401d00080d000003202c640071442d05003240d8001c03022203011441d00e82e07005005600e4407108144c1000601107140c800c603440c038401c00d200302114251400400181821400026168910510030f0201200c2ca41c48a030007602c0b4000c0901103000007200c0142c101010000240c1e8820000c0c080388000c150b81000c4c020300303e281c040248940c0d6806201800e1050b000c031070380c041c000507801c8224200c0f2120010340c1c03120140e442e4007000080004014040b1320700c00814050a00e961542440303402c0500c01c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 887874784 1250 887873534 887873579
    0x3111207122d050a061a0301031703130809130e0f01050f040201090302240a0e121605041503061a0108070e0d1502190f03110f04030303020c0304 64
    0x220740800390703001500c20440448881200400d1412042c81040c108111204480a07556150000159440302e03030b8000707030000c0084010401c0d07500030700400c04245410030701088801c4280451060141d030b44441c1900d00030026003083e4441242980e580c0c0503a030b8481c000450b00b1000c0880c2c1c06032145040d104001e4002c4640340601951100d9031615421182d005080805a805010a010141c1d0b44041c18000303483d4141d0307420151660044c0800c50400901c04902032400740051005010359210004001c145411b4404a045180e00d00c6583d0f2581c000c003a02d02c4550040da00200a280340c150425900d0007041c0381d01284054407034942e00c0a0361074524618581d6a464102210b1650788110455030140d2240303010840284124001761850410701d40143c6000b100042c09241c400465040f03a40000240c0100c0740c80b04003098015128100381c1d65040e01003881c289800349600308440468034100813400c0078904e00b03815581d00340c000703421030754942c1c2851005000c046540303070f81c07403a80101e102c854 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 887876034 1250 887874784 887874797
    0x712210519050705090a2c040503070f20060c0a030f0c1e03080106080f2a030916080a0b0c030403090503030d0209150a0512090f070f091406030d03111207 68
    0xa117000d2201a1705994061309400212202a8050030090403225031403210124503040f90792203d040c00d51035406501400351041b080d0188640130020282c44c3d203008003100103503440c2c0d80001041081168022460031000c2d64201054240004e40308809500034450a4103285a0341c603281d4864503040034004040208440304181900c05042c0c116080034018445440c04403e546080b045000d107518018005001001941d0020b02d0180c52807406c0f2041035071111501d50700c038504080c00b641d0380c0031110310801c035960410802258440000c101072071303510b400102122840c0c03540c4400e094035500c01042a01088402480482c00350390038030080041c584081009a21000510b0410040003001d910b5025044810004403481c00d41000699525080041001400c2d59540c10541c2c1040d1210312000000d005030302010a100011800b030900ba918441c000f0041088881500c01a070482610301682c9940000d003d40c1c00c591294010313000c120100b503255414000000d00a40800d0b1042c0c0f03a4101040300c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 887877284 1250 887876034 887876047
    0x260a05030907090209221e05072a1e0516150f0e06031009051816030c0302190e0a020306010e030604031202070204021e0712210519050705 61
    0x20803042e005040c2c1e0800c210310b0500b40303030000f88100c1c0203070410303420201070350310140281507096000d40c05400c1400782a10300d40b501800d80400820080b176000e0041091585403840c0c003900101c519520800c0c4000c0368441c024203454400c0004d4490341e03446018100d080000e40010818484100581e49401580a4032818401e001090241d84954142000b2149400c114840d5220389001c80c40501903c40302c0d0f4a07100c0b000340000c1e03000180c11441c11b0b18204018040006100c00445031050342510640f80100a461302120643c10b1070b100240c50104201c000340007504d409500c0602440e4052009520542e4038480400c5c58041150044ca1503035001c0200300041d45c004001440c0f10074210301a0074149040d980150807011003032a940c1d00d9550104445c02151203944c1120407080c6581a040980105004403100550060008072024504c041002d01480c1c09036240c400d00110b4501c1c480d001c0c80350203145034001c02d0b00078260341c8503080d86070400422000340d200f03d80c010510ba07070ba110303540c0c01c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 887878534 1250 887877284 887877301
    0x120c05030d020f030d0b01120c08091902030a02210706020c0901120b0a05150a0306050a0608060106080703020307051908060127120201020c030d080f06060412260a0503 74
    0xa509401c9066402015454031801404401c503201008481000214000ea42004803880c0481841040300300345020200d180540d0030002d0036101ba12a1411106210011200d5081c2c0c60342501d80250581d100308822001460711204c00440d82032210b25051101c001c0101075450704000760f103d0070250b0400d003404c0c107050a2000050303000d0f00400e00034413031560290b40c070300410040041201c105941e451011414100301ea031082c0410180082581d8141a00d90901100814080d40c80030202490b00c3c0300003c0a180c0030800034126101515040314a54030307014241c000e580020122000c0002c100540482520400104c11241d0f1803692122120304d09400007400c0d080c403005803100b01012061810f01c140d64a150f8500907141003008610040c0c1c2c0503c0142e24042d81804c0490b8140500c109000c10b85910a80480c440c010524109071580c4070341041c40100c0c810307800b4800000c942c4901030804600c103100f41059081d0041d165214100d1040a100600d800c201c0003040000c03800403d010242 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 887879784 1250 887878534 887878543
    0x61b071124031815091e100e16050f13020d06051201090b06011e050708040806090f011a100e0a15030b0405060315060d1403130e15091b04120c0503 65
    0x1301151300b548409070800e03010301d90b40c50f403d0100c20103000c0300d10403c03581030403410310a06078110044441172048440224810391140300c42126041d0a6a001800003150303e070081c0d64406600018103075000c0d001c03802c0201d4000e035002e00c2041c007100d621283c00043c1c40e02c1d004001c144104c002c20001131380c0c240500d00710dd0010300c041c18150400590001050000c4449161010b0f0100c09041203035503016140b526800301c1c082d41e4401030881c0175680411611650205420000c4024007000300003801d45900401844415040260341001e010750b0b00d2030509001d103841440c01e60000700301040c05541d03142501214050300d1000c1c4002070325441b034610582482e000d0650400c4045003d801c0180303001c03803100c100b004d00070300e107901c0341c07810001c10010b100c40c00da0408503d595400540350fa030303007040c2170755910000e8522a101100348418009000e212200070201d6800b00f0060606035903445881380301070b10f454441000740d040d220400000680544c1911400017480c400d0181002c0c25240004243c1007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 887881034 1250 887879784 887879803
    0x3090302150c04060e0d14150c040b19170a0213080c1806130c020303100915030213020c100b0a060507030e010c031709061b0711240318 60
    0x22110704001e00c854600d10360140c4040d0f8420346000d0316100e440400180c007020f032101d0084c01900c11039240c081c9050000c42e0145a149907600424042c3d05c900001c54514842c500c545c0d400128140003c0d1a0080501501c5104003032901e4605049841142020350b481010758200305125400144280b08030350700d0020b84010000440501550440315010842e1003030b01d051507203600410b14000481a40c0c80c40b21511011a05000c20001c003030296101171355079807043c4c800d503001403400c00000404140034007944003640052154102107a140d07900744490030171744c440560901ca0f0280310b5140c032902c0400c0190800d4018000105044c01c10005000c3c4048582d000f20080103c20814030000c250490f409100401e020310382110410501d0504a441140a00c0d018810648c40310500c913140390005001801034000c2c25010300f081180c800402e0840c0725440004254085d44950032129191030b048000038000400c0080340345001d181d180204c1c66000312600002452001511640c490042144401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 887882284 1250 887881034 887881063
    0x709081e071403070306050703020c060702060a0b0f2404090213150206040210120f0c030213060224091c050d05010e0c030a0f0e030a02010207110904080a082503090302 74
    0x344994402d0120b52294101c1c08085c110f00d440d0000701c1c0c070b980c1c4280e0440e100002d901c801c2d1100c90500c010007d4a071102512a20202420043c901d82a440c00400284035044000e11013064550800c50308010145094455000100107220010380402140020455035032100c841c0c425035800c1a801001034002481c9140855003c10100001610755118002482d00c3d2800d000203060490031240005d401c0e0405d060320503e08250303404078005e030140c000c1c0410000303282441d440b080c0c480304203d130380f8003070070803810074101c6049070015041203130706d0030340c0e0704020740406403401313074114081107a2520130001020300000c200290008422003036224540c00742c2008000342e0090304010050814900000e40942d000302d584800d682420390175548030b4600e0b800d0803c2580d441c4c2c01c802002034000d400001c4103035141e01010021142e10320f071140c1c0d054401ca500082c400e0410401c0841198198001003e5425041c2100b4000002e01568095140034140c20355000c10030a01c1c51400900f802c609800422 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 887883534 1250 887882284 887882309
    0x110313150e0c090a090c0e0402010e0d0b0c0f130e19110d020a0e0d0b060f01080105030319020a170d0b09060a030b071202130f050303030c030406050709081e07 70
    0x140781a4022408021280c0101c035844141d45500b03081200500d480d4000420b4400344d44000070b1513960501c052840399000b601c8404a011480092000080a483e00103095280c03a80c0010340d40c1c2440005003800e0113002860f0342c00c102e2a1030f20070b41d2903015600710381020b0b00050200b0044440200031540380d0402c004082c400403200d00164501030041440030040c0c00c1d00819400c0b81180f10301900780e2401e00c001e00321040e510007070401220260003170354118042c07555080c11003200d500a018039812114040d0013107180180fa01c01700307007094035802407400c114003e054a1002003006c01141240c50b10081d041c00340d07aa00c4860380702c01100d003400070160281344107000b0001c03a40da42c81d040c50f00301c1e504800318610669580100300e401d002d006c4c6010808134800700b280e10b99404454011025942e240d040c00c0c80181c1c59904040e92400101e84010154108000040010f14280c204540000c014103050802c1a224040d0360b0400e25100030740c00e04da542840300038284150810038440100742200924 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 887884784 1250 887883534 887883551
    0x20714060108010c1d01080c0705011d1902010e04020309030f03151f050703080907081006030c0602070b16020301020d090b060414060a1a04032405010927030311031315 74
    0x30030380c85c2000007070f061003018000183e804c1c04480440f840241d001c402040ba0340000d030301490003101c80f80120170fa917204c0e407480b1031404010102e00c003420075016128603544889890800020350300040103124240801d10020748070b8a50500a180600c0e03128508800e0020031030140309030101c0d030304054000d1072440d071096600181c014044170301d40d5401d8603010310940d0300c85002c1440c20845500014891003105404e60000200b45d21850a8a1088800c03407404e41c1e594008030b80e1030080307000d41c10405004003d440c500c20b90744500e801d201031007d0f0004d400c0c0a021848402200c031104019a6043c904004008052500707200d0813000b15041011000c003400c0c0003011500b010303014018103e0395a0fa5071901c0c0d000511910680740150f41c00740d103c2601c09110703034051112a40d15009203070113606200020030030513800d0140300800301c0613001d5015154041e049608a0303005120054050541d00c0040c0341c0200d200c58002c5d0f1207800c1010700801c0c68900f519041c03070884120721035090550300c2c0241c003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 887886034 1250 887884784 887884817
    0x31908181504080306040b150409051812070507030b01030c090506030f1b0102070b0f12091c0c0206120f06010906050304110f01120507090f080102070c0513020714060108010c 77
    0x4080e006030f003280016440383c0c0e072000410000c0888840340d0340d005215801c2c49819038141b40042098802000c002e0100342c440701001e000504140320314200c01d80180481c51b105002400152482c54003420464001d556691148540c1c610283c00603182c0344d01424043c070814549000e815000181038005205502d0122551038a41408403e44561014102c0319950140e200b08a4000074068081840d5507984800d2102e045903032100c0078908070420030000280b0903080100c6c400901c0040c0080e80940034100a6080350142c0e03034002c0407603000c00248004904046a0040745104200300c0075550070a060241c00900300140da5888031041000400c1044000b43c15035485269810056540e01e44003544540144c0c0c0e0b992501e420110610315120030007186590040d1000f08440285e401e10b01c65a031100c1c030712404d078072500d280030303000405400d0100020f04040201d03400300e030502c120040c280011592215548400b042030701401d540004018030000d4002e1086036210812814201c9040340300d5502e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 887887284 1250 887886034 887886073
    0x5191b020c011d12011b09080304031211011508100b0604150309021503151518010908030c011a01030203091009020f100309120302250503190818 64
    0x128a0b0400076a16940410b119401c1e0855020788001042078220790690070000303008240e8202e0341d4140314844044d01c4e031101d0184045030241c1e074410307020714a09401c50300c0b0100d1707009048445804104079001d04400c804030a2203040c1070300c2d0040d00d107000010f25015110746000148007000c00340da4540a08100555a510111401c5402400e41c00307850062b604420f800902e00389002a402c522000700008180840d280114416004508220349200c5800c0c02d1008a0402d10032422032504100071881c105660304098030580c0c1c805240c400e40d10f039240c22030581175410000d58004030783c2d103490032800700c1d080040c3c403017007074010a280031429480c0100145540700301c1210403000fa030342d0318089101503455407400200306084c068418412001d0781000213000b00201c0c4003da0349540000480e0044a12900846046c1c40c680e04004400749000d051292400d2200c1d20704075803503c0200b280c1c08014400c81f0407102c503517a641c0c0301c0a00c0c9160007404804101d00f0030300d0420031600a202e0503201c8120001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 887888534 1250 887887284 887887303
    0xc08061f0c2301060f1a070b0f1f060c0b0610050406110307081207080702010e1c09080f01020406110c0315042405060f0429031005191b02 61
    0x1082d20003041d825004100c08081c040780d2060003942444804100701c410041c020086031000d00041d8030450030b4000e281d0b010700842c1002444100f0517000b26131082d49000358a40c00840960f8920b104992074410f808407a000c542c07080011651809001040c844034801840e030007002a10b0160030740cc1c0c0d112009005100b00d0180348180003002c4040c100c3c850003082a12500c1d80e0100c0c1c0c0a9480b201c070780059200600c21a081c60014a00c500080c48051060140864058060004100c144001040200c100e040e2011000030042e05050019560700200940a415125030b00011307600c90402074010075009000710b150780c00e9809500307100900c0c0c4002449600207281c0d0040c030111926145040807c2ca00800d58200d1405002034901117030300031584c4154003d040c1281d09078480300741036007800152081c2d8142d2000d00550320880d030001100840c1c0250055000401351501c1154a11501d000c4480c01e851140120540780501850784803d0b01c5030145603c002c5030403d0b044101444020354403080030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 887889784 1250 887888534 887888543
    0x40b040e2a120c010c150f02040302100507020a0e06030a06091401150b0d0b040b031e07050d050606150909010f0806070503041e02040b1203071112060708040201120c08061f0c 77
    0x1490704014402e04d400c2080a081111200f030107c440d50300d48020281d00a400141d10842c141540c0c83c4a40c0c0c01a811600800e80c064205540c040c076042001d2a200002894036805009030300f1040001603c0b03120315000d8038030800140038044030000c00642143c060380c0c14248640750381b080034080010700c030b030551300e140080801c0410301c80b0b042d50106010b482c07046000c0d50984581585c000e80c900d03c004224081190704000c0b6041180d071501045044000001c01400710f4124101041041c108100014049038240042a2406c6480300100c2c1c1005001d9001c1600b03000014414000d101d070921117039400485034542a401c60805480d00a00300220b680c0b00d4500d09031205141e811504c0782d0308641c9130880010048107c10490385e90302a101d9100400031100b2000d807040e400758901c1c0549041c080c0440040c01407d05a480f0841030300c51110180050341402a40c0c046152220b0990060094800b0203607211801030800c04244140114448404582c1c3e02c1d0304003203200c507540c1c448040c24085400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 887891034 1250 887889784 887889797
    0x5070b07031103010e1e10031b0f03140f06041104151e17010c050a121b0f0e010c0201210905070e011703030411040b040e2a120c01 58
    0x22428141e0042c0101034011008400c0030000062a116602c2401c1c8141d00b80078102d286a0586040040c68134004c5503001c10501c8081000d10124030494102d6503081070f095500f42001c0e46404c005c0521031b41035402101d10324010640380704da0310414815a140690240014030003402c0c150f40d00c03d402d0300d441000303900032542c0d440040100c861510b4a20b004288400c00c0903c072803050700368403d80826502074034540e00310490102041410502c600400304070719a503100d08180d010001154901d1050b500512042c0d100d00d200f20400e03d042a0411641d1650f8031170f10880820014040e24003909103003094103111304003d290000d42d070049003071a0040800502c1030410411260a64018a8510b0001c0c0851003441000704000c1540d26600d410794041c01d8010500c1910388810995901c41110020405c8001003951000340c14075400c40028290b000b80003103051058296130070f180814030b09101040135407145070303401c40301e00c50300c10312030f142a0903110109190f04a003842075454903007920380c904102c1d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 887892284 1250 887891034 887891041
    0x2060906091306090e0a082d04080102030f0a090b0c1b07030c0509060a03240b090a05040204180807290708060102061006020d142a01050705070305070b 67
    0xc0d028215809180014002d2440b00c9080550000800c01c5004d1103034020b00c3c180520422480000e0711046440e0b200c034259113440c00e07104c0c210350131901d80901c1405000700c0c603080940301d070010409080603200c0d50000684a140c00c03100e009426002400700110a4034007030309040865551152141d000c5591449503070341e14140108280d04810080c0c0324100341c0520351012040025209001084440403251702e031154885208101c031032106c40c03000602c18107414034000c00c03c00e1244000f000c0440282800200080c80d01c011542403c000c03190440300c0c0740d441e010041145054894070000000411381a090000903964002d1184181c000280c440c0d01c04d07030310701000ca500c000e003c5098446001045001801c008102620492058501a0142c0500780c0000e41c4810601d6a000840da0280e0081000a184032800c0d560240140c042001200b4100074030f44010001500d80084215030000111107030031040104c900b1182d000c2e02c144100001001f012002c00d88c0320041d41d00c1e4a802c200288920349 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 887893534 1250 887892284 887892289
    0x609070c110102100e010603050105090d020a03030b01051207030b090108010b06120606130b040612231f17010b04020c060f0c0403050703150507141902010b09040807140a02090103020609 82
    0x72541d000544d0540c0c00c2819400c2c4281c8190003404c201c81c07140c0001e0000340c172410510f0ba1650b000410400040c0d000841020100b0b20a802c40d020040e010705005190801c10003c500c8038520485560010a4035036040e40301600342401490300411252008000c20101c002c0010741c01c2c45400840b9204c403116001003041750740e560046408003841c4507080d0164030b91b0350504c0c0c00390342c0151240c000441c0d0082d00002d809a5103000e00f032403d0118011080b8880800d001c17940040d14098003207134030302c002c0380c0d0b45c1c5010103030081511000d0700c0c0079074168030400c84001101c2e0035180c2001481d40101d006202600d014040040d08a40004e0030b1f180d000059034840141c7d2606024680c0050700922070808004148841e0f000302c01030844c8201c0e803d10655480c01c4040d9120545403481c280c1c0d00e1403c204861a40b0752a52034988070407040e1001180c0555140c00062044600b502e0603540102c000401c1c0c0300300030705030070001446000300003e40140c0b00b41360001010082c0c1480042d0140d44002200b5056030b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 887894784 1250 887893534 887893543
    0x10219081b0f0307030c0b010605070c060507030e0406030b190e07060c1a0c0a26060402030c22260c0616080703092123070302060f120609070c110102 66
    0x403003001c203e948880803402d00600308004918150303000c3c00d000002164042c85603046500070f9400c044849100380c80d2150031181617100e0341c3c0c154100841038a103641141da03140203101c000c501a0b811000d041c240261a1040c0d01d425060300c2103168a005000892224046005011a030305070a003210104810306000348621525003103020382c00d00080400c424010854003804045c0c40e01c2c0e03956424078590300f110b070030b232501d0580341000e1003180c080009080389495001103501050840d0f4281c241308909003248203403c40b0f0b020601040d04101380900070000c450101103001ba0840c0080d40003036032955500303a12900a494458011000094040111aaaa480310800d940c1c03001c00c40d5a502081d040c0101080043c0c0900c0745040005c01907078041810b03c107035200c0c1070f9420000c1581c10407481d280f180c24031141200b070202140100301d000800b590300e002c00780041e041401c0901d540e43c14000703030190390391030300a02d081d125014040c14861025840120031100c2503000610503188850200141e203031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 887896034 1250 887894784 887894803
    0x2d0e030c0604050d081311130b03030c06091002090a0b0702010201020f1909050a060e04150e010305100c020d0c08032a0c0601082b03020d02120402010219081b 70
    0x5612070502803000300840040c944403c003801d0341d14850582c4851a8441c01c1301220321001d4816104901281c60501c0c01001801e6100550303080064a0700e2074901081c195005003a2145154100e1410018220303c248240c544407240246e08624080107240051554001400350314001e03030000c02d200c0c0840e4006d5049982c50183c001119403660002c0c4410644850743c4084600015a58500040d080c20080b01e45001d036901a1200301d40052248140001000d80780e500c0c402d5440d00880000f4001308003007e0a001c0c6001d9806081240c00780c0d010302d810f64007901c0c1d092007150b01208002c9201907200b144092159444003a031079803607ca22411003208c42c080d0700c0c2c001c65004041d2801050707407034510091840f40c08080584c1c0c071f6a030f81c428002e52038000d070040b000480410620489440d51201400e20340004c0b09041c0141004c003084040c0e0200e821604a0b250408134500c00d100030b40da0100003502a0b05512000238403030034080e81d070b02e0000d405a4000100c410030f141c910780c01292414041100d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 887897284 1250 887896034 887896057
    0x1905090405012301031a0d03091a0301170708060f0901240602160803040506070f06060308090f03011b081008030c01090b0705030403090e04020402120a0c02012d0e03 73
    0x141d58682801e0103e54102040c440d24007031011810306525400390103006419800e0000904070300002d4000c1c46110340b00e040d821820011019004030b5511111220408000600d149558896040c0401081e028865240040e02680004410803a1803000100e0070f0b0700400b880300c11101a01c0c2c2c11403039400351400c00b0303681903030901e1000d4940640b09500520030446255034211050b4000440b500500d01c000c40c040c540d260b400812046c0301904080700140314040c456000140e4010064490804680c216042102c00e044000717600509850300c03090030051940100e00800c8064a210b00c511303891075101643c0c5040c044140c0002d921450743c1c0b08000001c00035401541c0e0b4a0b00340081d494020071070707114210703001004000441d032018842e41c2a42d10071585900c0701d01005041075484c110700000100203da10035003c0194400c14000c41c4003036405941c0d248008130b120408090042e003500c404680154000119030a0070603490005d07000544800c082c280006000000d1260743d81c258801e01d00342c0320 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 887898534 1250 887897284 887897291
    0x8030405240a0e191409041a150a0504020f03060909010f061e06030504230c040e10060915090b04020c03071214040b0324101214090319050904 63
    0x151031a8000300c003c6802c000485080541c8582080c1036038461103140148003030418622244212401c10011a80e0818060700211004c08075013250b03c00310060407508072246100145910b400d0341404003106014082c122000d5041440040c8105280e00000b083c1c50f01c62807102c0040741443c8000e61140c108105c4002d028445c070760b00c2e44491602c003564400c2619001c0d513103100c0061014442e100d03c60090398400810065420408100e0441d9041c51544030083e0180340780001c056580c41c4503410023041440c01030300c0b8810000b04950200d49242d0300c0040c40c142400f00316440b141140c125a0190380010b080040d400248101060090040d652000d899210000c1d0710030a0000300e084543d180d018960305e000b0500800a01100c240c0254465200341040500101d902c0d4070f1609007520305441d42e00d40790030075100c00500045c84144100b0741034010400c0d200e0f012011080c40d01030b501359880103d844280034200001d42d644e0304d1244101046003003125580111009206004840c0410001013050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 887899784 1250 887898534 887898547
    0x1503080f04030b0f0103081902030d150302090f011401050708090604060302091c0b31140d02060108070e070504090e0c01110604150e0a0803011e050a0803040524 71
    0x49029401800141c0c2e11451420004a201c0100309070316051b25406010181420441041d20303c06039440100e50040d80024480c1d40801c15451203841204020303086402d01c0e5903d94014030035003144c064404000c5011500051000152091511001600c28070300035a443d807241c1042800c038000ca007501a40020006000a40c0342d40c550060300c60729404079540305007081c0c0745100b107111109003c0020002490700c2c0004040c2c040120a4032444d5081500340d04440b4443c0d9862100b000154004503003005041c8416408824100288103408410380000c00255040000c2030f59519101d1003a11a03440c070307480004e0803030381c0300c1e005840060602010512550a0651583d0380758445285400d0008040307030b001214219001075801e01840d00100700740c58040308145a20083c11020b41c1c421601d01c940c40c000000241d921004500821103d2003080c180301c0e20b211011b5030f51400d940003e209107042e200500450101000f100c0440c5c0d4121012800080b0a0002e04500110030411234140d06000c00c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 887901034 1250 887899784 887899807
    0xf081e010e06041508060609060f0d0609150903050306042c010c1d062a0d0302040819080f1602100e090f0108030a08150d0c1d0415150308 61
    0x101c03400340e501201c1c103024040d55585408488880d602c00e44811b40d1000002c515203003064407003941c1050014000501074028180820f10303c1168440485090381d0f100e40c880e081c03084850f40800b0440c00614103002e41341c01030b01e0050090002401d110b2240c1c0d0780c0c0f1880100a40c50317104804198811420410710411607804072402810b81c9002c0d80d0120b589404240c118200b0014009889500101014100040a0782d542016050310189d0210300d010102c0e000e00000c000c00440342d012503d95405640c5c1c505003000903042c0b850b840c040b070a10700d402c1e450041c0081c00020a84000c0039440c103655440360803010161031000c00c200c1003c0e4010b5007140c446200c065001c84020f015213029070b2884281e440c0c0c40b00d40403062001f44600a0a50401d000c1d180c0c030301d441801c21940140c01c010721002010082000294400c00b84503003203440d2420b1400030070201c003001c100c441a50007010345401c401d1609481d120f40c0c803069034251505151f92151040c200c120010500e031f02460308480e01b1501c9d514008103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 887902284 1250 887901034 887901059
    0x709050c04090507091a1c020f0c150f0c071b090f1815110906180a090203060901032312030712090c090b060c150114040506010f081e01 60
    0x107030002c118100000152964002d803011821903054900496945c070304420514240d41140e02c1091070800c20380d03d00d40111080740050549642a544040da49111100d00285046441d0240508011060301080040e1684100d60340d800603800e0b060a03a290180c0c5041111b045007190469880014400e0111b141e05080e4081000104001e0082050050505035494000c1030010010b0000e030080c00c95880c1c8244c03d070021a40030091340c4c48070b41000300c190005541c0b83c120500018030076520224284072460b000100300001e280501e42189141401404a044160140806400b10382c00b842504100c008401448402c4100751044d1511030680002e8080c1030b90042d612600014004c2e06603a5180300c141c498111f60030f0b0301c844440002c91401039000040d18031107450030360264041c401c02c2e41d130b12010301c1004880c00c079060810510b50b040c80401c003080ca0360061820b001e01d24010400002d40d030090080311a445107420450b079255900030940c3d280714148054082078a03264000000d4103c10b018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 887903534 1250 887902284 887902289
    0x1d07090507080604050603120c030409021b01050f1524070501090606050316150c021c061437020d090b1803040608041109070509010e040b1e030709050c04 68
    0xba0348011680300c500421040d2036040e20702c0307a4503401c10000e442005648200505851500078281d9080c2070759000e0380c6040740c00101420811052040340c50001035000e121b035550044010b0300c40e00b41401c108021243d100304a0103100c0c050000c0c61981c200c4a094134aa0300c03001045481090340c1d0f2881d51a009000c3c0102e03107011605a0b04014000c01c4c646808201c0b9118112500440032019203003082020b428900d049003001803040160074030300561135113542244041c112140b90300c0801051f143c80c45c215030b0b40c48048178407001800c0500240000d004100c1e409103c103c00ba29520114040014009141078080d04941501c005400214600170390402d4180714042e84080d042a41d501c024142000d50400900c1102d400030801840242e0181d802c55402a0064030582d40240400b000309203c16810340f407010104001141e548040d683c0301d08864401d01c8151014044a030403800410f00c803049582041c6400d2030b14820354110f9480400100004200c04442131005007026040c50f01d03168400e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 887904784 1250 887903534 887903537
    0xd02040e010b1b0106050127050d080c15040201170402011701080a0b0f06032806051918050601050d03030e0610051009080703030503041a0108011a01030e0a061d07090507 75
    0x104201040b83c0d040c4110340c11600c041c0c54100200148000c88100c403c80f201030341615826844c4045403a803911f80c0b044000034030640c0f480d6942c98000286600c3c00b000d0008a0403000441010040140d901c040340009281e145a40300c200c40e1503c0c0300580342031000c02d0070000000348400c00081c40e0100052840c1203a03028061112054403242c204070b00b40758040342c4032034040d40070000030750514004406460700c864440200b00c0483d4503d50301c040540d001030b1640d400d0300e80c01e8849a0208030192040d0141e0344195585082404469030340c4a407100e905108182c407518107900c03103c0505000ea0403400c2c2030344c40c0b48207881d904e1512200c20700d0070b5a244e01a8500451060010141c864041e10400c016520341700b004007080781c5995400c48507603200400c00c403000c20031046044030031014240d172903010b008801e002042001d401040018540c1ca0300321150704241c240402c1c40c004080128050a0791038011502182c03400301c1000034030303845030000084409403081c502e000614403110303400180a0100d0b0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 887906034 1250 887904784 887904817
    0x305040e190e0c1002030708090f13090308061f020604080d06030c0e07020c09040b0a020a114309020706060806010e01180207020906010c03110703291b0d02040e010b 73
    0x7022603507400baa5000801e480c8041092181d2481d0801ea42206240000c1c8a042f00d108042d0103207003540d43d880d404a0108a60409000d9503142c020911120000540701041c814901407400030b64512001d00050030b000c0e40010700410320203150b00858040c5800003038000c03005580d50250000e0700022907000c4018000d10380e40d024980b0b051081d41d8080c2e41c00c8011300c011900c52030042002507000b000340105101c3c9401130203100840607c030b62001c0034a11104101c0b529465017600342140c0d04440c0d4810400d2880c5546500811740c0d000000030381c1d45000c40142c40d40300c0ca2a200b4000e10b05504889180e101d008000a81c148020061303605940400e0413440d6a1101049030b41c1c00d0707008070700e03000354040f4280c0c000030019481401074426460107032508507224650031601d1404c200250f002a160710030101010b0364035095010728451a8080ca20030b400a0345000c290300c004a468903a10000f03401c400013040003407805070740c05890141100001d15400343d6540e201d40d1000384c3c4030507a5a05400034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 887907284 1250 887906034 887906059
    0x6050102060106170c041206090204050c09101b0203010510060e0a061719110c1204050306070c0311010510140a0b030705070c1703070312090305040e190e0c 69
    0x40461201d048075100c0d201d96108030703075248140113400c0c0000c02c030359648001400001006403401800d440d017140a0b4500080d1182c0301d00501c001d4500061802c11000002c01040e070b030301d0b140d00030100c5980401b8900744203120031624192020402690f4040d52640c2030109100d60170914085040894855071070300e0710100301040c18401c0440c11803040d000440c11a150a038020746014138140e80c0040e00722403103000750040180400c1102c0500240d400074034408201c803202000b040000a01408041c240103061030300d804c0000c2d541c1c3c1d80042c5103078100208130345d99008050281006006001150009000c2c61825000d141b81c0c10850303110b02101c558600c40c82404a08125a40b0b5081c0c480b0019814610380e01e00d031081c0c61703d9110b0310040b5101032020400140001c0e5000303100c0300c0485018003030759030b840090074014003400e4030917032020803189007000540002c1d802104807811511042d0004441e5274032000c0200c40c1f0358150002072006c50a0821300000101c0c04103403480311a00842e0601000c12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 887908534 1250 887907284 887907287
    0x14010e0c0d050606090d0c05010e0105090f060c0f030316140c100b15030a02030601170115030f1d0a030207090b09060418020303160b0703050c070b1b040b0409060501 73
    0x6890620300c000040014030103a03209500031992203440a064649825404004100c1c00c4080010540707010314401d01c05d002c95030344801020030038442440e1680c144100d4000040390840380b588d42d140f081c14002600302a00109002440003185440b0949403a85400c401040e624000080100c1c000707040c200032000c08a0070a030944814840704002050427140e0600108024084003048a40c860104500d0390344040280d001144980f0111401503100e061100c00502011141d9030110f00f101003813001403010a07403e295071141c00d151460085011000d00302c00d032000300350458110902550101d04014803c00014001030603600c681d084402255030384900600b100d61443d43c6540c1300859101207440c510381500800044000b50300b10a654460311382c0020f180d6031000200c3c4407441020032040c410f01c00d20844042e03020a131400d0911051070b00c0b904d0380d45e031841101c0307004002101e010301048028030605020504540f40b1081c05a40b2a150804002240c000b8070510314600c2c282400442d965 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 887909784 1250 887908534 887908559
    0x303150d0308180304120614072a020613060c03120606020a021513080d121b03090f02060406020c031c02030901050c030c060406020c01050702121b070e0403031401 72
    0x15a016501d140c0d0a499a480d0741c200141d40d4043e03c26140310074400400ea20343d04840c2c141c0c010307118034800280c5a5450f44451110701d40180b5800c20704c1010311054080c001e4404a400010103000750313019446903d03100003100d5020305142d180071622480c03004226140c03c15414400e050082d21030f442d0034100380c0407003c281c5281d40a24401030b002540c00000500740000100c2c200d00014500a081409600f80501c5c1c542c0301d07a100c0b40b40d6030b00000c00041c405410800024040307035001418000603c00c020190108880403001208140e60383c4075003002e00410402e04080d16600520656803990f445070001d6584401d44002d9100f402021b44030600445c20600c0340e42d156100da0091828003201d58015901a00b103001c02e10118081003140380350010050103024481d80c1b240e84010b0300c41444c00c03d0381c1c0c00c40380300620841c20b550240d030b01850403900c941c0a890764007180c030305682c042140d510f04040c00e1000b543c3c0b00720b14600c500404c3c48100760301034010a048150f844c1141c40c60343c1c0c0c0c07032a141032324 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 887911034 1250 887909784 887909809
    0x4053d020d0b0a0b0f09030a050a030314070201020309060c0a02010b0d0309261e074101270b180301140f1303140a020706080a0c0516061805030315 65
    0x7190300c100615205c3c0d581c801c02900d0308101c0141030f00d800000070b45a090602da41d00714100d0000342d07160034040d40000c4d00700780107030000102e100841c03c1d8034000740100e0b1f44060140404a6140010507140340b40303031007504041001c01015040c44051421440d0250031f99125016003d04682c190358955601c1290950802581080038010001d101c005950800c50383d085020640d03841c080d503d400301312010348107150450610040c0000090031405081d0740a0360420a01012031105540006040c0c1d88c0d00030b9a1200310820740010325060800e80d44038180111059006000c0c040c00424040b0715030b9000c09149601100c10b0f0020f214460060030036a05a0707204561200d0118803138804140481e84a05c590500244039080190503900c03a84a81801500f056803802c0042e8424082400482d50042115403c0005000f00780070b90255000301600d02d020715580200c20000c006152400d00900790040340c90790502900105620a00d030801f04e03181d6208032503d0b01030801680703a8940030300701441e19024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 887912284 1250 887911034 887911049
    0x607030207082a060304020a05090403020318060c060609070513061d10170a0b0901080d20030a031e0e16120807080d060302090c1e0304053d020d0b0a 66
    0x240c002c035a0013009401d41024000740d800c01c54820021465440d202c4520380198066001142c5a0224000c0b00d1890482c90190500411043c0001c1d00b0b503560002d8116000134049610620540e24441c00b1106409805041c2254060b06100020525002004002d040e143e041c03692079000c0221050040c000403d003c0000002e403424010295110407442c4070360000c0800402140c00e00308000000e000328001e8000920507004400c0c01300d074103504840c505180190207502100344800c800c1e0800d80364091101d600c0241515032171111041d01200b04030034281900c01000300071411003280c001c0d503604441a9880d00c4080019000310300c2c004454030807400c05038060803007898500d4a070798840300340d081401207155072601d401001c0b00581d640350300389101e042c001160b191a10344400200081d140b0078140e0300e513044410414070011800124000101c0c0214403043c8490440c80365a400184005148509039210f10381d0800300281090b8001308050306010105020f180c580008001c607c000ca0300c10040b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 887913534 1250 887912284 887912353
    0x6090801050708011a16060518070605090609010905102606090a180609030e0312090906100207121a07030e101e05090a05210d0b0f060703020708 64
    0x45000044034403107003982c00c0d50304551b0424401461030411002c1900c0c08980c50b90701e80342003040e045c10764026605180d00c1c2c60300070b041c1e051902001030118800c104240e802403000144038800d603402840c61800501014043c60701c914241e00004002102c980401c442c060130590f00c207041030a04220f4640505002800c044498441c40d035183d0051158034940c0400c0c045c3e10952b003020a11520507000258000e0b210110900302c101e080504041d90420320100040d02031254441c3ca071076201c1d00552100c8180e5400b0300941c1d00c240c0a038513200c0b241c1c0c45120494441d0900c2001c00a07081148016282c00814012082c2c07a030180940c20f40f9050b4a40d0300c0580e01030719841514903000e030411204108001d084003214400d5070074250940c1e4040301c0001459001648070000c003c801c2142d84280c00c84e1201020301205290243c40e01480b0340b04800703940e0b9454100c21800d0341c0d200300034008000700c0205050756907189880e0203512040684151071242c05004920100e00c40b084500f201040300240910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 887914784 1250 887913534 887913539
    0x506010206010e19063203150109110708040b0c1005161d1216050d02090109090312020a11010507020f10051909031d0604150305060409080d060609080105070801 71
    0x30303043e90708030861540a0a40700c60340041c039124901c02040740c05102015a2203992416031100200340d1046c0b058038003a80c030107010f1019131900020b0050544801040c0421000001e05040e4818000d0200180003800001000201c0a00500040524403140030690350081d4028021001300c51f4103e4aa01c0c4450058150185203446420f0942000c4c000341114840c0340c4010020030005c42018100000d039a11101880881911883c1034070000c1608554440d8101215030204290060600c21503299944a4014804042c01034009000c0b0440c0a002151141e0030040e0040c42690701031500c0089528280214081610110758000407542c1070000f42400c44d2861000070041000a01e5190020000103a10f03000212600600d41c01c10301a58a80d4140703003d070800300c0084411659040e02c00c040070401004030428080016600d0030080c01c1c00181c07a96141c02080242001480017488100000394900c00300829a02480170341d40f00d55601400980c0300e11242e804c844d01910548041403108004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 887916034 1250 887914784 887914801
    0x80f071a0421030e06011512181b0e07030b0f0d020312210c0a020708060618091603151103150907020307240c021b040c0e030616030506010206010e 65
    0x1d4800e03101c4249800200100c0c2843c901d81000300c2a0807050b01410b43c1a200321440c0c1d0b0101158007031420706801081080c031111100d03040803075800707401800d0b408034104a038143c0340e040c543d004c001cbc545814164071510741000000c00030540c0c4c1100171300c51600d11130510184d0500c8010340c0a050382c003800908034280844c030508001e4212490070b0500800854804050204000260f070080209082c0316446625010001c1e04044640c0c1010106038064801c22520b6583c2c06482c01e015070031100c0281e52a103030300104900700081100440c400f503440520020030841508007a14960001c01d8041003103051030000740d8910310060720703105182880079440c00010701d01401440c1d0004203600499141410940d076600e80344958948207030348602810304e41c1900400350301401c0340407200d920150021117a500d01c0b81141c20b500e455140d01645d43c8200780382e40f0134014510081c3c80c01000b81102d81c0c510304214818040c0f82203001d82000641031101180e4594000116503042e1940800d000d0190b0351242d40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 887917284 1250 887916034 887916083
    0x906071b03020a03030f0e03070b06330706181a0a020a0e060a02151005190803030f06040b220b040615050d290109050a0b09040513080f071a04 63
    0xd0340c01044e0b6103200107c0301032000c100905440d0f100741d1540741a4940202080703a0a01c80032020350b803c0d03e00050401d807100d0701186604141205000c41c1c0d840d4100740c1070000c0141818a40303284560380e5500c940060041d10310307034094a4600b1003941c4143d0b540368198101a405081c2031030002c140b01c0c1c403003c10301c1c1c54198090008800319204032001000030482183c110803050352403002c01144154144852f0401c0200e05030130340340e4410211401d07803500d0700160752888010040e0000088c01c50200b046507a40703400000c441e90b0010302100c2ca62000d50608212154005100802e10b85000c14000050805015040c21640d00e03e188084105051106880c07903440b9190b01c650090f9100c20400300b100c010343c4606c41c02c0c2c43c1c042c11103061000010000d00b15032480d401807031040480c90820020b0800010031181c4404050b28086410384038038400342c02007510721000400507440401c40c0350000049401403c0300c103010710551407514100060a18101d0000d0b100a04400811410301804c00d100b40d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 887918534 1250 887917284 887917301
    0x40b0915191d030d050a0309020409050618011404080702120114010f0905061921081209060c0a12050402120607031d010b0307060c03050d050906071b03020a0303 71
    0x5250360701d0140422114031001c00e150600d40d012481000e8802e041d404042c000ca07000d0a001d9004010000740314070098241d0041002120801d07855503802d00440d15250492001c01e580201218903d090112255903030050b40510b10b40c10358a0414842264550140028069504903640c2407800c680303a020700440750300328480e00301550348804080e100c1a0381c1b12401c500030016001880402800d0445e10001c0e1040a0855442560b180185c95080d50f424408501107030030b140c0d003840700781160500203865692080c0020b002c0d8200841c240000300d0b02c4400d860711601c4450260f032295034a03040320781245e024801400c1c0004512520445401050360700c440e0704113000914210340070030071942480c51300c0030031111000003e481e00040d110f4181881d80d54103121007910000d005004045000c0b07907441c581403103850700700301400c0015803d06004030111001d89020031000c1c011450001c02403942d0b401e060307480e2400940c00741c0c440010b040106a0302c45116134142e014090b11030030340d10100d01802d1503c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 887919784 1250 887918534 887918569
    0x1050a030b1e010306021306030b0f06030709080105090c2724060d09030e01030e031204030e0307090b0a050603190e160f031505160503070201062106050c040b09 71
    0xc821103071001e0702c4400103000b18843c05001d40d682d1186114442c80e0461070b0b010405241c18000c0c1400103980b40041c0b03c104007070590711141c881da940b80080310f480140380d00c0889154a00307402e0000341000404c01e012241c2050312009100c0e0003110804143e40203106024030ba540d00c07040403410340f40007403481214480c0669008010305116000041c603607407003101c10903030542e95146080101a0000072240c4902c0090800304640301c002e01c034440d101d118445000034030710210300005040602941e00844c42e4000501110109e0751103144400051030491803180c4030350898800005ca0313142c6002141c0c0710301c0718002d50840085000c5040c0020f041d0082c140780c010b02503d400b201101d0602c010a01c001c100001510748980d02d90b060a1702c205495140207110281043c04001104e04024444011101c031440c005949581e01d600032801000c1541260070785010780701e50218840d0b040103c003031009001344030400c1142c44500c5d41c0201ca116503c14850300c0c500c140105403051810b600100c0b04c04001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 887921034 1250 887919784 887919811
    0x405090a0f08090f060c03190207051c0503070b040804031509020a21150f0e010603120c2d211407061407030e0708011e05060301090b010e070e0901050a030b 69
    0x15200001c5c019040985802c08a510200d00901541c42d203226403c0c02000c6400640700540c240000309865107001102040c0142000c5d01500810908000b100c1c50306800c1400c19816003441d15184501c1d620510040d01c2e44007100035401f41c4101c0600c01d107610b41d980101200c81700f03441c00209030385042c5ca08070f00304c103100c0c0c10980541c0821241482250031019503a80029450b403521a00c40407101c5203c2e80000c5d9070315080d400c0c4006000c030709602d0f98008050070100b01f130400a20307024601c442e04c060100c03121101000e1000090100c0464900624890030a10b61a00d42c1060071114004103c000e61001601103108003030071418107001428400e01601000c540014500504041044241c960300002980c90098990008081c800d0710041d0903020000d01c0070007100003041a283c1c112081e0500b0059950020801554003584108104d5a110441e48080e41c2d4622200d4918101180d00c1ca003c1102d0000014851031f2580c1c50b14141c3c1c10081607034035140d081d03846a030340110340202410f04d40400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 887922284 1250 887921034 887921059
    0x42114011a270f06041d07170703080a02030717070b1b07060e0d0e0d0506060405070e030d0e04050919060c090e101a0901020c220c030504020405090a0f0809 69
    0x9a82c514410000d511039540e06007020710a00086910344c44100d085040420540c0d04090790100303c8030100d444802124001d07081108080e030900b1803e500042507076070001448902e19401101400c0020301650407081d03034075840841c40c00e442c42041801803882400f07500103081e09035070f00303d010111400300d11054207004066484004503180d07a41210600e52080320700d94001588450007540302d910594040c1042480c0d5a0350954541014011601c29916500007582251240140d0a0219802001c89000d4203040c40090320031035960b20300d03a003e1801c00c00018100b132000a420303d8000600001c140b08501d8035200e90009100d03d2000004028a0700b00001d00c4041d003021890041c0070610241c48400e19200c1d25100341d04803c10111390b100024810455681c0e0045041703014404140da03401808105111251461401034104d00c00162800540801c804e0b815407000d03108030b1095804000c0303500e80001e020760f916100200105001c20030411880040d2200000c0d014500024102c0840740381c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 887923534 1250 887922284 887922349
    0x14090a150b07140a0305030411130609050a050a060f06080c071703010e09010b0a0303051606020a020c01030f02030402060f160503120403021606021908042114011a 72
    0x38a030380d0110108140100c1d640050158124030f2501142c0810000c201819440d50040c10364040100081d101c2c240c40240d05d40907807241040c40d50354103180841003146d503440300120b40c0180341c203958030b042d124585800100181e45500c603403c20f0b5402200d01c101d001c2e1804808484561000300000f07800c0c20140403280009020900e00c114410f080a541500ca40c10003005010588000b002014181e041260081490303c0f041000030503250141740c010740c0c9101c0703060003e09008000d44010205840000d00500310b07503002c00c520340251801d0340d00b8800c40d00c62851040980c041500d01070740c0b0a070304100004103180d2110091941101c40c0100710b801171950b13107401e03081d6009886c07018800d8070785070300700000c0550500c181c0c0c00c84d6400001580c0702c03908261000395500c2034040402c44d0400112982014024040107640007040070003811084d42a00c410100103c0d00040c0f42142c40c04c5000c0f10320b241d100390602903116420140c814075107e8100803001c100e4542000103528110f8035210441c882c800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 887924784 1250 887923534 887923571
    0x3010b09270702060709151413090b151201052103070c17030711010e060d1a041514100c02040c1d030d0e0405150d0c030302010606030614090a 63
    0x200c401c840900503464115006400c0c848014054001c01404690a100303000c5003400d08010716501e881c000811040282800c119841010b42c140c200e040a0032000175003039125000550481c1c410386440c503110030344940b507014500800c0440846034000400600c074505011101035000d43ca000c00c10010034007403101c00350a55000040584104d0034441d0b041c420074140b1801c06014210140c02076150207000d844030000070600240790f9042021000707520300140c3c1d401007a02c00075028004104840030701e004500c0068181c0b49001c43c007030b6040c011030300400406154200d0450380360062945010140c901080301140601c071100091180c900f050f0400b584803403051044c00e024545610049001859809a64219118089109904c1050031442065114000804088041c1ca0100d0151280c210040d81e9440b404501074011422100d94001d012111500c1c41c1103034040d40003007000d030741c559204800b13036590b5014100341ea103c43c2c2c501d100b0900380f1440c241e5001116900c002038450b003070100104d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 887926034 1250 887924784 887924839
    0x308070804060201060b04061b030e0402120f100f0311040f050f070207080f1510080109031d0a0b040512010b040c050406120b1507030e0303191d010503010b09 70
    0x126010400b0320003540c0921403c009050502400780c04d0520304034004107004802d01502c240419500302d201c00300b5000c0d1941d078581920050081d0340b500341c40000447c2442c000c6540e407007907201103004a40a610140100c0c02681c0c8420f5582e280e42e4150386841e68402e810345d5030190055520541c04d10380b50344912459000e9030340c01e10030b0401e5003002d450092500419400072082c0360000006d060142c180001c03050420384003244410f03016a6031524503480c26896a0000ca065428820600100f65009800e880c1910014940d090020003503410321420b424240107081340c1c0c40f0100018401131800c0340c260340403e0912000400d00100700008282911104540d41e00400c8e000303d01800415002010080d017020310306402c20503442c510001414141c407610308086d5551001404805041c0b169103001c1480c0009011280c0e11350015088014440b0381061150010ba640c1030110040038100c050745c5c2415805954190a617400c0c840304101d941d01921540b47d0007000701961074005000b050301d4410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 887927284 1250 887926034 887926043
    0x702060a0804121e14041724010b04050f0d1b090c030b0d020409080c1f05091b100c05060f0703060506130b1804050901051005120712030207030807 65
    0x1c85040900c2e000e0142c00300c005041d814030081180c2c1001d1500c0384680c0440300c5002c2c1c580728000350160b081844d400e10075500300d02010340b84c1410001a0070800100078441003528550450282156a02d100e51090203018210400c40c0c01c010404c00b5103040e00d6001c0840304001d0182690102660b10803d04a00c3c0d9000711080c2c201020b02000115160700c12040d00f006142024025441c004000070b540101421000b4030960391030003410140b103030710415105d40c2044d4000700e88071010740422a007143c014018952100307508150000d4005000030415101d0300e082100c075081e070401c2610801c000305000c2040d000800108119040110f181089514040c418899507100a820040b00084c1901c2c0c0700d8000c64000d1008015800b850601010604101d514501d401d90311030443e030000c14a01110103403c10707400350911040c89a480b0040d40480c0c0600c0321039298070505541c407014403400580804044200390032901e000c2000304103205251301220711a105503100d440d00c95480005603084000b0955 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 887928534 1250 887927284 887927297
    0x14190912060905010b040209150703180906030c090e1005090313230f0a0e071b24111e040302030a0b0a060602061b0a090f081b0a050904080705030702060a 68
    0x400b07103c4203206050b0458025201545402da0010204007242000d100100219000180e004113140c414040b41200101400000b5803140d80c4070403500180c109400192000588d1100024501585200f0300c00b00e440480080d106400203611480000d05c802802030760f035400200070a85840c1a604041d50141030300c4500c083c0600c40c500140d032468400e0310501c0d03010766543d001901880e41d5408100080321854000762000e070b03642842c125804e1250408008004107820000d404020720118046540c0c40d0090405100311892098401540c40c90500f8203019401009001d074007442002e2108103100340b80701742a10b415601c1e40407170b141068181082da0150360b1401400400e10080c02010010400703440282441c1c10326000600461401c0381600e10045400108a0412401400078400814109500004441e9940210760310781c074044151084009941c44444460b1030100f0300c40c02503d40140400040346e48aa03140055540000010f841502c4140702d81001a40c0341002809102e100d541d585 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 887929784 1250 887928534 887928551
    0x60304032d0e04060509060d0309080a080a0f0201050c180a050928020702010f050c150901021801110c010f23090a080a11040b01050d06090e0601061419091206 70
    0x601400030909824031881c184001003199945510b01c0390307041f140854002004001521341503078841a5640220700c203004400e00700c814442903002402c0072030000d441e0302e40d409018901c124201e50044501c840000380c1880b06a441d0306414405003942d803070203840b124540c0d4803100003a1902404458010a010050300c4000c40350540715806a0011a159029400d214090b40080c3c518202c0322a001c003008000325064421180400a03080c200002e54a00c15060034805600b078040d51140c86881d104140808229103154400c02120603004c82c484044d003002e003c1322004403010b15440300c81004200c5250500b9a100a105619480070031b0348000155031407403044103110710080e20703502000f81c0b83c2180510b070740425592286415400412500011505c0d0880c1c01a07845000382d0b840201c816160242c04180194254060b10020f019801107804a0780e030b81e401110482614900a820030a0074483d031030603e4105000c080030001c041c289025072940382c04070a481e01003511419519962030b40c641 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 887931034 1250 887929784 887929787
    0x18010807051903050a0201050325020a120906051b010e1002040e06100c0f0203190602040518130308090a080706020d1103150d14151605030411060304032d 68
    0x640d50b1024100c51805040380f56071503ca407101070304074000c0d061010000001d55400802c40e2500310449581440c602101c807400d41c0207594103900602114020b01d0840054461401500c1c40c100321100c90751428586940180c600f1a60580c080e54440c4964070b42180681c1c5140a22000c1107145241100588803450814036400809020340203d004441071115034160300d500008006c8800e801043d5400300f40e0941c0302103458002c40c04070b80c80a80401400e10000c208240e00100300b112000c403591020006540a5104403002c1a42e160400012a0b5140c50020340a00206603205040c1825602400c1072501c40c04c0712035005030340449078107170700040014041026219240c2d5111481c681c42d421440c0c00900700a00f2a02031050600c119000420501000300c00d41a00c00d100d140002603507a00300b5040d000c098440340584a040c014440a20102000d5200b08207503407007503820240d40d03010504102d00344542a8000b80042e0100042030000c103c04241c144210350340d0850001d902e00905130034000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 887932284 1250 887931034 887931049
    0x10b0907020f1501050d300c0524060909010908030106260603031b03210402030f0a0b0f060111160f09091a0c160b0105130c08070e1801080705 63
    0x2401403000c2410014003140e00c0e0b1010344408240c2c080a8074004080301d050a1f000c218028581c00c1c11658403500102440b5070184884405030b12a004031001c0743c00c040c00300e24803503030304500c03540f106854003000500515080b80d646401240e0304000052007101a04c480d015644241c00c61070200d8030801c50507012101403001c0e4030040300ca14168640310f040c0b601c000313900c91048901021860040340d03075544503010140100da041c0c003201d458910000c03045210f604602c4108031000e034800d0141c031082c040d1075107000c250b54001d29032045c006091036841c140d5031242c60401801440c10003d40071152480c3c613030200241c5841e01012900c003400d6910f40828a2004c40c400c6d081606054100214100000e800c42030741320704c4000038144440d242c0c0c0c9105040100b4001c01020503052034004007243c051082c00e24074281650026120451250240e024070402d56070841d41440016034176400040945105206585a54a0080150f2054140710100c013140701e0b82030b00a0341040d001281c0420842ca80240c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 887933534 1250 887932284 887932303
    0x504061409150a051008030d0c1106010b1617030906090c0f0303070602161505060117010803030403111e06180f06070305060d0f030c0b0a1b0c0203010b0907020f 71
    0x2000308503164182ca0b4495600c01c01a1019004907116400b0642100c2c220100380c0140c8440b1040b00e03100c13844150040040c02d00000020080383c1081803940014001144550507909034682d0f040c6030001d118081358032440d0f401e40988096481d40404042c00a022005500030412000144841d08080700071a06100c604030303520b88500010000e0300c1203078034080182c0b40c00c88e401c40c00050300c5581c0400d091020001c8443c1c010003142e510180008800050b50101c0d010b400281da6202083c20400f13165159104280a001c04036072091001030300080c0300f0310039680f2458508054403119441710540040102100c036171941981c00200402c104085a90140401d40282e21700070500c01c2840c94080da02d03460003030003110400d03480d8030004001c1d44410355808002d035400030751940c182016040003040041c50540440b98111071401042c411120b60141e2a03c40ba0030918180400481d000c05a548607a4040d049806548814580740c8680e41e0f88099403140803580c020f40300031006842c0050a16244c076 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 887934784 1250 887933534 887933551
    0xb090f0714010e0d020910080c01021603020d0c180605010e030309010c020909330a0b0a0603020a03060b03090a050d0c03080103230106150306060201051506070c030605040614 77
    0x55408009044a18000700030000003030a001200e101c0e040c010895407102070300040c1d002440f00f070621010080e0345a100c000c648902c401c0d5401802c46500482c1c64003041c01c4200a1030040100c1407000d49065001d84070395070b21480c01d61450310b540d0241e80c51846140b041c00b2000c0c3c2d5440004000c2941c11900d0222000c4040b000f031880c0040c6840060035012415801a00455140c2c0004040c49410445000c02c0c204017004c1070602002c1d03080003048155140f040b410022002404070343e407080b943c06000351b1400e0003003074108502d00b003e40850081d0081c001c81010980c58000c00030b88501814011400b03200a40054000300c141800d040d86048003150540302040260b0710340401190340520040d05403075001c0e410011211114401e01900403545050461952074840001800701c4c058070142040c4100c2d44040c44401d69071074041e401c940d02110340d20003001d03807012965018503000c0d0041c000d6900c2448240101a02c2e51501c00c01c994003190101c8104d6510050003550480c080080b6501120390b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 887936034 1250 887934784 887934793
    0x1020301050a12030c15150b1306050a0309200103061a030604020a05091801030b13051f110a0305010e1003050d0f05091216090b060a050d090804030b090f 68
    0x42001003250400540b00d1200c072a4500034078141014805c0603041c0795160400c21001c020b01c00341042c50000c0180341a4055207416200000880c000d990040e52034481c101c02d40c00105c145071002c203031401d60240b2103100405554028020000ea07034102c4040c8415059903200d80c1500b000301c0090210f40300364120807916240e03c1d4421410700c2507907086a50240003600e0150300c0f42c05a40042e5581c2c011050007a5200021989010407000802811412240200c0d0650682c2c2c440c05002e0088006401001d01190818940c1d42e00d004c042c042e800d03006407481030000410381340c20049000c1642216414200203610380d0010010041d14075010742e080650714a40031415451030b07441590300c91484011000340702c6a07000d0820014060b030705852844401900d07101e85800b1040c1c4550f2030b0318035000c03130100c8040703026400b01307000d1010304c12481c1c02000501490b140044d030400c180d9554002902142001c0d4903400e1480004807142d024000451280d44402e849007403036801b047c02c0c25101046100150311 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 887937284 1250 887936034 887936039
    0x708030907120c18062d090203130f14010903050415090e010e1807120b10030201080c0d200d0e0a030905010c050114011d09060702101e1a01030e01020301 68
    0x1414180a0844e0340d0045416804c00c40806244050052684181c07070b690046908403180e0001c0c81c0d481c410940c48003005544064440c19a40b00324003050380c01404040051003e10000f0361903013108040c0e5805003c0884a0000c408010750030f4921102d030031800a4004142041802d40051030300b0300303150041c10318444203418000c841e06843c205200d00500c030360240011545402c0c0e248401c2c89000001d0b400e6485044d1900c24003900c1a040344421140b403d01e00c40041e0140f545400c121080c2ca41c142c2d6a0741309626504031800d141d4004a02e426207465441e00f25610a484c0400128460441120005c0c0c803144000350720400c990720403000d4451904500d805000195022240c5025070b402420010318014050030701500402010300040e084084d000004900d4000060b849400404200c2d5590b8469449102658480d6000d9440e2405a440760310701c01c0118081d600a40d1880ea00a10b05914010201c00b840044d9010018000400010821043c1540d41d250141c8642d251f00207000f90b01e55403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 887938534 1250 887937284 887937293
    0x3070f110a03140d020c0d090f0611070311031c020a031e140f040f231e041d010c0f081e0a0b040e030714070e04020d1214070803090712 60
    0xd0a060318210a030f000051100740206641c1c15194090b203088101c421003030007172401900002c0e05020300e0500c00d140f0100043c00c01d104070748020030114450041d044203450755542000c1800310030002580f502600d104100f080c805501a610303030301c0b0145d0080002008508004c0c2001482d601c5410b03106071480e98450501c0c0e0040d50401c2d188280110995480c041003c60340380350f0099801543c3c01d402ca2030400500f10702540f02c2031482c408251410760510303c141c0100980c1244480800d009007040d54040d40c1180307400c2d88024043d980783e04c0038002030342c0c2d052400c600711003c80f0245c030b0200e2003140112041c4ae50166215510001c89110080c0400609441c031900000007000c161040b502c1d0880040d06844507000144000703000011603841d415286081c80c480303c00400e0210180c46400c1000a0650122103000e0241b0b4000e0500e481c0105a034440c07035000086c0e084c106091004d00d41449030400240002417061900078425142c89040042d882400d080c8903500c0311500e5850b00e4540070109 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 887939784 1250 887938534 887938547
    0x13020a0320120405190507050910120312021b0a0302011a01140f040308040f0612090b0f04050a0c141e030309011101060504020a0309050606180c0703020c0603070f110a03 75
    0x81c001e10b01c29414554903490140e00d80340310025102038240d00d43c880e00080001c005860019280100c410807055540c801c079108400d5800c0c400c0083c0320307040c00341402c08207000c0e5a502e51070075102240035140c807000001c1c28400400c0d03846640542c0d4840c0340c080e01131690a101d800162484000703c10520a918000201132250307003010185810000200f8101107a40311007164011540701c2c03440b5486030350300e903845c150905452090710042100c1c0c80c4001e540b10041e10804c0c0550f903000e20b40c0d80c43d43e25003910349444884000c0045038588138406440c0e0104400d100c44c24014844500b09000308603070300c000d00a2a021042c9102004804001080c1c542c0e5008402d4404600c42803030840c120481c0c0c01711183c098031199000c2500144001001743d00f081e03154110a00181c0100c0407101c894442c202440210306441d8000110321045030041240d4241110003064401e00030b07c100c54801125800050044d40244c3d480d1002c2510103c40b05002508400e249045550a2000d0303ca100c5254401a154 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 887941034 1250 887939784 887939797
    0x60303040603020f09040e01060602070603020324010c0b090309040b04020403080f070f120e04110a0f110a020301110c0c18040209180a230d05090f0f13020a0320 71
    0x245600451300d4401c1e1807aa00544190401c001c0c0203201204111300e5103402000326010381c000501030400045101400381c02100d000300b043c402d040e901c0c1c5071413030014500c2c203800d020300d181002842164030002c43ca490031200d01401100015580d188000c0041104590318000c1480c0290f005100400110350914280c81c040302146003c00d80e2140380785001000d460070300400031702c00c0007026624000e8540c00b48243c992904251400c112004d03401050981c00c0c0191102c02001030311403122402c1942c41102701001c0d0f14071307420494010a1f01c42e800a825035030010f102016030440860303a002d256404100c01c1190f0740c42903074a0101f003059107849128140700184040d005140400c007090046040400c40d100700342480302078400d01c030010326203401e03580c10040c000d0a28900b021400c4010002c0845c18000f25001c1d511030b14600745580c1c0c180400700703008844065002011030519102ca413114510070101d25480d00c001641e81541000150403a89000d8410ac0f828000711150b01e111504a400c4501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 887942284 1250 887941034 887941037
    0xe0708060609070323040312060e040f26090a090213030b0c0904110a0806040b131a061902010e0d05030c1b010c020106080606030c0d030f03060801110910080603030406 74
    0xc1070f5039644026000703084007500003c0b40c440024012100601c800d000c49010700e1181d5124005112220050801d40e0014007626184220101c041000604003060108020384103500140900b070f820b207141d044030060384129140240c800108070340300e8640b8414120103802020360031800c0101c6400c5001d0326040e1030000509120212012814480841e42075030302c480802001880300088020001065130041c00b07194000c142d81c00c022844038602405107004040d809031a03030100d08001840a0050150403159003118041031403100003e4a64400400181c454003001d04030700010480001c0c2121200d200c0c03e00e854024103451921264842c04a82c0c11000e510030740b5441d5a0180d080308008502102c0d00100344d031070a02000400380d010b4010307008440340b4400b030302d0960b41e825052503250b4507103208065001122407107078000603008601280310030340d80f4a4000f0710f00340ca5151082c00c42e110290b03201030140003c1140500c5103050200c0803d80847d6140800c5541018000710340e80b409503008a030f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 887943534 1250 887942284 887942299
    0x52e0e03090112021306031a040507050306040b06070b040b060108010b0f03190e0a15060b09030a03181203031d010c0c0b06031006030c0911030c04031214070309090e07080606 77
    0xd83d169281d0301a10601c00c001c50a0342c0c0020707034a02010f030050000c500c800c81ca2076091a1080702c240f4141c07040b0340c891051611083d146a541604000013400c4040c24580c0c030400c14861003000c030340d00180030751042d481807402e031115040020000d05400c005034405052003034200409100b82803100244d03500311202e2000302d002d803400b0151540141c402e80940e074810344212413454062096100e0140040b5841d031404000c503a480b1550740b58244503900703000c1c0e0158010042c10780000c0c403a4484141c80544c228284d05c0f440e072149941c070a1992042d000b900000e0f11817801c900f184048844000100748504001c0040103001a00a4801d0b02004c002500d50400a00010303055141030280c041c2a0318410b45c1080883e45929207118019400d0141481c22494400b0103043c0c1504401200d01849025450a060526640d2801c501500900d0900d042020040c903407404103050401500400307100361030301c8840c00d05140c00031007207030b400c2da401901540c001d010400c2402d1021491300d81148059a089 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 887944784 1250 887943534 887943557
    0x5012c1506031306021c0f0902011b06061a0c01060e040f030c05190302150f01030b0a201c0c0503060a06080a0b0d0f03090b030f0604050a09052e0e030901 68
    0x10f026040070044050400c41c00014064600121420302610303051080d981003100c2c0c01d1007480d403c00c944e00c0b030700000d010500c3c0e50f1402207001511040b8030701451184401080194030396103520000c4c8414407944e80b0394040030526140e0130344280641c40c007511010100411034030300358580000040c0c0182c0c014003802019003141d01400018449000080020710303440c42c0d101c1c102d290095031286500a2040001203900114416840c0d0f000c01a0403a034101ca03080040d40c903204a84401808007030041752a00700c6150024a211440314058032842c0070340342d0a0a29400d0101d030700c00031f5407015489141084000c004005855890700d00b00c4007528050714020b5043e59400c04640c0041866000199010841c0441c001c10070540707900704008548a651156010340c1e0341c901901450100707561042030303540390b440040d40390b01749607100550052205d100440c2c10b10040d01c40f6428a20741d02032484038071083c0e0300520f130740d8010b1140d094403040901004002c0c808054404544a00074003001030f04108941616 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 887946034 1250 887944784 887944801
    0xc090105070c2102011403060901171c05091306060815012105160203030709030305070221031b0f071e150203030a05061804022205012c150603 63
    0x281c090801c2c0310080240d03076450209a40300d0001d203c0c00303d00080c24042000e044080f180241c3e401000090120130300b03030f400d01079640c0c03008100e1210f2041d94482c203049550540f401d028a41e9031b14615450b0140d64080034400c1c410040c804035854020075042950400445030f110070441d40c00160b620401c4030000c6c0a000407503801c00d0100c071180140307252200400c8443c00760350025003d51031030503c142c107030a041003050f6100e010403500e400100714a100c00b0404240103800a105081c4002c0c142e0040342071901080c0e0203482ca543c4071118603807000c00d0f0043e104200321001156100703043c005100507001340300c11558500359402501252828808201c00d00000c444246011b40032038400b0384424485160003c0d40ca410440307a1401d90740c100000308256040035400b03140d10b0262500506490354468083c041e41c11150354841c003100864501075401d884031449024040e015216030384000110784003166040280600384541e15800d51024055516401c0414007400701c0140c0e15141c89030394407040e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 887947284 1250 887946034 887946053
    0xb330d0624030c0f0305090a0b0c030601090609060503010302060d0b04150807060201060f1a0f0304050d030b09010506070314040906090f0b0910060c0f0f030c020a0b1905030405010902060a0504090f02030c09010507 94
    0x6004280c50300107018400ad5800b440083e5104080aa0700e00f1061551444215803c0600c5d100d880c2c04907030104018805411306400074543c0048008011640d01c070740c41c0c0410100d40c43c1c0c45030384480300c46030b6106208690f070071321054004000b40c0c40203111140c1009440c14403500e0510400110200424160345208400c0b41503943c6041d00b40740d070301d031a0700c1e0a003826034548180c01d4655000901d03000300c0c0405441c000c3c802a06955018004504094207030794150303101e4100f18407411910a09200c0040c10100500404015151110004c00c044035180400000e03255008241c41c425101036080151101d2101d0b82141242c00301c0c9002d001195040c1010307115090703004006410100103007500800d05400100c0343c2c588a20940e1307100e00c010740d6003031004803074000e4414144802c02990268011284a50060b40d0810f02840000440550917800a070865001d1900300010440114040000d1001881102c15043c0c48a02c20340c07a61404408159807445000c0026060120115007002884290403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 887948534 1250 887947284 887947303
    0xe0105040506090a260c0a0311090a0b0604060207180b010f1b0f230109050303070c1b0830070206030711070b03010503010b330d0624030c0f030509 65
    0x6100d8091000402d007444605d041c40c04400072144190200c00e00d480c100507101e2812030750041c400c201c00d07041007420010300e4500500561031040d01d400740c800c516a0395a000300000c0c07550307800407d0000d00c0c0907222941048480030b1403512610f800c0c45031a00f070742c011285599442140c83c0803030301401c0050301c01c002410403180280c9650500c2500908114021140d819044807a416101d1b00c01d401c00d01c91402c0c4c1d0400c038001841d0b1303001440800d4065000b00c0c44003004034424204184064140c40003d40340341510340c407230000c551080c0c0313071079440518445040d040340440c40c000c54103000c403600a00085224003000240200c60010008112074442c1540c000401c0080c0141c0714140d56803248121039810a0160b14843d52078204c40c44028034016088128142e04d0800707110b0303505000c040844000c040509100b00c000c400b0441e52004449510680340582043d094045c00e018031342030414112601e900102d802e05140200c03441c3c0c1c1e5a0040c0403e840d0022624000c61196a01140740e402c000181c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 887949640 1106 887948534 887948549
    0x1203090a0e2a072a150c020d0b0901060909111e0a03061a010c0b270106060509240d0e0c0901030b04120e0105040506090a 54
    0x900c22603500c0440036600b040311244690146240424031002e0b41a8000300040d0715040000d1040e03820030b08100c4051400a00301d031040d01c000319030960300640700300448802000d010103225450a0741e0030b0340e000d401e0b000e800c4024580800d00c40b40c143c803890029428220042440fa00324070440e503090b41c1116140c226803503090140295035080b02600e10001c1d0440341c10000030b440740a18500154401c6d800010060000b40c02250f44902d6101418100b1508194440100b1100700c3c070207410040703004078098440042401c2c0401070700c0c2c41410071400e5003040030001c1c00c1d41d0800040c1820ba0380c103940c0c80305000011043c20140300000710144490b4013042c4510300b504403040d4403c014544206084030483c0304190002041820300f40e0086076000e0201c41004100300688101010701d140c0381c2896140306207480c0001c0c001e0301503401058082d910200d000301040e41c0f800c48150040150 = true := by decide +kernel

theorem cover : BRFrame.Cov 887769784 887949640 := by
  have h0 := BRFrame.cov_init 887769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 887769784 ≤ n) (h2 : n < 887949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
