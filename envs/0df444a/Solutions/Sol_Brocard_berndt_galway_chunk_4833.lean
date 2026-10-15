-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4833
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:53:09.183355+00:00
-- url     : https://prove2.me/submissions/49955daa-2436-45d8-b6fb-ad019e09f0e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 869064748 ≤ n < 869244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 869065998 1250 869064748 869064761
    0xe100206192d02040614090303030f04050f0f071503052e0801050907090614010905060f040e010e07030c05040f030609020607062d02071104051302061b01050f01050d06 74
    0x6040820242400100c1000b1980b42c1c105909a1500940e0303481c5426001812910a11182c4c0c00302e0105101401c2e890f40c0100407039400100ca414084a503454a0420754100001d0002ca0a80c6102e00d8241108417072000c20000c0441e418440514800c6207004400c0c0c00350b134800c03034115640c20343ca1020060081d60041d001c2c107178004440c03448000300d41c03070b0184e00e401c603107090b9103152556010000420248d000ea000300c00240c038404003110040c0c0c000740000717808281d20b03004440c881c035004514104940f002e80160380003071108200b00707201540d48180f004070390001940d4810009041248200b440c40c091130840b0704880c82406c08004c2c20b81f07540c885000400003254200d034000010441d62010945c140101034006482607002c0f908200c41c0b0b007101400d05440441108120700500a01d804108002ca010108030380584000c211a5101280b50b00700794a02070009521080210300f901e883d5403c00c91400e00c00d000480208800d449044420007900030900c9000c3d8031200711285113000400c56000f40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 869067248 1250 869065998 869066021
    0x1f020303160c0c06081b0c0c0d11150c010f0e06160203040312020f0c01020d020a0b0402150a05073c03020f0609010213120201050702210d0e10020619 66
    0xb545141c40c01d5a030210b80e00040d5102c280041d91010a2040c00b000048201d04104400c4405502d440b41400300c040d211940b07242c450b480395038078030704440500140050304100c1070700c01401140e0b00d80a1915440c0741303411015801e0139541c40c14103541a15601d40c03203100303120f0003081d000340071603611010344100c00004480d03801c0841c001800000001072036982000c84c1810a80c003d401400400302c0d045242220020016046511003c8400c01103a004120380075241c0d0458030845050f516800400d90301022406001c031003010004183d124a0ba108014158081c400c5000b080316900f0303021100350700260f60707410303450f035600c0040d4420200200703444000b16a41702c0d0050380ea1040a0b40249418081c040703a03e00b04594000400c40d003030b55051581da00180c000c049481c0075600260300000d01c05e000e80103000340a1408e54031070b841074454140f00c03071410080f103a003152801341d84114001e00da0200a80c04501450075580300858945c0042074143c0f140303d180800d40640f10020301400050040241078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 869068498 1250 869067248 869067257
    0x7030e030109060b0111010c210e0f30091c052517030a0f18091505010503040b04021011070b0307091e03030309110d111f02030316 58
    0x10816580c03000c0c01180ba04034000c1c040019070030300000000d0b04613010304c19680066450003114105550300b00307903001e50b00b01058649100c0b1030302d00c6220300014040724072007111038800c000111443c648000762036084440f1004c945980884044a401503295810501102042c030030b01c4100203604001d1000303042008035a40d40010b514843e04d415041c01114034402e900c800340c0a900310703050707941c264040c002002d954011072001c400040683d61039001e00c210f810300300700c1c2000c3d05221092240d420a0001c0400014021606035991803900050429101c950700c146c1050000003215809001034a1180c1d0b009403910780d20750b4039039003040104003c1d00313801d50510480348545420b03014104041005011900d02a6079a41031240c0081d00d840b00603404011894071604560070764101c0b00991070b084176070605000c40e07003a6061030f2001c00303014009200d941080a940707001c8140040701346100c01c200e070103036200c0f101c043c1032010011a504103c03d940300917a02c10000b045480c5960303074602448150302d140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 869069748 1250 869068498 869068517
    0x40e070c03090e0a0515180f061206070801140109080d030e1e1f0e031c020904020705030d05070203090a14060c1203090d0e0d1b080d0f1409090c0703 66
    0x718210303c102c259490a07250f50740b001040031810000c8902c41844e1b004039240e20440079444070803c540680102081d00c10080200880d410381c8074803100e0b001751441d4a09a07025031504500042c1440c10034800c40354044106044003030300b540680301c103405540b1441d000e08043c06c1541c5c0706401600c24407040800b244102c1110310240c0700c0506a1101e040702d00800707002c5146c00c3c0701c0d101b0b02c42440c42003001c010900c0c040503400c44041c004201c072644c0c401d4400101840e42c14242005c000c0c0a481401600f150000490000700310000c402040c01d0107072340c20100941e4a414100702d9aa008900003903820004064090015078441c00329250000c2004004074076120190071160304080c80301c1c0c6150360f07a501c0442030111429003401880801c1c0500d00e03100c41c400c900d010000d00702000c0948003511407d154160402d1066061040704041c110440c1102d00340b01d0201c00042503600700307242c00d00000d400c038000d4810141c6103408a40041d40028800c820035201d08001d1200da40c0409000c6082c40130900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 869070998 1250 869069748 869069759
    0xa0b06190b0a18090207020a05120d0f0c240c0206061c0f020604090912051204020f0414040b100801060302060a08100f0305060a0b060a1e05070609080301080f03040e070c0309 77
    0x81c01c1c400750404d01d00141e1200b0381481406140c600c5030700903078810f800185140c840400300144011500d038152911080b011500c0c8000d5600110018004e000040401d003984000e102d1140000d19003407901400b0010051448001c0340c80341c80999085501518184000070795a030010003400d0302c0360113542c4941d1580d6040d40020b140d03510642c09510000c0d00d5031411803d00c003480c0f0a10050781c1950170040d02e00341d4071141c410040800100024410b030300a50084c601c94641d9444030001e40e08803041444c803403d20303042010a4840444901c076809400c81408035018106008000480780d003d4080c50906400c2407066a1190340100307051106000c0e400c0c0000c500c000b1040e14002180110013070050390500e0301d842d1041c2c0b45c0c25a030f0180905410000c2c02d43d43ca501c0444010f4040d40d00e402041c1c400b08224040700c03288600e1740c1c0542282d0603e01c0e0715040c00342c010000d50407103248404607001d01c0c0b003441409460b40105d124102d90300491200080d20b031402a90440c843c00d1291500040050302d44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 869072248 1250 869070998 869071037
    0x7110405091506180f1608130305030415090f05100c050f03151018050105070f02040e030c0307060e1501050a0303050d1b0203130e06030d0c02040f0606020a0b06190b0a 74
    0x8503800d0b0b046800c00030a105020721b080711060000c45031403038058010319194081030b000b00301c40c0e000102002000800102800078140c1342c0c43c0186000e50060010308040d0401c8520040c0f08001070b5000c2c010900119082c8145128440401c81b8903200e007414184200c0344600d940d0001001841d29800d42070440700700d0303581e9001304200104144c690500c6940c1310074a4a80344003541d040503062007010001407000c51402c2c9043c89515504807408281e59900d030000f5411405202c0c5803100301e00c0003082000400c050354000040410115007200c9126038a40100741502d402131243e1130b006520342100b440802c2c410401803d48255800000c103242032168070513000c4a081d1150000160808110700c2c88080030000721074000c002010500145050070030006e070315a035020600d0300030b11080b4003046045444a402104407070400002c20003200796140383c007945861006104541c10044000000d43c540f402d180350705075035034411110a010509002007641d10f03500c0b00b150b02091001a44040030b110380395 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 869073498 1250 869072248 869072251
    0x215040609050a1208010f05010e0f010c08180f040902011b0309030c03030528140706111206090a0513170c01050405030414120a260f0711040509150618 67
    0x70070100000d0504c500b0010714120041e0071585580254200070016a0b0f40280c400a04003c1118443c0c0009600d1006a94020728558000e107854000b00e02000c040d216080050301014069580400d20340d400c8082204440940c500240441c1e510510220942288600040202d100e41000d12145860303440e181d4a1600d25801100001c2000590710000030184000c1590b00509a5460340a035141942c09040c49504c04186440701c1c1b07012445400340140ca4004610b040001502c880d41d80082e0844000d18140440b049401070615001055800f60740344031b40c51180c0a10031340600b000c0f10603940c0995001c2d00624403c118103080c4280b14645000303102e001c0c0940d114100a40d6074034a010f844980e031403e0301c60780342e02ca0b540c070440f00c01500001141082e46654000c46c10800c04100114850100f0207150440e018040c01207045040c04070000000c1003c603018400b458040e804110030042616021030700e1030080e030030610f9200c0035010240c007000d400c148018032224061000c00081d01c0010360 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 869074748 1250 869073498 869073503
    0x18010203090606181603020d0f060f05040b03030f03010e04020a03061e0b2709071502060403030b122e020d051e0912070c03141015060215040609050a 66
    0x2d0b00c24496580380c03212528048070b04498110007549040c1d41680e41e10b84a149001090640000c0e86000000181e400384040c3c609400c41000042d84038640010366107698091035008074500182d010807490004181c0d03169124001030140780d0303070a1403802245100003038000c0340c0040741c60b03d022000030300740c2c041c080f94800394101e4100518115880721050302c1494502c80d004e01d04600050428055030300c05008e030b418006501c0c1055803100f803030281c9072400c554407104814030800c0c000141c07582d020460300d00441c000e030f405201e081504410408191082c1e0042c07482d0fa40040da24a8160b84412100308540d10702910861224170702103800d80a0381c1c068810b8144540d0b9071000c0003102c404a514000e141500080101154540005002e65070040512030340b40070349001c9468010000355010400285a20500600068800200346584e030750042188400003420300044803581c0d01500f43e080102d072442d50082a0589100707013a0707800759201400940d58103444e078400c200440c1d801c00c0800345062 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 869075998 1250 869074748 869074753
    0xb03120f030a05010b19030e0a1208070e011d010e0112020309030408061b030121022706010c11010c17040609051011070510050c0d0305010f17151801020309 69
    0x50201c68500c200d503c16002101d0503841032194141200304245400310304269801c0001d594010f210a241c508804048020b1000f0042d030004080264451805030140321503131a0400c07105001401035a000c0e85089003000e402c0301440e0340310100d600c151020b2089a8060418211103101915514140c0e40210351280a981c400a000c008808080180ca588049403900c0c0381200c1c1c0124840440038401031040c8465020500c809400329868459041503803a0b0052a5070f0000c2900e42003681090040c1d5003e4100005c824001041c0754020a42c8205243d4071908000e0405015001550003203442d003404c3d2800382c00c0c1401e12515400700781c0108003801d0540c86180c211442c1c0400c002507101e01218500804c01c0c40e01600415001c0046d00302d00ba1202159940c4c0c000c1620202218030b07010705c800301140c92080401603540c80d6019440141a525540005400f1948130604025100208060b01d0032680c0603260380350031040d10099564002a070801307071240c0307405254920b5081e41c005071032810703154 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 869077248 1250 869075998 869076001
    0x31d0607230f0405190b070b010609120302120a030b1c020f0a0810052e031416051207080609071805040b16051b0304030c091e0b03120f03 61
    0xd920142041c0c0c0310800c2585107140104030441d00304140a0341c0b0a803401840d4420804042d441d0040103080600100600f584d152046400c04040303a120a10982020030300c001d001040e02e2800c2d142100f06680c1640003082d00c040403500030302c42c40e840f4105403010556607c003010000ea0b24150305152003211039100c0d0130380011074010440742e880c400891900c10f5203144820403c1c0d0001040555803030340c9260300020f455880e002583e501090030325040801ca5410600c900c15100704805480a40740a013410b42d804c2c050f10f07010280c4d60b02d00000c80c0086c45030030b084104110315003000ba444c00c200102003076494250380d50320b10503c0c1c501e054031710440d40d810552061040319602000c901514400c00400c0c031550900303894120807810701406a0482084d5140c0c1034008a001301c0c1100c9075400b105a640c1d65046090311025180d4109010441e601d1084c00000240c10b85580a07038109944000c01c04001001e251504a004143d14840340307400d401f582c03001a80d038400b610050044601c1e0b090110340e49 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 869078498 1250 869077248 869077277
    0x100b0f0d0b010c12080406023c030c0405090c0f070b010e070311041e150908011b080613150e0105010e1e130906020a0e03070f03050d031d0607 63
    0x80c0c601c01085030341002400c801910104140c4240341c2140103807824441011b45907400d0040103485400c500a0b2644034125070380c80c0154801d042107444e40c80d407031148000c581074250740d45854401500d4606c0c02c42000c0c0028085840d0088242d901b03c2000800546071003c0483e0b19000c540049006480410054004220440000c4100c542c04400780c9010800d400c9108900780440c0124054425042d4441038185101d00c2d00d07440340d0004d0b000640c030018205140040c01081e421070b078040c1c8840c550928624481d20180018030300c00c20b004c561039111050303480d08184000c00000080e035280c0503444045241c40000100004006070480e6401340c0300945c1004000340c56420060b65803030050003c8a0044111030210900720108407086510404510322001c9210142011a80c041d080c10320010702944519040080301c1c0710710700c050741618022a0b80d51030717000303061003944006005904042d00401d2458400c0e4403d4140d0b10312001041c50b609947c440282c6030000c125940700103da2081d0a0942 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 869079748 1250 869078498 869078501
    0xb0922060515240316030b040f020a14180f03030715140c031014182403120706050a020712020a05390414130b060a140108100b0f0d 58
    0x20240d4448401014a03e505074800d0903888010002c66010044c0740d941ca039102e100c0c0c1c01894000c04c0040003849000e5000011074000e42c4501d45070300100d049036620304070680e90030701520307400984402e0b9005540c1c0759509006150928408507130307050008100d60030003e18824611010502e010400143d039200101627146020005402c04241190902c01c1000d0741840c040c40109a40701c6400d580b03000545100800d105081010f0720823162820340b4100a80c0703004070504081c0040203000c60740c40514680c4103060b110010b1403101c1410140401c203d101081103500303e1900102d03080c40042c80c01c0c3d515122803008040150302c181c0180c100c034442200f07000d0708020304c94140f611948007528400704100500305171410040502e05d18040249440305555031540044d440c403800c10320210251070f0803665120a14800841241e2101e8850302007490742c204412600155203800c040588050140c40041d2009000144102104504054007150054401020f0034024075150a010744600c01900d1100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 869080998 1250 869079748 869079769
    0xf0b0406020c04181b0b1c0510030201050301061407081c0f0c09050f1809030307020f0102090d08030a1e0902030f0c0102030412080d15180b0922060515 67
    0x9110303a04001000010040d044600d84c034070f541c020107175140081505200c2032000c1c0c45600120069070082817001d4400030110700e500320390044007401c200c00d541c0c2c0440c060340c1090038000680080ca0a00050010b103004045006041d0b00d504411401c1c00510740d115040d640c005241e81c18280480c40d0070700070480f81c82c02048402c407901ca800384070540442030010400000c40c03156520440d8052042d070100d85450182d241603030301022040100c0e03d0041030503541c9900c25908000148920704e01011404030620a5640b441e50040c40c1c2002003c103501c4030300b0180c02c06841c03800030342e030388024072903013a007030486034640702c2c42c0f0840042020300150041605102c3d03071041e0801da6421070211061a03a901108a5080e650410284007040080d4180156140103007010b20000a10b0310000c4000d1202e400204000c9908012444018800d01c042c0282a0b8280307c01c50b82d0071401e2040442c2245182100b0000180c00180004000045948a403401c2d0707601a20403036005003481c070003200300781003100717080c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 869082248 1250 869080998 869081023
    0x12050f0403031e1d04021c090606150c0506061e040e06071416030302304201020a0515040b0c040b0f090d08070302340308090402040f0b040602 63
    0x519440000c0d424058209404c607244034400d5a00040801d141068441001014000d035407081201c2095403800b900201400e000d5144007205500307000c2c00c0144030300721400d0120b51000150000e82c54031030902a40d044602420408002c824421400c942c9407807203254402d458000c010b003014145040003409400c003510a00c2c110140402c59800d011500c40700c81a40b1b1603040c64016542c0210102d10b41d903a00000050b90b01741c9003959980345106000c0c0121130301864451078100941d44225100301e14004845403450340700e10403200890407016150b48000c01280f4180181d482d0051030b0790b034540c1001c0302040203507010a440400d206c00d12422204180d0f00c00052200103107044c6c14254a0078490184110940d00c000e0000348207099502d0301140003031070aa0003800140c40d41003611b4040e44070f9400c89008542d01144c0c5140781100750041c442d43d90076548038034500e2000d5007541c51f148140e034045040943c10540801c400291503910b031913030130000c0c4079585100d522035050040007070500d011030019 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 869083498 1250 869082248 869082257
    0xd0506070f0c05030906160804031214070f02010e060d060b04031104051e09071d0601110c1011120f0a020609070501140a0c02120d090b03040b0412050f0403031e 71
    0x141c2c0001e0760000490b08590021100b260300c41c0c15404420203801844580103201c0384020900208015984c010405400a251540c01d461016035581803205c0c001e01c400500743c801044070304d4002d54003504118a100d50b01910f0b091614150b041d4000c1a15603681c41a420450005010000d2103100456000c0001045401744003a04144640040e6100048110081040f5403c0402d550300300c1000079000034081c041034036409030445145c080f03203a0011200d182c0030802c0040f0101d41504040f800a061450044c111400f005416070b0444031007004040400251160700d190096001030907000d02604400c810402d9681e44e80144000d00785000a44001c42651040a00740002c0e0f800c268000494100300041da40c462101c49800c843c084408100039400c06610b840c075000d603200110b0701c5100d0300f800b5203900030700c0b903a00d000c18403082c07000302c40c0681702003018070200d4005407110340c22040001c40d0f454004d060501c445c298542c241d000d90300441c0032840668601c200c20010311f01d940c2540311a13040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 869084748 1250 869083498 869083517
    0x9031e03050406050307050d060303030b0f030601050a090b040b09013201020303040204091a0c090301060e0c3a05160309330609020c010e030304030e0d0309050d0506070f 75
    0x14007410324081c60040d0300600c280400010a1648980b040c0c8214601001041c41055568200076000380b01c9112081c1c050b200c9a040480f560030001040c504a640150065941500e071004c150010300100d42042c1d441a200e0960240942e50310b940680a00581125420b90442d4071143c42c0c0e081100ca65404400b0300303c8485000c4e26030700072007500e40c440d806913404681c1899031710b458000c000071400045034210000c03041c0542c501c2e83c00050075101002741d0080103e0754a405500b00e0b24075003143e81114410040140b80014a1100641450000d60601d1100700313404100d030401131f40d410142120305140d5140e04100096292005009484910b41010001020580c551005400e140d4020350079584d2801c9901002089034013184161000202041007150b45501420001c0d5120030311310802c035820300b80c041c0e640900110880e070099615868000c4581c0698060041140e0071003010f80c1401482c4800140c41e0700c50754068260a84500042c1245103041000548851045021001080503204 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 869085998 1250 869084748 869084753
    0x180d232a0625110613050c01020708030702060d060b07030201050603011b0e0405090f0a060b09010906121b21050d0f14030606130f0603050606091c020301110a09031e 73
    0x900c009401400398610b4070081c1d00282a1003403502d410543c00680304070800c106041c5070a0482c148450b00c204250b407010551407004985d6004e19001c1c50034607400401c800401032815500420848180b0500841c0065a50241c400e45410a40065016075198402c03c07045150a00c119200400401244c107501452088000c06c09140d10503d9802140d5441c04210f00400410510128100b80c03c203c0e031140f609441d00101401d000c15805014000300d50020842a6040c0a004103503008551046001e02c00d076141c0b440315503110306440d0325480e0440c0c0702040b000141c3ea80d8505001080c101048507288500d003a500d0300c51030218040401203a480352450132640841c102c442e0720040c1e42c032681c03691144000202248520188800120b603040000210381140b000c00a0850b62691400c001955545061000c0c0d440340300b10a42e80418103005083d9100040511050424000740000440241a01c01c0c01000d500106030760001c114500380400420100ca1502078140c1121071418101c0310386503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 869087248 1250 869085998 869086021
    0x9180506040f062316020c031f06090509060408070303020f07200a031502070507050910081605061207030b130203101a030106080714040f0e180d232a06 67
    0x14001c1c48421008400b80c85d4414420081c1809a480040598042055110000c0c90024100c20002c2c006030414400065901c007502c90607100b8858880900300c01c0c3e50b40d070743d80f602c07681c0a254120181039003030100101112110014280492141251480c2d15070740a4407601c2d180c9a402003d4810310840c8010300000d00c5034030b0021402146260050389520151814134203150f0700381c0050707420400040030000d010500c580020f003100c3c180e40656030140c1c1a00c91800c071102160180a400040030000380c040410a15210740d4000078030310700004c0160405001943e1f1420f150301400c40a60003200b030298030505201e031200107028946401c8024100711880080350b000500c56002070100090004003170300d014900982041c2108544d50350b850791602c107024106543c50240d0386660409000044c0b0344034003466021107030084c0300018007002c0d10303846003210600c014900c40c000b4041c0f2052824101c0018001920003190016541e519030048120b40d0143c00c154408418902d030b002c03c05000d41801d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 869088498 1250 869087248 869087251
    0x10209011d0420070b011205120a090902071b1508040b04140a0503070c0b2b06050a18050703112502100206090c010f0909180506040f0623 61
    0x50300c10141140c0c000c50300040062040d03e24866140001115640d01c443d1002c00500c1c0c25489100c0b0088141d0300e5250703144034102203800007801988081c0076044044d4201002d04551201464228016a103540b0150280e0b0040c003401c40d5180764003641c007801810481c1851001d005140b581100c02c00c0c040300010300d00300001d480544030891a90128041c03020042e103103081d519a81c4225020001c051800d40c0d0f40b0361103100c0607111901846800701c0c510254000326800070001300c0341e0080c010070b0210f0301e4070795500800c0203c505075980c0d600068152100e000f028000c1018209210280c1d443c00c0046054a100030300303000805103082103450f5640c0050303060f544c00c4002d9082c804070001549081071030001c006d020207540309d0003034486540d9841e400a00c180c407905500b010365410150143c0191040c42a900c42c2d08041240040188581d940341c0d8003405209115a00e06001d00040351101400e104080c0c4095592605100c032040a01030680204113000c86c0c0d0000480407920104c640c026000300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 869089748 1250 869088498 869088527
    0x41e140a0203160c11040617011a011d03163812100e0a0c0e0f0d082d09010f0e030c1c0c060905030f0d09030303050c1e091318030e030a05010509010207060e01020901 73
    0xd50013100c44c00c42c0c80402c02c000d0b42c41c0320ee24038440015100c000424000b01045200c489041c120a00802515481042001c0782c81c0c0c01036199003048030401c001d00324080c00603d5243c0103120721800041c0700b0301e080350035030007821007207000500e1000a02c0d00510041c2d2161819020b40e01c00211030880d511a82c400d01510b13904410420b0710b44000664524224140c00494000d0100004540341c600c0104801002882e00c03d0321800c0b002d00b00340c001a1aa05100d1128a91540001450041c54241240c05c01240d1124403546840c802c180d581d108280002904480006002e07a8414031440c1002c01004c220000c1040003840580c06c2070740300521108090100908050300d44010600641e8a4002d50746100c29606c842d00d821181c401f055030041d0022250f0500ca011512850f000a2209200725601c8a201c0003101d0400c80315030320159210544403101c6601417140070074810100b0310078414140103217415000036a40780c00a090a03001d0b140220a28011a40b0401402c81540e0b0003100181b140f12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 869090998 1250 869089748 869089787
    0x90a0c140a0501182c01030503180409020a051c02060c03071101090312120b060c0606090a02070b01030212030c03040e09120c0c040b041e140a0203160c11040617011a01 74
    0x21710b92100d04085010620a860121000442013000100c05070060100030012450016a03c1d4104420344130391500281d0809020b080c280520708207414200d40711488100b03418800348442d80412a2580480107040c07c540000c1005400c0200030104082c0f60314091819101c1c01c3e0071600d40c0c1003d6244041c6040a22103102042200c64225820594001c08000c19090f101c41e4081c5c1103070380300d0008030740d40c6125154000004803509030f28829102c40c1600000303041900c2c0c1c215800d210001d0240c01d12044a40b0051061794130041c0c040000340050140502060343e5030800c0742d2182c0c6401c20410b01420110f0303042c4101c4041400002d05444a000c041300c0119184140102040040500c40054207801010f41d14080038000710390001140b2a045003200c40d195070302c0100d20401c80c0815500050100c50458070b84100500ca070003929001d42c014200c80342c0310010400000e088031140d174010b104030850f8040d405070381c4a084c851400000c40c8140309880b001584400204101c591800310342002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 869092248 1250 869090998 869091029
    0xa120e19110108043807080f100812160f0c090b043605120901020c1503072105010f0e0f060108011e1509150e0a030b090a0c140a050118 60
    0x400006003400c042c00114000d20b00034240513200070021081148c01c0700400c00140d01003940844607100181c2182c40c90f00141416070ba002c000c01034207174440036014014400260044011400400c2c02850f124481d2000401c05403a0000c01c0c015281d0f0381c00340c1445907103461020001c8407180c0b021822003c0f0200e2440b0340d40c5d048089031607440001542d01404505c00e40140704400c14080c0010800b2182c01d808940c80c0c220004200040ea4026080c8900c1e008024000320303400c14054500a0003441007961603103c00030203002c1080c11a1001d90014103261004202000007080f5200c5564001e0b007070402c505440d241a9001910302403041c0304461501c542c2c80d4a0441c180d00c1c0c5c0042c4805015a29180350744208400c00c0105010103e0082c01000200c16412203216400b0789801c5502060142802c2640e9145031104031800d00b00074844080e9000383c0d036000e0001000003031010084e00b041f9010f100c550400c8400d20030504680d411480c14020002c0044500c03559107940c403411501000d01c5071400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 869093498 1250 869092248 869092313
    0x9020304060f0c1d090c0a141b06040210030506030a0209070c0203010f0b1c1a06152214011407111819060b0a120e1911010804 56
    0xc24082c0c86000d041d42c504074481d600c05134030664002c92210100685a241c0340c51000300080c0c4074040e81c070820004010000860728030b0040d821000305041c1d50103814100001041030303540f5244842c1003e217147e049070040008500d80410f01d202c1011142c601040309243c80004030790360300304070b00b4060b200d180c02800150300c3c2c610544000e0b1065901600070702040e41a01c4254004d483c02000b40c92040410310100c181415481c140307a241660000941541c21501d034488210418018101076000000d21351810301000d907c2c001003003600040f02c119800070300c0d03a41180c00c40810a410409008030795030000441c1d0b07030340300442070074025285031120350f10385682c030b49048210080344515411034070100c12501e101c072120784403610071111480d11190804481c035400c0d04498042c0503c140c420428004c4840061154041805246c0c00d2580000e400401e003000c585480c080c3c009ca480c6040d03e05034048100300320815002070510302030924408500f01342d5034040e91181040071116101d481500d00d10b04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 869094748 1250 869093498 869093501
    0xa0c05010f1a0a080c0306040b060a0f060f02010b030d020c01080c040801141609232d01031407020718091e05060702120415050f0c0313080c06040902030406 69
    0x941c0e001d00200071040600148485a105801e242845a100007030300155000d000f00e03141001400050280c0181d903150f5070b80c0404010040d10a0760010749109001c01c060402d1309507030002d055142c07545000003004820003401d44441c031038920b010b904142c4180d200c06800140000c03418030242400f0030030b42c0c0c403200301c0e441500660344107507007070b600300610380c00417003d00720301240158020b09001c002002030403015112040c06d4440c10040a16240003021704003c4201040b42c0c03240700070018905940c41c440032403400303141d5594202d041d041d40c200c0e60a040da00b5200c1e040d210003038071908001910f0260030103901d5038610f220303000c1c0f0240e4001900010084652242415540c03010600c41580708964000c420b89060381421180c0b0b224102c0806d0845000007840f02039494550241441d02d4241280501c100b502c04882c4005d01030284680c4040e00e00b0304000e002c180c11001e00654613035802000c2d0b001a01215400302c1d0064000d040c007440c46850f10f00844090710f0111700d01581c0d0b51214a8110b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 869095998 1250 869094748 869094761
    0x904020f040308040602060c1c051e1501020c0108040b060909030403080409060315150303110a06050117060106140712260610030608031207030902060301081501090902060a0c0501 79
    0x145040e4002008002c02c141031000d40b00780c901650844e40550b8841741200c01a01c200240c2c1302c10382e1081031501d61610070301d42003503a2141504140784c040328142c0c1d82030b1411200998032200c0901f54990300e06440e50341000000700400c02440d00c070b4941d09081c2c40e95180d941d405017190b4012030602c000184180350400c100e41c015540034404641d920355454085009061078001107400881510a00c03210400500607001400c1c400d12050740d8083c40d668054542101d44e1010003036a0040075801e1000ca0741030710803540203260031541a88404180e455090409005030843c406000c400903005040003500e10039150700c20f40c0309041e0300e81c2c04020351040d06e4513104203603050100b002060b90185400a5140c5081c0a58001c0e588807140b03d4001400341d09a51450048007903a07841480703c80c06a4512071116500b101060a000035005803030380114007554804d0b04a62850303440300c4c081c3c072400c042190300309006018400d41006500da0650000704944a20880f1000304a01e80188a06100d000e60000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 869097248 1250 869095998 869096017
    0x610020a050d1805010914130e070b0c12130312020102040b0d0903020d02010e120f072a080705010f0c11130902011d09061302090402070807021c0206040605090402 72
    0x180c0c0c0c0d280b01200020b10b034285103004080400c1514000003140d5000380290002d6400030140d228206e80c4c0007040c8031030759098550b20480c05490340c407480103900e824080d00c400303800074081c010b1b035909410f4245460300d20404d1807240c81e12020490441e000380c100c0fa0303d0054a51101200d1812091300f1300c00c0340a0b015581000d5020140000c0b1036100e1291548403c607854460340a0310581c1a48100603822105100d03102091038205400709034000288100601c4641200080755042c01d4058484021806485120000803842c0b10100c00003400303048a06001003035000e0041102a080100007405c0040b140e10440034414408410020483c031107070950034450010380017641d00310314501344d40050f099010f420f130702040c01ca0710340015409a40000815141028000750381c152202020301240091002540301150303030a000074005540c0794001001d40600648140307072141240e00410007100c03219400d41d20403541100c0072500503207911040e81c048480c542030480c0c0300e0003c08049000303031080343d402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 869098498 1250 869097248 869097253
    0x70f06090605070e031e030a050703120c051b0303060a0504050a0209041b120b09010501180803030f1501170402010e01030e03070503041401080705160f1b0e06060a05030610020a05 79
    0x3040543c950108400b1216042103040702c0d1045d101c10000400f00200e81c0c04c92a182d0020801d282400b40600d00501c0c0c814461f150086d503c10800c03040404940441481b000003a600140500c05440c05c1c1548c4040441d460380590301d0340c14500300103040c8030501d00c43c85010b6501e42d400517801407da64103544c113917003000e00240a10683d065009440e07100f001444004502000c5410313000a6103880341310f10040c800380c1400c4643c0d0078071005607099140b041c41a82c2e06e0001b00000b00d0130301d40501c085c50050504403000440790030300f041d51554190213280568100700994105010841800540d903030020b070282020924004402d00480107080c48542c00c0d001448001011010080000014000c540c510303451400046003a000455002c02c0944c0d68000040741402409040141e07000340c410018807900e981c2c526010307160703900c0030a21215035404001914405c4100700c001d000e080299406003088614514010410501030940d02000e80854001c6600d03400b4a11520b00810042001d56045001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 869099748 1250 869098498 869098501
    0x1212030f090c101d06070539010c021c170c0c060a02061f09091a0f0610030f0b1002010b09010f060c1412070b070e18370e1908070f06090605 62
    0x20306041403200562000300b02858581232a03640348201f48418492805035211001d403503c503001c00008000129055641c3c090200d03401d000546800e460861a900001e00c02d81c403119002c1e4110304200031601207070f00607801000482c140980c0810360035485042215218520b5078080b08540142200303070480302c0000c6c502070800f01409442c2076850100b401c41c603480b070700c0ad555401d10341d16035000c1542c1d06070f0081036800c420402107019800c80300b404c10211800040da032a45a0004803252088003c4d0380160355554805001c504040d80000e014000818550b0b489520b45100140781d400d00700d0010f0046e00c5002c0310905500740a0045204001504080c01c2c0c4814041c01c11102c1c400064403031070302051483c514400b582c10012036805402450016040042e42e641d100c84010883c001810000000a000501190403107810045551504594005401c0c421071174050f182940312617074000c040700b503e211403002800c84000c50f82250340c042e085640311704a624049028000c0898003e011900b07210 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 869100998 1250 869099748 869099773
    0x10506040612181514060402040608060d050a24240603020705030c03030c0405130b060a0507051608010f0b031911010903080d050a0507081003021212030f090c101d060705 75
    0x1000b900e2103c0c1e030300c4805d0156442e04000c0000701d124503c07440c8081030980303000595902d0941c003058400c40c001e0050722511440c580c2c0314520040c0c0200340880c1004441007094034400d00740308010034a4109408101440e102d1148002134003050302c01c28080680014000080000030300a80f818000940101c80c1c99007400d403d540016017060050310300420422100004031021806a84426503000d40380c2498450780a4088a40d41d104a500395800d02c101c03851011004a111010401002e0042c000614000c0c6c0b144601d003034401c0000905d10a900080750903032130311064403030000507550008291141120010040c1c4006400d42e2000c4c0c108940840c160300808019007040344110000c0703804001d941e540f82c0003601c01604c25031b4241030103480307950280014100102052a2040d40c1030445220780c0d007410151189906c11100541c44100030b00c18424022030810520301401404c403002d2680901d004d50041c142c1c0194681e20030803142054101c3e0180d03c2c0d0204644045810000340e80f500034264 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 869102248 1250 869100998 869101001
    0xc0601080f0c010810091d0a0b0610090305150403090510050a0311070305030f041103101506080910051504090f03120b030c040906020c071d0105060406121815 70
    0x210500c0c009000e2450300b03051541c810100d00d4401c10703101c041c45680702e01300601d0100400140003e1341c01c2d49200311200c24016010030500b06050707c99040344449260007414040186110042401030002403c024070002d14041485c4050300003200191074513503501d0034105c81c1c50f100d5902c42d903042010381000140540d0300c14000c15444140340c4052010400300c1050325010302c185013001d400250306002080c0f0440b910100290481d0042c08018400b00c2110002410410a9803401d945070385c0c1c5400380e9070a00c0c1151041300042c42c00b410606290700d804a056910340e040c085140c4a00303907485001860040c420042e8000d80f2030040d10402980700e43c0d181a044071117a0000c1a4041840851040d600354114050520341400150150500440d00e20500000d00010482241c800c0d40074014001103c10401c1600d0003021130007141c0c01c10710a0058200d032064410380202c0e000301c104000900c8410f400544083d2007960203540054421005603010400c2e101501c0000c00c0c0090429201c5486a1107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 869103498 1250 869102248 869102263
    0x11040303020d050909150d06020301060c15230a2301060e0d0809010c081b010c0f02061611030702100923090411060409020703050a0809060702210c060108 68
    0x40c0d02121008801c0d0201034486020b080b104c150b010403401c1c0029100d8448501c00b01d034040024002604000702d6698010a07078001345c00050000c0c00e280c509600f88680c0318440304100744000c070108114074010001844003203224440d0001c14034108086a03081c4820343c00048540e00b0181010008130211040040c607200a2043d48001141145075410a19001141c1c0c1400c56012441502c1d040003000151604503080c141036174840014055140c180001c4040d0709105041c800c00011190f0341c3c641c020384450342c21018081150701c01c20070003100107480840c0388444111070521002111000a6040c503603c100a80250440d04102c01030100641090b603900076540200c0b0700840c0780030143c2c202172445c181d40d4080c50f84940d4000202d00441d5071f00304000740141028207030a141584800035034060340d04c030031011400503000103141d92865500c205506e802c000450090056814034401c001d6640d10500b600e0f080428000000340034118017803007161f000010040a03541c0940e51400015100c602 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 869104748 1250 869103498 869103503
    0x403050c0f1c210201054f060501150507022202071a0117071530050106170a1d0a050a05060714190e300d30110403 51
    0x1600f000e84207010340180521440384030040405280c901c4080302c8801c00201c501d01502c554880f11408044c50070106d00e820228030352840001031007030564070f0400c0448505902a100210301c3d860b0307501071598840d041791905501155852950042900713040d940030540401900c03414400a614400c00003100d105604200307106480921766030341e4481228551700b8507410314460303400010080c4220389210b107010782c00302054600038850496000610350003500e619000304040120402c10145101350740512030241440341f81910014180c840c8a4103030440280981500320348510300080d10301000c40303440103004240f404031405541241005501c90000c1e8109603164080d00e00040c035264001c0f000150440c02e100e44840c40e1083c0703440110780306281110a2420050220540c01607980e82c10030710f9803003501c0c8010401c585180e56881040b40b04400ca0803400d280c01900c0b4004841d904003a002d8000d2401c82c040c0105001c15054800c51203181001e0212160310b00f040e400001c01690010340113691 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 869105998 1250 869104748 869104793
    0x7180e0606090c0a080a06050901080609060c09010e040902220b120c01080402121507030e0d0906230f040b030105120105041e05030c0714030d050403050c0f1c 70
    0x84401050100d504422503c40358001001c2000c084614070a10040d079010280400005845484800081c0f00300d20030b80c09030b08282e000c101440003140c800c1c010f09030892031040d030b25440d0804040019026118000b0010300c6039a13120281d41c19500d5480c45410781d132008101280c40c845d00400c0d90802000d0440c4100d002d00c00009030180d111500203000010050141c40d40d005556880c0d0800460710411060303110301c1d00446201c0c0713802c21681d00c901401089551004104990001c074058a40315203103000104100c80c3d51010007540d9080b0b10041c0300d40211a44480240c40e0b0300c4070341003040c840c08140022070480000c001461200707074400b640c140c820458045240e00322000c1194280c500030754014100140c1d803000d001c443d40405008800d42032051080c2c5c0d040200c2c0c4401c6505001e40c5520860304042e6000a4026907d418400a080403039141015401d01d401c40d200c159855543c1603200d4080c030079098540c2c1842e0b449001e210b0287e18401904080d001e810701d400100001307010080714808 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 869107248 1250 869105998 869106001
    0x309150c110d020105040809120f030c03040312080f070f2003090127090b12030a0806090a1a040203101212200604112106060910050a090e07180e06 65
    0xf071040c02441c0c012034200c00d5150406082c0010400020250701c07900c0b0503807180044241c00c3c660180050603210801801443e202e0b899420911182c2d0018288a810880f55034200720000710401c3d0525001149031074100c4240c0d07808001a101071f1254100b1080c0039001a81a040340c82c400001456050b8082c0c0e6400c024100030003001c03150100c0f00e840a232041c8036401046c460402e241c2d10040138000c1c0100001c808100e402402400c0d980021072072000030340c4000400c82e41e410720850045d081440000300308240316808003100481403259024074070440d000008a030b1121114800000039000e10000350007074481d00d2402c0d00303085180103451000301c0c1d01041148561201508020701c4280b008014140d196600c0e03032089205106864016481000b0903610119102540342d540158408407005000d14100740003000030380f0f00700412400d04d884e840041400b8a84454001d101201e89041e40070460a100b5200203080c080b060700041c2c820700140c903070a04d6a03681d603040240b100d0703014019520309 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 869108498 1250 869107248 869107273
    0x90c06070c03060615120e01060f09020306041a010f0c11041d06090321100801020c030d0f02042105030c0625090f1701020702030f0604140d080402010309150c11 71
    0xf00b0800040700008901b003000b02e01440c403c190003030204c00c020500001401a1602024445501260000d20429a021041060ba82001e10403800420300c4001c80207040082c0c80002410700c42c2c001d1800040000c680c00b03110802c030303100a001408540042049c050301d200c5603a00d07183e22901c0d499407031451040ca0081240c092011017105c08034003144060344a5a850035400e0350301200301816160000c4020742c0700080d00007084c40079015404028000e50390b41c080444800b419155841c00300c108951042104000c6660b0328010b1210718814807030080c040520f41e0411b5070442c0075201c4940643e006410030458184c3d502e02054080c60302d0042d041d20040601003040b108100c3e2400381c074000a41c1190203120700c2241883c0b0181e0000701000240c40d00c1c0c03407a0f001c80c0c02c18948032084a1240d1201d401e00c02003001010700301c44444500d074002c1ca40348951080c01004980e001c0c01c06414903644505d000280041c0c1d0344801c1d6240d162500030301943c1c100304070081105401d043e1007903144c054240304001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 869109748 1250 869108498 869108519
    0x51507170f07060e1c030213050405090604020405060d120e211b040f0615140703170a1d100c09050f040f0902031504021005030105090f090c06070c030606 68
    0x7016004036800d003052140e9031003800401c4145100641d07803080c00c591041229480018880c106032558016894184003220b482d1140340036001144240d00f040c3c100007100c0c0d0009030041d0300c03a8044a0100d056280d01001c6100d41107500005000442000c48040419030421401c00394110141d49050721400503020084001d6070204802c52141c00c04003480f2004240c242424003207030380082c030000710060400c031703480e0171200c095001345030400a6000c12070303c15801075840168640c4a504103440c11507503603401004e0b81d8015541d4264442c07603901240b00c2c911103134800c582055075070407640380c080050121180d40319100c45a200c415410f101302d49407031510500e031000c12544054240c0c095060940c007040f000c4c06d0075420f8102069070321070401e405030340c04000140403208214098200d508050051200d0302040d82d181c2000d021040004111b00e482d880c42d42d03a8410901e10b2442030a40344d0442c07040c2400d140e02002c95005402103131a500b40b140300506581128491042000256500c1c000f960 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 869110998 1250 869109748 869109757
    0xb0a0504020a02030d0c05091e040b040b03100519021c0b101407080d0606050706140f0103021c141e06090304050625060e0105100f05130605150717 65
    0x2d005802c2403025822582d190742000701c821125007085400c1404070340c0030902411049503000c00e00510103c04440c6418580304025404505131410b004045100c40442da5030036500445000d40756903280042c1102c007407030007030f103210340b10969055680c0c1101206c80188003402c546042001d0b07281c031005078154034140c00d44a408030715070b0303ca92030503003200a41820950440c0101b902c400404004404007240140b00756409441692079590303c8481a04100c0f0446801e41d016082841d054070030700c4501250708c2c000b5411642e045402da00d80c1040d000a4501203c07a08030300924100000c00d0200d040c0401044003126140c440d500380081c210203100490f0f032010b00361058800f80d00204400c3c000743c1071000040c00000f1134402030000c100145100035804e2a81e0385800c0c2c440c69524202d06299040038000c6581000b10340b088940d03c41c6c00c01c1c980b010054018401c5621540f010356003081c81d1400340d002040100402010706d0021007450089001c03541c0100d00803034812255506409200800b0b00035078 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 869112248 1250 869110998 869111017
    0x1813050108150906070f030b0301020c1c0c030e0d03020a0501050c03071404051302070317010b0a03052521090f0506060a1a131206060608010503120d0c140c010b0a050402 75
    0x50002d510307024010346d503404144004104054494800c482c182e2024002018409124002059000300703400c4404021045040000f0801c12490139002c0031a501400c15030312000111849548440b040c64107a00d0920030a5006005500346401c01039008401405188102e0298807840401c1041030742020243c46940215580112002030a81059059a000d00011403190a00c850880000340810080304026801900c070500f0010b40c40c600710ba458004c3c40e030080314003011445029440a00d58003000302411a400c01c10a480c60014020608030008204580b031072070080211018a0600802d5220501c800b40c45610450000c20010700300240c2020480790300841c90703d080600354140044a0f07100700d50030103c0005104010400505a440002e4001c0c0f20f0b40002a130985402c1c800740c046581644070903c02c0c0c12840c540c000351079140c821550224079a010000d00c00003404e07410b0b5020300303182c00c3e64910904045103194007040158841034060000b1a00f1401aaa90b6000c00c420b0740b00f8003850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 869113498 1250 869112248 869112253
    0x7090612020f071b051c020f1f210c020a050d0e011704060906020c011e05130206071a010f0603240e04020109090f09230a0818130501081509 62
    0x203c1000c20440c03d000001d44408003043d0040d5581e0310006480c030781051681c0381036180360501d503800318070b4400c070f03821000381c0160f030815404940701e503030080c940d8440c0c581e440c280000c449030201c21081100b850300c0b103050808020000000400e1000f965849201c02c00c03070740d5100782c41054206c0c50040c2c3c8103c2c20b82105940b140f69a00b071081011448000141c4103c40903500c4400000c001b90081c0050441403074124000140c0000140c1c0500307040e0241d001c283d41c0189000305101c030840c2c000640c603c06a40503100255500c00500e089151130200c010409070380d010b42c1e4004100c403840030b10b8080c205d968690b400d02440c58030034800e0002e03000016855030705201302c0108010b00802c1103c2d03298814014149604000e58611010b420b5850501001c401d45070b44400e46d0003000301e070f4408080740500b1400d1407103403000030741001990341541d01c030b000e080b812001c502ea6044946203180c4540d012400703030412210f007669110a401902c400e00a001c01405032400408080081140492245850100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 869114748 1250 869113498 869113507
    0xd1a0901060f09110a180e160e0d050303070f0215071107060201110405010f050c010501140a170d0503220b0103060b0f0a06080601181701050906070503070e0d0b07090612020f 77
    0x141507501c54010140144005586c0c3d50000b000302c0b400382c0d8244146021840f000843e8200c0400801d0000e0725111140310301521603551010440000c02e684d4010514100300394400c1c00f040003685451a032140d420340c00c5400d01c0411440541c410000080d0103160800c44030b80c2a2a04026401c0c0c4071700d441403c9103180180400c01056100740c81010002c0c0315410450315200040070b0160030b550f07090300540d6088140c905543e6203410000d03100360090640d00042c4a8203056035000c161900c0500c0c00340d0040200c08000300c3c5aa1401c000720720400b808000700d884d01041031b0300c0e20055585003440140d0b0381da07103000001e03207042c10447c1c03a0016112004121641d400c0c10f200d005d491840e0081c1c003c504028400c0201380e50401550a0840039000ea1810f818424403403803a0b00307081d40c3c002014079400d07800803028040166002019a0b8101010b400d04444201e10720000c50001c0c1285240580002200c505002c0c0080c1c0040c03070390f130a507a45680d440c040c00e030b400d040c050b0a0388a520b0032075510110801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 869115998 1250 869114748 869114767
    0xf1106042909010c0f02030c0c04053303011404020918031303111203121b28080c0406021b0d4d0d1a0901060f0911 51
    0x2480e0040c51880710410080c0c4040c80c00c034a180910854540285a5540402c544ea02c0d8104c004003142104910040d407619140401d056100d024100081d4003e82d00c1d100402d44000000d040c41030041c81814100b0901515110100011028802c0050003546844508060006859506440b95401400244464036641c0c3d0300103100003e00c502162030b000034000d000300c641d694100034000318060f2020b94280f4010b80300b000406111600c011401d80e00c100f00314483e043c00c0e903d00d1a84603c0034040342c3c1d00801c0c0c03004008030520079500c141c0148903406031481d00c40c83d40209506094450f540d101c900c0d580d10b03044154100d1007076029210160303000c0d0580044002e800e88003842810f0010b0030001aa5440740d603909a9000040814106505010b00700c0c50007000303400307250040b010b00e00b8480d140310b224030703405c000180c1081d019180983e5412650703509011114041510018190400c0505071800c0300c0b03002e000b0603250040300d001080303131040000e081040340030b00e0003656200599039240007480f4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 869117248 1250 869115998 869116013
    0x4020a05030c1309063507030f0c120305180d03020c0f0d0b040b0403320a0e211009020604060f02150405010203071407030207030b0a060b0705010b010f110604 70
    0x2410210a051043c0008070310300d5064000c060003000d007820000041c40000001d404640802075003100320201480c14201d600d540003551070222501704580300c207a907400d410070301c48000d490340001400621204000c820194044018100c400d1003140940080f1001c070100041030360032000c0a0700680c03104500c60a03910340031580c03017008800249103205404c03d0f551545021031080b03805640250803d010401459048400d94500903003030b40740d00b51030600028420602249810700c855000342c0206030702030704d240070700010b4541e00301c014145406020008480714501c0840c01c0400005c0c01107055490040e1440e00400c2c901581c000d00d0242800e0800e00101d079102c05401d0b8010445c42032050100c43c16848c003200ca40918018400507a83e8a0b20280140035400c44042c950f003244810080720011039408501541900c0e4001042c0195446020030900070b042c042e0070029000c03800107503810801034150301500c000d00c2c00381c84110364001c40120a45192503a948100c031250424400030340000c640 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 869118498 1250 869117248 869117257
    0x3051b09040f090602070c06090b0a18050910090c1b0206030c2506051501170604020d240f030b0f060102031207021b0603070f0c140118060b04020a05030c 68
    0x9040042c1481040c00c0d01010746071421001c2e074450754002803040500406040c40b0700905101e0074202c034400d14062040143c0d00c10056081c040003440c0011850940020212a00a060007000c00c480c034200501c400540048600c01d0000b0240f8240584480d54011021802c450580b8100b0030900e41150302880050b900040c52026070340410400301d0800800c0404201d8145410070034800800c601d403070110f0466102070900b1050240443c1d410010341e0b484510a000d04071040307581ca0380c64641e1400300d000380c01016900d4010508000002d59807048504030350ba8910741c4044443c880a41c0c40c01601410009030002420428000e070000d60f20308030f10300e141a00b00e0010310440c0d28020103042c08a44002050381e9840040e040030321280000340d07041200500402d07080b140383d8610700309508064850f81c00b10000c841030003a8171460a05100e50b001d01261244851070007404603a01030f085e5044079260312101218403514141c078895250605109460f000480764413200c0c5142c5440c03004c54100c0e0803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 869119748 1250 869118498 869118517
    0x90605100e0307050d0f050c03190206070f05030d09050709020304052e020403080a0e090f15030309040501080303100b07030804060908090a0801020c1203040c030f140f07140103051b 80
    0x345450006044e2211020050b40c0740c080c2e251b040c0078040c035140150602c04003462051081d0b11a14503510710703040000000780c60303c2d070444100c0c1d500ca106140c902903103800510007a00d08e000220301c000008400e500851401c41c42101070b00c00103901c48010740101e00050f01c004d802a4800c13241c1841010309040c9091010455899000d2151500c50708903090781e009030012208500003041c1c0d500d02c5608424808602e18007155800c8003450a1240f000304080c1c014030114112122071040e40071502c09000300c2e40080701c003510620039582c4070401103960f98401e503002600c0d5410aa000101a0701034400d40c1c03209503165071142e0381519207071541c1b806040c5042d0150707031924040040545075540e10b0029801000000300150b210402940a10308181144418904015003002044000341d40c0649000a513070f40072414900c1c0e81c01d0b90602038003440d2f070003580b00d00d0b0784501c005036048160001244002c49804c140ea011442c010b08004600f652800e41d818810b07500880900d0707124000f6200074040000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 869120998 1250 869119748 869119753
    0xc04230604020f0412031d1c060203060a030204090b0f0907081002090616030305040312110d1d0f0a0b070c0308070e1f0e04050a0501030b0703051504060e07020601090605100e03 78
    0x136200c5e001c03001442e080c20300850110740d10300501c1d4103004140c2900c1c200710000b02c1e0000760700410150030b0340b05d250100b10b004100d03640c0080000c0b8290703038500400f4041c0d60080c00c100940380e00d918004081d64000d461841c1c0f2542000d00003007070060006080d07000e4880320800740004c10310000c040000394100c1d10201340d1180042c4401c900c1000e60440c0c83d42c00a00a550105444c2003600340038201120b0070115115407400c00c3d003c011001c003000104c0303104d1104403000044604405a000d10440c0300403215840e80c0c0110112118001000100311000741e016940f130400688400e0401d6417a074480840080109a1100c009410180240709800840b18007400d4100700d05a042c11542c004506805d480020a0040c4c03442c024604240c801c040e4002c9100310104041d5046407a12041c0b14401011b4608160f111400250750b940310b0301089038400702c090001e0001c940c0390586003014000c112044401446600e0001800c80c1e030300c0c0155812140c001e0f01c03100c0c03084914601283c20610402840d901071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 869122248 1250 869120998 869121007
    0x305073201020703081c0c030b0f1309082701022b021204170f0d0804120315140102010b0306160507170a030204060216031707060e010603050c04230604020f 69
    0x41c105c0401000c40c0c222407045100881004d840441c102c0e1400007503002058640241840030f0b4503070020b9042034101c21104039060201c005a801e0142c5600d15004207180c20200705981c03e044403411100147c405460900703c00d1110000482e525010440c0701d01d0025031401020b4540161f840383d95880040781c2c815103a0380780003402030855903489688007100c040c002d400443e503450020b01c9020f0064100d44080d2184800810005080c2d2070702070809007844140940080c42c85000342d0143c3d00c1d5080c051070118255a45462214a048070f40c24014050f50818146004a140c0032890500c141400d150b078101750b00c903000302114a900482412160f030401780c1e0b4810212283c00000d00b40a60f46a0740159440303042140003030402030340102c0c032100201c03062001d02c005000c4079550348404440c03074803641e00d540090408501806050744060000c0d441d000c00401804030114000402d000c05540038804000242c40280c1c1d070300c01030090300741666a1a00451500e16164001303041e112022030503103082 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 869123498 1250 869122248 869122253
    0x7020609030610050a0806132406031b1715070c05030d0c110a030503010b0a0507080a0207030201200a02060702010314010b070c06081302010f02160e010305073201020703 75
    0x10b0810a48081c03980140d50481000b851400b42880340c00703071003074001900c00c6041c84040000c2c600040e6000401402e0614010801c46a40d01c11040610300307094414091681d6074140681cac41e40210a458030b5402e0160004208000c0c45400c1c601604030020040c200c8141e00004a00709081c0500003108101080311136101103032040001d0040c01c8801940055a01c80c400703806080c598107d03404a9964000617070280109800c00144d0341190100000e9541d2039120030400c0780c05224401c8010584035021034070807411035001400c3c00a0368801c2c0c0320782441c982020768140d800010300028451a03400500c41d000142440b501511b00e09106050200d0041c10902040401c66400d800c04004120042510710920035a445008001d05150908043e1420403000590312401201c0d4040d06010000c800041c2649c401c00030002104034041c20f665036582c50318451141d810082c413047c0c0d42842a44008601c01501d115451803005c40348030f0001c1030181d41107441000d02d02078201c2a0540c007642000202 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 869124748 1250 869123498 869123503
    0x1511071e11041401090b030109030503150d06020d05070810080d0c0206040e04030c0b0c031b071a0703020903120a0206061513090914070308040611010204090c03021c090807080702060903 82
    0x3c4011400c500781c0c41da5814042024125030004000794484d0781400c2c4000003113a0404111794108100c60304181d400c030f143d032001c1004200f400c03100800305032000411b040f620880b603000d1401441503942d82640f0b41c882089951005845014802e482e401c628031140e0118082c2590307440ea2440a82444e00305580ca002610752070702c04071016004a488464100304101070303105066070001201191906508000c40161401c0c6181407400128000004042d0144a414444070001c4440410480d8162801c0d601c010003a4109903451401b920501c0c50490391250b001d0142c5040b4201ca074024101c3e41e0f00c0c0c00401c062102100c2900403504d3f01004590070592100d4818405001c01c054045260041407900b4550301806c0c00e29041c40750032220043c0002000070048034211a40d900d0300d20503200c0c140c200c0384d00900c0781d54416071042c0d20b801068020650141c000e0001d502003045076000001c0741122031f400340d585c00b01004008400400148002424080c09407004500203000c0a0804c0e120801003403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 869125998 1250 869124748 869124761
    0x1b01090b04080f0d03050f040204181209081630050f07051302090108010e152806050a050304080706060b280509010e040e0f0a1511071e1104 62
    0x880d81c0c0c110700c0b80c000102004002d4444a44c1c00c901e01005103140803000d5100404016000078400c0d61643c0d0a106080841e01052030820b41081c496821a4234820001e403040c40144582d000d00c2c044c0e25400520b40f0f0425510b003003140c071104544180d403032140900b9420155540340142c4503481c01a07000b000320700c1c1080f1140030042c00c28000d0075414107100812803d180d8840082008500402c03686200b030364130144c61811100302822241441e21500e03420b03500390444030a115048003c03402c18488924042c0e20700b41e0544d641e4040b41c0016510f84d001201e40303224550010300420b5041000c103000821200081c800300f0b01071080000c0440c0c84114422259104164000c420010751118a503030f0100c031681650308240e903003003c038500140c000000c1d2900d00744d0041c7c01e12559680c100c400c0d220758140203000d1035081f041c01f56001c0c02d0181c6403072004070921050022000d072400000301046110f0030101c6da210f5030004502080c2502c0000c4003100403050341801c40380111204030031401c6445901828 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 869127248 1250 869125998 869126009
    0x20409020d080a17010f03051506040e150f0708060a030f2607021008240d0b0117190b0a090501060905070207091103011a031302031b0907111b01090b04 67
    0x94002c01c01202070011513801a0401d440c00e07070002104100141000450380c0b102460001c8680260341e034030000a009000d08034070282140115040c2c460084000400c1760321480100000e552a519568422900c0080c100c4600ea04420420360174030104480c1000002042d00c9100241c1d04002e84422100d1042546d406e00b902094010605504500e000304800c1025600340c6085030440c40d0503500307282c0c04a031020352288e10204a112980064a402b00c040c00c01c1908810f000c851969696954080303030200850f00d1200d40111580061414102414154055080100d03900c4986070013141c11300600c6412021540c940d83d80c000020108102e0051900c60030603500078001c2e080c50203c0754010b0319041c10450845903010401400345a02c000b07028004480088002510703a918401c2000802503a82006035140c89003825404407104090740003100c00805a82c0c6840c50348901c04143c80008014200f2031282e004481105000a4860711404015605242254500d1f40c1c800d00c1d070000f648642c000c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 869128498 1250 869127248 869127257
    0x402150c030c07060f0e0d050c15131202120123060607051b01020d0201020301080601260a11130c02060606030901140c0d0c0f050a05030c07141e0a080403020409020d080a 75
    0x221243d80d40010b64100c5010007910820781f250342ca07a4403940c0b42c2c0c40007a405031041d0002d000140c1c014000d18250780202401c403008001850b01c58010051070303060640100e10500c030141c800650041c040c02145005608a00c0c110560344000e111220060b4000f02140c0e00418180402c0c4003064040003d00d030f00b05030002d203032040c0b076402100085c28a404001c00c181560300402c010011203000145460460717402240c2244d4299407990705000c0e526070442c4102d0180b141d0241c500520000c0711901c490f984003250a1080c41494222020179203100040c0c403030140c0c100714000340d0b1500f000401594403e10702000001e46134a19982d01d6644e0100740c542140f01007002c21030b031400d40d0003440b503000d0601c074a0521100250f1100b500030090700c01d0b40943c400b08000800821030314450b131400e440d110b9901000198000e10308180803035550340300200300c07201e10011a840a84245c0040394441d91540c2020003507240c40c4c25070b000d20000c0c204400080340c220000700108804214600e010380502e40540d80c1d0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 869129748 1250 869128498 869128517
    0x41404030e030712020d060212010608070e0405010e07030518011e15051c1a04050c0a060807090e042a06020705030610060e010309062d050402150c030c0706 69
    0x28001d01218078120000c0c0250320020003031107010200940e09608680c1204e841700a040c0929119020f40108442c40d0030629007500007040503504003031024865a019a100b51805800d03e040005550082c0b0a514020b05080b01140c1c5040c40b94202a601442005100d0003084211001900719442101080107004000945502c0d41015000b01e040c0c41068202640080d402d00c00090a070b04050b44207283c4040d0b00500c0d006c10409041800201c00c104003c56450394909402c000d5110444038004920441c080440030a005000781704a0307005911035642c80c4101820071410b0b03060420b020b0070648070004403024502a903012558401908082452800700d00c034902800646000d6090300507510942019040000241d480d0750150115021417500e0900030a10100603402010324000c054001c40c00c18080c91008217004440300009130715807004680081c5044010801c440003920000e40c0402c03010040c2c044040040050051680c1c1d040c15a483c1c502c0c0c984501d40fa0820991208012a03103170350 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 869130998 1250 869129748 869129753
    0x30c040e13020a0b0a091d04060f200705010608060703020909070f21150905150303070c030224030127020c07091a04020403051b01020307050a02150702041404 70
    0x10000e0700800300e441185418000382d40011400d841074018002500c0011481c080442d106083c00c0d0001d02080d800c21700c00c8080070000c00307418a0103c40c155101810b00c40f000d246c040d007901c0f80148103080c0c02c1609000440c00c03c1c1185003070780300020507103240d901d07500301042410091003458000d4125480050ba0380320b01300180803148800a00300014054208441c2c424503070030000307203030101350100b1645102d81c808005950040034030002410020041701004216884a944003074000d00d2000b0401001b80303003000c10940d0b28828108010901b000001003080141085c80d01c20b120b8a01c4150b4810300300c42c000c495508290804d03400304070f84401c06c45554405a1382804250b024500d240070079841c290551010032b5640c00240b2030040c2503640d5104a501c0500c40d1104015003400040056681d50350701d0508079904d034400c0d142d414601411002d00740c00796000204460450364130101918898089400f044540e01c24030300d0b2810f1081040059a0040e6076911070a55001c03104140200c8904150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 869132248 1250 869130998 869131019
    0x315010905120d201c0809160b0307200114100b18010210090302060402030f0a0b0a110403060f1a0913020405040213181203091520030c04 61
    0x258841d900541c4111104000c181000c20301140b820220305001c84e0000c0b074203026030401038408007424900d02519003102400d001c03600e4055501c858a03500d00b50b654803114417007a110252a00ca038002c2c005542d0b0200945c2c1c00724805117038000721506040081c100301030740206040d411410184001d0350754041054403008800c2c0071035000041a11011040e5080c0b0b84003a0700b600c183c2c0051001c919403008400c410703038400c100046005000c1c403c00d00065a240c68065035440302601d0403442801795800920010300c000424440742d0b0f0300101c001c1d9041d22071002807001070084411030310002004000110201c1c416002d00d002d0028040c20001d1113147d1350510040345101c94074980e1041e440c080a115032190707600120148103404560016407500d40e0710025210500701991180304600b808076422071001c22016a0480c14041c02e200c1d100345000c1a0100d080310407003100101170a20042034100c0601d01e592003070900c0940051300c19820041d820760717404560403c803101c0c15100d00026040c0001d0135174 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 869133498 1250 869132248 869132267
    0x106030f050a060f18020d0c0306110909180d050714060c03010303030c0c02060d15180204080601080c100c020d020d12020708150106052a07090b18070509030f03031501 74
    0x190200304841074030798040c3c0c0003010010801130711a101403050007007800b486000e40780003507a0140382080040340610b030400a5812140089206003710400240c0030700401c3d281524a424440c0a0f241c980c1d055002a2165007040c281030b00c00083e04c00c10a60040e00c20860603020300c1e082c0702255160362440c030707000b800d5510100300e075800c001e52020b840e401031300c41c4015502681000c49020414100d400100700040c203c135030084840c40c0c4000e4240c012102e00358000c2c0240d4070b80106603400740c0c0c2c0f221081070340d4600281050750444d241d040740c00f00c924410242c100d059440100a185250305580004810080100c000d0b41c0300c081e10145024001c0d0108850801028200040c08100c558000d105e424524144103007001e000c00060540086a40c108010340f00c1c0c211181000601440041a141da5074824080e0004981c80e114800c281c0c1e20345070404440030700d00010ba0100b240c0e03542c0c104440780c2e0024050710341c05109000c0b5441c2c03980d4041c40074520902c3e190b1102051000542c0004041003507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 869134748 1250 869133498 869133521
    0x30402040b0f18070201020f030c040501082d19050f16091a0d090f141b060a2106060309051005011802031b070605040c0f15110106030f050a06 63
    0x1002e00c0480100d4070b4800f80083c88159080c9000b040b0741e103105050780a4840c0300008194aa000000c0141122510002c0d03c16100c007030b600e0503940c3c0e80700880c0e01c1c0075a6a241081c038040440c2c0d80b4040a0301c007210401a80480517003001c100c5080a8401e55042d540c094842026404069003000300001c0800d2256281c5c04075440c185203034514064460030b2580e40c0c1400640391900000e45029100201e40100c1c3c41241d010400300301216141c1000030304950780000c581c40324000ca0400346d14066492010b5070007000002c24840c070345003640c01c007034520601ea841d0b4040e006050541d80d402d0b0040c10302c1040c004148546002c11151081d180c014101000c49513151043c1d440c00340148a1380d04500c0c00605280116140146c0d25200c02407200283ca1100c035800454240c00940c1c4001c20101d07407c07450040b4031031001c44100c552250b0681c980c4d5038185c05005506503444a04400c9988200203044100d002100005a1291640c517404204004114291010340c481d21101080007070328811005c001e003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 869135998 1250 869134748 869134759
    0x91406071202090f0d0804031e030509040b011206080d0305060306070c1e0506040c1e05280803070303021902010606080402120f0706120f090c060c170301080102030402040b 76
    0x9040e10340a0498001503040c905401d0340801c104640b900c0300801120744030401480291411100e140150701030340103020072a003d800c001e00f035404000300c84548203c019415100d040c104420b603414400101032401c045410800001d0b900064030300340e0710490016184890160001c10003400d030150a40c1d07009442c1c1d0703000b90300a0b0100700c01e0590110440c03078002e91110704010b00204000301388201d904c01038405400d50003120240401c00c8186100e010450780b900b640c1c1c01d0040c0030015404007100040c403039280c0000311201e4050f018500f41d8001c11018003007518a41000380c550100b01d2444d00559401c8000c2903001540c0b50300307d500e220503501d0340100f40c4000d0240e1410030400400b00240980000e005001c03443e003111a41030b003030140c90300c80c2a9040c1181c41c403650f64100103103c0f014420a40d19101e160510054602042c0e000b01151684c0284800740070614045086864281030403082c0c80c2c625000d44180c0d810003650000f1402040300c0400980c482c24540100006c47e0160043d130b500c641c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 869137248 1250 869135998 869136001
    0xd03032c150f16050d150905060f030a060203060a080f0106140a12060f0f051f06090b040e101d041509050604020f031c05070c0b1e1e0409091406 64
    0x514030b00411035210803803400558600d882600156518001d620f00031018504141546a0a03e03a01d1407030300880d0142d800500c09900c8070b00c00c1c4400902c14031909078254004068007400b203074098004640165028014040c1c0c10f6841e185641010008030803003200d03944911041000041c480b0f10420920400c8500c80001840e0007403810008a00c250007d19076503c500c50317184001d02a5210b19046c02d182c580c280f01c0d80c5810040d4000145400076030b824000e0a031000800c0051203000004282c40300c08204915003030030000101d40c070071030081802c445003803c140f011440018440d00140b0441d0050030141c914181864441512044428050802c07442e025440e00400d01c00102c50b90440d030140d0b00418010f04400100e414068000800c0301400e04d45010b0100c040e41c04001484004e000d0380000030803640301d85071a2503510419100305000d070140c800300e00c0017070785000007410020b802c16101e401080b040f03079003140d05822541c07051000940e2803080000b80001803414000320096000500030b103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 869138498 1250 869137248 869137261
    0x2f01050f0901050910050a0b06070b09100c0c02010e13020c030c0712080703051b0105090f16060c02011101203001140a0807030605060a060801050d020d03032c15 71
    0x5030707a02960b0305d103083c6840384007040c95006a07500440c10142c0140007aa0b82c1c110302c2c06d1280c0d51210a642c55104d9120781a15030000d08002e00c5540d4030034040d0758440101c010213800440718820310505090b40312050700c02007804030466100510040f01e0f030070b000d5919070403140030381c60801e0310f5648030361070948030142034070001042101154070166140c00c00640b0b030b2000e92182c2d040404074030b04040280d031822003806525440090340d0300c3d4030644081156402c80400703011060007201c510614011404200d111030056002d00045400e0003c0c0200018000803000d081103501404003600c0c81c251000050a070f5101c207003040504148030803040c0580760b02d40440000d2018408148104000404000009071140c3d5a2040c0c07000180340c61000c07900301988905081000b01401d9951620910b507034140040c50f507000300741d0241251801031a50290003055003c1c40020250f01500b203041581d199503040025465940c01488403011101d5000e1800b6503420301440d01841030309580e0880f00e8103040001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 869139748 1250 869138498 869138503
    0x201020616231c1a010302130b0304150c18061e0503060f060d15050901030b070c020409021807140405150a051c1505060f0306012f01050f09010509 65
    0x19540d0030b074181145800c284220301465802100c080c03200b0211602c03185a0b140710250005080c019019071006a40700e42000190205d201d540a0f0b07080b080c0041c02e0402041c4051070195a200d800380c8545000000e8101020b81200c0300c00402c880801c0b100c550303901107407814511000250400f0f08110340050b15125200400d040a602d11004000300000000d05603240c8190400c2c07540d00117041c0a840d030141541c031310081d00c20608a00000004118009414076001c05141d041320b4006410084a48850004950740c0c6980c09090f0f80107501c070180ca50040e2140c00c108204c0c60031100d01c4459608241c00024860518000502200101403100307201a607a0a04010760142c0150000c955502c2806030540e210f01692120042040010000407541d0449400845208285001510070952a41c2c200702c114042d2007890010180c0900c00184154007075440000420850400341d066650768001611061790750a0820505946600074403180e034240e04400c0d9000850725009000c145040c250255 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 869140998 1250 869139748 869139767
    0xb16030b06090319150e01062309070305040309030807030f0206070e10110f01020f0703121803030b0a0b040902070c0e06030c01180e1e07020106030213020703050c06130201020616 79
    0x54035400740310315843c100410328070000495062074000340281081903046c54020324451140200f58540040c480040d14684141980700200043c1800216210850203c00400c1c0051003101031240c402c0012022420f54000b920025110b540c425a10740d0341c1c8403000f07041c06070160030b2000348284400f04074103c1e0b494040f91100400e041c0b030109010402500740f903107480c10b02405030001d548001000c90740314400d0350050422074040d44413503600381c0340258417008550035602c030740e25040c5030f548a01001912a0300078241500780140788203001621105143c803e6800341c1d200d00b0030705034005031040030000c6c240c441700b0092103c600e10760264035107440402c1e100c9003a24103060401419040e485a00380c0005085006446d1510b06002c07176140017400802d01000c18001c2c42800c96110b4001080d49105000d588140d95000c3c1c07805025600301c078414406900605c4046061140074809904400f0f01000301034406c000398200c464080b5094000a414240e01a0101d03050b000040c2080d61242c1d0000c2611 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 869142248 1250 869140998 869141023
    0x140915240303070606060c12020703030f050309011d061801060b0301140d06060617090c150c0c0411040510050c0d0f140c060106032f0a0c0b16030b060903 68
    0x9100d1012400002402c0d4411544003c10051510b000860803943c42030170034818074820101880c041f00c0303001060342d80350b44610000b0006017880d4028083d161050028640120650001150b01d503a040d28132508550054038250b15075001d1000c101c0550208070030900d4011401000300811400d20170301101510050088008000a00c8101407041d00c0f18580103140f640c22110800642c0e4586500601c2d4000c550744401801d605100407402c1c2c0307007000c0b0b00c00c030512000521002c0c2c0c0c10740b400510340b619001030b50800e0890050440b19003541d2a83d0252882c44001044140c0c1d41e03030f041c14108222401c0340c904440070031405020b60030321044002441000d803102810315040742c0700c0807081240c08414030784003400360ba100850580b080000004200d4142d460715141403004140c28906600b8a041180c05181140d000d000305210804c1c500c0d00400720f10f10035141c081d0401889850f00c22200d00103440006079450801d220039030340c0f07030b16100b5a040054210b03605031611030401b002903541c0e461920348 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 869143498 1250 869142248 869142301
    0xf1209060d090c030c0f031505010806040b091c021e010c0804170f04150906081003020405090c0901080307030207050f0a0521010f090b0603120703180306140915 71
    0x2c81c14030240d4007880d40290350100311848020380f901004a42003065110840317901d5104c4440c10f054000702c3c052541650100e1004014658031034454070006000a001440f29000d4654021001c140545501050800540081458210403c0c40c02500e44001415512507454003a200c40c0b4aa0b010602da40c02980004c4445141c0d42d02054034071540c4250403401d00ca1b8280080c00007807040c91f00c0e40040c035040e850f4881d0fa0816507030742002d95078460100e6910341005a680014001031500364021504086240101c640417040ca1000c201d4050007a0001411a031011030160300709581044080007501080c0e81c15044072038000c0100351908124041c4911175100e4528295a94020800c04411455003234000c0c021903800c907528000400d00181d05403801c81041001a406007000541402d41a4060140c2460140e07540c80444c0c0b840c485500c04106080300c0d050000211b0498001c89644007113542c0600300f24245205010b140040760a0036075162000f4004200d80882142c03000c00d40c0c00d15030340c070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 869144748 1250 869143498 869143511
    0x16200c0a080f061801110313031d01091509031a04020a090c0f0f030f0617070605120601081003080f0a0314270114180111121302120f0f1209060d 64
    0x440d0140031403481c1b07035810007800b00800c60f1000070303800f00d002107900a45448903110317280c040103007641c8040d0407094013188101004109414010517500202c4e0114901a6203003030300c0342e607117014120340b46010b0040b000304007051009601c0c10095031001010060300c1084008208071016020030702c650344000500480c03450380348205000e900100d01c400282c40e020080942c40c3d00e0900308a020741d02c601f540d14800e10070082442802441180c1242d071030040d0422156444100446048100074451030303168546820000010fa9810054241440c2c660380140e290180300d4401403c4070024404002c804940c40184041009130b60341c0d6059501400c40d80300300e62111442040e0240529800c00c010190000041120441440e014214000c01d8180280203101c1103e0f0014118000c101c00d56a011010030080341c04003054102130f06c3d10300e1000e00300c0070300e0000c8481c0301e40c1007610300703650722500750071404a80032440c2040c4200b69419406900c1a0305210f0100702180e100c1c040c280070f0306082c0b6581d40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 869145998 1250 869144748 869144791
    0x1407090b09010323010303030f060608220203070303030507030c080411040509120c0102090f10170a090f0501050717130615030c170c0d080316200c0a080f06 69
    0x1080044d00001c84900c510701883d822241c041c0800342444140e0010740344c891032006440e118007e01d0212266503503404070507182c140d104400308580000d80340031030b0003503500c0c1001a2018800080118002d840010f10303898900030180954038403031045020404224208000a42e1305e85079000f46040070384001401ea61418440f524010190314900544000450420020f180540003445904020740754003411960360300920100f40c00050200c40441c15000c62455511380086c00194008095540401c081c501501e07244a0403024010554959441e8403c00c81d095400c4036030300c01c05000200f015070302440c114207141c0d00001d4007400284115120400040c515110801d050b0103141c005554500e215903400601101000f14810f035001c2d40101d03200881c040c07410004c008003942d04101e9407031840c1d880114010550304c080b404e04003801030b103104804203e030072075010154090400c00200f10400c404020807220a01c0d40d40103100eaa80501da421942100109645812200c03d0f24060080704450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 869147248 1250 869145998 869146001
    0x111321061a09151e09190b06031914010e270d03090302070b1603030b03030d05180c150714070e04121407031d180c030103061407090b090103 62
    0x2210215032240710b41c014001081588216040b4620088540707940c0700d100c400101020401041c03111342d0181840700080d04250a0007001e203d425040c4c8400034100309544006002d03508159112440c5007902031011403021510f21881940611085140c4095071614000582c0c500c0014082c60f03403040f8040504a041c4089106ca0f2001030f03101d0140c44c16500c0b0502c0050003854000002d5005100761000010f55145540403140b00d90035000f4040d1116109840550260528155940e010310042203040e820071020701c210f034000c0d0200800c00f40c0004228804518006224884602c00d140c4810400100301c0510203c0741d01645c0181d03060142c0380e0300c1003000d044c400f9503444001c054940008001c00c00c900c1500790740d4415015200c012410b030200c14480e4150042440042c0842d445010b031254803003081814241c0c0c41002000d00c2c200d2100440307000741c4040280c49040c160750000c4014010401c0c40e016500e80f11803a100c8600c10f0740f0b8992801040c0030401d100d000000070000800c0b18103a4482d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 869148498 1250 869147248 869147291
    0x1521170405041d150403020c010507030e06070302011a01140315010c0b0705130b070515100b130801050615031602190b06330c010b030111132106 64
    0x300b0411503095070110810a40b080e65442e84000d000380508611598800190940034507007640c024040545c1e6000195201d503c0b0740360540520440b00841c00d4156100c00007086034500c280e0000c100901e96501010801c41036040c21414070007880d510b012006018030a40e035009140c000c0c1da82c4001c1130b0340b0040e030300d10000c144003900c601558802c1000c540d070014001e00504104002026200340e6a6900b07212502607550000d00b590480c0010351141307070084000f1608a9510b11244a41d50742c0c82040c034110fa80000c0101c0360941101d4020440100c1c2841800c4c3e1000054902c0c0c80c00c9010301c02050050310000b0300b18101c11003a0407251840910801c54548485a655840b001062450500c2d16242000301c448a02c60aa4204e80441d0644c82c6a030300801188080040303050034507602d0304500240c10244601005641c0c2d903041140d1640d007401940b8540e0410000a0741d5a1030081c4140c1c8041040d810415090500c0c50760a18180002081902451740041000841c1e50407418518032400d034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 869149748 1250 869148498 869148509
    0xa02010e0411042903040201052a1c03060801060b0403030c260c0d1107050d0206070606030305030907080a02010905040c030e07090615020604021c1b0915211704 71
    0x104000c1480c1141c4107a20003118502c3c4030220840941e1000c1309103910080710000d00042d02406101622020610680350b40b060310045007081e076005104140c80d12182c3e1110380079450b820901c449101da01442400080c114000083c0911070520340015068462880018100107a0820300e009202c00640c0552028282080c0e01016101c0840000003d803c8481500c0e598041c80200b203006500440c40341c024240c8840142000c9458503080001d241c0248100b0b03600200300b003184100040191244034055403207a10740645a0921711249454508039411a01c9554020b41c03020001d41c1e0091400022220100c6022800030390b0a107045024003003002c01c02d02c21b40300c2c0000c0440d03900440d4100000b03486591404018030f508034501240d40324010398029400034040e1240c0700c011071008004000250082045482c1d400036407131040300c403200e594045c01d400340d0348004401e08a0a41200383c0000d01d920303a410303446d8886403080141c600c21181401031030344409400344640c1d00d035140c041c0c0d0300070034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 869150998 1250 869149748 869149781
    0x1202060426010e01090c1d0a150e0f0708010803041206050c1b070303031a150702040b060403060504050709140f0a0f11070209060301020f12150405071e050307020a02010e04 76
    0x800303e01d9000e4413400c0401c581100c0d4500c00428400c0b690340070b034441c00e000e480c1100300303c0c2c42c1d40c0c0705800240208030301840c800310f90300301c0491049908410742c0c0c01405400c09041c0d491810342c07401000400180c1081c10076810800c010081c4200042500f9201500308200051a0f241c40e2004081849105d00010429681c00269112028007084c03000440b8000d85003070095490907800c14084030b0416200513445003040c071124102d503426501a120051003d0070004540380408005001a00203600490b1101e403a403040104019042c010b00c001000c8121040c00568120580d00e0f002800052101080100800001d12440010f40181614020a00c4104103100c3c1501c8041001c0e40940c10980c01020130202040e540d086c14403c07181c4120050f410103050006c8400100702c07000000d01800110b43d903d00b031040c541e40e5a84030b458003607a00364031016140c075041c619010400c680048070f01d00748a01881042281750300842d40000c202e5092915070750f910120000517004160580d03884030b651703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 869152248 1250 869150998 869151011
    0xa0f0605030a1a0a122d06020306040204090203010806011d060105091002073c060e100c020901120318060e0d0602251401020403050c060306030f0a05010f06120206042601 75
    0x2c5040942d5005c840340600019440041c0d00540c6001d180310062842002480c2101c0e4140482c0a0360b000e50b0b00034a0040001d85070680d141c999206a0f002070b0400d4900c0d800c104c0040101e402d5004106054020b1000c920409281c100c0c006040c1b4081c030f1640e0390080701c840400c402d44510a001c0d07032000d080380c00030448040c83c4198007070034011080040b04090714051007002c001401080b11207030458000d50345010041503410309202d00a084401c00c1c81c107000300400343e4030059507843c0356540a80503c20603c4400b2199040003004003808440100c0ca80c2100c2c4024400e07203a10605401e90b1082c280d8541c0c40e10159450807400922540403040c000409058906080442d8407010181081c0114400c0030b00e049803145107803c0348036910008110b0380c8030420900c66030a000003c3c50340311200405840c40c801a403001507052004032042119565940c480c010a030595622961015100342c811384451404250b001c07030307841d110743d010340b0030850100807104925031054840a40c688040720001e0010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 869153498 1250 869152248 869152259
    0xe0411040c120f0501060908150406020a121b0813020f300c0108071d0d0f061406040e03040311122b120e0616020f030708030103020a0f0605030a1a0a 66
    0x3004207000d0640090b1411000042844d800104501c2e07400e40c18270322074026159130f501c02000354001d50042d002d0066106034800e16807205c3c4101040c42034200010400000300720001400020002c1000c83e41c0c1410fa4442005a1078000c00c48203c030030141d8400c10701e02056015800006240c0350945429684100320094800303010840c0a1003442c00e880c3c4403042c0e01c0d2150305541e44808901c1006524209102d610700c1440c5c0710341c3c015400303405074200108041098850609841c211280003030145484010b01c501e601b45071040d060703c025100c0207141014215900c00d04440d100740301d098852126404800700c040e901703004035458800c101500065900d1120740501e150f00e005842940407a030185e031182d103881c0803401340e0030200105001412059031b801403d40c03000881d10034000300f10301c181c945900000038208001c0030020701514809803258514410488802202c0d00240b22482d000903013000100d8100050f82d800c0840d491000c2652002e60b180c100310340d8030404040c2e90080e4980d000044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 869154748 1250 869153498 869153501
    0x1603180b0d050a022b0e010908070f03050706020a02010c0809011802090a02090409051e030301030f23250f08070b0f070209070e010318051f0b03070b130e0411040c120f 74
    0x7544000178006005180d20000c880d03007210a500c001402d0503a00300720708c000190035000c0032a84d15109003441400c00b4603503260101282c1003100000017507951040000c01841d00305c003900f41d00149001c004c0c4103485403188032444481e161030303000f03000c1d044d81004901490f01d40d8059801050018104101c04c0495007402e40c0d07600160f8001350354200c541050080003084c080704507416260000400142d028207030b5903e0080c01d01c1805045101658074035002403944040c80707101f090215200005c1c005d0301c051108030744e104a01c4d90260b04000510360040200f400301152080480c0e4100201a4449410b541d0b01200c620696034002c0d400608401004009a080180b07548001d00c2a40d0404c11801040701516130042c0548000d4a60342c006111b901c0740440030b184581401090b01c8001c5405403241000c24a0064180c0169901b418041072450907240400f000d9001810303031501d04400740c1060b03100d45280007082c1102c0c0d4001d507103e0210007001401122000407650415904000a0506c00780250 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 869155998 1250 869154748 869154817
    0xf050a050d0221071e0c0213151a2701020a0c1d13020f061809040803070212040e061905030a06060302040b060c100e121603180b0d050a02 61
    0xb65140a070f0008515618407546403404059564180350306010f12441050713032000403001c3c1c12a403009089003000d0350f81545002c0c22a050a06040301105281000c03555a8054080300c0600b030342840501c01c0309401000d22480d1603035403122000005021044a0040342444d070707030b144050187c1c242030f4800149000c4d540c0704016034090407440c6030056107840d0881c211100441e20042d62064041d000d00302c0c645421301c0200104507803840390801682034103000c20701c4c5410032641079481440200811041580507c04007810a64050180d4901400c0100520b514040a013556000c0c1018004203843c8a0411280718003070480101181c0e40c0039828540800070300203030b0000324000c9060030450001400c00d801603606c05c00e0307034038050702c1c161550740c180d04010800410f002d03016116203051035030500003010007030400031855400c0c6140340103c1e00340901204440c1c10300c903030b02114034041000640d15a40a40c7d10104a20384045015126040c0707150190056040081910000b079600014a650840100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 869157248 1250 869155998 869156047
    0x121f0e04080c210d150815060f120601030f0314120603010605040203070e0103020f1e0a031b08040b040c0512070305010516051e0f0310030203010b030a030f050a050d02 74
    0xa980700c80c440654014540da4001c0325941101c2c1c28000380024030413070307080046009460b0100b1000e550366030146604d050320124803c8103c1604206101c0f41381403101d580a003409003940d80d601408060346e02a66200c3c8140310140424000040c542c04140c85541380d041d003010a2400503840c1d094407100140a58804e40d03200788203601e80307000002c82d82400e0007500c2c410a620f4856007068581140190040e600980c1e008000d51010410b11200c2c282400003840901c007117403403a030307100e1101c83d101804807111200d1859030141030342d1080190710750008005e58441e92010040c80c041d1500d16000c05100055044603600c548154000b800b88100002c00c6030072240200c1c0240115160840409100e114074801540021010040e50b0354100700a60303548154048158038510b00b0500c45022034090704240e4811248601ea10400c006515017409044580d15045020380f030b015000e40d81c00b500e101880c03072208092003c04600860341c240108180c65100c50b03c040709543d610414106e41ea1034000d070300d0f1340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 869158498 1250 869157248 869157253
    0xf152d03010504080a0507020118090b092a0702060d0c120f050603100c0504090903030615052809030206030108031b0622021c0b0a0c0302121f0e04080c 67
    0x8203150502840c1e005540124615141030208001103400341c0c00507030180d042c01039429800c4940742c41410440028100c1c0306000804590400810040d5540070f000715125a900b2400d0207001e141035042400d00d406e00300210303940c1e40110f01c08a125402015440e41c1002d1902d003420303012a0708544001c0310302408032810840d203000c42000404840040d224113030903500c001c0f01820005503650064904200b241421420155241044400c2d5407070306e4812030000e0b8a9000030040c080081c035107401c020340395090043c1051051000c1071105040b03d94501406072540801c503819600030361503e07001d560058405a52580c488168a6580d84102c82d400d92980c0f4488841920040c007255560182456154180440200c4115124a40d07103404007a64440700c00044030b40e4810462075505503062184202c8003407407620364107240880d11042113410a05004204d940501864a40055031042002c040d0030034079642c800d584042c4d045290800303044482020244002e00c0542000380c10010b002008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 869159748 1250 869158498 869158579
    0x913050f011406070c0510110607030213050406030812041104180c060e090c0c03040f0602100e06060a030f060b04020c0a11031204090c0c081c0f0908030f15 69
    0x90125910410201034520306600301c050146c0d1810f00c200048045080c41d0000c00c0c00055107419081010944030940405e0b8006800190702d2010640701c4001c00d8120740800c1142c2c0307551642c9909101c0d1404100070700b0000000030f0100030030354142408080d4003030820421111003000305405002040001e80380ca5244031400511213101ea604600f039900d002d031001246440341030211416400c00c0b664446180010b02c80443c1c1910f1400011008104590082c08401d0800b40b8407022038540d005101c0460b0024020095180c50311502042100c0d8400788a40340309896043c00400bc0c0200111799901500000da02c07180c2d40d00000700107800c0d502403c1070040c89100c44040550301c030038010000450040c18031042200322180d034030071140070b0325508160349441102d90311707400241e1103451041c000b80000070b10840a64070b1489501d04000c41d1240c1041403600079192207155000050002c84001420300000e281801c0c011262080c40700060b041041a840c400d407098000c08040075400b414010001c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 869160998 1250 869159748 869159789
    0xe030a02071d0c040308030a02160804150810060e1f0e0928180f05010e0708030f0d090822091112061908070305070e0c0408030f0913050f01 62
    0x103090780c3c040d1105003c2907103000c0c515642c400d01c9810081c40703008080e9080c0301c000d4600078000e07000d500700e61084503150303a03070b60070001c402d0150108060404100700a050403c000384080258000a17100c842c10306194507402d400003d00354003030300500850322000c680843d5903402e13007005484401c5141140d000e0a0391352401c01c110480100c03000f50300c0d150f400854200117808429805880b682c12001c0c0081e00b40005510ba40c01c00c1d800400e81241d40f41c0d950380840364002c41c1800b8440282480202030340c0350005c0080e10004500503009408420340e80ca071036980811084c48200c030010384202c0c6104600c180900c0201c82c0e02152071095080d4bc3d404c0c480a043d0f1001c010007140c080106c7d07100103050350b498400a11038041c0c03824103d2030000440700b501050541c000c20a11008600c0b9000900c0d80500700460b8100589002e082c80800700070a11040c00300c03c0c000b006440c2001c00340d03982c4230f494a0815000504000240b240d10b8240b6180c001404011030001c0c0c0c0480c16600c100c0c010b100c1020194 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 869162248 1250 869160998 869161049
    0xc030a05120d02090418020301050106030915150807081c21090201030b06131707060203030a0b01030b0d0b1605040506040302040f0e161a0307210e030a0207 69
    0x480051464002000300c1600048103409407807104280310006041c051003201180445103c0022100408403042c40001180750074020a409026107281c1802040060364800300414038000703210f01c0f5551200c0c039000519031028801c400818850041381c28450342c3c0c007001a103802c140901c1c103880b000f41d021810042c5025a4501001c103011180000260420700807200003020082d004904054440043c1c00301030761504013409000c8190142c000c842403415010b12409002000b0003040d5030013490042101e50380200c2529442007030258007080881c51040128010300b44c00794059401f1414480d03900900201c103505c1c9200c0c2c428880441800d030104542a900c9000e588640c950000f810001803006081136004581116040345010803883c0343e1049007401d0000c0d24100040740340950318104045030170074661200032046800030900c1c0d4140440300410117000120544902c10140c601d4400340641d0307620600e5641800c1054944418a031203001392a080355100d02003014142ca4404901c00c2c245 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 869163498 1250 869162248 869162263
    0x307080a0203062206181d010e0c09180307030507050c0d11010f05071e0b01150c030813050a080408070b0c0303040209100b0309061e0721090c120201020c03 69
    0x141030000105003e400d182c4084502c4c89184c007210f03210440040c1c0d8100ca0304041c4001c0340c1d120000f03d0710007503880c040d040c080200701840d2266814a07201c100340c01400b040700000003009503210622943d80807154440c44066840d08843c0348400609041490390040c003402c5c445104a09440b50640c1c1d00c401c00c003109401540103401503000ca60007440e60b41c0100c082c204100d4050401c141480a651100d1b1500001500080c0200416103040310412841c2810140500000c0302c81c0b03491203844041c020005440b551005040c000c40002140800e0103503c003124040e6800422500d944590746810300c560f420603c511003107440342c6100445e080d41040f0540c0c160400d11401141503647d2602000070220024002d80103c014040300400c404090304011481480c1000083c00a8186000b200c981400c0031816080010042c0040c0300015038490ba142d4050802d044003d00611004003940c00100260440241442c0a8450005044a007030704c0d040260350003602602c194185481c141602c5010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 869164748 1250 869163498 869163511
    0xd0f1b080109050711030706060504061208040902130e07031409070302010c060f0608030a020a02100e0f0d02010519090825060305040302030d020d0f0b0307140904110a0b0307080a0203 81
    0xc0000c0140104400ca50160341e10a5051a00b15110103201c101d0500713513440000251000c545541090105003071a024400050940c08072005601249032500e2110b40140e0080450140e000202508403848040f0040044d0054080908182c03c25a40143c0100811150050300482190010341781c400c010960b041180e4040e11842c1400540d5038410000340003081c036110555681e4000801d5481041000d8445500d80750000d10600c0c00c11300401c00081411112102005000c030643c17259034503181001c0134030513015070304070b2b400b000d5502c010b8403680960b10b003052042010b50902d60415078003000c4c0c0c5045650600640300c4600200003024480d148240e00000d06030310803a010051548a94420307035016000f031040c1c1c0d09020380c2152201c140d82c400ca0746491044c2e10707010782c04076100c0c031031003050a00c00b4224000c200442c50f0074440d07400000d01990080c0b04110642c0001c081c03000f070941e61400003100504140b038207503d402c04079001d50016903107040051112030025030155a140700300c070f00402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 869165998 1250 869164748 869164757
    0xb030601050f0d0603080301081b03030a050409050403090b271503070818070e06040b0102150112030c06110408191a070519021f060e0402090405120d0f1b 68
    0x101c01c0c4041c0059106803d8502c0a41e0fa9280c0003012404983c083c501030910300002e0029510110070f003405072403540700c02034840c1c0c00421070000d0341c503040700489003207854410b004243c503a038505040c0c42ca483d440d841007880346000603004100c0039005040c15090041d40102c400311078009002c1c00707001d0401c100d911706050310410210301907501580b81d069018000440c81c3c14500d0681e90030606240e82680b2002041401105000d500d1070180115202d01d482840207240c40c0c4190001c07030b1604001031140d48030042000d21800141849034206e0311712240c0001040c440001d0103c2401e2183d8802c2c42101d9807405010041040d20b11400c100c076003095000550362617000c20b11081d0854048003d0544014002c040201c002004046590651160700315005000400701840f42250350444c03088261003401e24000d014004084250740e201c2c1c01580541780c0c05803a03980c524045103400c1040c0300300c0318450310215103c0d4031640c203504201034041c10008180f154488880d800551860034480f00000305 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 869167248 1250 869165998 869166007
    0xf011a270f061c050a02040e0a0203071a07080c0604230307030305070c150e0f0a0818010c020a090218120d0305041104060f0e1f03031214010905040605010b03060105 73
    0x244415001d26000300c0b00905202c240100d050306101d625010303038421901904461507034419032506105192101c41d44a01409010841d41d002944030040350040c68002e02000790021071043d5450300340c982d07466000342801d640d03500a0088690720b48048400322410762543c03100342440d0304152503007000282040300441c2084c0c901c0e0b5044d0041c0400500703440c10001c0180000b80401c0f0b4003880791203040380b10400054400c2140d540c40d4100110f1b800802c1c0140d00c02902e603030006103000d0850f140d0003042134264a28495060040359a250040b4005e5444000da11000c07425180380d5004242d2081c01ca114104800c600c0002e109400008446c1d500c141d41100c0301400d1403500039003080341e00c144100318007210b5100510002c2c08a50843e0000c0f0001c0e0803c0c43c0a00020806a8160341c0000076140704009040c000400300754116158017000341007200d4009540d603548007541003200350000c008146515580c40300c00940050004443c1034649908103000050f0645015045a006a0042c0c2d40d0620b80b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 869168498 1250 869167248 869167261
    0x7060203090d110d0b04061e2c0f070f2d03060f0f050109140901020301050d0312020c1038040b2101020a08101409090f011a27 56
    0x800e108a42c0050b000519004c038800000c1001040e00d10983c031880c000550713042c0503480100d440c0c4000c05030100c0c0924141c003c100e030248210000483d041d00f00303070b2103029001d40c10711304c3c0c01d1000403400100f45d4412610041020048804003d00703640c2c510f40301c4204031a000030158060140750301c5c0060742180d008814400325070383d40c2111145a03070071103002c00d0100d03080b0020030407110241d010041182d55071610303035030309049118801d411048110080d030071541013400060300c961081d81c0c02000d014090502c120100d038503406031962441003d00f40c3d40ea4407031540183c0e001d070049044195040312400000c2004401d52119480078070300c00b0035024000e0658505010040100c0700700c20758062248054950560300380da0240c1c2030390900000250319130707101c03120180c1400000741c06d25081c40d920705001d0000100780c105048910000b00d425074010789650200c6400d286c180c0003a178109508080c2014075191142d41c011705c141c0025648176500c02d04100384900508076080c0401e0032140e111020424 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 869169748 1250 869168498 869168513
    0x30206030106110c0a150f2102450117071b0609080706140408190507060e060103031107050916020c0a0609081009151d03071407060203090d 62
    0x1540b0742d03910132110000480e800080082d880b5034010304a44400c2a0030016140d445464441c03468010b0a1601c0050101041c15519402d03c1030080a0281e003c160412424000c0580445070310082e60850740200c9038078010545203420072000414030350b035602528859481010380150b4078481c210f0440a40d114010101c95004054055800315485455881c0205a56202d000c4042d4071070740a1039030f2a03402d4078012064610381420b001001c0e16000401c008511024116402c0110b80090030061100160064910b0f0094410152410b40341100c80038001100003010f6040e02d001c1e880d107810a042c400385540d582c0000340100c9802c8454480450640c0d04079814074005014540142d55181411034003203058050140d00c40000074541c0f980410195005204130819503040c00814000c41e00d9580f078140285d055078003c8440350742c0e0358074511010314030701c0313500001c3d0402201560782d0391040d810008451514100c400d01745014641002078614000011250015000b03130900354032140c0c5460340385 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 869170998 1250 869169748 869169767
    0x605090f1315020f18060a020d050a0c1202030a020c040203010f03020f0a092d3c020c010c170106090e150604030f0510050106141c090b01060f09030206030106 70
    0x101c0c0c0140125905003030300715030300141050400c1010341c1900d07221140742810880017440106400742200300030f00c040e46907010030003d40c18821828855510a81100300715801e006408001c1c29006e0b00ca000c00500710b6000c001000e4000c96542140e2500e0a224200030483c4001c3c403803c3c1c01545004004c00050810700540001d8042c0203085a144956460148090302c150090f200707a66000c1d21101034288802c1700c012061018540d008002c840c0400c2c4106d1141c204c103403280c003801107850811305480c03802c5904020190340404c6081d03441300041d64582d80602083c00c61540442c86a10702e0881c1c5190403404107048603080e50301d0b28022441c200240a200b06c02504000c05844c0200c030070015a21098020030065100d00d01d12414030030982001030404405040c10000c541c00e2400400c1401c0d0301980140b06080c1c4d19402c1a5100e00001030498200031017003040741d03032a0411030703032070188107158070b1007030494240380c45504040c0850001154040501e00000794411020310042c03040c40e104242c0e09 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 869172248 1250 869170998 869171003
    0xf06080606100e090a06060212071a0c070c1412030906030a0c050403050616030606031a04020901030f0603142119090b0c0a050d05160f0f080301030c090605090f13 72
    0x6007800320f042c0c004912201002c4940504030368441c2e9040000c80e504002002c0c480f401201000c5c00c2440e40e65601c5800341000d5008280c0e00005008500303a290207904131080140d112071860050750fa544c1c4101c490f51000e00800381f083c0c1c0d00a07117210b41c1440c04401c80d83d0900c0001c02300742ca195941d1107213000038182d101e40740d01000011701c0302100092042000c00c0c0120780c1000500400a11400020142c4002e900440200340c1000721245000140c4010740741000c504403000758540100f040120000e042c079116150005060180000500601034002e002c50080c1030b013580d00a010051920010000f28001045508404c0100204009c0f540524000c41e600c5c034071703014150f41d0b85d41c00c964450b5040384241c0c2c02d0300c1c0c01030411142000310402130508800c0c1103080c00303400c00d00d80c0044407500012403080038201d18103030210b400c03c00c90400c80544215901c81302241c0c50b1b5031203003850080401c4c540035000c841c500d001d9000c00c1c145409904d00b8130810b070b0f00d1072400259842980285001c69003941c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 869173498 1250 869172248 869172257
    0x270105040e0a0c0302040305070f0503011109010e10030f110702040b01080108101113080f010f0515190f060f14030415020a020f011e110307090312020a0c0b0a030f0608060610 77
    0x7c0001241070024030b006141c030703840003020103042c10101821140d9601e07001245481c200044065640c12480040a8100c03c0381c14509080e001d0006502412130440948206850300c02d100511700341448c09011018000e8600b04003403086034005458180c0300307000d420321503803155060075502070700c6402c1010160141c02a481c1410401e07050500760720800c0c0c010b14855080301c100d0780c91b42c81d024885c131600004000428031650500a1a41c90400f25802465005404039051340c1c03144540381c009040144041951410300c00e5a401c8010248062100310000048215022920043d94041500c0c05150001c01408421130303412403800003507001c0c2d103540055001c0c41c01d0f191059102840741c91468000342040d0902506414140002c640c01140480e1600320b040c8240008a907100c0702c036030242d036444501003a010400450907458401d101c40c1c010855007440801140c142121000f03450703400c4864505100c800d401c00300210130b0300c0d83c5004030b512a90000c000121a450154003201c0900d8041c03d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 869174748 1250 869173498 869173507
    0x60c0c1514160218180601140f03030c15040201020717100b13092301020c280803010902130801091a0a090b010807031e030f0f050906270105040e0a0c0302 68
    0xb04075100d4080d46584c0c14070012904018089801145540c4014021406407045e1360510981d404414000444071f402074032000c000d07a40c0380d103040048508e460401c104960384810310801d9451812400ca030101c2c01800f4503200050008500c02e01d607a10115a0700160845811034901c10004203101400142e01c40454070410070400d4041c0300300a4590300507540402055681d807000d021202d543ea100c600c040c0c1c41005a10001000428015854001703200f20103460a5544c0c100d81c00000d01c07280141050900000001d0121480d034018032481c0c603591100c3c06d40e240d842c1c6501c1c0c2218441c0c8009004100e00744030780c1c403030f562091514036400407800030005107140f0341da00c07554500c1d60240c2049a03d9440704100b0700500403c001c010320391080385c0c084001c03400400d40d0001c2040c8282c018010a014411402a00340341c0100241c8860f05000351807691102c000f8401440006500114010000700310300b0303034005a511a030226416039031075500c00c0903143c4500113010010301d92040d5a0041550900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 869175998 1250 869174748 869174753
    0x30302040b130303030e0f0303060d020a03150b0405061e13020c07030f060b15160501140a1505030d0507030e040e070b0d050f0103020f0f130501060c0c151416 70
    0x1d02070030904181c2d0481c048010704518028003100d402055084407030f8000003400e8940c0c8400000c0300e03401182030b10001448502440400e100030b003179130001024003001c000d0701515141150700071030810508480507c51500c0e42418030034007004480f803100c1521004502800541044130201b00c1c441151100180f5280c0422039040c01e2501c56042120864a4441d03200309008950243e1440ca400449040c100c40241c1460440148104416445800464030124060210070b600c4200080b103914101811440c20700380140c02000a00d02d01c1110004078032022440b41000128451600c0c4151031b0315281600dd91410b65684d102c420f19141d215440c1d012036204554140640c500410b851900c03261075060034040c06003607500040202c00610503c400400260340c0b03035115210a00f0055400720344142209003c10241140480d1042d226403d100001860701ea100d071898648502402120388220b84906070040800315440420300012104441090b150701020024540e141c46240d44a11b01005035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 869177248 1250 869175998 869176019
    0x7110f1810170a17090607020d0305040e0f091011160c0b040e090d030515040513170a0e0904051c020a0c0b120108010c080c0a0504050901090209040c05160f03030204 73
    0xd41e5a03600da0007400d00c880800c45400900f004c0c1241591242e0b0814210300c01249440c000d002c0040c0c4a00080c921100c2894011320032900078000d11504a4107910b04086e6904103424240c030314511b02e20594682d400105460321501d40300940412040303146c0710703102c605040600340c500c109640d0300740143e00000310303071400b440200b0041c280030900c8000c0c1d180a88089042501c03004003401858103110800203903540701e524060010b541260006069201c010420004d88c2c0314580040240d07400c41c400380800e8900c00054203501c0300e2642d908642452039001c0c420840b00954004100354444840d400012030b0038202001440e40c0c130f02c100c030000851034642d000410b00360340c8401c0307900c80300240089220804c0140c0f5805030602000034446026612001008018018130400c100e03d40481c9200c00d01d440780084900501d0000d103080000c1d40c40303000b160000d500c2180d00a02c074a00c0c01800610076400b0b04244c480c1d00f5945d0a580c0004450364441c0100d01a04810440405508000101346071054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 869178498 1250 869177248 869177279
    0x30e03030313080f09180f0f0f070302071a044407020d1704090b0105070834030e03010b1207090f0f020c011a06130612090f0807110f1810 61
    0x100b01c6c910041c1400c288054107000302510340311b200305180040019400036401400e4101c0c03209d00d001682e4020f50700701042003140400d640c2140d203540d282844184003c441180008840c001d000419141103601d02e06c461540004031402c0c40c0100081002c4400c1e081c030b024080340350018254400031303031042c0e85040c541030b18032900d02864500800c041c0a140c1c40c0d80b0442802c0711082c00d0103840c1a106480d81c210700d00600c16280c00e0310442d0002044150700800151840341a4290036030480e8941e450080c14201003001e4440c000d604e031014000480c0380c0340071181195034501f00a00406814080044080c0c5140e200f082c01d03250300c03003100d46d0201029200404484611500000710700c504c41c0d20114207101080380315486590300340400840351682c562280700322103d6040504c00c405140046001816203000701a2070711070446121001d00811000a02c40244200141d040c5801c000003041070619106104540101d0000c8d0904811b4031401794042c0c0002411503000340440d9105c0814851410b0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 869179748 1250 869178498 869178529
    0xf0303041506120b0a0e07030507060c17191d09150315100501030e0c1201060f0914012c0108010c0f1d010f110709020403030e03030313080f09 63
    0x104400780460880355204a5014080b406000304120505442c2c603804c600c009442842010360fa4200c2650045040100500440d4041c050700d84445d40c0c1d41028050503141202945c1c1c1004030250030f07042941d000119681c2c081183c50703080e00c0740c548480c02c441c18900c16002c50614003003c0800740c6070340d96074140507100c3c1100050312046a50b00c07905060808030101c1546980208078410710442904000060055440c03c0ca0001000c1d141c4401061402da1503c480b1500030607902d800350b010a0064000c44103071110041d0410301c1954480045049500c1c560038001c2180000c0c4c014071005849405c0b142d11200d1800e0322011004442d0350385c5002c2c100c01c0e0300104032a0b540b0f04518088503000304110300302c80128284504103449400510000103649602103040040715179543e21140e01074008074485001c064103c40516850b800a11b0082d4040d000560206035403c41c0d4031102d203400002c50348204102074810b03810000c150f80d9515150811340540c0c441c00c1042c40039600b01d842c0d030b000502c1180ca = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 869180998 1250 869179748 869179763
    0x7030303110c011b0905100801050f030c1504082506080c0f0a030c0305070302120f130807060b09010b0403110409141605180601092c01031a070e100509030f030304 72
    0x70114000b41c505d40b141c0d40414061210002c00040e01c82e040340c0a94111101a545440ca58503003000082c1841058810301c2d03408004540e52803500c2440e08060010b44141100301c55015010b10012192044666580c9148848846c01030213440d12890005410555444c0320754180512010140315680202c00c0c20b42c0001d54907010035001d564107010760f42e00400d46050451a004c034a81095030301581c001e2418900d22074100c0402d002c3c01d941c41e4101031050300840c080391030302001d10340400500b01041c22076105a00030310010603016029001c440c1141d9000f06121096601c41007070001404070030006841d01d6952803520091400180010b0b42d00c088089603101501d4100410005015108881140751280c2c80c4100050380e40c10008a0060b50100c400d07800043c020f05d010441a02e508074100119100d074200000b0400c03008106440f290005011800b00c00e56404004450f100194405281d000302482d440e16a218041e0004050450020703041e2101c100300020308510396402074400702c0b81c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 869182248 1250 869180998 869181041
    0x908030406021206040501060c110a120c03120807090302010305090c03160501110a11010c060209130c0e1009170a0c0e0412030e06010306020c1c120c03060807030303110c01 76
    0xf11245802d00368441000c0304c040100c1d50610030018840c50316110020820340914640d85440d5444804080013055004440403488405181c5110340b0891440100c070342c0c407062281e100500b4003034191a031062135142c3d45c060f04640b0350f40045014100103010b0900f140580a807060031901e0500c001c6100c3d01401c600d405000c0d1610000601c0240c501501c920940c01025488000900000000f01c17810f80901e031640240b121400c00000a200d0140441c0d4000007980101415007880d4001c2d2504181c0e50310b80d414001c00a800740b000ca042541410301c00255014800d01c4101078506d80306642c00000011a0303411348003a81c50345c2425083e900319045608a0030108810000c1c802d0400c10345d0301c1546018409080b095800c0c0b56141d1060000412964022811103150b48007000a03403040c100b44400c98080c00c0c50110090160711103250f01e070209c0c0b42880d140300c0403c3e011740541d000303d90918008090840c03950300c1c22001084d2044034101e014004000e80b100402d424012402612021420038140d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 869183498 1250 869182248 869182267
    0xd05030318070e0403080907090f140105120a080d0f240501142a0303040609020a05040905030f0304030203071b151b060c0201061d010e1b0d0906090803040602 70
    0x1219003041c107407811940072910034001c8080c0c003409981c01590500b0211a9911120419410844283c00c503000031440c0c200055503454280d048013241d85021400c00c5d4803640c0350014003075007010000740f0840503440300a01c100001c10b014010030090001071000600f400d04c80001c2c0041c1d40c1d00c9111514540207a071090a0007090b0f0300a4000181400d0038071301c400d02c4000c0c405d4071032402410011241c0d080d40b00c20189c0d0002c114001402c0c2c1079510390640f556440c09141190040c85ca600040e0b029007141c0d00041020304080c1708810080e0f8100c0c0c02142410b803480a844495800104124210b001c00d000700b1340080c031070387c0810042800d501a000c890908202c0212100c1c402814941d0802503101608808207020b1000c00c1415030b04a031001c10041d2007031106901508460b03100170000c3c608103401000d040030030540103050798207000c070742a03151b00c415010f100051005c9014600f11881044514110f00c940c0d0b00c8400170300c1c8651000301d864074181e190b10800f5002100c05896541d00010503442 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 869184748 1250 869183498 869183521
    0xb0c0606010e090f100f15020c12250f06170610140a031b0f1106060102030319060504020d2a050910031805010e122b02090d050303 58
    0x14012028a40b0b050214040000600241c401074144059075162501003544c610003040701001403d08540102d05150b59581c90080c9002071002000041c003581d040c1b01011300d001d1141c00115252503000b40080c0060b00c010307103090b91288034825142c001d2410002900300407035003004001c0066442e14031140149403445840d4180060102c1d100e02d0b026080f59650540010b60112b000f0b40003514aa03c80c40000000e500404e06c91451503220700d4048800001c0a82c821122085c1d88140d035900d401c0d03a81550b100b0359480d10300b078a109016030014000900c10700460126030402004500010030030940d56400304040340d01c0340b02a80340c141d0b01d42420700070003a449954144e0124948aa501d01e000150704000c0c40390140d6050244a540c010540c031b200302d4031907000a60903000703101b00004c20441c1464014002c200020311180b2038041d0a072030300a0015072005a8411040140c10010b24070301d11124041c604204d000300c103052580c02d1040c85a04d40300d041d80d420400d880b9900569990808903940d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 869185998 1250 869184748 869184751
    0xa021f05010f090b0a0e09101427100c050409090606030c050d02030705060c0c0301110a14030c0304030c0c03080a110106091e0518060702070e0c0f16110a0b0c06 71
    0x10740307050610300031141c00c0d1141d40c400406c8803040350790020395841d041e403070b01d0514455032940380d1550b080032036520160001ca0101ca00903205c10b0b13102450000c4200d40079041c851645110341060f082800043e0100c1e6858000c2e120100c1985071103450f25071148421002c41e0314a4200b40c54055441c0d40038010000d00311808005820211402c8070855040d0303000a582d44524080c40c0d0040102062005d01301004000340345202d44002c00901890580200e000d00a40000504400145065140c900004540c2c400c0301c1c020304085075441d01d182d807591405c3e556054200c4041b03d004240810001c04601e24002030490440950341d0282503450003005603007550801d800091343c042c61701410800307441403460270034030380201802c000c51569034031200c40200c0c0c00c4442e100445030199078100280c1a90224004054504000c442415a2038138074040e0560b00440c0424001e0540c1080000d113004800e505c01c41c2414401e4502d0381e0321b0540756000c01d81140301075002140d41e00f00410b810203000760038044ca5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 869187248 1250 869185998 869186009
    0x81209030c06120a1109040e150f011d0423010c030f0b0a0303031503020a120b09150601030e210903104d04080d0807080c0a021f05010f 60
    0x40d040c03101802c903518280a003e0138000c5901d65808070007a10003004820b0b1065030340014002c00c4106640f0f039600b52a0201d030008142c10040345000100a145815403850685528005e80401c00707800c8094094501350113807040e20044c401c1c020145081001d0310b050030380720018100104034407030001c0d400380039141e8485600511508000754090a03071640c03180300086036050b03e40821520365410000040110b1500081c1d005051030401082c51103180c000034035003d10900d11066075681710b24041d0b86401c0503a500010709400070000c00c0807580300f0342110140304900419240c4502d45900c440c2002900c40405034562180452130194a240a020004a600f10020180140030048080c002e1060314240c1003511100710700d01c40511a00c06400b08030710b00e40c607030404824410094000040ea0782041c45035403068400c501c150314440c0d00c6404000d02840c00e80c1c13601c010030749400d00e000b42a40c104120200c114032854040590b041101501814004011600040d141d410440002304c4039404c0d4005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 869188498 1250 869187248 869187259
    0xb04030c02030f0f25030213051807080d030c17010e060a060305160f0c0b010b03010509070302400b190c0305040e0a060306090b0a24120309081209030c 67
    0x1c119445074049100280c0f01214800304000c49011035005d079600001360000b07500003105004194001040e80c2c00507000384030b22025040c0080c44d04151550b10803840c000c0503070075045000d0780742c48280a9001043c0c44516820b02c1c1d02c01d00c00115a88c003000409a02c0f211014600340f06000306820a0061030010300b0b0b59207000e00c124500b03042100000700e441d011600400140280451000e07119800c0f205003d81d000e000700314a56500c540040d0b281e0428040c40c2e01c11103000d80452000c500a20886a00b0180010415646c003442908400c40c01c84103e4050107540d60107981e20400240c4a5218018111582040f0344400042c41490382224040c00820305019001c03d1407008079801034290b80c00c86904a800c19056503507048400302414003540020306440c04d08000f00700f04205200010300c104218041040310303840d258864440300000c4107011981c600b43c0704080c8807109511140783c0d0400d0180c1010000c00c0e0762542c0176032420700700e107140103e00600400c200e95540790500c034000c44100212103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 869189748 1250 869188498 869188513
    0x3040c052701030803131b0f060509100c150c0507050c0301110d020a02010f020a2d0909020d0905060c0d05090c06190207090c05040906120507030803130b04030c02030f 74
    0x201d0048030001800040c1941201100041025a180c14045042c550001c11840080e12001e00810201d416000300345e80401d14140219640c5d10506c2607841416005050107144400d0140c2954903031490941620340320f17195800c41c220307042103006140c5105820765805550710441d060090401018608080c4264108802243c40401000075100c0c8058603003c0169642d1540070180d0040c002c20500c203840724004195400ea080d000310396180300c3e03016840022000550411002c01050070031a880c0b010540e00c2c0c00500804106902502400050880c0060740d15951b8a035030380350020032101c050709040c0002d204801d411080c05003a0300f2a146800410641c050040001e0460260082814403100340102104495100700281d0300140310100c82000000f0503524028503691140c0030f244941c40c10b2240000c1c1e0076041005649981d80c0000240180c20300f16030750503440754805010134a108048074041d001044169240360b000c0c501c213898500d2401010301c1450b00700110030f42803002e950400326 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 869190998 1250 869189748 869189809
    0x2040602030304021c0b01030c150206010e0a0213230a080303060d02010c0f02090109230103081b0a0c0e0109060b0703020c0111030705100b030c0a030c0504150b03040c05 75
    0x802e4a030070a0381102e010411080d601c4603210f0785461040080c1c8001c000d08000010b111200c034031501a50b09014281900b8a61b04400382d994483c20310071046480000740014099200940c00380c1406e1000b90b80407228103a5070f5143e042d10500c01c039940390007080180540d0b4207501e440305001004010a1001d0350951801c0e00024507444580500a814420316001e1441009207241403030400990082440d50079584549031580144044000c140c1100221101e101490810017100ea040b254803107445450091508011409a55a00d20f204114410349002070002030900300c000b0043c04134a2490b0b07140703602d00250f840580c0c0d019404803826220404c07007180400d03808100f02d00c10201c20300302508074206100c19540355101d95a005080f5004124888249110b0380c0c1007612000030490031140310300c00900c20413101d40214440203200d07000311881004582080d4201e022401480740d00524010794440b030b40c0e64103a00844040740c1040901038284081e151000d80b9408100b40000319081220080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 869192248 1250 869190998 869191003
    0x10611060c04060c230d1d0303030103080f1b012f03040615260c03120421060903030e15100902030402060d060806091005041a0a060806010618080102040602 69
    0x1400b07210f0822000e1405002403003045101841c508030a00c140c202030101800300f2a44a02901c1c2d940d80001d0b905504079003000110031002c0b00c40481c001c0140d442c0da4650703658482d8640c006148000e025406010307400390b1855518024000b03030148400814010080c901c400420a518200c0c1d04d070152007109100ca03d05071031026280d016a020a00040078140210754140700e01a1381d2013500150020307280106840001c12160071b060012104680708031500b4401c05072514071000c031030883c03c1c3c004d010800103440d00403e40c0701038080381d0b0101004041e494488070143d46241c40181d01080c4c4440c003090980d401001851217000600601100700d040c048600c00201055101b4150603603004070204003950b4034101100c40460b0102c3d000c02402c1d5490490b2038503003004032200304250151015604407a50030740610b6104940c4002c03103c801d0340020004107195140039040480081d540c14003ca1622002c03c00d00b0f020340f030309403240c0711031084040034101c075202d25030032824180e40140300c20010103400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 869193498 1250 869192248 869192257
    0x81e1005010c050c150702030f071a070c0503241f05060a090f1d010b130302090c0c0a150b010509103c11150f09160e010611060c 57
    0x1d1810b00c0d02154503042284c0342108100c01aa0b020030b0961841c0d04e100782c0350004200d0703940300340c003600c7d10082d1200d40b11352191218841e540d901004110070600d2966804001c00c981d42c49000740c400c031181c80b0400300c0d1400c0c100002002d081300040e008001c2c050508007034241d022103020402207072140308041d1300ea0a40e04030b10665008940100342d80f00381134083da0840c00a4940400c15009007a03884514101403851118590180052040003050400480b0f0448550440d41400e0480382ca14580c01d101b0b50040003011015559418016100700180501c0002002c40c011003002c0800810080310404a0f982c00000c41c0c14403100f0031821050f510303800f1348414600000e04005600c0503941480700071b00c012510300d00c5404183c0c0400308407032007800069211044815900d2482d00740b965a05d0581e268201b4040d410880b0039032000423a842150800d00b40d00402003001d5910114260b0ba00c0002402140c02000c07480345080014801d140e40080c5000d404010080248014200245180040d216 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 869194748 1250 869193498 869193509
    0x1213150b18090703140f190309050319080901030204030204140a0c02070305151b0408100506040e030909090c0a03110f04050c0a110304050a0e07030b03010209011715040c081e10 78
    0x1101800c1440c01d01800030b0f65030410300c602503440000040382c80d100c104015000480c00720709c200d0000319440c100002c3c40401e21200c01c0104026a44070b84540350a40c10004807203040540070040400181c80d07500544230a19110b1208000d641450b42c0502c09981d5010b4001d000c44d402443c080011820002c2e4182d40f4141c05007042c4010384800502d06400141e41c21405030340e800002e40010f1a0400041d0f151109014000c01c0282e911518208026240e19108505507507105105c0002ca900d0301101464220388840121000c52036024040b9040440300c2d070041d10900c100d016100d5044c10540f0740e03031300c0307015040314208600d2074041240c000d5806103144240400c81d090507a031512690070403c032400340c07038001e010181c04caa41301c14680720b6400803a91440068100720103540141014025960540390503110030007209001d100904414100402410014051000d00c1c2090f88407446030303a624281c80d40e40c07107040740b0380035860b292030000351805041540e60b48800c00105031442c08651090310f9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 869195998 1250 869194748 869194763
    0x80a02490b06091903020d0c0f0902040f050f0d1506030311010207020a1226030610030606050301060f17010b07021f14092d0f0d081213150b18090703 66
    0x620300051840c03982003031704025004802501c0b840103002d03002d035192080312196481600d03850b403100d802c002640034600c00c451062402d410f0034485490049944a0554005001c40b00c1500081d100c819002c440c5034030111103195200c80a10034541e200b24441144e0034610002d44c030b0034032150f0110700340418500c0368000b406000100c01c0c0c01c10807d0192004200b582600d40a9124888013045d04a40c1c820f54942d40314406002541364094024001d160840e083e0743c071003900b103030310300402600c110b940410014100304400403030040c507182840c0c2d210b01804890303262075165142071040c0403040003000091070610303032805100400b02c1c2c0d001c0c84090f00d1440c1614196104c0d400d05011a41103000380701c450f5617201c60b80f07290080c1401e000390881d9440c14200c07040780d9850f10000921860701e14403040136010620030094556680050310790b2942041004441076524900e940345c001c0020b544620320351416480e40c442d5403040c9820400b950028110081424140c04d0240c1510342d1961103210007403010303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 869197248 1250 869195998 869196019
    0xf0e070e0127020315041404050703060b04110c070f06050f0304122c010f0c032a080a0302030601080a020406020a0b0603070812030901050c0a080a02490b0609 70
    0x251408500d9110721400144159105d04111508016811040088500813840c060a0004a01400c4c0c0f50318016904407020301a090b0550b00c507580540100c2c402641c01540b82c1229100c505020401004100080c201405103030b410204000110f414950110342040f000b400a40001811001100e0300b213940030342c581301c074070405410513221003602c00300008030051414249601d640b10f1100100d250701c03090b40d41e5100130107030f0f00e02514030384444100900001c81042c01c00340f242402030350036070070f0501641108411401d156039a402c2c3c1d41c42502004002034012003481110358000c010290801c50408066051030f0501800030f50b12085060040c000d600c82d040412403945041c04030384003400101d420f03200c0307443e40070142681e00d0703009842070801703907203003100083d141e1018000f6640958002e0707a0303841e401e40301d19001402941140c8849082001c01401071342c00040d682d04480b540083c00c6040d0440101400d60311400c600b040b20452401c0e90410403001d80c00d0307860204aa00c01c00c02100d1004d00c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 869198498 1250 869197248 869197289
    0x150b0103140a0b0a231c0c170d09032a1e03140304050a0b0f0c1b03010c020d0e1e0604030b04120207030f02100e030d030f0e070e01 58
    0x26004a14450402681c52014422040200d8210310741904040d640f441295688015024030401c1d0340a40641207a40a200b2440720714040c0c8022110ba82c88140c18904440252034682e05004558070000d005110580324512008003481100300d041050301301420001d00e5500c034501345140e8078181e02000e031001d08e09480c0c01d00c0a550079102400046084c2c0d0014100088160030110b5a0b00060300d880d0107640301d48052000c000202c600b601c201400c20071a0600e01100451070744c10468031454103c00c14001d02e07001c1c110070030185803450006d0501650300d4100340d090508403403200048008640091190003400c5800c485900358158050f108107400024202030203a5040b1180415130740003800050000501c01c1c6203c0d0700c2e0089001d43e80c0f080003c880c0b83c60582e551140d030312009043c54034080c08600507140c000380461200807182040040b02404000280c144000e8001100c0425520010b811041465128900300555104002c003215818031084100c82d910510078180581c5500c480c1001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 869199748 1250 869198498 869198501
    0x70e07051309060f09150501051c0e06061f08150f0a0e1b030103030e04090812040f05100e060402040c0302070b01030c1508060d02010c051f06030b070c150b0103 71
    0x180d0000032a1140586590b01c2601404152003100c000115081c0049003e103950712414003200c81e0100d0140002d490080103403100d0304500c804210740ca040d02e0141c6001d036594000c1a454108100c058200b0740303014420014001e10000248203408245654494180d030000702903900702007a036440d00007000c4030400203221f000980403010b07080088900300103000340d02d004019005e04625000101000f5880b140344c0f0550000744000360003c0c200710440ba0160400351710803001d250051081915041e08126001140c7c41c0c04d075421920b44015a0013101408000e102c1c0202ca20000c40c02030018400118543d503842202401c043d2045955000c44c18030207000ea4115216076500c551140059a92428070b81403646540c40b402100c061084d126032504c03032041340c00c58440c8200608021102441da0011501902900d004803000d104442031410140d81c0095150035480ea1401c002c00c8850541c5068081403d001c0c1c9082c0500071074030400d4000540448010340c68000c1944002a07801c03030540101d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 869200998 1250 869199748 869199757
    0x20f01110f03040e101a12060604120b06011808070506282c0a17070b04150e030a0c0b2206030f0c0e060d0906110c0c0108011502070e0705 61
    0xc0c071480001000143e01c107211220500c1040c020401c420034507996a80d00492500b41ca0788109040c00800030b101c0400c00c1c2a4001e0307000100030f00014101a1261191520071a4486056844201c0c52082011642e80300340c540c508240c100034012071040c0b42c10880c0d5660403c601540d0f1195201081c003030710300c4001c41383d4000b03070f0724034640c06582248806502625a40c440704002031101010b1340300450010104002c0580403001410041200e031811200d9034001d00c10388040f0409000d0807400041d10210030b0041d101030400000b64000c441021140a0b10b0303501d8074101940a5001026501c010031f0301d600d407040484404680c01c80c1e80b0142c804100050883d026070f0106003062815002c1940b03071381940304442400c10904104003290516400b0b41e44011000003080e44408c041003480c156030302d02d42004111910070240898044501c82000305190003d1003096000d40c4140e907054610740e80078440a0040c1443c0c0c40700e00c1c0c00f141c4410004e460710541e0003105801c41c4480040340d00c4510800c00c56 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 869202248 1250 869200998 869201023
    0x1020312040606050a0b12010501120b0a032d0203070303080702070f06020606090c090f210304030b0405010b0d030e0108040c0305062401030e032d0d020406080f04020f0111 76
    0x88200e403401c0c1c6028801072501e4004c05000d00c0d0907a01c04103480f1030b42ca0440342d40007400749070107609a00c3c0c04011240981d0701703001d0302da54503241d04590b013154446502070f801840c800c03c2c4040c280c9041c400d40300c2c0400c15011080c0915003043d0000c40c0540c40c045100000e50f500f40c0f0300740900e55600001a07181910760780c85040d03000c10041000070b460341d02241c0c2a01030a011100a11030f0b869554015050340141e03408590300c004900e0704155503180c8081482c0002e03540b00300c0164888200144d26055401035030090305c030002d1110070402088800e1090a04403101180c0c24004080e180e20001d00300303107016007102e05110810010030705012054a01000840e8481d04444140c03500100804442002001009030b4401e0070004840c5903000c1d0140a60140d9010021814050500c40b400c81c0040203200012084c0700b08011030425140340d0b801030140084818001d44d80340d01e4100f0007031510400a00701040f0455400a000c0160b880500a40011200746860070301008041d140a0401c601814031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 869203498 1250 869202248 869202277
    0x10060915181d0601050301061e1e0c051501030b0a020706021603020c03011b120504080c06070c1104090305070206181009050114070b04080c07090c03020315041b050702010203 77
    0x2604510041965608150006600d0340c90340f034400065903e400203000b14004100340d04074400344003400321000d0001074842e00d024560000b000300800b005008003071170000041c03c4131155109001082002d030039281e04c002c4c0c040e8460740c91500c481c0c44143c0043d025050580d00068040d05101da00e0f0152600140c1d040030880d114503803071402a5407103500d03110326406542040c0701d00341c820700d1408400740c0d910559182c0c0a401400c0d22080001044010005c0710b254105000d411b00b140800c014142c480c4e40c0340d880303a05030030085045c0380404241603601c1c14070a50409040c0f000003a0700c60244c841166040c1e45003510381400081003414403d40803103290704004100c80e409865980010800c00f207031400c0e240c0400c011489111038145200e1058064030080d9040e0200e07001600c2c40000309026a20032041e1035941d62500303403c40507105a0303100040000e8000c400e01801140c80d580c82e024070007044408205405a450480b01902c0802820405209011601505590081c011920074041d481032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 869204748 1250 869203498 869203547
    0x507030606090b041b020613030201270b0907050d1e060f0209120c03030702010f111c11010b0d03180b070b09070602031206041d01090b01090510060915 67
    0x2d40c8401001c01040030361081d8104105010f2040002e403980c01030050b9540500965500c1d45c1e1403850840c101c8100320115903030360070850340d2580c140c04074130088044444500381c0b2030510305000340314000151107040c00b904503039810045c070794461160b13000c029444408144c41da08060b243d4090761000caa800b422240c1400c0364144441d550f54028072580c40308407080c41c50418580d64040e1fa403520030046981542c000c00200000d5805101440408161407501464504d000e5045a05241f044d2814900e0302c1d503080c0908113881d400c0303681e00031914020070007001041d010b20001508412180409001d0148a032021007480020849020142c55503500351951000c1928106008200840c0d508030a801b4603080813034843d10100446d6181d10030090f07180c1d095110501044010300c125903141803180c010031343c8114201028001c440003240641c1701c00340b1540c5804844c4090700d000505200c81c80744144024801ca5400400c0381c030542d202190003004071405108252840300090300500d80850300b142 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 869205998 1250 869204748 869204759
    0xa090501050a0510081f1104180b030607030902032d0703140105071715030a06091401110f0d05100812130906030206090103050702011b02280515040507030606 70
    0x801050044802d2103004c001190f50741002034940d18a0341007005150b0541c40105012030090b0070a0100c4501038014a10f000e40d54450051610070700c3c80c10070b000b59151458030085240a2200540c044140d0030203000b909003a60000351207500d1011003002000c2c0455080446e21080d600400c014825613048903403090312030a0080c01c107031210261021b65802e190000361030300d1107010b0b000d8956540d240c1400c41c1c1c1d103e1040d010b504c130400340e22050301482040e02010106006000d44000316003e104038100002c860030116080d51089540c900d050700c82040150b410a0a500443e5043c9151110026442d169040701c8050100598000960780c803400010700b90000c4002c004090040e880b880c058940345d41d42c009002a40d9035480065400141400203d080d5400307070b0800e070303031020720b502c00040d50210b1603440074200c00341c058005e0016484111080c2000f01003e4451400f50840d034004401d86502ea6200c0e0b030b4900c0040b1403210441d513807102003020420308011280207144c3c400c10500c040c1780c640d07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 869207248 1250 869205998 869206001
    0x21309020a0609030b18030405061b01020d060302040b090601120c0c140d08090106050a090c1b0606060f0302030c070615080f030333041503080f0702040b01020f0c090a090501050a 79
    0x50105503030003504c42010900000380c1840340e40200701b024020350b00f060b28050400c0899000402c01c218404404402c1081c61002880140b101121070440020010b0442c0140700071030751102c90329400b0701c0890090000581e0080c00c400d421a0780c011021400d5002c0000442c0c2d8580b100311b00030000c0400300b060b810242004246071094009641c3d602c45281e4902000034240e4840303109040d080b0380604018400c1821640018184e0340c683c2c10b0031103480100032400500030821500c19241c1d59a948000c2c403d859109074420030340c03005032900794254101402d441189215400c0c000b0106c80e41d0303c134030f0341c104a11904031100401c001401e84040000300741c01d0b151203502c1201e0385020f511101294a0b0b620400080044900010700c000f403840340040c00c140801007072069100d09140c51141e40020000d0340355401024959042d940076a02c1311498410305c0190750701401c2490554200d0407101c007001000003101981e0040455070b0303900a8481d000d10100600704114060f10b0780d4280f200304240709055 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 869208498 1250 869207248 869207267
    0x70803010e060f100c2306130c08030406080a0b01030b190e070c0f262107080103020d0605130f060c020c06041a280c0c0b0a050304021309020a06 64
    0xf6180c4408907903070b850800100d0040d41941c0000300d14401088404200355441d400054108203c2d0400c2265440e42180d242040c2160441d00264002406104019141c04171500a00d80040114202401d1440192290364018921480d40796a0307100001d03540e00c20741140030f21305400303001c412040070400c198814402c0c55002d0401082001004541014800c00e01e9004190b0440390944c82c07011590342d88982140d8000e081902c07205c0030351205003800c0c25003000700491403240300407600c0da0b1240380103019140f400500d2103061205140040000da00c1e0840d480004590101e80098540c0c0c4002d18440a000420400b0309280451102d0008100f00c9900c03007964250203400729a040301c5045c0c1040b40b5840345001c1c074bc98a451883c0b19100b03000c11240606500c0044502c1901010201c2e07522211000d001d03204c03076000030080c801075000c0c02041012407011303241e80c8902c43e1130003000b560080e280d444060030082c000e42e00c00114401c14002e991161032480d074005c1a14a4541c0c0d1000700800b200721 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 869209748 1250 869208498 869208511
    0xb0d0c030506072f1e01020c25120501060f0902032e0501111504080406080109020f04060f170c031f0503060c031b1914030603070b0f070803010e 64
    0x2100c0100301224040d440980c84c1c1c0c462110407000e001281c0742060410041401504098032400803500c4900c07050802c900038021240000585500d50b644060303140c00141c0840a55003040390004001509070003008100351000c0f1564003288a6075458041e0041a45a01c8602130030000040480d50250a40045000b2402d08408102c03005078948400702e0f48a00d00e00a450401c45d240e41000194098403084000085023015900103100701d05c107804804000702c03802c031904100042c080c482c00d034011111901501d50050308609100811b02c0d103019a00c203500401082c0104aa62003448a1280322806c21140c00c03c0769400e1942815400d20031950003c0c1c48611a100d00303a6a040641200780b100706040303034001002062143c480a4a54160f5400500140c03920245401321420042c6075100400311190386078041205040c400000a00741400b0504107281c2c00e00030014030286680001c0d510f016a113010000030f5980d40100c940c802c05200b905401400c0d50400f1000203402e05c0301c1a6003500c1500f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 869210998 1250 869209748 869209753
    0x81f06170603011418030c03070b180a24020423101d0d030e060309070303080f0c0307080a0f0f09060b0303033d0b0702240d0b03010b0d0c0305 63
    0x441d0403080500381d6008504203d10061080001070300b01c11611031007246001c088090302d280c04001010a8190b600030542600c0c0a2902c0062116034014138603109030141e00300c0b0103050400915a05c020710b81e40080448010445d89680c000d104e0702c201d80c126402450040a162240035a5065840d50002441281c40c40780c3c0510b40480a900d000f21400d80041d00c58400041000040030204880340da07103040240c04002426102c0141a07c8900013940149004030050030240c0ca1451300410300d2000408240001c08e04a06021104402006484c1c105400d820081c44654490180000428844400320342c03150505415442c2070355240c1c09003100c14080c0c0e00c20712181a000d02415500c0c40255a003621003100350001d100000001221160700a220210811040402070036072440300c0150381100082d02e1000404100710301d0b000b444443c00d400c220b081154500c0a0007001059401402c0100070f826850b01001e04090341c087d44500a480b034000c0000405858500f003d40304120349000440307251 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 869212248 1250 869210998 869211001
    0x901060825020d1103040e09070305010c0e0f1e0619110f1911150c0d021506010c0302030c010e031309050105060901200706031a01090510081f0617 65
    0x40e07541010918614800d50000c1c00c001e0a4000c0444d5260044005908140014400490010116252140500b500c0070007405a40c3c11400c10342e003114841da000b40c0a00c003004180c0200c5860720807010003500d030104c0d62407260706083c0c400c1d1326045010f042c41300d601000005190404600c1c100300355255501d682e503040d200e8a2000700607603680b0b0410f0406202a0f108902400f500d502c0410500b00c1184603800032054905281e02040034034004944103501c15001040c03e2000304c8042040c4004103a2600c0105501820311032100380c0e010018022904025132850742c1401e0600810444d010340d64100c008001d8880503601e081e4076500b2100800f01c643c04551000113900c890703400780380d040c0c80000f05003524001c0540e0044d90340e42d00c00966001c2000c41300c03c488480080502000e002000c0c1610040b07490700c01280400c1d8404042c19159042c42700c04d100c18800c07910f076108440006603850512060720b85074020340c2d00542615400040c0707002c01c80c602c0815115032110440c900421450000c1c50030303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 869213498 1250 869212248 869212291
    0xf01090b090f0a020a0b0309070f03111e10110a050307060506030c010f05030f041401090c0306060f061e0c0f110415060c020d0c150c0203060a060b07060b0f09010608 73
    0x44401e50f05011703504c112816001d102c1a44404011504520070030300f02c803407282d55403000e03284d40342942c0c5c0191401d00340ca403181d0501c0c2c04c101c00000f000040742d140c114a00320040700000d0341c040d062441d810400c40082401c4140c0c00b004c000024403550407804407910303000185042c40c0501400c0300d130f2034040d0142e41d0301d03443c881d4098943c0042a150684850b03086554078604840115030040040e40c8543e00c00c030000745680d0007031141300012070207245002c0c111415820300d0320586d0840e41c030282c220700042104002081e4000b20300c00804c039510f0656000146003035011a0104400b00005e400704010b40003180c10880c1041e0508615582a50700740300180c004a1514254101c0d841001d02180801d00307024018035105a5076010325200d800c1017549240c841e0006030345c140f22a02e40f0b401142c40c6204410551030f01b049480d80c0b007030045400f44122400c06032000d41c18024510b0044c9144d4551005111503a00c103684005030200c083c0c1101e0700c2d90fa4034a80200943e00030340b04c0403103841d03207a2840d140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 869214748 1250 869213498 869213503
    0xc130b040f170a03181508270a020108181f141b030a0f023103050c0105160803070e09101a0a0306050a1415070c03020907020f01090b090f 61
    0x8100410b000d0f140e840a0ba4806440360f1038101d41054801395108004606240c0c010244c400c14007880d034500700b081c40c24146400301100da9480a0301000e444200401500b00700264982e006582840c262805444585a071010104180c1c80b0311030700d00030000168607100800040510b145103c62080c0704079400000d00c012242e80940c0c0c110024884600c001c1c4510341d118004580054200100007071044002c00c507442242c0143d102d4900c2003d039800380314564600130702d40c03010116140404540d820716540c0c03131513900e40e15114054103109022802c004c0c08c03645407000c500c0003608107004640d20701d48008000e04108464020503c41c00c40800417490150f0b1161003442900c008040c584202c0310021140b180d590080b804100415485107808140b6449010100000f0300c509442034242244e405c080100c2d042c012210050b40ea20140b24030004922001c0440085130b03015541d02c00c1544440703108038102001048241c2141d820016180200a0700702d052621401e458002d5850300309411100f641c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 869215998 1250 869214748 869214779
    0x150907120f1b08072a02120a05060108070b0c032a010203040f150c0212090a091119050a0905040b060712110c030f03120a1e021206010c020d0b0c130b040f 68
    0x407240002c0004d01c1d003200079205c00c0784055000400703e49803100a281103170301e0411011000c07181a0084001004490001c116900241c60121040c0d400c05005070000c95481c001d000c0d00d00b4900607403110a40c0c101c2a65003c0343c4aa0780ca180095540e480c10b800c058440d00c541200480c0c142c10615004003030700d507251080420105160b0f02a00c0407401c040ca445259070803007401194402858200006d42d00114400d00c0c00c04d031920b0310815141c181c3e28148098119009400005100007004040c503046d500002003030a89108580000b000900c1101140d01c1c0c1c000c1c0e80c0300400040628100303800250300804215600a4410101c60f90040310b07c0a05803140c454100800141e03109009103c0741c03145034140c4a912a441d1080042c8024411041c00c055400c808025900c2070b030b00080006060349a01000d55111900f800c010b10001c106a0220b102d0511f214000f91941c240040464501c0450383c048800d2000c9600b412a840d0340c1b16044a0300c0b550241c40b808040781102240010301c088940d213442d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 869217248 1250 869215998 869216027
    0x1107050406060f1d10021c050a080712020f0315030f030f0403151503080c070504050601080708040507091a09010e06061209070803030c030609150907120f1b0807 71
    0x10500c00f1a0101500c0200403940b05242c00f4103a907942036003981300d0800180954115900420007900c8024142c120070b100d0442100400800300030401810b43c0000c1080c1d000000340c5446040742c00c114552100a01071608405880c2100000344002302e2003140103064201c000300c00343e6801b40f19080c034060340d03441003404601c4081018001080230401c88080c01c81d0710340c002c1d030010602d100309222913141c06109820884e109140450403076243c240c10000480504010741c0c04001d5800c000e4000303000c0d40c2006100c0745c00c01094400160400005009900007014051001c0c001581c1c000c0c62895a25901200305020f06004000011034414520005000341000b4010318505036402c244c040c01280c0081071594584035026000440c04010030082d0b210b8041d00c000c480d00d0303041800401921800203413030b48101440e01010090b071070342c50444041e001402400c0040c0711004402111020b4a0b6041041c00b4440c035040d40000900c0322a442000c80060550f02c400c90342d138551405549540f2038016a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 869218498 1250 869217248 869217257
    0x4030f090e0109020a142101080606031e0102130303020c010f02160b070317040303140a0c1e031d0109030f020610060302030c160c0609051e0f01050702030706110705040606 76
    0x108034210f044e90003407005408900d40543e500c1d81001c12402c46500c890301c002c0e1980c00104501540f030000c01c01141c0982500400f81c182404c0490010f945c82d5042d1525a05440f100c0000f8110403000354111000c84001301100d01113584e4a05002c0d4a488400d00c4880c081030b00015500045440401e44598200000e840042c200c0c2c123298900b074250f00032020450a0104c002002004000c00900007446284a6600810102d03807004d000c1c5c0300342201030515001c80b410264445403660704040146c144a0b200c15404464884110088010345030b0b0300000d02c44000b10b0b48a170760320408107410050049006e5201d0485410310389404036034408080707460003083d000d50702061103030501c242c00868100d028144c0c1c840c20051102c3c2c0703400000e00d00c80303c126203005440307008000c0c060b080281d000003030604070ba0025905c00da040400c02d081d011400081c1c03003001021070814641c0e0140060303440803034000c0d003200c0600e6251140078145d4030311303603005807842c0c031641034001010300e4a0f000e4a0280c4009544 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 869219748 1250 869218498 869218501
    0x60910080a0b13080424030c1209081b01020702030106060e100c0503120705090307140f0f0d05030310060801050a0609141f0c0b0f1501110f0a060504030f090e 70
    0x441c5840341c08090010501c981e400021100410006805800507204100340e1088401440c0c0070a902e0781b110740a0002894188411f19401c26000812001070381c81e8402c012a00841624008209100c0d561202120062292141e81584015070141c485144260000c01c0055105c000c1980d054078550003003540310550584129a551082c03181050940c816802c0f00d00f06000e500c2c0040007003504a8211000500108503500d203484e003001100020b05114801a2204501700003081c42842d0604407103001e08911a508501ca40f540300f0701e0a20150041c00352912410045082000f80c0080e116040000715558000710f0149001000c3c4801c84485481d200c46441c078003501a841980003140c8660701103180d58035800e0110180c41c4249180c0855503401001081d03a00d05191004006402103c00c84020010000c003001c002107400b165050900b8980c41c0c4503213507040f003881d2203961405c0141d5030084411750b1080286c190002c81c0260b1207621422640c0b511060700b12412a40d40c480c100c00090000e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 869220998 1250 869219748 869219753
    0x902090103020112020408010c11010f0501081b060c01150e0901140a0b1f09090608030c070b09130e1b2d0a0f0e0108010605181f090e06060910080a 65
    0x2108112400840050300b015031f00d0107250f003102c0810754210302140710484c025030f01580c00e1240c0c14641c0c0006208000b10350404040e02d50b15803012020018194078007414281554031841920b00c2c0007580340007404030380320035491800401a0780c4103100130740410b180400c00b00340301801400002c031040c180e0407440707903610010000a84004100c00b50030007881c01c40014100143e08034004214039640720005414944506c00007101c1e166403090001d0b40050104000482d0046000d408450b50a40c0803034691011400007811200c0111111880c5840c00440880c01c00001c905400c001e2001119014030714003400600580300140940030700c1c48140e401c211107100010361865011300c4405490f140c00782da200c00c0d00101900540d0008050314004200400601c01709001d04c0d00607040603900441000d81c0d107040c170360381c42c070028003410400801c1c22110000220170801e94001080d80356030610a40e000c0840300c64540c075090f644503019030b413030b2000181c111803440c0d0b09004860102004210510954 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 869222248 1250 869220998 869221007
    0x3060b030955080a020d091706040b0711060a060e07050f1b071806171f0506031f0906060b03010b0d020304080f07051606020d080f060f03060c0406090909020901030201 74
    0x48800710202c101140441c0041503182015006120041d0020080c0003280070000c1d100da803060784902003480d0070040c6601085404102590469030060a50340305d915032000907141510906100780d0103104842c01c2000380304468001c40c040740c003100c41d000159201c0d408115120300c43c010740755103a20401c000454a100c00a07a00081d10522403065422031502e98400401c07011403c0d80324210b40303449a10030300155880c0c00c0b00d6110356114800510b18900e80303001ea42c0b15058003e000080c0703696164006132032503c0510802d5582140c0002c103800038241c4001240040156a1083c0c070004d00e0014085003c010040447e03040ea100c03100b01a091071b41d09005080a90700044c42151010381c00e00144c49209451300c0075000e100d00c51000b608402d80f83c02048020940e440d40202e0840d0b1210318116030b11074100c42c040d90041b43d01c1c9241c034055030703408020030240030321550003540521440080201844060000d00309881c465601c07403044a555800c008180e40320040069881000d00c0c00410056008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 869223498 1250 869222248 869222383
    0x50307060629071a1801110915030703060302090f0f150102030d020d020403060207060603050d0c020108011211090c090f03010b060904200705030301090e010207050c060a03060b0309 80
    0x182c0c50f004010081300c039481e1034a1006880c96202d2503840541008103180a0080b40903404c0000744960030300408100191012840c0c01d40b400780c5850010105200f140300350801c0004d142c02802d504464100a22001c1c000c000844500100c44141400b16001c0c0c070300c01d01e0b42002c4d400164015810320b0a40c413031740c40080d4000c000381c1006907400c2000000003600f5002804403e80500800a5420b26508003923042c401051410010003024446110042c1c1c0c11110607415280d0080403258520a0342c60300c41041d0040507112580110307400100001406648000d007404c020954040007041040c0c000d0500b65034003103c0d0b07158484414040d5070514140f607403040c27403e841d6074180c034071814080d000d070387d01c00e076102c2182074890303403c000018809280d2901400c00c00301d030743e44021031810707055407240340d210010031321018464400001c081c4035480c4aa0400000b0784007107000745989090071418682d071100c02c6900451460040c0c0c41c0c407030f142c0b01040704104401003000101c400c2c0c220310020f030a208110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 869224748 1250 869223498 869223503
    0xc030f060d03140345190b0402010c1505160f08150f1008040303140603060a0f02211803070309141804050c130618020d1805030706062907 61
    0x200010044085d6000841e800029148081034105800714075074551100318a441c00255120a114034150700300324000000c00c03500070403e041e50f6141c2e440100c804050079070f4042c10002082c1c122003032070101d40d4410b034000c0c1c1c02941100401c590004055920500f00305c80030011403000c03000a03950030702c1050149601400205806041c0c0309800000748a081c4115418000440000c00c000425806105905451517142c884581501e08500060307950940100f41c02c03511034443e814409020b1050b016510f60044101c0100303400d00c1403140b80020790508540550075000320702403540c0740c4000841118100c0da05503640c09515410044907959000740c00d00c003507070003412642d4031405100d0300c0152180128172032006842140301d00002c10105400c8500010700c0d076441c210717081041911518981d000e44c15002030250300d504800e21540000d05400401100d50301c41001e1007410084c0100040480c9842040d00700245a141e42c44003018222410000e6101003011211111145046001e451001c1c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 869225998 1250 869224748 869224771
    0x3060906150714070503030310030c090615230309101109030d0c0305040302100f031d030412020a030b07030905150f1909060c0504060e0f0303090402130b030c030f060d031403 77
    0x9517110701003465503000304c0d199401000e8005041c0208585005180001d0800100c00e00c02d29040c11300c51b184180462415000380710020b144d12641c10303104e808c11001003c24242a1b0345a21384000030585816485810940441c0340009500e40040c49000369622280e001d002800c8009031200266036810340c020041d0140001808008010303503988010004999269079000324044111001030240e8080d418041310302096005a0021030170000252011205c00150302c858031200f60000c030b0220310481d00091320640c60300c420005130a400d80c01595243e072044080306c840c410954a26030803043c055616990660400010500007400c941465164002089000449031520780e1044111442c44409030040740c00410100325441c0c00c10394450061800341c46001380c4429490000c0e0b1680700e4980068070403036011030360380035900391650070002800da0404020b88d83d040542c0e900210f50403c81c1e5049280020a0001d03480c1d0800142c060b1526616868440da0b0704086207080d80d940d00010581071059 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 869227248 1250 869225998 869226013
    0x17030c1204030512070e010210050a06080a060e06100f030f03030e100b090105060406050904020307030e0a03020106050a270e010f061706090705012109080301090203060906150714 79
    0xc003140c04014001d51083d103455540b0951001100c02c5050010a20f03400d0090000070031145903008148402101c0c1c550b0b5002403242c2e11625146c000f00b01541015151b4441e45800a0070402103031702402c0c0c402c000c84110356a9a41320b8500342c024200c14060120180b0301c5610800c00521402c0c45030200d02d1103410007260280e000000c191501300c500008085a54641024501074108002c16a024180584074645407a0900b10050128403940e9200c0780119800800106118482d40c00380340d0740040e050a44569091509009018054038051a403003201075000004000412180390000485d900aa50404d2500d0985400040c0281202103500b9501c917803c000d0a0240351041d08058007442215015414200b4500c030b00d4072400500c1081c160340a0801408540e8009180041c0b00034920b051104070900c1d00d660202500800d8801440c14001100101e203249a50300614030518003583c10384480d958041c20401d070b424403c103042c52114410842003010600c0c0b041038003244040d00e0100c4a04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 869228498 1250 869227248 869227267
    0x6020c10050105010c0b0c1c0b102a05031306050a020c06070c0504020d150b0717070323070b01060323010e0a0f02040b0c0607081b0415111b01021917030c 68
    0x2240507240300f01c80c4a954012441c1c00c1d00d00084109458029403600300405100b0303c5280c0c54060344102c41cbd186a41c2400c0c0503000b0080c0c200101c441041d005402403c6850740d40c0c2c0040c096402400c0c450015004040d45180503040040a0b0f62859400c44261640d15151205210003903000d640b40c2301c68291520203120003000111508001400c2c540441c1e640c2c2d4166013480802c5001d42c810a030f0611804010441c00300344d2160260072501a0074840d5640d402c1c03141c06009140c81102001000301880e08000900d0320307010744c032038003540c0e0389100052450180c0b01c60a1b903c00209000f44801844035034003107410b1816981c4840140d00003610010300d420f0f261278142d0400e810425110b140b40e44994104282c4d60303070101c01d0503000f03811901060307031040c0c41700031458450141e801421802000c1003601e034172046c402d075854002140c40d1403c0c1c030886c800406240711894940001113001d442030301c0d0b880c1705500d01e0b40c40030080180c001403010030503035035040080556400506000c40d0380b00d06200d00c13043d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 869229748 1250 869228498 869228527
    0xc06050c0a23151b1911030d05010e0103170c0d1b05010e010504032303150103091407030605100506030a110f030709030b01060f1205060a080a06020c10050105010c0b0c 74
    0x404030300e0704070340050901c1c010b4000c1e60844890720244a18040601110310039095442041341d03041181e0505206c0710014200e071a1860081503000220181010000201044031304074480c1a6401141e0303501880c3c1035455003561034440c3c200c504032654003c2c804441740c00e00c14501850242604845000240c0c0291582d81c203403044001c422002da55240140301c100341d00302128907100f403400101d071012007801d40c0313940c00280402404041c281e20044580b9203583c2c03190340043c400e01e60000e034403d202e05514440d141e032900180000c5501e140b41c030340460040c40e10404030404586005080e01c0c550f540e0300500402400c0c59060000c1060402d004036018811618040c5109081d103070f6503255854078508004007200c0c07041e0b2001c02440000000070310001e03800748078404280a0208041170390785603074000c00d00031103080c0d1240c440c0d40030b6640e1850401c155a0001c04c44c1400480440790b0714180e5004282c1107503020712800d40400c00c099190300015803101480c561040d000300c440c1d4100204c00d5021035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 869230998 1250 869229748 869229763
    0x3020a122004060e030d020f0a0b0a0207080d090b070810031b0e07080723040b0304020f040c02030d1a01080f0406021c02070203010e0a231903020a0c06050c0a23 71
    0x1004c16480d01c910511400c08200340074204169100a001c0d0b042103c14060b1a640107041c040c0c440c03100000043e030042002d40450300210b038400d0201e5038444030240018020300d00201e0807682d88510001150203075100742a405e01464900c4050040680b4590b0782400c00c400c2182c030048501c003e60303000600c0c40c4144480030311450540d03c4442c1249003020008012846092004042a00f045840380c11090b40300d040e601950f42002131140e40780c0300c5000183d0220002c0c4030a41d4010300b00308500c560381d0f50100281c0202a4035802c04d1000101c0c203040e411441c420010702900054544001804840c54607400076000f80c05414010b1410740c50000d000c040761b0100c001c40031034640002c0d500085042c244a09481c14a80f100a0b080d403000564036403401001020200000c14a060858108200240a0051080850402800968083d01d4042d449525542c0e00740c1d6400c590f601c0c0080c0c11402003046442403403520300500684c000541d207928074165210180565001400c01c415a689020810507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 869232248 1250 869230998 869231009
    0x1b0606080613150c0315080c04180f0204021b07080a02121515041e090c080f06240d060e0606060a0918021611030d03020a122004 57
    0x450100d0800202a00e45103000c0c101c081e8050200800c48086881c890601c00b4a5981e45404110240c1e03d080441c007500108032401000341d00140001005800041e2070f05034400b0555041c8000349194076913144c500031015000d000c115140700c9100061400c1d6000f40640800d508000c603030800304104140c904000ca40000b9081e902240f0703504250300d4440711707218085041c80002e01d803022504902c540ca14030f0190540d00e141c96421a050503c0c1c0e03a5170071000c5601c01280311003a4018507505194080c0c030002d074040d550001007070008280e0200101e015048680100010079850321003021403600501441d1039500502d205945076a569a101d400ba02861070046074042802c85034001141e04009000e0300003803140c1402c00540d180a40c001082408940544069042219100030f82c10068401c4442481c88064403141000400c0303440c10b200b440190080e0200c072010000b031b80f003e0b4220710400d2580c10118061804403450702000342c00841d0b1700c0080381c03002408200380310703031000c540c0d0003d8111 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 869233498 1250 869232248 869232251
    0x708040b0d110306031f021c020d060501020106050127090c02060405101503031103190203040915030c0b03040c05120d02010b191e0f0f0501020d0809030f09011b06 72
    0x5000501c01501403480ea1011041105155051072000240c0d105084256800c110b01c10078100400d03c40c144c3e05072002280c90341d2444d4484420b041c8510002d5100a44e1100d0040c03809002081035441403182c1c41c150790040e11501e404100e5400503403080003058a86501009010302d001c0b628034800d0048900080c0b403a002041d2038201441c0040c00c003601d051080d01001e01d418401c0785030008403807800c4101c0e0303003508103010b20003210442c0b9400d5200e40440c0c001c4400321200816810b0f50700000a1048800050003040018003100c201c1d00c10022510000c0c03c3e5000c0c0c104c0900004600707900840e0090301c20074a0000f8507584d070000c0750700701c1c0480590f81c0302d503000100b54140701d54082c0182604008120703440c01d48140012150302c1c03400715500500c0b0145101590318070030400341c0e85550b4050690344220030050703651003134041d40301250390046900500504a10100c882c0c020600c06000f2488500598104020026280703180d030003030401d09042200e040c031486031081c564a031122302d20f401401b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 869234748 1250 869233498 869233507
    0x90c090209040509010e030910020f0a0c030201090f05030a03050d1b0504090b010c1203090215030f0115020f070e060102011e02030603060106080c0d0507110102030702011a0604030203070b0f0708040b 88
    0x1044101c0358010072803046179050100c80201240c010040360440c1100b02d600d500400442c8104a02c2c00c10b07080041041449028081014000002c0009040b24404d9880408968030745105941c03400062050035016848440c0a9000a000c0d402502c104003810600040981244120035002c1e41c04400c003502056001809002e043c0450007051001c0070282003624901c0e11940d0750040d08092606180e0805540e00440c00865803002c00d03000d48107c20344170035910f0381451800c4158111302032203421a4181d50b030012540b9140041070030800b0f8480d54002e04402460a00b00e1912200c2c018041d074119581c03400c4600071038000618000252429000040e02d034a8108181450914103800c8882031040e6501003006048001c001c4031030080307a030503021a4a40b5480020f5421310f21450030701e41694000b204001a955056000c8001050030458800c0c81940303000500a0f030744114080030390140c012020074004654698001c1c800311840c1001d09180181ca0745441846820580201c4200700f00005c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 869235998 1250 869234748 869234767
    0x2808010f120213180203030a0509010f030605101d04020d0204090c3f0c02030c060c0f071403070206070b190501360501120203061b0306090406090c0902 67
    0x14a503a028003001d5101160504081c0c002075503070800c1c000112055615942c40c00c09125010104c55242c80c0d01804480d180c940350341c405800d64000c0141c0703034001052680c0304c444c890301c2802803400311080030b40300070780b00307003c40c0001c8608283c0181046041303d030000039544a6106c0384003c003070540340070384016112800c00030710f0425071b03581003840f0040014010899414020030000a002110071400140703810300320b50720b807098400012800c0c4021a03e8020060740c01d1b80c000c002403522414003419141d10341d54840304281c25000c0d00c90000300d076130014844000020798030b181c510f0482e00d100003202d0030011140d00045c651b6000c40d80485040c0d0380c0f50b041c0502c44141c100da42c445011101003e002c1581400c0106441641400c4082c070080c000b80c000c03480d10300701c160380100030009241c410710903036846004500300c270f9081c8070f4124041d108680000d0000c505400300cad02d002c0c5801403a900c1c43c54490342d00700000c61038042c105603413080d51240d0714000280d41004060080140c0d5070b0240e03c845007070f07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 869237248 1250 869235998 869236019
    0x903130807080303220f150f06060e06090a030533060f0d0809280504050609041b121b24050a0e030a08120c120c280801 53
    0x40d03216100a600000050028040c0402030380d500c4490075802c000c0b1341200300c0001442d0f0002031000707000c01d000c02c640c804c14041c83c1400c503a40040411820302c5011380c5458120103c590b58403078100055805220b4050929080005212103800100010030f030703030780b6a150b182c20b0440c00c4400030500c001c840360303420072a2034482c0b04140282c241140581145000300c0401c41d5017454140d4644070f60200c1401c00200002c0e40281d440c035400c05000032040c0c1c06569140020b40c4080481d02c00d4542041d0800503003441d142c041c0398418400500203815a071159500c2079000101c01c40c104080020108021900e0815031000d5011680160980141170011090003280c49403d5042000d820004510150118810717109542e055040c070b02c1d16555540c8401c000302c415008402c0800c0d8540180100b107814012014040c1a055112081d01025601d88104d900458072404000d03c0d002d0380b0180024054061180c050003002c0804101d4404c022000f000740d4a080750b00200c50000700d0203000040c0000b4020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 869238498 1250 869237248 869237287
    0x70e0609070c0503040b0d0f0213080606030123071412041a01030b1506090a060e030d1e050903030909010602150906010602190f1a040b060f010503010308090a0e0903 73
    0x2030741404003400c90301c0c0d101d0907124170a034019403518480019585040305a664000342128409400840d107450f04450450030ba0422485032508134440c45000c5021494184158141101e2014141c0c00c115100d9420b990f209800030305020522100101400040402000500c15000300c0c0040869625007031030568080c070000c0c801c030f84130001c80c00c0040c8005541449502d030091710148118840c11140000980648680020280c10000310500012082e1300f02c2113014041601714181c40300c00050010480b04210818107a050b040841d440c05039419000d18000c0005400103401c0c0c900d801c0c0c00801042c0020800e84c071010041c0c1c018440614103442d000380032600880314802500055240090081d039580200c411449a4054054a6420052003a444881c40d5511540004095001214550118804603002c1d1580b8078010001200c034540940461a0218141c40780360541e4216103d1000d1a041450007581000440c000441d4514031100d804d441400c000c0007c1d40c1d50080a00700b804030020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 869239748 1250 869238498 869238511
    0xc02133c110d14130b060d020a08070906090b030c0105180409080702040b040510060e01120608071a0c073005030c010b0405041124120a0605011e031d070e0609 70
    0xa00344107201c0306131001c04120034075513041130700c480c00c80c2c03038000010b00384078a1814004c0d40310820420010742c3c002701040300380458131401006c00c081075858076040265049076640b02d9040d0040191183e6035802003014040c240c64403410007540c0d100703030380103e021110201ca0940c0c680d403010070302c1011450700b4011001014000e5130b050006040c1546d90507240d6409000391310510148046032907007a40b0540d080c41080e805c1c42000d008a0750384070040ca446407003900070182d03240d946084084094080500321503032501c1000041000c245040d403084121150840201e85c03140060742c13058841c048800110000c0e50213000595601c140d400461421500204122030080d41420304200c00f0650318034003508080801c0c0c1f1000222504913038a40c84034044811300300a0048041609a0f000340da2042462240801c02c02c1040020317201c3c1b0040d52102455491180d0010b81c99100e442c04502c030740c002c0f42990b41408281c041c03004520480e02e080168a822040c0480c82c84010001c46241541c04580c0001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 869240998 1250 869239748 869239781
    0x6040501090b0c0a14030a09080304140d02060405060c03100b12060901050a12020f0102030c070f06081312110f030a12050c070308011509050904030c02133c110d 71
    0x40e001e900c0517100d5000220f2520702c844011000030401c09894002150132540064441e03034a01c4c00b4036011070000060458010988140b103815003495000140c0d55009541100042c038441d603541c0326034107051303100805590510f002c0c54400908804540301a003e0014100404091454400c0501c0407a00d41684842d200c0c1400c030744100010300303000292402141e01076841c0c0030340e8000c0d000140d10750b02c610002130200341308000002524000b1f4203088402e07100d20307503160f401584801d0702603020118240e0001d42809000c11140000c1d070301602c4d05549007140c1d00706440b03040b100c000e0b0090a580041060300c003c030300701c1c40001741a42110302c581a40492500446070a200590710028002d90301401240c900461450f008440070f4007807130141c801068000c2c0003140364a082d1500400c20310440000b00d000c3c1144030080403003c03803280120340b100301b07041c51283d0507650300a4980c00f130900d001c0e03078030806003d61192446a411035270092000c241801ca140c1c0d82d942c82403125850441306580440e07540c0c3c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 869242248 1250 869240998 869241007
    0xe07030e0613060908040515040e0708040b01060c020a0b030907050307050d0c030b0c1c1a1206151207080a1b0b0304080306060d0509010f0606020f0c09100806040501090b0c 76
    0xb8100b500c01d0b81c9900d410420000e21000300345000903061199420080d440581c0319000c0b42c3c603520325001041030ba07015010142003502e8806c0240d59200082d9001844c44e00b84200600445120340c041045880c00103081c60742103580e82000300480d40c02990b403400507400591082c041030408100800042c4402e460946a4000307039114150b443d070361170100402c54a0b14802140c003143c142400d451402c3d0300700035525000811004150300070b20200ba02e6402415086800040e03a03c1d0550310784011200f60303805440c8a036911460782494a6040000d1580b112018016640540c010070400028040b003c00034000900c0c07030700b821078261540c50003890709000c50170014044212642d00340e98106511030f01a90300c5c5d445150014000e4001d000c035071b403145441e05082020380c90054022603010701492a0421400751100b10490f12440025240107841c1c0c004d0f1030440c1d5909240c0c078015485808820301c0310815848400c0caa0400c0025101a03540f60345404400007840a0200c0042d00300341c83d4207506180 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 869243498 1250 869242248 869242261
    0x605030327061c0b0108150a090e160f1410050a08060d050d0905010305010f050303040e060f100e01081006122f0408070f1a030a150e07030e06 63
    0x41003540000c0305001d448030072040c0d0315103550042c1c0c0c500c20a0984100080725540064400603c0300405007070010b442c0c000441c07081d90303462540c0f04491401600c024100c1d030801080c1c40107414103d000e1001d600c00c0d40c4a5000c206119282d4401404482c03044021403890000141040e06889040388e10404d074030a023070310645801c6407c1300d49160150800680c10fa46540016110b1ba0a40c08050280d01402801a500d07503813106848003900c509032000c02c12a41c80d88054071800305d0314015550035500400c42444280f02400c100c551040005002c0b41c002401600842d5a400c005205080800e410441550381580c000c0031040d441040c0107030a41130301d4a07001c0001d2503413074034040b02411107545440700c140b410020801074600b40300b04040f640942501508a10003580319118004203801500b10105802c00c00c44126004c484099a1401c04262000700c0703000b10760300261003140300b1503131041504028140342c00d480c802084601301c42111454184002340036944140d040026981054003080702 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 869244604 1106 869243498 869243527
    0x402190602160f0807050d080f07031e0e18072a03030b030f030703180906140907030b062a060c040305070b07021305040201021f0606020106050303 65
    0x14860f503a01807001c58030803103004001c0c0d2a000008104541e14000d8004651640161596894006070314200071940c1d01203c412000706448807041c0000c2500000f4403c00303140c46050060302030350090300040b071460758030b004043d51151840100340300d10b104c0c0003040005d2070646900300750003194a200c080c100070315081c100e00280c10710600c09140c1c1404203541c2541145480118100503a90350291084c801141c0c09020bc000c0c0f030540050425000e0140d03400608042e0300c0c41107919000c100380311030094001c141d80c0906081154031051500c0710300407030380c2005003e0004404c9101c0c0a8044100801c42c90040300c840c42000d041c010b90101c448020300807603110f40c0c1240c410558410403164540215080030798402e99a1480e0700300c110007a0861344e4030600c1441a03404501c050501c1080f115108100d41e14072982e0340405001c103613024800c1a0191204030003e40c200543c0da00c100c0c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 869064748 869244604 := by
  have h0 := BRFrame.cov_init 869064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 869064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 869064748 ≤ n) (h2 : n < 869244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
