-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5442
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:53:01.021725+00:00
-- url     : https://prove2.me/submissions/c206b989-2064-4c04-a293-62089f56b1b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 978597122 ≤ n < 978776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 978598372 1250 978597122 978597149
    0x1501120317040c053d05070f05160b070c0510020d1101201218070b0307030f0504050c04050c0901020318060d0608030c16030803011e081c0305060409020a12030306 72
    0xe2030545c2c030908a1100a9103441c8071000d4011480c0c0c00365600300c0c001c4180200f1001d1156a0100300002100e11105102c2e004917562240310041030310407550780340e11001d1000d1001031400204640c005a8400510054138600c0d0300300041103001c0e44402c0700804907070030003a0b494a01e0083c61002d402c003440c051100030503410001804811072031158018407145d001d080c4140c0200e0007007000000459803181c40c18018054050030040c000d206030340b01600501c00c141d2981801488200c851007014041d510a600501c16404182c0600098580007840904807140501c6255501e0740c0200031540d801c5014500f03080c0c582c884e000065183d001d07540e503041d01c040c60220082290180007000b440b80311300900455500d91080e0012020341c6885000051003d40244010010041d02403601c17614045000240704403e0703120004e40d0303e402c0120041c901c0141c981c0c44200c0d06150035124840d00f180056506000c9084e03503401203040003521f4416100d803240320740710300014540b2941c401400342c6207000c603501c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 978599622 1250 978598372 978598399
    0xc220f0f0f0e060c0a08040303020f030709170a020a0911071a060a08120403080c10090503031b030105150a2601060e190b0307031d1501120317040c05 66
    0x100408200d800d8904581c50300c2c0400446240000328075214400b021519458040f078400304070b90303e2002400c02c40625400b84a00c400c01c00c10003001d984201c940e07690740d83d001840c1401009803000d40d082042403d41003d6804070141c0c50b03141554041e914846404119050890f20a50302c40c07251a1001c1c00d140080111185003410441040340100000c0b194105c9503a10b034041240c49040c02203111094140c200b00070000140040054003126035644259036918549a82c0042520f10710102222550000000c0250b9404226446440c0c1000440c0040c2590704044c0031481f04242000440700d424400309489071150301c81c2000e58607000c00e140a209a03d241c40c450f58011110a001e200040390000301d0005141c01c199400c41505140ca2010b40b000c00d162484c007403200d600192600041545507004082c10220b1029102c64003c3c10500401281007100000c80701002c041e0014003100c0501d420301e0012a5001030800440000c0c0e0004032802c4c1c40720b160441c026445d540c03106030001c0003040e410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 978600872 1250 978599622 978599651
    0x70e0307050a1d060306010b09040f0b12010c03061a09060d0b120607020c09061e06090307080c0f0d02031c030603120507060c0912030c0f0501020f04090b030c220f 72
    0x10418030828210a0038203407121800c0645942d03090140903080300f400c0c089d01e0100c4c03400b0f422112080c80700c201c0004698202d000440c1a0401c03441810070a80e468444850319154584140c2d0020f00d0643d4074030340400900080210b90784941e090a0b442808003003014020a04035038000c011914000b801005011040e4107055140e401c2220000054014a52040707000e04103c40414131440740207006503d146028204003070b403031942c00c1100e50080824031103039481c0c0c0c40410503540a01030201c01081d8400c002e0003000410fa0708400814000c0100400910040c1c40c005180c0013000502845490416900b0508500070700059001921380c1c10f0188400140036040340003042c04502800d0103001101c005082990719610b54418550861219088200072a10404902c3c0315641305203014800035a058071860b0036608a00e00036820315000082c10002c00c0028800d040010000b84c010740400c100c1e020004101c0400080706150354900109903209462242c1e02158020308070707540400c038280310103010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 978602122 1250 978600872 978600899
    0x607090620030a1205062b03090e0a1a0d02010203040b160c060306080d0c020609040b0114040906080609150112030c0209011418060d0f050703060c0f12050906070e0307050a 76
    0x1d000290740342c44041901800d049905103014556164400c41800d1224a03500c7c202c101e0020503000c02140f0300d00401c6510060940d6400303502001000700c0d03002b0350700051241d1810501c58091249494403034000c0141d8000c42918204c80b2400c8410352180755401e203080b0704d0120b1400c0100a42881e61000c81c140741c0542c45001669586000c40d031046c424001d0689403004500c001070340c40201071199918914040e04500ba0381c58062415004400050a07a403c8a0700503400c84524503071255028041c600c0300f007000907030111a4100030000041c0c5110000303040d13881801501e402c2ea010103440b401b858014101c0320703085036000d0012a000d40c0d45212a42c1d00681c90a1980e1061200000b00040d424400041c603008410003001484020820fa841100350041d000b01268240120100000071800c144281207082c055034503560090242d01c0d600811400c1c041185106452600d8140610f0340700005542e91300103903d090046481c102080000d29040c40cd61200354001c6025001140c0509480c42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 978603372 1250 978602122 978602147
    0x2030114193e030406090c0b1c02030a200c011112012c0411030d030905070b070f0506011203080a0207051507030615110106060207270207080d0207050f0607090620030a 74
    0x1440d5150588514007102d481c441c003003800703044901c404c256040d007000390b600031500024440310000303040b0007031b903000d1102078603c604408dc801400304106814407803e001c0c3c00f81c0c40d4008140d00e0714107900301740c036880c5600c1c060081c3c1c3d640311041d0b00e0004860f030881101c0544502280003e016034501403078172058004e60740910310300034043d00000081581c004e0161000383c69026011b8a0014104241d00c00140c100440940340d061500081001017502801014040c205040c0384412a10782802c028015071800790074040030600c1040301c8800300e003022420101c4140c0312034110f2500d0b1611041100644555000501c0502c180e060100035140c206e20400d2000305a0b50003030041e107035280c03020303078a130f111a00c1241d91090078411402d0342c0300100031400c8070528003034000604082158840d4819508807804207103900b0307400205503061100401c070034040b45400c0c0009100038a00200000c0076110f1354400c60040c800310000e03102d90401461154200940c0d07000490351178841e020350080c210709485a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 978604622 1250 978603372 978603383
    0x60905030d110313031d10050d050106140d05060d0605010f051206040b1605071a15032803030f09051c050301050f0609030a02030114193e03040609 65
    0x40124500391074002c10380744100d000e0348582e403480c2610384003651482450903c0e40f0800c0100b1134482100ea6803100200b4140ca43c43d512240c45d0315031213280c90304981041e085001405040d2080700c105c40c8950080310460200b1440226440d190000440d0180c0c1188100401880c103020010864070388480d6110101d88082340c80b50000640c00c200070751605800c0d035002e48084060000100191461403d89588490710b1521034904016503e81e101000000e49101c0240c240450602c03107100c880d005072968001048010780204142da04200500c1e409906204100742142c0303001c4d005041c00303a4041c5c2c0059013258002e001044584c603107a501d506002c02c100d004040f00c0c120b010400c41c841e00c250ba060701c8001d42500c4050000b05c040000c0d942101e49502c2c0c0c540f2550f10042c0058800307010b1a400010341c41c40341802402c00d084030781001c5409a0000c0310f1241341c12881c9021040c03001c070a03500009520034207060400088207000f6601660609603a24000c00000d1004000156000021403030081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 978605872 1250 978604622 978604631
    0x810030c0501030b31060506090f090c040909050601050109061d0906060c07030f03020f07080c0118090e060402030d020a020112180b0108160f030b0f10080f010209031507080f0a09060905030d 84
    0x35420081c59009950414ae00140e080a107010346041c020368080d001210200c04506080d5102400026601414012100750300a00b0041101d5600000c08901a241c40e00748405182e217184440b400c0203c4a4100c5031040180c90045003258071403004480080c1040d0307050318041510785c18149408160700b10210014070440d43c2031040d40602190f514141e0301c21501810342c1d0310800b130044802c2c081c50503501005503028400000c84c11020301c611500d203001d00f03004d09103d18150041500b021500840304096400600070700c00180c1e4803584000e4101500e080009110401465480000030b01b035900030b203448100da00104080d08001803840d01c403c020015200016207869060800c103403144001005031080b0700109240c1c0050f4100154405c00800310302d5a040d91b19603490340303041ea00b130300110500d95000464aa46040901c030040701d0308040c0741c4410b1103083c1064010700d20b64005009940c0c100c42030002c40c05000d10f03600000c0c91550030280503c880286828081d459074003451381480800c1c0780 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 978607122 1250 978605872 978605879
    0x2060717220f0e0c19020123041b08070e040f050703030909110a080a05090115060f080c0c07031202070306050c180406080d05090a12030c030810030c0501030b3106 72
    0x30702560901c0384c1405a80e9505040300c4140703422605000c00c040e101955216010700c030640c40c410920700341101450410841d10300342400c010200c001892103042d2515a020001d101d880c40000342e24007142d4a1240c0c0e10101d903140d0030803400410b00060020514000c05000005140d404210305c801c2c0e4250107003c002d1100c0c1e06405001e548150507039a00865117103400195100380c5540700941c00600c45002180b1340400301c1203024040340320780060010405840c20a030360154000441c40d032000c0c030380d825113107000e80180a07207558007002d100052441d460035102e011014030a00c5100011644200148250300700701d40d85018542262806503640700c60700100102c0d600e8507018040445503808040c042c2d1141100048801b076011150b440c1c1c008400b1140020700d100b0408010300300307a009070340c1c2d044114498a001030002c03201034801c0d184450103071018000b01d000c07003071524210350007400e0001d0f801c020100401c1440e1000911040341184101c88140c0d40b401000281141a8910808020039600c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 978608372 1250 978607122 978607139
    0x102120a1a0103021606060e071d0f0603250c02151201050f0f030312150307081225050a1104021608030721020d11040302060717220f 59
    0x20455500e80d2080c00103160507035501a40c02400382500d8840000708420b481e442e002c085c0c030490b60020b48030b9103002c001c00003619441406083c2d42001e0720201030f02a003220002400e40d91205221502c110030000110351407a4024409100e084650b10704c0f151120344e0304c540a400070035915010b078000c14900b002035001064050488040640440d025081a401c140500030b000c200c404206030488a0b081c941c10203a0f60400203009801880c0910200502c1c01c05508204900b45000190081e4007104c030500140c01d0100b01844003020740aa800c3d04d42d80e032001a0054001219104032608140c10403200501c00042140300e249030003501c20032030f400300100c01c0c00704920980240d5002501c15810180004088000540e0040c400b464183c3c2e5440384041480d018209551880000580c00694003603842e10b03600502280c40e90340341c841c0741064696000300781c082c803e24000400d004110000c500404e41c5110545035070305810300c203c085580c000e0001109000b11402211604400b11030002820301 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 978609622 1250 978608372 978608381
    0x14040506060114030f1b1c0f0b0315010915030c150201110f070336230906010804050a08030907031707020307030308070c0602120114030f06060d03051b0102120a 71
    0x30140e19154819078841b1100d005407108080c400001900c00c1015850381c00150100710101c48255200117006203108085500300c40c110308480340031380c0021215100c02c07000c40300d00ca811075101040225400465903203c0c0c0c0f952440e600000c140107100d09011034400305543c04001580415002005049a00400c0d00102d01a043e40b201c055002041650002403060401c0c0799003500d04451403421101281c018a0b0100039800c0095a8441ea6203040100a001264020b0304102907007001d100c40d04000049200d1040c0108194140b100c0c00020404110081081040090300032503441d480742413010203951500b203284029a40f00c0c100310740745d1030610702100884810603030040003042c0203031860f5410340381c10744010954010b212800411002103107080c0014160030300b001c40103490a60401c12510101c14105402c1c0f40650b102c075000038103010000480b150406022510018512181c2c9030849141c0f00f11010303010840c009030184045035005401078803c601140103000b046070717100b819180841d0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 978610872 1250 978609622 978609631
    0x9030e040627060305011d150f0a0504230d09050102061e1009091b0b030f010b090303070203101517030d0b01030e012901050c0709020d1404050606011403 68
    0x1e40b4070294400d09080100c2d0415040c128003401240b078940d00d4481500b19a0909654003624481881c8112601021300401c10b5038090291038480b103040103100c078800c03104018030450620360b942000c01c041c840801203a05003e0455100c0c02040d2081281045e11010300d0b80890740401e00d4084c02050a600200c0d00b02d01c161010390128030070641c4050b00d01e800c400e0103001c8003e0044030240114080d00c01c2c1c007901c80203501a598055600c03610709400140500d03941d108410312101030003401b0307001041891117030441c0c0070300407110303221110342d0006030441c42103038002545803007101062003211019410200c58000018441070303200d542c41c08810500341030f1102e600400c4e08104031100c000d0802e540041138042040c90700103802000382c4405800c40310400003840316040349015280d62030082d54405100c4010030710f41181031108108000d0381d00e003d18010180101d4000c540500c004109038000c40704c0e4040b2121548560605041c244c1c0c603068191000342c0051440d5680c04119440c410480e4042c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 978612122 1250 978610872 978610889
    0x21b1c081815040c172d0d0f03020c100e010c0201020a051b0c10030912020d0e09060d020a0b07030215041122060803131a090d061e09030e0406 63
    0x400c02d00050105603500700030021a81401c0740c050100e0300e9401c03400429002803040303008040c0030603e00500c078480010314000c80c03440e0b009401c010307520f00004100312850510f1824a4540d030704040b0429006030084c00040070286c0b103041e00480f00a441c40d0081064407240308000c00c00c118107075100700e080c0d00c10f0f088000040b42d0700700034491101130007a18500c4007882d180c2c203441c0c0700c0035101e000502110302d01c01c165001a0705c0b42030303c1d800d01c00301d554500c001840c980001d02c03403020400d40180c860b00032200080d218602d0340000a52075180e0340740300021030707500400303110700283c031202d046a00350001c1d0400d80045c800d20001115548070507205600454100c904080b550030303020100f04d01002d511854003d85212030908008114860140e5400b030400318000c0c54031441c407100207103080a40f99104510300601841c040707024604040c00c40341041415551343c125480301e41840e00182c096580c03460400000c0e80b5442583c1421075000c420142c0c46591400d9003c002a01000305480450242d040d8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 978613372 1250 978612122 978612133
    0x501110405150f2218021206090103120f1e20010603020d02090405210a030b01170a1107050d02030304060c0302030411061e03041209050a140103021b1c0818 69
    0x12400b80d51412407120002969041100d441e100520441c044a80c101c1c00c442e46c010030b410043d040001d03003040d440341c0b054403450307903d41c510345400680389841b107071600601242d2080905036030b1060008140c0c9155074484981c0c0300101042c02010b030b070012140006010000000c202c003001041c0101c400310380d002000710300701a81d2a000c1015490020300122518450584140c590100c0c0542020198100001481d1240801070b4040c040e186000762039410481d070610741a00c0402250040381d04640d03443c00000716800348110038020392090307500103080ca1150303402506d90580c0c00401540315510030300c424000042d8880e0107400f42e0106035002005569000704060490034024083c01c29288030007401d4188680b21140300340036510545040c0c90041e4181d100358103507900099503000626060760703998204c0c0d15020700780c11000c0240558904041d00001d545403114201808001c10030109401d9039141142c20900e8511a46800c803042c0224481c000018484458490420040b07134280d001b410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 978614622 1250 978613372 978613387
    0x1e1014100614031f03020301090c090f02090108192d110403150522050a050f0c0a0630020a021b0105160c171f022b06030501110405150f 60
    0x2c0079101c4035141044002c13601d00002503a07090080100740c03400b1781071040a850030001c911080d1042c102c0071182c02401041840900e0745d224140c0e030b9100d0b540440240c902400107070400e000d41100c0030b50b880310b9066940c00700b000e040d640380c01e40300205040b1001c210120444442076800e0043e840b002e064a0550f403803401c009005600210303404000002c1600401070160221003140001041c240c0711b9a1141c84620200303c810061113410201d01c600500c0c0111074580018040001c034000d8000f00700000008a0100b43c421801d0f101f042c218200d0307400342d00010b103c40e000a401000c84034006100d8000030046442004891641c0301c0c2040e5541c515141058000ca132071f0151b8200c0c121070b040d98006001442c00400240d0080780c040c0240500040c0042d1941d00001d0701070700d6800300d81c2910420a0314400501c01241440846d11090911404500420020001c11a035880030300340f5403c213101110507601a01c01401924030071986440b000060700080829409a5508a24400401c02004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 978615872 1250 978614622 978614641
    0x516180c02070b0f1b1b280b0d0e0d122003160c080f0c0d08090615040906050711070b1c051305030c0c0f09040201021e101410061403 59
    0x24440c60307150702185d40e1950040e0100c2e03403400080c21140303411041e0307102c0a1081d6107003a10030034800f240440c40d208400d4a0840c00e00d116001d9510500c0c1441d040090072010f80c440310340044100c0806542501c04001d001000070700000000264800f0052625980c0c000c803c0000a1204c0c000403004985804e60b0340b40e256403240140405814000d2280c5200b90f40d00040003100205207480b40c0d4502d03191104a0304203c541f0744120000c030142446008000c0007090707480010260360101d00042660035a401d00d0340850020400e81c4000360840381448200102e064001501e504210360040c00c4ac1c01e000e5071011004080d0040d80145071986c002d40b411640c002419801c1a50010502040780300714035920b075295450355202581c0c801c120303000307d0081c0780c40c0d2500035078030300716000d00360f60120329032900b580001c0d141c0d81101d04541c009407044d5107000703550808004800d02d641c4d080d4030811030002804c0105031070000031035054000e04100b200204ac1148552030a000c1100a003018504544821006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 978617122 1250 978615872 978615877
    0x1103270a06090c0b19050a0905090a020a020d080115031e0207050f0c010c02030703060e150703201207140c070605030f06040204081207081c0209130c02030f070516180c02070b0f 78
    0x240230400c2500c000304c0c065440c11009400b90821000050f91410701c00d038040e08009280501340f05212001300101701050506603081c0710700c2c0052500080380352001c01076070558650303060411a203900c04101102001000a0030b1860a450303002100c1002c0401e80044418480c0300707a0003905070b0402c410410028805401020700c0c06202c4041e07030f88424000400c20650b0748116000b1000070380b04c01600030803107000304060032145950004a890048407107845500c0c203402500b03445c1045400c0440040d104280000d440340e03621040d00b07881e451a95080c0041184e08107440145581c0304a074003250b110b1426208580032900d44001505040081d030030321401e55000f00c1803d54641c617007000348030f07100403008191000400310480010385a0703095a0602150041d9484c9503840186010b4241c6903d40d000002d55507400900441300e40d443d8190b1911608201c58118244c64061040700045110345c1c0a001240c816901c00004100d1a2103800013242d4805040c80340841e00322013000301c10348010f1103c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 978618372 1250 978617122 978617137
    0x61202070503040e0f040b070509011e0908010608070e101212020c091303110a1e06020c010c03060314010216020d0206070b090313091103270a06090c0b1905 69
    0x40d00c1c100f681e1800302c00b11004040f00c1c00b20500300303210100310410050302c16164110509240c80c03400d00943c440040c051071070000d1004040350402400d058a85c0c40f0302a00f40107030280c403009114041e95240302aa603001180103c0c4c3c070383c5440030009445194411207190440b410034650311600780ca15210f8590b4444500c6a0b881180a40f0108241a840b0500414020811216182c09091a504008104c503071072591501254104c18401008909000b07500f2081071a84082030104004a1814800910038041c1c0045c2550030a902c4551454156002b001200d00078141e100500030075001303a600300c0c4180f80d0b400c0c0302c011444102d14054100518100d64451024040c10b2a10781e0076100e15a0110044500040c6680001101705180c00d401050381e00401c6545c6040c4001194402002804d010052280b0342d040c42c1101c1070100d000340d5200c840a0141da140a0b186560700b9428944040c014000e005e41d000843e04500150344071880049684108203484102ca04d5010b156040354140c3c0442d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 978619622 1250 978618372 978618383
    0xf010806090303060628120f150302150d0e1b041505041509060e0709081212040f05030c06011401050c06010b030a110f04051f020303270f0a06050a090201230d0606030b03070e0106120207 82
    0x73704048102038811302500445080040400c59201301c071245141440402aa0240d8188849225182c440c101c2e9181929030444006c03800ba10410b029041c0d40304103521103224a0705080d030005007411541000703406007281d5940c030007071991100441d56480620312001c18095100304030064104510107461500544074565140c460242030310303001d1035500020f885440f20741141b07004124040211016a01010b02070802c5420420010000d5445040511130407039004c0001000980701101940f10300301c012045010f40d91503040202c2d4101040d0010701420f8010404c1020740006443c0003840b030600b6203001d500551855880050707040015252107501c00c0e1004400c1c0003144503020038042e1800c1d48850f400108911503190070018240d490107000c090300c551503e0001e20160740d011074a089072100420052290448042924050707200d2203803800c880c1c0c1d192030804100b82d6819000310724440c030200c088456031512144100c406507421700c07075400072440068050142030320507009495058003d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 978620872 1250 978619622 978619627
    0x90303010605040311030a0c080c041a0d0209090a051507090801021317070f14090c040f0506031806010f1d01051f050f0706050f010806090303060628120f15030215 72
    0x26a100d11030030581e0381012000e50480f1140c0102b070704261145511005820046a209100c40c4000c030b001d42903101c0000e40100881d000160303800404005000b61540d1080031941c100f1542c80440d112000300340c40410000b404c0c0200020451014000d9810f0240000064246e0601c0d124010036603114848046c0107502035040005031500c05402c0701d90041041d603180001c1c00b140d6000704010301c407000300000e0120605200600240c80810141816150182d0f0050707600d4030703803c9400207100c00d0f4100708445ca1007020004184415a80e41140460342d00c0040040d015040c0c0d0603043e807041090107070350340110804000e420303c2e01d400e14550040917a141445458608020f41484060f40700340e00030307200c20707480e0801c0c4007a8202e0310b402540100b40c1400039000c2824103c07075507a2a4400503000ea446082c0105103110080700312440e000c100300259000d40d101240c021000391030280100a86401945442203e160020702d501501440c0c4110700c1354035400904540c20400d80a402036050140003506 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 978622122 1250 978620872 978620893
    0xa06020102070b31030e03070906080c19090e0304090b0d0302120f071403041a040305190c0e091c0908031209011407110705010924030b0301020d0e0609030301060504031103 76
    0x312004d11489000740d81d040340c0203041100741803404849521407001580340c64010420300d480850715129000f001c54180408900d40d1109074450700f500e400803030b5120320b03196000c40340f03d80c000000c2013122980e25081c01000640410000300d16038980b8054096001401f402c5500b9548074000d01903100380104007400c2c80c58540302c8000c14400f2100350b4509900004061012011900e40200604a41c86040f85410305641c1c8440d00e0303641020f025041c01a1070034a040401c10020403440180c1144008002c0c10f00d0480c140698588c030060070003124810480c894520140f203842e00700c3c25501020000d41c50481407071461180d808006203880025503945044207040c0030300d541104d0003924690390310703c0c880d60010011814681d40c1d51001e410701000c2c210412144868620b14854440818900101c000010342c041e400340885130380c100c2d0306501c0001c0030380030301072541d009854151200c0100d07000d540d6003c15259603407200b0b01840c000701d003081c40b0400000d818a0702e1140440409001d8640c075015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 978623372 1250 978622122 978622201
    0x402011209050a1703220c0b0304060902010e0445031e1701090e010e06011707050a03020f10030b06070605090f1c0f0e0616020a06020102070b 63
    0x3001e09040351550040c2c80041d080c8802452003526100007405110700e907042c600c030f903a0013680d41d112072041c00003150340200c418040382251000042100c0b000241e42c038a05880c100c0020b0020b81c000324041644803000c000903041c60f1241c404111010701c1003c0140c2c1710440d0707401e281e103107081814150044040495020303c1001a51b8421180300b615583c0700c49280641c102c00c88902c0152190070001c0c1b011241e8400700c0345c80103890445140070000035044035402035050140848255070340042c0b007044000500d0152031426680d0507110502590315840c1c5540c20841000000d200c040d40c004081410703c40d0900d0011955921610035040004c0d401940a0100d42140c10000f01621810303554003c000603400d007407041440c50500794000d020303034100a926803da94102031132880100034034900d105c10754600031011100d00031001807500f6115021700214400d4059100c2c1e00324000c0b40388810002e03905005009070f4032810f6005e02c2d0086030f6540c45400c00c451030701c0101e08200690448600d0b680001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 978624622 1250 978623372 978623381
    0x2061c18240221340f0309020901061b060c0810090c14130b031003110102031615090b070306030c050a05130e0307080c0a03080f0c0a0804020112 64
    0x5205074040d00240c140441c1c2210007080036040e80540c07500401c50b4000b004441c0b50540700c000419407000d5120b440d841200800071480d035030034800000c0b0800c3c404000f030003000c25081c101c0c205a0340e2400340c4420f080040303080e603103040c90007034001410381c005115440c054404542560f4111010100c0e04205882d5542a102c500a440c40480c1186c07041c04400c5800700503400180054500a1004514410009000c0004010b0400c0c07107180c003040d000b02801d160b003c00c0c00100540c821040d22801c1040801d240400c0d1448110b0742c6d60402140c010f01940040260f0318401ca00b20a80300b0861603544070b000038050005603042640e03607280c0c1c001000840039072034503004030001c0e80c1c0014000c1c1140f5203080e4000705500064802c803125202008150340300300301c940c0820145540481c6846400259920b140035803600104802400310310616144400102c40080900030380e1003410070b4803a40c500d0071040e04152070451101c1c008001c0b0700f807820300481d01c55800ca44107141c001e8007403a85c114038030b04a8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 978625872 1250 978624622 978624671
    0x1e021008180a0b4002090f0f0a0c032409141023040203040b0609090c130e0703020d051f0506010c02120a02090a140105040c0203090d0c08120a0f0c02061c 68
    0x4001c40340d18000c5d070416480656200e50002d1a0018506040010201e00c820050081c0b41080d10f504c807518005100341c10818003001c041d041e1100e0030441418481c0150401d0151580c814681014004802654040540101113440d4a24031443c10900d1040c4038606041c3e1040303c0009002c0700804944440c030040d03104a015404445190a10504101040314060503e603559402a11751000c036907107020703c0c1c03910055081c0c1d000544030714604103030b4148500c07940040c3d80b0940182c1500107014000c10030455590a03044090040708281c09861300300c4100f5a42c80e40010715440c130400042c00d14a85503019400031204458612105600144034880c0071121408525150300840a55811100d5000d016010072501480081c9026070020340d41d01941c40c400788120700d075031414000d000005030107001400d0380703006945e0345030303100003040003240d11006c40e00001451007401010494841e800901085500030145480c1c07039207010900310558070703908440030300c0c0b40d89800082e0448080c40f1051040b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 978627122 1250 978625872 978625981
    0x60724060303020c040c0e010c020a03150507021005010f060804060f0501060908010b01091811070512031512070b0d020c07120c051c1e021008180a0b 66
    0x601d09500d402801c1c03601850009003c2ca0602e4400c04a058108250001264003860700083c006828000a24480088d40c00035103040c003504800240c04e465074002620511241e0210783e0300070f2441c10814101c0340309203c0d6500303001e0f003070a06200e0248101c8540340c1007401904007045210a445804007143e60a90002021443c09141005103000c00e000301c000c0c3c10340900385810010701d13280c101c14401d100e031420044102e60325103950320840900025600309581020884a4181c260020448294025204900080508060083c0b07a18140b03142c40103050b901d0028214540c5403414280032600300c100070f4006076800b840760341c41400301000210700405480c411110300c42c02e6030030018003140311508010300075805804038005208003200c0c025072542d80107044240180401d444604000d0265000a5004c1c09102d00c03041185d60091060f07000d008548480780d041c4001e04403d565903076a0403401004108d64000003400949107095918941c0e003d0014198042c2e07403450000402d950740d006060b0f1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 978628372 1250 978627122 978627131
    0x405102303011104120206070602120c0903012a031a121b03030f040312140304080309010b030115031b090c11060903120105090415020f0a11150402060724 68
    0x8840c41c003401001940003504080c107107043d0800c91240d00f840300455020703014450014030201044200d41c101d8124180c0001241d80c0f50620200c10300c0d1591005071118425030900b288502d0042100c06901c0c4034480298122107480751305c41064002c6c0c586501c9160100500020751031203511060980c40d004107202c400b4082d088103c140345100980c0421210b80607900c20300400c9041544035003150140c80c0c11444030701022860301421078040007500b004017001c4070084180000c001c02c4502443c05190540002d22071420804d05050884020601a0200e8480c48108001003003494184d24a002e06024040c48401d0300c4049000a0b286030f4984240000c01205d007500900c0000d0080f20340180725080a5032a00140d0300e8541510301d0180a5184078000d0035001c641000345c0044440d100d441620030541d00d400303000d030b10b404094002c482d8007804240d840c0e20304011990049444085445000303901d51042d1195000d110194004010480e1100c400c0c108120b60000f00403480000244070010114 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 978629622 1250 978628372 978628439
    0xb0a05040c020d110d050403140712080901020d0c030e041e0e030304050d0e0a061407060c09140607020603040b04140105090a21020616020307150501170615040510 72
    0x105130003a22840c80949070446948140c0c0103a2050866040f6500300404a00d80301c0808200303400c0010700c0e0300c102e80c000c100003c443c1c20800c220019240780728098007a81ca54018004c000e841a000f0120000c1c005600ca4070420311625081d848403600d102001c24820b50325020381c00010855152440746411640084100410494100102c944d00a458a0022000d100181c0850f8000215009407401d0080702600200032010040503101210b411682c1480407440e8090050810046401a0340074419030490f06401400e01504480b603095000e04028070310307510341d10350791400c4002820442d06901c1c000541c0307441c12400d014540c0034030307081009080c22400f1483c003054451049107190b40345190400303900c4a51600400ca81360300c5070320341045d40c07001158000201c0c08c52013034410040544604800880d42d070142a8400d9050340e001c207a020410382a0f4100c255614141221400b0440400d60040071950038260885034000d504505044440c6031218007104000c80746849104101f0410010013 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 978630872 1250 978629622 978629627
    0x501050f0d03080a020a030e03130314010c14030405071e0501080601030c230f07061a030106030c030303150308030406020a18060f0e1302030c030a0b0910030201030b0a05040c020d 79
    0x110924031003201c90810088159402502c07200008043d8100940d010804820a17400303a040030800c840301c075096a130782d0183c40980f803109014034001520f1500c1030302c01c00c00000c90b051099040d40d0b035003601c0e1680d1008410052a22544c802001281c6900030b150740082e00700ea080c10304012035441210400b800d58100000102204d42c010100790405041060000400b41c00c500d503200200340c12a554411800a6800c2c590300e40700795450144440e200180704424040d0b60b40c03000c404501d068550340c001c564440100750a940441c00f0207021034454440410001c1d00a500043e40c01c0e105d0001c250226541c1d8440940c3c075041243c05454142d0005042c240455202e102d00c0180d02955002a2030740e41450300050060080c4a007420908c041c11a09540c10307030703d2038241d07a1a080e000c4400c3d9a01d240001011400d904161214035205061403201d500c1440c020300c180317114200c101001d029062540c0c004401504130354442903001040380a0104e8261038500a030740440c040361700100080785403039000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 978632122 1250 978630872 978630889
    0x72a060e01020111090d02030109080f130e091c0903062d0e0d030b010e060301080c01020f010c0503060d020f0a09022a03040b030405071706060111031903021803010906050105 77
    0xd14116403501090703003141c1e0340420a50b800803005940d080003c00c2c0c00d2010900400b1301641c05840c2410100f40d0100c14040003008112003000c9044100c0c00f90b5840c1d00a0914841c150744901c441d0700305070300510401003220b00380ca20f4002140f80c40f08905503240c481c00304941aa04655070803c0e104100034100c410b034007002841d1103007905010005035042e203803034030388036001344a2180c201900c44013045c0950384102c82000c1040b00082c800e82c0c5c1c950756050500e542da441484003a0250061640350031031f1a10600c584440b00348030743ca5041c5540d07074803800c105070200c2c3c0030b1080341d0001c83e4035480421a00c03100d8104000e00828140182d54074032009094410000011411801c402d02051500031101c0110aa03000c45401c1c0c001c0c2500c944407480c0550a01d9650b0b000407018200034a104881550b000031080e0054800781c0741e2035915401c6440c41901e9200e003006171380c2d581c803045442412542c4039600504040c0840160b5540c048194400642504d42440c01a2001d94a9100600c041e00d4020381 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 978633372 1250 978632122 978632147
    0x7140d02010f05131d060414040f0f03120207140606040213090f0204051e100504030b2703040e1005031f050901020f03090a030f091a072a06 62
    0x20150181449a40000e00c0d1560044294080140c04507680c00040312146035a0003800e082013082d01001c07014800340302c180104603507842c40f03181420030b0303000100340441d1100e01494000381c124902c0f0869403191500c10018030400c60800420445021602140380302500b40c2c14462405c0a0f500d240c00900c0500d04080a08844c0c031482c810848039031850b5000d1004c01c11100c03544408a07018460904044c001d0181d0b43c002600142c85101000e19004004007140c5100b00440341c284030304c2604442111103000d180030041805030b81001250f480000211240074211940c1c554810081110a40c170b0300b1034000f40d001401e0b4584807010b212071504402144006801d05078000c0505454070313607070014482d41c3c1140924056903541e01040c4181801c0d012a8140640941859601e00b07100318000c2d6911200c81c8180d0001d5550300400c20342e540314412490444000e4000c0c400740700001580e100305030303220103000c42e4102c80100300c0110981c1c6051081805095038031200310810314110024114950814 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 978634622 1250 978633372 978633379
    0x9011e05030405010b300a05030415030f05040c050904051015050a050d0804061103070b010b03061c0510150510050714010e070603020a030213030c0f080703020d0209040309030807050714 82
    0x80b1a5a07583e24506442d9461b501c82c42440201c400d01c14600e94140310005001a140303000010700811031858840c072000041215a17001c002c40304001e15681e0480f402603a00511002d4130110402c1186010303620503400ca030182082d0b81408040c000c804086604035542d11500c0c94103040c08201d030f41360240d0248c00502e0161590f60389402e156641280c50705c250700400051150440201d41c0034034080050307070300565001c485083c040d40c55261100ca41c0e0012074a0600c24182c0411902e0701286400716002e0f115070010040c0000031420441801401c8100c00d1420b01c160303000c00001d500c0d0342c0c014080c0500912512080e54030221030600e000000194245203505a0400f1004079140c40700040d941300b00c41c424580184c464005020440c0a441880e14414840c0070408021060042000344002110074044030030304644c0c1d46d15407481d141c1c0c44c0c030302c40130f07500c45440e403a174034050b080c0707826042e030b010f407081c5454030000b51255100403c41e000341c40191041d0707204a50034041c00c41408035410668104a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 978635872 1250 978634622 978634639
    0xe070f0e1003170409060905010f12020109050f01050c030711040518150604020c03130627090f0209060c010c2a0320030a030e0d2309011e05030405010b 67
    0x1d500e030703440d403225070710000301455900c5052018100810f0140c40240649802c00d00c191a641c6600401808007030160b00b01d1401010000075413840b00b8803a0b22281503041e110b43c01c0891901381048040d40034204800c1c1031000400c1207152402c000d00007080c405208000b10b00c00400d1700814072084890081414281c050191840c12a45100040c910762210101450301029a600750114010380200da80203449884003040c96a21201a5544e21090302d14954030780f044295075526004040b41d5116002c0418031301c6003000c1c048160203400290507642c0060340540340c4820003005c11200e60045001064030395507410750104040d4070041c105c4d94a120039150342c41640c2c3d00a0301040c0b8800a41000b01803013502541080b0303c1084400140003e010318040e41e80742c0b1700116000d4084e00007074140b102a8010401c007288400d00400520501410410a02000d403291440070b0070b0552109400e903041c8032001c11160951100b460360b911400c9a6076544503207a0500d440d03d1420f6954920a25100301400e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 978637122 1250 978635872 978635881
    0x10e091803040f0324060b1b0c0616021005130b07060b0603191401030c0e070c060e0d090b0309070b0706060503070b0c0c03070b0f1605060c1c05040312021c0e070f0e 73
    0x1400d40b00b92201d549400c0013408d90484007240f90051703603407480350480004a4040c08806012002089043c000d80d003e2190380703038683d401c541612070400206c000109156052040d813032254060599244540c000240c01c000040c000351039a042280d10f9002000d07201030a0803010301c1401002d440060002410bc0c0300c2d41907545451a40255015900460001d040080d41c450720031659a9840ad4001c0d00030003c40654105180d15039404100401c041880030300d001074017010050482e4030074100c18014082d09800c0a201118552000d14251080c68881801050590f005e000510003004002c00c1c032603680000380c440504245840812611a401c042c401300035000344003040ba031804600b91030ba580d8502c003a51002601240754030b80540310b4421ba00400c0070002024008104001a9000e484116003265907404203560b021500180002d19034020742040701c1c080c0c0c024000440c0107050036840003001240c108104c2d01580c4040c201640101020041c81d2080105000500681030284456141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 978638372 1250 978637122 978637139
    0x90603141c020a0321051006020c09060312030601050c0102030109090212030a0f0e150c0f1504031209030e1e011e05070b0c0702060304080301090b010e091803040f032406 75
    0xc3c04100a800d102c0e0580c0c5404440c5503100b1442510034028008105500307121903003503405c8a0074001c45002d40b14200e104465450902c03010740c458100240201160010800c44048a801c040d010030705003c1c050101c44c580d64002e002544c060080e58000152054607801001100504a4a541c051b40c004000d8104e20b9a48140c2d00240d00f4403030304050703e401c0d4a0001050007012305402000f25800085405030783c041e0b001c030385080ea8254a1040350151070002201c802d40d01003d031802408a641802072000c0380d0b01d19013040384120b000e820166543c042c14030125900b0345083c000c0115001022700411074a40c1c00c40510301c1200000d1401801341070760410301400302e00c200380e0050520004078002401d4140d60700300f29030032540d015007565104c0c103080ca0022890741003802916030a40c00c2a00689082d441000c40e00c0b440c9034014800680f940301c01120510b01d56100c0f1040c982d90104000216508014080400007503100359a00e55000da44446182c026401000e00300028904121303041000c80c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 978639622 1250 978638372 978638383
    0x14100501080d11030c15011406120103030e06070209070c0b010807050d02120102070611071101031a0907020c1f03050606031b220e15010216090e07090603141c02 71
    0x21400c1c01d21030f03058910724020901d10300905864801d02c0c8102200501d0520311841c505040382c01030000170b200c1008100c20005640110482c0303081c0040341c0d80040020134814040b03480d0944000e4100c91030b24043d500072031130742d50048844d500482c17480345508080004c484c00090041280304042c1200b02d0600001401481d592280039208004007055805a00004c1d0704032006540d102608100101000403480f0494000400c00d548804a0300414001540207005c1c0988085107410b4a0f501c1a00c00c0d420428283c1d0050071100451040d100c000d1b0141d107494580c2c010104948024070316078000d0404c014103540c40102201c0c008d40d0184184805134001407036003100c61580c0d10000741c8030000c92115a0b040b5403000c440d03c51031120103c00081c8140d0074074109004010540e0709209182070308005980e154100301d08136a811030880b004003d08006540506288002c40094a202942e07030110f407029908281c00544030b1850b4180072401c200780c100140b00202d05862840709617803424030000394968 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 978640872 1250 978639622 978639643
    0x206030c0405030607021b1201271a09031c090b090129090408280e1008060d112e090f0b0717091c03031107051f0b030304031410050108 60
    0x1c1020546041d0801421340140840d142c9100b60350102c018000c079400c00070ac2c0c500c0c4003616032a0308652900001c60640025601c1007207918020361401718901c120b200407500420b0704019503a501c80b0a01c000a441041c01800b8070443c0e0004150101d950401e0200007501d08c610001c091510901c0300f5a50326003942c01a406038209200c1741d140e8882e0072482c80c2150442d68100020aa24080c907440d8642000b00c00e6440101603440c18607801c01c03010269400c250030340e0382c00c1c0d019100700340d41c0c40020800356110a110340040e006000c500c41d01201c0540d2310a000307001c030b2480014487c0c5251800e900103000001031984001e58156245409003000151044560203481c0c4060043c2240000c400f00e42243c2540f0405056900f543c0e61410142c0920b44000da41200002d0900701600b440d0010f0304142e841d03042e00200030b000b10040f04c2c400d1100303041240006035130403922014140d901c1e5a00b4000b5000850045047c8800b01484540c07031b40c28004c081c400491420316000c014800300740d00083d2001c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 978642122 1250 978640872 978640879
    0x1e05061e03061605160309090f06060c020d0203010e030a1d091608130206030903031902041802030a061706040c06020a08030f07091a180406030228030206030c0405030607021b 77
    0x10841000c12641403003040c0032070030960001710303244c810541e04c000d010b001c4504000c020000b070710488402d001652840d2041100282d02c0300004005480d0a4801d00304051000300001804a95141030702c0c1150801c529070f6012800c1100c41c1180446e4010300300c050018105d51159152410f0201012440c80c560069400c001d035a00000d40411980d629540c3c945d034000341801d4a82ca850507042d5601d500494140d6950010190451503001e81ca000365000d980e214503000707000500c8032003d08029000101640b50041d181c1c0d00c0043d43c2c1d407003411900c4045001d032000d02040d251508120f076088130141e100408562102c002d02010070400415240c101164003a12102074944010448062950781c01c1200d1f852000c41c100c0038600c58250040c0480c3c000003405a13010041c08042200316280c1c0c3c48080d4220b2000540d80c6694280445c412108800c8941507098160720780e0045107168108442c9021080700014060206185c2000010740c890800d10041106452480642c400b0b058003196007800f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 978643372 1250 978642122 978642151
    0x60901060503042607030e030a020f0d05010b0607081e2a150703060603060512060103030e0102210d0b1e04050601020f240f09070e0a1e05061e0306 65
    0x4002a40c16800316000d100520b803113012068038041072841d03000a800314080743d49a8050b2003541800310f01c8041c46a00101580c8059201781c09000c03400032403000440d42d95586602140f42642d5480140ca00b25005020241c4c45404d45840d8450080c0001040103c00f54107011810111000070000d442526190304000c0b081c040a24803185000d05560942d9154908a0100034103264160b00040c01ca820303950701401010f6441040c00300d90541d171a1091a07540002c4018000319001e0190081120030602c110369031220107101c01c11041401c070b1030900314894000741034003e500e880d0041d41c001140499000a1282d04440103511030305046410038001c584030f1700090341c3c61380280201504040001c00356110340150006034059032440050900b0a9900d036808180400c080740c2e030103072142c51544000e01c0c02d142070128489a0000c000c091103d40c6407070318101040704903e1086680c080821070070105841c1001004c00035501f0104c080d41c84164042c0485410903035000800c01c0c1c10400c07da40e4081c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 978644622 1250 978643372 978643381
    0x30f0d0f1b26120a1b05030c03130803071d1203160219090905061e070c0c030c0305030933070f0c08060a0b010201061202190312090518060901060503 66
    0x42140840c00010410703000118403028004125400f81e40324007030f4080100b00c000660102036103511002420503002810034400100c01c0b912800041d904008103803031295421621741c0d9410240c1d8021101100000e520b926842c03207611043c00007000c803600c2220804180520148000d949000b44808041e03851420488041591030340705c100b018420719222780c2c034840340d02c43d41144050180740b503040340c880c49a9000a00d0f495000503c40c212800342181c000e40540300d000085903002100714041d150602130b0313040000080d80c00d0031140d006610400207180c4074168101000310068541d941d4211000d120341081641c5074003100520792541c1e25102c1d40e0748a00b044c0c01d08541c4044c0c00750005162201ca0b000203d80c08100142c02071096400300e40612101c81c81c28012401c2c0c9041d40f00c0c55081d0b001c2c41005200500c1d010f030824095800300504d144009a41c1d4980341c1401524180100101e42220014032481c10301d0810f0005119852907031014504201020440710101442103004010002c004103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 978645872 1250 978644622 978644663
    0x40f062d1a030d2102090a12110d0c1743090533090402040209040c030507090e010e0f0c0705030406030c08011d010e090705030f0d0f1b 60
    0x40d00c0220300a81103c0e80c100300c0740030180c42c03094031004a90b540a000d5440e40070044150085408405010f85042c200b00d1a003078008010300e6009000b16689042440e215540d0340703d001707130302c000d05000c0c40b400750116181c404060240f40c0384030842e03000c980200302103280041404140012001404603001040d00b070f1070b2030500114025404041180d82100d0300081d003030300260842070003505000d9aa43c140050f051082c842c80315440700c0ea5816400785c49001e08245413400d40709034802e00162000d80352080c404006000c1302c0005103404c003c60354500c00e10a10a60010007035010340b181c1000c0c04055410a0419041940018584461101d4210001e07841021039000e5600d015409001c8980b141e03255903020b00a07102c0e01c0e41078400668080000211002c24018500c0000d01242c1428050b1b402d0001c850390b800802003900007030348502c040c00a11910f0403c401d80304c07607070410040e046010200f000240406004c210120400060940e034040f00c0c10040f81a601c025801003603480880b407940b110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 978647122 1250 978645872 978645911
    0x906010903020a030b01030302070611250e040b100902071e03020703050610061e08150f060f0414090f0114041b110d05040b04030303021c0203040f062d 67
    0xe40050800f80300204001864032101c1c103a0388240c0036989083e840f44001ca0f8000e240000081e00ca03032044600102410104201e044816540700b205d400880d154044601d4102c0242d0f800c0b25094070b038608000320485808200c4002d44801c4400394508912904c6803401c60000c1a440d6245160322440001014000c00c0810021540041660b05900d04510f010b01c00380001c1c031070600498900302261f018105040c1007049030340758a88401ca06a20307620318107540050704102141c1c0040b51a40710f0181c03940e400002c2d0403080581b44586550b18188000301c60181004141c6078001c200d10030034400203100103180103043d50406801e545075240214005000b5090450802400c0b0080c0211005003617442440750000200740c1088071901c040700d040c00c032001c0c403070351044a01d502001e12003400068440d4008180c01440c0c961a001e007200c00400b01c2c030032179000780c6048481d4012035054a040054601444420160710040d021000f810003061045c96031045039461451551020b5041904012454 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 978648372 1250 978647122 978647129
    0xb10090b13051009030b060619121508250506092701090e0606010207030308070509010521041a010b0d0f0f09050d1d030705061b0d05030a05060607020d0209060109 72
    0x480424010380f28003506490f0b480c00260303401d0200c0300015910b420007000300c500c2c604882c1ca04680c180c02e4a102100c00ea48110300015002d92200d02c0303112151a0865000060030810380a0041e084511000507108040015a94103850090320200041e0391500280c6800d0703003040e034059284c0400000700e01040c140d100501002c10445000218908002c0ea1001040401d800c00701e0710303551a1711006907a00c074800c1c8401030008040c080050740700c512450140201401c113040c258201010114100004440b00f1080c00c01044e100c000c000900196800070342641f07048075200703d41b65050003207101d058800c5440044619859030310000495880da4810b0026042d10b40041000304031605c0e0144d1142100514280000c031a001c90050f0142c003207201a4804400a00900e501442c200502542c2e4204884d140c0d24900c4c400d004008100701403007401d0005c0069650b10340c1d289022000e0004998026013800c1c02a50305004d10300040c0c54081c210240035404403294056956804012290450142c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 978649622 1250 978648372 978648379
    0xa0b0301090603030f020303191d03031603060501050a0f0507111f030b010315180e0d020105040201090b0a0c060b030c042919060c08090406080a060b10090b1305 71
    0x5008007250700c280181c0388a0f6448600045813400100e96a00055600c084c000e40b1a046400c04d010300c541c00b07181c0f02101e0012405045900c0c0000e1403d6070411903040903002215000c10250540c148030710400740000742401401d0649400000b07156419440340300342403103070015988041c000e269000c10311131306006203000004001e11901c502489100640d40c0301203411b01c1040049036019000b5501b12062003003000d422180303400c43d520014030724020a0030b501c40c0d40746124418a44140b00003124208640c00104142c2043d1000511007006a0300c00340a4142c240301107040c103544191032009075600844046820060000080c1c10585100c0d5029800362900302841c10000c0c2c004185804480030320001458448040140400350141d80440d801c00822504180700050107842020019402803840a050004d16404034044415175084040954003904101040108d64011050046019101050540d4200710003904078640c0d40903c400321440400c1800c110b481140b003500082030001d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 978650872 1250 978649622 978649627
    0x91503020903010b01092312010204081c0f090905091221091b060d0905161e060203160807150203040b0c092115090601080c0d0f020f0a0b 61
    0x440580203610041105000b5401c00b2160070f119030081880b501215a00c403540c5001d03105000c410401c0c0000c40c01e2103a070045407148020000c04092002d040a0481c000c02170601903038004a103891054060444020802e0746a8000b080075800480001143c540001c04500c6458042500b4100720a510728071402d01408240d00041340940380c4170520304100704003100c041e92150300e4500e8603145080850381000c071484000c080d1071f00b440802080e103108028400180011030340e984c5410210030291020040800e031600f40080384407600032907440d2240305507800e400d601d0068065247d0040006000800d4020300488090002040440d04078941c081103100c01030712481c0302e40c0000c0d0420780c2e090b1014002080000c084c65801411110704a50042c101200c059841c055600a00c00400d0240800d0081d1002140100032003444503020b034241c00d02900d42503050081c003501d4250a00300f000d110320459410100031820020384034409580580706191041e0700308001c80c0d40c00c20164020042540300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 978652122 1250 978650872 978650909
    0x91e0c0e0315180a08030c090d14071505120105152209060803040308120604020c0a0f050c0a0f0e0703140106090905130809040c0e060d0e01060806070212090109 71
    0x103504042d1003901c0c9150f911102102940e0219558280908010140981000898955280c0c400588494100141008030301c3d20156949680d111f90503a0343d04041e4001c80d0203000b040d045603840442c1c0040e519001c0d050440d00240f0b807076020010311074076005285549800d06040141001c071500390740c0621000e5a00c03145c2c50b5041791995003910600c07103501e10b403400104051102000300c0342103d0300080c8450808102604c0440854000fa201d254420b50070444009502000d100790b80e0b0060040c00e01007601503036420050700b02010508141d203d290480c006101c0c154500e41080f054455038410154180d845500990051070b00c3c00c1c42c0804850f40da80000b03020759000e000d25040c0c64000009120540744c1802040c082d106621008043c81001d1001c10082c1c241940039000c40110b610300b0001101c02c240100f00315078041508410600d846801495180109001da48010040390004011030300e00882c000352201d0640029103007903100080c900c90380380e10840d03000000e0b000350070358410382001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 978653372 1250 978652122 978652153
    0x60f030a0b04120c3305040f140304051003020702030309030a0f150c0909180c181401060c02012006190e0c0a0911070f0c0f091e0c0e03 60
    0x4440c2141e9002c10038000c0780440b8810041d06070181c2d0302000d503c1040c0d04041800074142c2c4148400515980004145d01d013074641e60142a0045006000e03400500f0005d090520f244803030314034500384503801080300f040603448000940744245e05614005840d40703900c0c40000d046108041034687e06100c1e1035240b400344a6a501030302c10180c4950060450040c03c7d12158080d220000c13240c401191b84210100040c00d585d400004000340800c0303181d50f085516503242c0600b240702c0d070009441c44032640071048810100e88100320103840c007841001d54035890401700400c0b00c3e8101c1d000904000003210400001114242c034081823009640c291501c0e03141c010703002114843e2500f04801018248854a00b5400b00032580001d8110080c001c0740300c207401d03c294500a003e0312001c03130120603020020b1030003080050b00720012071440b03114810303d45498841030180103c0b80360011aa80ca140100728180b1890360301950416000f0101c0119940305482000e80b48000342110b0190980580c0ea88d24a4040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 978654622 1250 978653372 978653393
    0x2714191202061b030c1b09041529040606020303040203120f0d021917041a19021b0f070b1606021b1e0c060418020c0d051207030203090c0405060f030a 66
    0x21788140071030307000c0000602d204085404e1704082640210509012174041140d241d01e642c0002c80d103120105a04c680300309424509104220582c16011015041c0d81d000c4c682801150002e143c948011821824207070000794646508a0f0302d5200c4000000316091030641c2207041c1d89091404030000c5450385120801000c5103280f032620302c0c0000710009045252840303440d029a00135071f0040b0022030948901100c0b9600c5900140140207180c1c0c0300e03180c0e800c0581280c002804031525010034a120902410328092900400c3c41014400e0340211a0601543c0980c0c03058404901120210703010034141800d1410080c414a02c040c0399600202a103560100c1d0002403540310103e00c011b840c1c203c040d0b0303010095241d01156031440e502c18010881003144d007008543c841c0003190078040042c50a6103010340c6500d4208640300c2140131401c04103064400741060050b055010a4600f0107615502c1d160803010703110303289408140d1080e42d41c1c0c1d010840545a0002840c00b1074405800c80f003401c0075070b090201502 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 978655872 1250 978654622 978654637
    0xd030302030f010e0705090d110d030e090121030e1306060c170f120901060b1908060d0804063902030f010c020c102714191202061b03 59
    0x1640d0000000d09105000c060900c0b400986d07541c0d9080c440d4900070404550b00b02e4a064031141d52520a15543d5600d00c0c80c44590369109884046c18100d8080030311803d018140d0100050807010410b007440524000c282c0031416030305261006088000e41d00103603415038000d2804250b03902d410004070b9040c0c1c000c04c600c6041409003001c2c103940310070760544140502c038034000c50880b101d06001920b440c210140d85290090403410000c5011929641c1400290308000010103801840000070001c00e43c00c0020301d5001802522031a404010030384a81070b0318407880c42030000308000b003400c0b090580ea804040b20481d5040401810b02c10b003450f00380e041b000c4a428000da10034000d0104900038140f051148100d03200594001d41940c56007001006070403002c0c0414001404803050780301028500c00b1515056a100c04541ca100c254180304d01c5482075402e80142c0d40c040d1a003031600c4162110700c44000004c80d003c40d822607140c031110780f010485900544c22a00c141100d1070960211022003c8042c0881 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 978657122 1250 978655872 978655891
    0x300914032802070812180406140d021c080702120708031b010e0703050c010306091812111005180f060c0d06030f0b01030501150b040923070201060302030c01020a1104020306010309020d03030203 85
    0x1d5052070101f00c1241d420741b00d0008e14026010301911a810407000e00810103000501c003030101c244603511140c92620501088500324000542c00b0708500c2c2c0358251040c0b50342c01c400181131090074003030309503528480c0004a080030b05480917400e40ccc528094005000c811545000e4858465030380c070b07025540d811109111400309081080101300c1da02d43e40304103000c12003040c581489140c003e40fa1960b03045813036413980d0f00308000340c281c0300c40c0c009041001c1d140c6107028240018041c030308030000b04841130348540015420303044a540000d000c000042c01d590082c80020034031340d8415480c490b0303100400381c80d0300043c440408101203100b0301c206002018105e074000c9000380016240714403a1004031485009261040d04144414415000507900059090309c03026400504e00390100000700d10343c0011506100140e454290610850506110000e00241c00303000500c800a02a665061a00454400140155404000200c480e131007a00142c030001c2d00039201d51505e10075810014081e610807500d200c0d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 978658372 1250 978657122 978657157
    0x6060912060f18121e0708030a05010e04080a0810080d1205010e0603030715020d09060f061e091509020c061f050d0201300914032802070812 62
    0x3404200341407a11104010000034158540d58400604002d8010086405401c83c101145042c0c54017100d0003000082e0103000345544034074000544c01c042d80d405030840e041802c008000c2c080001c0000c0305550481070203043c60a110ba6810010700c5010445901c040c403248514100380e54042e41144494483e003d4603842804280e0325604211291001038442c682c059104025081c00700326410660000c0540d1f0035405443c1401c3c000a540036259031920595905a07200d240d2800c0c03a00c03e20940000b050100d1800e00010a4510220b090100601c503485806880390300004a00103820f40c01d00140c5103050003152600c004407001540c0d0741f0102d561707031314021202c244070b021030300800c2c1a00c0403940b0041c511894410380360700444114007094440d84c1c400702d040d003061012900322100d41c1041d10719260f000170200c5031424000415495031021000c2070300100a641d42c075900c07200608076140c407050140c030003a03200350300220314040c0c80c5e6004551601405406541c03d43c4540c00030800c3c8400d03c0b000c0207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 978659622 1250 978658372 978658381
    0x3011d0c090403020a0b0702010f020703030606080a060605041502010e0a050105010e070203031006031d2a120a08030402031216020a090c08010e0604090503040b220b1206060912060f 80
    0x1280d08250b030b010380582d00044101001991074a4519800182c2e4800419030203040940c1c001682c03c090400c801282e242c1d0010700145074440304c815800b5054800511020f03283c2500500316102d5800b80d003159903600c40000c44000c0c002d400800c62622a44c2c2252a503a40c1400c10f580285403e0042c40702c081c41510118101d02e200005480c020b00e082100700d420a07150660541c014800103d10200c0743c00d086100c141142004d01001c182d044d01c1c0c042080c503504080c250415001c0902c0d0903684144442c0f142d940a6203400203811b1015944228510354903216400002e1034152110200b01c402172000441d14504583c12640041d0244250350059100d61248801d100340c4141910000c00207115000400501c423040c041141c000c907019200141004041c0c44107402d5501a402c038150110303001500d1342c214040d00000f0b03100755122020000119060403500c60381e91007550702552000d030300e40c00440c0312a07461700100e5030342d80c1c0010305040070445410101d94443c40c0485400000d110441c0008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 978660872 1250 978659622 978659629
    0xb010b07122c040e1f0606020d090e1308031f14060d05042a30060b06091e030609010b0d1509061113060c240b03011d0c 53
    0x1000c40c80e9600c0e51490000c40144040c9042c10150140c2c2c2c0c000e445200d041244c031001e1005882605800d404008005607901c40e14040c1c80096100e4400c55008058600310250301050000a581c0300414004a17601d80d545211a00c0b0310440003e01640000401d00c17410740a11404850b000c50440306807908030b1350300c104c03105029248040c0c19401060410a03002245585c0c0d0000754018440c0d20300c1e60282100340d13001d9041203000d01950081850000091000b0480e45240925801c060b15034241002110001070502c060700820040c003068455100c14095034075441542c0c0c0c0404050300b410010205444d03128003070703d00f4000c043d000c1c0c002c80001c5101003a0600903410254406450008105102d50700c140401120b0098003a52071365685411000510358003490b2240c094006c81c903901d9030f44074100e01d2074442c03045d4404c500b4042a4001036001517124400e140c01c9540f03c05002103024084204000035000900c9181c1c1d05500c1d054000034204d11560150194462038003c6840001d00d89050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 978662122 1250 978660872 978660887
    0x903030f0903170a02070e07020307050c0d0f140c0607060c12140106120f0c021507080f01050405070e040e03130902070c0b0f0c010e03190503060d020f0d0b010b0712 73
    0x3d0070310286024880610050200100088192441121001a62000800d4a804080d51b480313005070800191882404810040360081020031102280182e02c9652200c1507030101d004010810704480c82e104008090a1084a03a1454050039a503602d0644d89490f5004000e06070001000c51014041c4c0b00502085106a0440c40000d949644041e4200b00c07050b10440b03400110280c030030762030300b801c03c511800c60b000b2071107105100d03001854942601480c2900a01c00105042c00700300440c401c1005107c04540c00d84d044840586001609850303c0100301c50903445400c90942060820030307501481c9074000020103102038600014060140c540c0310f03240503031181800c05400782a591070284245d070300400083c04003a007192600c0d45010030304c2c8895400d43d00e41840c9160070f82c00c007203221842c1002071607042c2c080324060310741540355192400c001500d8594140c1c0285c0552100280380d030094580c3c048040806410200c0011590f0351151803089640c04a1011214a1009814182c841d401140c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 978663372 1250 978662122 978662129
    0x190e0f07030b030a200d0f050f150a05060d0819020f070b07080d0b031203010518012301180e060f0103060605071b0f0b0c0705031c051c05070903030f09 67
    0x80c00e21400c0548491400c00c080f003940981e001704280f000c40c90342c0c2d18101c1c01540b00e445400300304038201c15400c0140c00c00b02c201e1a14070142d08070304010f0380c11510100006902c071a00013030028640e19080c0125000c11050032005212207800038142819400b050300315284044160300b294840320030b5540844c0c0350409403280c8504a2028031a0100040140c400f0b0300e080e40e6005000a2025a044006441c0054034100c1612400e000001408241404202401c014600550302c107003652508644075600b00c19821520082c040d02d80351401c16030f12038140c03c00503081d01441e4890716a1295080500b19038145ca01620840307000c03424103501d5001c0d018000403502035449990401140340c8030980100c031464503045041c1c6480c1c001003010fa01c40384000014000710160f881e1a001c04440d49450700d81581c0001e07106e5440340b10902c0081043d1201c4000d4043c403071400d5074460150b11078041d0318112025840d660181403001300040b440c0d2181244003164003a03516240707603212022003920407140d10702 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 978664622 1250 978663372 978663379
    0x40903051305150d0b04020c0a12090f0312050d0b09070f080109060e010612020d141909051c17070c17033d06030b040f05060609010e190e0f07030b 65
    0x803204c031030402c69901c901c40d541c1c2d0141004d85041080c0380901d0402449800864245584501510b0016030119858001d00600d00398a045c0d607086031509c18468440381c908a041000000d1500c00c500c5980e0095072046001501000403820513000241c41003890b040600e00103a0386600010380362105005807011201c0c000c3c10001075900300001120482c2ea18000e85200c0c54003004a03a40a4505200e02c2440700c404d030700e4920031401c4c04608100384180d0040bc0000c480e050604070000704034007160407000300c00390541e02ea49440c0014425207241403030520126072040840108000c3c0c94010501c0c080540c81080d2a05003001040a0008140000e542c02c0f00e01c0c401418031030300400310b20348074507404010703000440f41c0c0301f8029840d4408615040d003040300000c0e2108142c100c141014000e07258480b50b4150184440e28045021410074080e807226103040269210307200c04c075501d0354111002c0e0400140c0e20400c9543d100c40d0782810034082500c5880114403203000281d000da10034401c4e48400c18004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 978665872 1250 978664622 978664627
    0x21240a06110f1b13090309060516050f030910090608040b1b1b0d02031809100510031416080a05070e130b0a0902040501140c0c04090305130515 63
    0x310032a100d0a0240040d4a80c0c462908990441003042011184090702031001200a2030404207009011008040c550000d90a10141100081e00110070b601554400c0c6001c0f070311109259848980000307441c001910381d009203654070140302e5012008107107101080d81d80c1c401062506e03404480c2c01c6c083d8404d40000807101d00201e00043c800b11086608401c855044941c01c8510b40d101f10010341c4002c0d0f8800d21403a521402410005080c456181100320b40d001841c00c040d00010720510420041000a10500080000038a1f1010103081003020303007006011501440d80e000006070060606214244058817102c000450598003500038401d055601c0d91206115180d000440014010241c80507091003078882000c4015120b1300c410407200c016447c40403580c1c0c11140f007480710780d0105810181c4424010030040c0010703600140c3c594008450b4600c02592000c3c4400c10745d0602250340c2d25903500c582000040d005040e4048c0180000c074400a90360380d000ca550703404000d0368101f1030810b0403000009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 978667122 1250 978665872 978665879
    0xe090c18040b0903090a060804020a050114090904060f0e060a14040231390804140a0f0c050f0409050d0c030903020307030c170a02010c06050c21240a 66
    0xb1403069070000300d2001105e08103008880014120b411a40040303000454100802084d490410107010040000f800d0620300d2508614824200c0e1046100071030140b03010038081001c2001c80ea00c0300301103c00210080018801c6601025101d003415a151072607141441382c0f408403840e00074419030003154001c0c00040524001ca150703011407174500c005400250810041c9160004142c0148400c1090000c804042c2c480ca2482140c03200d00745000c41051000c0c0108601e036083d802074a035981041d003001908907003007817662610b882e202a4103002403180c850364190703104220710030b0100815124100c83e2000c90903000c50034001150142ca0015100c0c0c0c1c001000440394074043c4192800d450b0080c034001c2c0c1d00984070b80110703142088a074811a10b890400000300044c141e10700a880c00c0b1a41d00002d004415171503000206624007030a00a08655580e601080580075031104481d405046c0704c0e000e5608895194100e10040c0049803500c4d140c43c042c1c0b000041c0d4015104d00407020764401803580b1011403d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 978668372 1250 978667122 978667133
    0x20319050c07180902091018050103020f012102040909020a052d0301020f0316030b01110706080c041203031505010e060409050919060608010b1203030415150e090c1804 74
    0x902c00c503c0180f01c1d6440010700e015072210104a0300c504408912088000d1500e9a9a081203c2da01da0002030203117001d00600040e550340e024181015070910346000080d42c41100180d00100ca20201c02c4540d100060021381c1801c6034201c180c04d03600031101c40700038665400500420800c0c10044e007000c044403052501861418a00074000c40d44090001410440310b0381d0703100c2250341b0981e80d500799600102e900e2600f9680c1401002010324003860440000083c0b440740ea5640c1009000d034000344200c1c100014413604409054400610f801744100d150b07000d06080140c0100303e484c1f8403861400c52030402050550044030300204480024108030300e0585801d241500070580078141c2c2e400d170302420141d8201d05507a001e090740e103140941c1001580d02e1502560508488080c01c800d4014420110075030115000401071320b1b40203400400700100c0c4410315004100510704110426111101c01001240700130805a01512499803002100c500001520800c0b212040214181e0b0256441d200010002103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 978669622 1250 978668372 978668399
    0x1a0d080904020c0c09010b0f03010303050f120c07050f01060b1b01060f061107050d0305031305070312021f020712322a100b1c03020319050c07 63
    0x2402800818180680c01000905991000701000c8140d8003c80b803103c813600e4030750030142c010050410744a10303200080310300c034400d40014400a010b1080101d81500300c1c04007202119000d102c1280004c04034a0700040d2a0349070742084600740c4051144911541001c0b40512940c030503207407070f14842410b04103078164480c4104604440c0002d19500c0e0b070f80000e12100c4654000300a041903440b8058034580c0040b1940c40d1038080c1d40290f01c00d8958180300c0011a41040c1229000f075104030700d071101d1444ca804c0c010702d0140e90b580300501d0320240601d0900070690200f1005001094410758070f4001d8082c160301e00c10f0b0b0141d440c019282d01854003c03118218001c450010310703018011405240b00301030341d0440441e014000120140580001500210702e40040d04000c031802800c40303403009000b011124543c0c1c070406112803c0c51140d54048100456030341490381c02c100e44501602d0040f4001e58a00252260002c01c0c1080341001e004840304403041c0100c1c261410b40280740e0040441a00d008012041d55 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 978670872 1250 978669622 978669649
    0x11505031b2803031409060906071a0124082512060f240801090c020109290615070b130f060c200a29010f05131a 50
    0x1000b46410241c1c12a07203082040c1c80604184801c40c03466186003006080b003400c0092034440d054081000038155501d28056600504044d50621b40394080c626008015005407001640011505400012070100b8102414501140b03156201004401140f041e100d20308141d4182d401c0d581078480c401424042080d42e4241c007140c6242200e030114600002104442c80b68000000e44810450f05004201904e00303090001c0036501e20b03105802c1061180140211010f00806081c0d54031365012601e424800d4104000b185d8000b415000d550309020b10726a80c0d0700c5692040d4207043e40100016946251407000d130f40381d0301407040070320b860f2021682e036030940c1000007000d14130812000c0c190039000c544904260408184680380008a20604040140882404400c6c03944c00241e40d6054800c101000f01b05c4040342c9900c948100088204440050001c14002c0000990314205900000d071590765900d100c0104c41064600c10b2803192000d5006061b11201e20130401070420304842d101550a200d400c440c0c59 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 978672122 1250 978670872 978670879
    0xb0a090b061626070501060e0609180304210b09030a02061603062106060803040501050405011110020319050615090907140a0207140604080a02240a030905011505031b 73
    0x843d111103085103008000303500000c01d03840e07000c104d010402c6000d200b690060003140c007450066243c01000100b0190700146203410b04103000344080e079010410800d0364040d00c10080e0342d40e001020000d00703071090782d8041001d4550751150000300701d000c0c1d00030044504400320f40d4050811036450140c3c0b103405030108810a800c03da901e003000206a40400c28142ea1040040019070050303200d814104150f5400f90002c001c0790304200410080d980e040170494040b20740c00c0c2003e4424000800390f150528141310500500c69000008000607101c1d41490181c0302c54413800c042280c3c0c0c441406100108a00350b071451010340013048101018030305560800e902642c0303468494064074010310340611036000341001c2000341e8440c100620840c1280c0d4144072910105844c00b40c140b0b03140c440482e5407007a000001a0140485040c0c442401600c10041104116a0340743d0329929100603d00400074002c06506075203651070682420a0840308a07442011070703034014020041c107400c520401d1900c03900d4488070742c2d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 978673372 1250 978672122 978672143
    0x31418060c10050a0b0108160906032a0e0a12150b130c1d010c0503180625021503273c0319080709180b0a090b0616 51
    0xc140b01d00c2c058148250f030000c20105000b104c4200140a1030806400c0c2c00849070440350349403000b07a000150030120761f10f91501042114200d40600c041202103c03202100c2e003035442d8200f120b5504a030119041400c259a01d03880709a58002500080c0b2000000505900000f07440d008200f0068012410400c4000c01d407007400303130281d0295000c6074400488140420f0600141c050710740c0030f0080443c0031080a09024051805070382c1d03055102d01c5205141241c2c1d03c130005039541c040d03c1e284240c0380b262004510003444d1112a1005e07501d00200500100c0c461100501c80c80b0f00300e00f800c0c003038a006240007420401202c0c0c5417030501d034500c2080005a5141e200e0a6903d6034003107124103140c0074281d07143c00e0000c0ca6040c40c05503c4d244030300b0203a12707440380d5108000d07040100e0b5044c04500300c6a0752a141c0440143c41b8140100d0340105c40c0da000c0d5610421100051104524540c0012000d950851300c058580359515000300503a09418503240c1e105409004c5e004510140700440485144520203812 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 978674622 1250 978673372 978673393
    0x14120103020621150a080c0102060f07112a060a0c02040507020c0604141c020a03060903090b12150a150c1707080c0c030c0f0f0a21031418060c 63
    0x81030003401300d42d60350000303025291082e000d085c00081c034406000304402070f009884080300044d5441d100504100c468941c03400008810038400c44440c485080c104091700d41002c503d060902402c55004050602010008114145483d162044070798000154841e10b0845a040e0200401020300402800035030151400241c90340c0d07a00001400584000ca80c0100d10003641014010fa40e03c00540008201350490840000340e580e26506a0490380e01141c045103410013898200c4074200558042c4180d04000314a41107040c1800040a20030442020301c561502212010450f20682d68410100103800070040b06a055100ea600c0e400454000c11081440c000410803040007079110510036102c044002c00c1104a02c0f0050090320b600c524220020403000b540003002803a61503075100014441c51502003100da564907052849002004001d01320344003014281803102901c1c1101c102100000e1480022011080030b1805452802d00d1108120101142a27820310241e0317400628000c001c1d205520100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 978675872 1250 978674622 978674677
    0x30807030b12010905060109110301050d0614040b010302030d0905060f0a0c02102303090606060a021f1b0908030405011116290a0c0201030b2e141201030206 69
    0x882502da8207500008a5013281d040c0141000010b07040200c0f11741c1070500102c1014907140031f49054520884814062400d00d01c0e041008100700d00c50710402035502c10412040c007000003400c604990082e401e4420300d004004d0111880019405495400001402501d96a90301c2c03002802518240d410f2058000f4140d0700014146400180c401c000106542c01e001c1d5281090b503a54421008005200380c04c50820300c17201600c0b1500180458000c40380440c942110380d108000302c0003c100303041c0350351a0500244c950170011704240c41c1c0496006003a80141c5034110b100b0311241c0d003240d540388040c5041504107401103039800e4510001c4007d030703c41c001e000e8006604080d1014000d28004c400042c889d045c2d0960401103a0350201d07118420301090100300c81c1b698210f5040040c0540c2442c0c00504c80002030001400c0007401c401c130b0b107060440345482e00e2000c2401200c0094035859074484600040034004030b58518820414010a40c0160030010801400c041c00a0416640c03400001c80460071032400c0e8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 978677122 1250 978675872 978675889
    0x114180430081f05210c090c090108070512090705120f03040e1509070302121506030609071206090204170a05070314031c053907050309040c0f031512030807030b 71
    0x14810942c001040ca540f020760402c804054146c0c1503a2800321780c540070914803224045c81441505002c54500040c00b0b0910600c00c81e0324020000307043e0300607414021f810542e289182e000705400762010303007100760840c140051200c055110880041d8589814104070305204000a4190700746403c400c91000d15503030b10b9944003803081145a4006071583c4c0b03003104500da10034004c2c10b4140c0303240800c1502d2045499580c21243d08c4035003a140350701c031038a420904a4802d025000c1e190650f5150040100748490303a60004c204807030701c0074000010002e4904529860b0045514010304543c003c100800001d40310410401c000103411090340d090400301004009525903c46808001903074641c00c00c4040b1f003c400e405520324540c100a50f8404c0403032811740e011814808545204514082800410480c0030001c5502ca110042c0c0140401c4010f10790240062418045081c04642402c100f00701c0e51000d00700c210112505040a0f01c0b50407880d46090f00ca070500038206e00d041544400c4101003036255000b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 978678372 1250 978677122 978677149
    0x12010615020607020c2202090a030213090201180b071403090a030b0601200d0509060d09060204031a1b0a300c0503010503060114180430081f05 63
    0xa409140381c0154024107155030b5484143c4585050504a100e80603107286e03620303c0c02850b0388010fa441400e00001109102c00360700096111031112480070641105811811096200383c0754401c50706101c2c8021400f0444030301400030692002d00c480000305001e500b442c2c1d8181c030b03480f0607203240c01d00303680c04580a5051a0800d494000d40b5505026455038002e403842e905002d5010300901e15888221500c1e02c6807400944102080130201c0c40ea041e07035030340000701c9400c20340c080c00400c184900d40c40c196020350801c0c4010b813541030441402c2d07103030442c620311654400c01c000114000030f40404030414101c2d800c01c500846c100003c2a00d07502c0c03950102e11002d5a451001006646004034008000f004c2c2d408100d0b690b01000070a000401081e1000140641501c818100e0440002d00d580085200203440c0504213490340b034010140004e01c00300c1c0100d8a1404d400041c0100c4c0d000c0c42c11030095103c00650714880000300c0d6100040d150034071349034200710781200c400d51740b00000340c1c0c40c00002c1092001c0312 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 978679622 1250 978678372 978678377
    0x80a0f050d11030f010602030327070b0c0120070c03020409030e1206150a05090c030c07050d05041d0105060306010806131119030c0c0f05010609110c15100512010615 73
    0x10034408500e81390b5001600408151004614526028201c00245000e200100d03c07104010b10310500d4001083c00020007406102d030800e0b0300e5a028182040c0a45507007410b4030780612103040007490070303100d0741d0494001c60781040308084202e15683c2840010a40500180d00b0805500340030111a074a21448c00b40b8000c03103200030285418000e09114800041e001014807070081450200301c80d8540c04a19984020080030b0300380c90b503507500c1941e01540300d811001050b40c052204030185c019040070181054aa08800e01c641241200e00c403040080c4003070065070790014080c000903940d0b40c030880d10a81e005070094000408004020341d1a41514110759000001c48400719860f00034200b0001e0355010355a403440d0078055038048080c09048455101e0010f08003007400b85d0208144907094014100030520180304000168000442003511f070070007480c3d183c050203130480c808a04a002c4047c40d018900c8141045010351800003000350303012100030300724020754980e540012026038080250710003442d42d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 978680872 1250 978679622 978679627
    0x151c020d020702032e05180102070f0308092406030f1009061512020603040602090d0b010608072c04060b0d02091002060103121b022110020304080a0f050d11 69
    0x207104050402000d84445e510000c240c2511017516400043d4843d500d15060400050741d80350501c060a0003c586402e1452030b40c000500c103401c0000a0a4400c5424021f84c0e6000c0b5039150007013a503031030b4807424024050244004d041e40d80f2401041c4021900014010110b03606802d020f00c401c1c1c201200c00c6400341203150341d83d034050203210306401841210103221030300c00d84440c02d01e4ce00541e01c140c000b401900442002c4000350800141e42e0484003880070003002c4022030354039441c068403e10000d000d00350011311a80041030b9103502651000082100b10072480760310390540c0e41e403410700080c202c11240c2c2c403613140d040028542d400e0a005020402c01c0440159440c0842018001446095002401194403034070040000c00c5004820a03401121807030081401c42e215000d0096003000c100e400380d80601c4030354190141841c91007500e910350000c403043e10021401440840201c3c081258007800c62030040141c4600548280555040e0351302c5402c00781c2c1000c00c030300d4141d0b007264900f50b200740106400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 978682122 1250 978680872 978680887
    0x30804112e020d030902060301031e0f050c0f03151b040e090109140f12031b0c0f010e0d12021b190303060909210e10030203040b010b030402151c020d02 67
    0x1440507540c3c80e511802c05115802090303011900c0d44c4014840030b0240030710804054920703801c0d0400e00e500750350004800b045400582c20917a448881c0c0c1c1d003889101d144001594102400c001c6210b640c1c00c00d038891604100d170b49140e0710040019290321803d1440c1c030b04000104110314440034681c0100900c20000414480520380303074018400d03820007811580c0c00a070a2201d803100002c0d507083c0601c450a042600e90b00c40043c030101092090340700c6032a00c0001301c0c001d90916800510310a40d58000300090203618500494580c49819904200c3c1c000b4000390400d94119500703070010a05852001109041e0100000b41d690030704101d803003003103030035070741e8501000506034140248405415600000c0124440598604644005155603030803507542403407011100784c0c01207c3d08101080040d207401c01c020403041d0000d0003940122011140e44003810004102c0c8034a40b000d4a100f6540980400b0004140e00f06040d6540c20425481d4950315100500800ca900d0741e0000d0003140b0120f40c8c0145c3c44503131 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 978683372 1250 978682122 978682127
    0x90307021216060806280603091506080313150c03050912060924010b09040914010f0b031c08070c1e0c082118040207081210080a030804112e 62
    0xb8107141d42c00b10307804141221b403071000d5201c2c418211145410300141c17141e1b803440c00c40601120302da100029103141c031310005031030480071008103150020144049849600c510112200403211f501a00000c2d800543d0079001074002c4009010f5040c008140040c040402004941b42903421210302c1603580100303001a4064080301c2403030346519070303211403001158145810100c890141e030454510a54444c00c00d40c050100f114444042031032604004d20066040280440140c6600346a49009100d00c00101c1e15000c1c0f611640814050582c2d1003072019140d03503104407180e01c1c0540042c0c40c0900041512800801c501d06c0c04c4911500c55901301c02118500b900c7c49080081400300e6604003401006400222a640c804a41070744c220b006012904524040c04a0002e0003283c000911013400000d0b14086400c0701100c65218005c0b06006981c41c6803200d503072a450300301302c840040c0441d6010f8041343c000f44100644001da010042c062140034030304500c00500380003440001079030a072042071031318401c2503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 978684622 1250 978683372 978683389
    0x100302030d1b0b0c0c100510051516140a05060a18050a03080702031e22030312050c071505010305120a05120603070f08030c0d08090307021216060806 66
    0x2181400e00c1003000544104610000e41180d00003400d0315510000900321894013000d03215518540c1e0100e0f010101c00000c000c00401060351480e40a8040200020340c51414101080c1501c00350503c140c20f0010b400c10b04e18981d089000c04075001e0900c1c0310300b0b42d48130b2400c01c800d0402e10b000703c004190740d060440900044603030120606182c2d940542c00c05000c504001003d40c41b20383d1600d018005076940d0781c0e00320f0460180c6851400504000c3c0990441d6001502c0134294800154042c454150382003165135031441d04e1840014080303201095444400d68a030350180d588070146880082c42e006c0182d450348a80c510030500030701c52680e02d9006006100d4100711404035000d040010518080200c500a8094002c001300410a0142280021000e80f424426000106034050000700c0381621103d19685175081801c1b076910038030415841059141c80b84041c00c1c05110200003952030701e5020380902c030241d62246680411846004c500c19100c9035807001c4200103180300d940380242818440100b06000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 978685872 1250 978684622 978684643
    0x6060a140906100203091002100501090b130f0207062f030915090a0803010314010b010f0909020a18080a0302071406042607090203010e2401030b0f030610030203 71
    0x5580e09010003000d803034502450ba046039003281d122910000c60300080380b85110fa0081d90b5044640501503180040e00000c0c2c24800c508104018004d5a8861018204030b9401c1c0408941c4015400303410b02200802da80070721028440c06a0251411803280c841e041603c031200c2140701a007a11400f184540e25818103c0703c0302556400300140ba50030203103540359882e1406e80401009071198404104019810010300080942c403928240d100c0da941c0c01c021140b4414003940040d01d5083c0000610b42d5846007a4582c901845901c0312a205030400340e202009403c10705911043c041c84985100d42c500000407810001c00321180286101c6003503240084c1007111982c880021841418880000d503501e100c190b805803070b141e40c603503402011062082910314400c180800c096014684000c01c50a000da0000c5042e01c0b14001e041003a030b180c0300c01d151180505000503062140389681941440c1d0310070b030005a0424402052401100c660400080c208002510000d0a10320002c10403c21418140410101c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 978687122 1250 978685872 978685889
    0x71e1d010815010530090706030c02070b0715090c1d010b0306100c060509030307030e0d02121c02130503150f0106050d0905030a1808030c031206030a05030c06060a 72
    0xe42001c540750048604085011030610002056809442c1c0002926006085c902088510b0380c050604240003034000c151880b03150780c040c0340e030b020560b28040c1c01180d02105c20b5074010012070f0315113020701e00030b50880201240d40201c20741d82000e900b01640216400b40d4040c00c100300b080d5141008090245246404204403500c2c4100100311010060080da5032041c002d94503c490300040e000200c0d482403050b880105550f2501090241c000400405184100000d0310108629210340424903592140d58070300c040160700240c2c16400429050740600481000c044581007281d00924140d416a0801c107034180020b10350035810480b52030100b0206030121901400903906003400d2009600901e81401a01c081c0704d40000c0b0300015032050b5005510300c80d00102942e13210045010020000290152911420140c00c42c010820010100441d46526075085c02035141614800e500300c1e00400c0246415810302a899513400440d4007400105100300c8150060202c6251100801000040ca900030146 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 978688372 1250 978687122 978687137
    0x70b191b09150311090d140307030c0c060806130b3c040903050f1e1603030606030219140702040c02030d05070302040b09062b090209060f01090e071e1d01 68
    0x70303612000c4103d03000315405a5a1010541b5582408100448041c0005509200c0040e210040c03542c0b003111040b0f1644a80c1840182607600c220850742e00e1707403e0f0b5981c1c3d4405034003030603640000a00c0d0b100c0150441c0c0036003030b1900300d22891080c2d0180340107450162070240c1540e01c40b01d0b201c49809581d03200c5807003c07901004084071a440081441c0145d4085404040700050503100c010b100d1507540344840020840555215040f04041c00540320704101100428100310010901600a0081c2c40d130b020a0040c0800d0070469481c000c550b82ca003070b1140004500c00820080001d03880741c0c0180815040540c00440d69201c403112070741d084640040c100f102f094030622085c464640381a003118400c030b0007214a551181628012446811075000c8070043d0300700061290010000355070010440f041c000c0b21420b0703a0703554200038424101c0c0f10180d41030000d040c4903403d0140d010310240481d0008034919000720070f030181e604030100c40c0741480045000710300c040c1e10b4517070880d01e036810009040000703282052 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 978689622 1250 978688372 978688391
    0x5030d02161a09060a121e0e060f19110f0301060f090303052a010c0e01021615050c1504061e0c02060703050c070c032303070b191b091503 61
    0x280341c090f002074240714041c0003486144483c480c1e2001c0c00051a140341c10050b4481c0903280d003a00251060b038080449040a41040c80c0c0c14010410742d01c5100440d0110202c1da460b04403480e03140c3d14a4003591b45c01e595400340484141550000b80c000c0b0311219110300d640c0c0d4100741d4058025a40c03d51890308010782c00c041130000a5012060318042c2264043c82c0890300407003403400f01c0c2d1b0201e802009100703600c3d103050341201541c00080c4040500302a001d880b1041200e4a01304034a08081c0251807000c2c5002a5858865128900070311a80c010036007a034a21a00d80c40e401205041e080c1d0302500c1c1140c490351002c59108041c0f443c107007105045102000941c84c0310034041e40350783c0003c1519051680e1407001039a03104440c2c0441d086160b101032400e003095202c0c41c2142c031117500c107044034807000003402100e0410140003084408594200c2c07050306499440048000340e4203c1120040f148540b02c5441180a10302007100541c8400c26840324444107060000494043c54110f044500701400e015151 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 978690872 1250 978689622 978689669
    0xa02030a03020a1b1a0112020a14191403073002060904060b1210030302191e031706030601060c0b0402121606121b0507060605030d0216 60
    0x46002400398200541c5034020694142c0d2481c8081ca201d0702c100890482c1403080284400da00038610501441d000e40316600e6452405090034004802508107041102c1440b64612007a403c08016400402c9802040704074414a80283d280341c0c000384802c1d80800c0e108c00d1500d0240540000b5001d0220003141224601584c3c00403020019203803507000120003005d505544030207045400ca10009001880511354400540c10030f036101c005811102d03491240483c54034460741c4103420032039400d07038000c0c666080c90003001c1d2560311554070704031400d50301d615040d151280c42030344e4203005034001c1c1c89070356007120481884403105100506031441f07500302400600c41c8a03048080c6031940741c3c00080800032543c480c80414142ca001c3d649080c442d03c610010203407a51080e4640344191500b650300d618a8403e100185004d95150302c4844801da030901c3c000c0025548958040d18205004440100e00c03240c1d10408070342802e09041038a40160408900101c42c5074110710b4503002041c41e05054441c0c120b00e6000b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 978692122 1250 978690872 978690877
    0x301020313080d0f0c090305300307051c0f0b190b0c0124030510020a090e06031e07060e06040f0b0304140f070e07020f0c040f060905010b090301110a0203 68
    0x180000b401003005070004445a002402d403c042000030000c821030302901030301c0d079070840c801100c0034030403005104000300000c10101420320040151859004a075240400d103500300510b69070402400340400f01440200369200c402c000003050b00011070031007185100084d2004100c50034052017011181202d9004503403008800c0f500d1010b801503d4404d1030f5501d6000d0041d005615804003c140342d21119a01000c0c0c012013280d208a0072204a80034040c4560203038020310003110080b030103840c010044010b044040560082d801000c5e541e60740c6802c98180c2c040c2142413030f05000b075444803005001040c0c010011411440323040f40c0e007905040c945559140d4490090003050a141c002001003000c02104620800220010101343d800b01c2141e00105c0e03030b803102644524441c840f2a080401e4110f0700100d0030460300030410001d44802c004100a0001a0080e4450318009607911070780051800d03958402e080c080e02d240c1c0c1c1d03c0c0b50303a524090105400e40d8050680d000c5050020020030211a400008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 978693372 1250 978692122 978692161
    0x30a1a0f060a120204030809040506030d020c090c40030f022106180d0e090f06060415090503010c020606030331030302030a03060618120c24080603010203 68
    0x5010ba50340e10100000ca0b1224000407402100b02d002150100412848030090440c03518241c6003000b441d607132001015603480c6c945840c8005038102000080c0182410552154030110280e49146080340c3c180141102459829029400800300300304031f1291714681845100c84081a0b078180300d06425500c6000c01c10964500003403041780507100e40c040b12554014170402c100115420354005183c529042c0d020300040b240242c2142c06820070940907030303000300180e80e2540b5024104e086a82d80d115066449610301606090b44038009000000d40c0c510450350326102c0c2400350b07880d40c030b140c0d20f00410305003502d84480760402590050020400a0345002059802e690b40c40300791601158900c0c44030030740c00b203101a100c04001c81c00e040080207150300007004281411455074100301c02d0b507440401700d600608107910400d140d00d03994010080d10040f910710782901d03400f40008502e016a42c45010b807110090000e200c2540007200e440d04051604000c00c075600c59070543c001e514520300154401d86200c0d2111 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 978694622 1250 978693372 978693379
    0x5070e0a0605221d010e1e0a0f0912021b040515130b10030501051806060f090102071205150a020f16060e0a0b06360403170103030302030a1a0f 63
    0xb56590311149618088200401d00401c1440c04c030441d0a4555816510034011003520101c10000705000b00507801081c00c28210b00d0900c0b0841d82c80300c810700b5000d4003280700080e00da03e49034035248012640072003009103901080e4009000c114000c00c61410203070f41c0000c0307182c41a880c3c081002a81004800009101c0c00d08079a62000111540080b00c02410f0a11140e038114514001580841e50103500c802e042e02c2d411100c2403402889080b2840c1d1038071045a002d60000414002c6023803990448000d0308541c401401500c22460b100d00f5001560501c40c902524503500c185140c821010601181c143c004032050020761400464444112480c0b043c41c456074194804100d40b0828080180e0080030781a43c840f01f80c41401d40681000d01d501503055030030902c1000c40d90034101c1c4046204410040352107a001c61001103000794090040300307480081060b000c1c025503c0d0b40402058001107118041d5100e62030041c0c80782070204030541242d01c902e9050310a1035006c449072605a645958012044008a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 978695872 1250 978694622 978694657
    0x60801060609060e0d14150f0a0b1c020f01051e0304060506030d020c10120c020c011107030203060103060902061c151a090d05010b030d0201020712020d08310605070e0a0605 76
    0x1249140c0607141c07160400c106040d10608c080d506074051000d000b00caa03480203104a0b0181020041c440d64402003815208084803201801420190801072074400141072207400d0100a0380500000030310091070b958407007800030030001085900c1c42115044441034008040e8071000f0030f406507880075090009403040d0071985294682500c2420007034200207401105000305000e1250103941c0b031310044490b50110b003000c116400c8010b400a0140210b0760024002d012903403079500c8030b900500000c20241d070018402c1180c6095180307056031011303560310351050005100520540d80f4225a080e030300120103211001c56038500710000b540c2500d8042030111a1703251441d072580703482d90040c03070003035101c54050241720320602180d80c0660103440d490b0f019200e00101039240485c203e071603c200c03012903808654000b006c215400c0c2d160a0050250407001c10b0600e03e00030705c040c520020000342504448036602c3e981004442507211070700e900a04410360b1150340881c00c103000500381e03010300b800315400403225 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 978697122 1250 978695872 978695903
    0x100902160c0603110f0325031a030d05091c02040606020610050402090d02130929390f0d02042903070320070309080d0c08070803041104060801060609060e0d 69
    0x5030f04402d02d909a0802c0302c1c450161600901030080c1c01f29800607138402e030040c0704271180e500300403c0c8200c40d0881c1b0383c0c80301d2821854004114007100e90390744903c440c0706103103050001a140d520401002e8034980d0000d112529000382c418110010641120b8040c9005000640c82512503400080340345904981c2c040900b98000f403244018614001b001c0d06288454000e24504500c00140d003a0340004807410038455038803490500744c1540020010302071b491030500581010740c80100e21001d07280216041514000d0702c03c5000c062500064604400c0c01d90010b07040104071600184009036565000c07640a9120459420609600000700710740189610307081154407180f01443c81c502c4c003074065108540c40e8580c6050003130400c400c0f40103003074043c820a65205480da005000440381c55034040800e61a0503c0d5a941e20969080500b0840e982612040c403150030f80c4d1a0f000700b8010b0200c540000560034601040141058582d602481c10301c0075150717040e0140e488003455845115048408900103a02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 978698372 1250 978697122 978697141
    0x30507050433060e09090601060c150f050a181a09031303081213050a06090602120a1e09110d020609030307050f07061115100902160c0603110f03 64
    0x7032201c2010700321038a950b60180844822020354140c82050f96002003911146090001c50305083e16580106d1344448010040381e80b049803e4245a446410041910794000c05410181d4030004070941c08191600204241200c4034410200212003e04010a0030070740f5803554503102c1b410f110031102c1140b0150003c0c903402410030403580c5507420081d12104841e96814694066000100014506a01940421105007000f003c099a035030b04800584514207659899130000d00107124211121a02408800e151514601070f070b0b8032820408502082c0900240c0100001000213000303140c81614200400000c00c3d4000794004443c4070540706140519128000510503006001c0d220341d15100004501c03003040804074141420203051021145240d4854805548010b040c20108900b503122030303000034401142e0441c2d076820000e035407101b00100e5196240d004c103a90044a010040c540841c07080c200704043c0101701c400901152404000303c0b040054524618883d04a00189540010011030b03e03484 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 978699622 1250 978698372 978698411
    0x1090b0a051b010209060d02180a030f03030507080c1818101a0a0c0f060608060115090f06170a0b061204260901032708040e100305070504 61
    0x2028404192100c99044005060741d000003070803010755240c800c6589002d4014000d031206003c4c010001c508081e101c3c540c010080d0090700e100e15540410301044040c5031100c5504501450040741d416100c0145410003405403180500010100040c07041088800e00406080c6c80c03403482c0025489602480301000a120590185a280d400d0000613041c0040e20b00f2458102c1c0407101d00883c3c0b80d5070403900b1903120034640a04001c200103d161412031200003009500c115503400c0c400d9400045540e1922070380341c5041000d0300110300900b035100a08000c41c0c0c210202d64010681048901180c3d070034400010050b10303400c4a000240c0200002003021001039800c1150a1800070f008192070b500001ca16242c102c00c162000d03140c000300740c1c090180121241000c904407080209141c0d10b01201100110000c0c9140000a1400d0b102030141d282000d078a0744c074540a107402141c07269112814004500401c01c00502001c011a60300001040002d0011901c18110b5808450007d122118a40543e1080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 978700872 1250 978699622 978699629
    0xa030e06210901020702030709020a0804171201060210061406090d1505160f0201180b0c04080303130b0106052d250c1d0a0507200f0c06270109 63
    0x4041c10085611030542c0640035080c000c5080390882680c48003140200d00c0343e615440700203048413001401084a1214541100d103007180c0482c9080100d0300c440c540c260007a003101006810805201030f628403540200b40103000c1003040720300680c003031000250b854400c031125140600ca20038000c00602c081880c42c2035600c201034000b440146404511000041c07914600700740420f140d141a9550340e0300c14490211107200105005106000a8480c001503d50041031025183c1d0104070201c7e51000a002039030145031401c6526800303c481746810101020140c02c650704100003400580030701c80103071082c0d1541c00d00d20642c011991b1000c07c61607050744a1040340341602101d00390381400c2c0940441c0403410381130148a0340c3c5030300360300c83c0c10508144c5808070880540308a5880403541241701688170680014071401c1203003a005404203920824050003007604400c1d00541d80d01400f0510034880303410031030320441e0310301d2a10018605880304540e0102400400381c0f61401180e9890f4019102840034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 978702122 1250 978700872 978700927
    0x180606090a0b0304050115060c030c021201090c090b0d02010518031e03130602011107080d090b0f090601150504060c051f0b04060b0705031905091e120a030e06 70
    0x40c0c0b035180005040d8010340701140c4962a05031501480c1c00361a03200b01c01d44105aa4200700300200e44c800710303980c0b2254007041e40e218540266611002409206004030305100e041034503841c0d40f03084407003003c0792922620140034030311840b140c500507a8041c0444000a001c2c2088260080c0e000000c01e140071801c1042c0c4580744030080004801c010004003800030300074502410200c9a0f102e2000302d0130394a11042c488034001c414440324000421000c00b4000c5400807a0000400442684641007015003d60301c89144a044206000341808240b01c0c50340034083d0840b0036894140315250060840c0304511403c82080702490341001044401d0003a10701d03441c501d810300d407042600031001400504a0110442c4103500d001030004200c02048140c644042c0c200010f581008180d010070746a4103810900e540401c4820400c94800e59260341260b400d92004801500c01e00c035068041c080c6105071007140703248540c0800c50300800a41d01c40c15860440381d0030b441c00f503210700b24ac0e007120408a401e4405201c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 978703372 1250 978702122 978702139
    0x302071719030824130c050c01110c160608180102070b160f11070918051506011b0c05010f021504050606031c0e04020a110318130b18060609 62
    0x1d06a202d900345002d080c00d134840c040104071050308108000c500b074803016013211700301440800d003902951080343c030f400300c40c1071403890070160340003042c21213815100482243c500401ca6080d41401040302e05a4031171102c1c1081c51003404c150014119050062100105070000d0180120542e400c0d010340d15130a5100030202c60b00d003040d4100d0103013200d10720307100c40004080861607115103226212502e21407d23070f24054001981005141c40143c0354808078110316160400e001d200103034040014a20b48043c4903501d8000c0d0a0081c001000c4072080fa00e407030044140c031808140883c0c0d021040d80d003181e1003420b14030510908003206a04000c00940c3c201000514241000180040828171a103e6841101618001811012641c030710103001c40180c0005916002c0d0521181001e90060400207428200b450300203102d001c40514650000d0701030011002d0b240b002080c1c9051602038142c9031405403070b0610982810902151502c0010142068110140004a8400c0d201d0f14202e030b1504002801c5c900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 978704622 1250 978703372 978703423
    0x5060d0e0109110301050a061d06012105101202011b060b150712031b23040b0c3013030602070c0611010212010b0c070b03010f031b0303020717 63
    0x400d007480303210f4902d00039420710001070001c2480303102c2c280955039014015000700b03410f000d0580d5000030081403541480407500c1d002c2070841030860700185070242c031403001c9407504c1d14511005c6205025805031054080080c1d4440040c0c0c0c005100c10100820318134621b000205030b040040240417042141c640050352241d880d405225039500800c4080d024102c00010415203107811000c0b61080501e0032400c0c58410403401c2140c0c403c80002c1000c12408000d6681801c503048000704690107a03101500b030010001d050040c0400a01c90000c2010303252061082d6440081000503250b00395282024070780c4000039680c7c4240340c0300503c200107590008000c64990600e860180f04100c1540607460202c2c1c501403d1202d211814000c581d20b80c507007030001c440580d01c1c02030a00440e4200036510b1040d4068500c000c1416030780071014500908041c1071814105185003800c4540384013a80400c010010760450038404650002003e404032011500300d140c0350341400e000c2d5801c0010440b030007890902886141c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 978705872 1250 978704622 978704633
    0x12020a0b18101d0d030519030e120c0d020d0504090c050706150501080a2c0a200f03070321090f060203031e0610051317031210080705060d0e0109 64
    0x101c0c540000c802c090b2814010f1032040100c0403a04070802000260f003045115038480c2d110102e07407041d03801810040f4204880205443c181a210800a6a60074001c00e0007402c1c04020814a6541426030000e48038005441e0f00092903441079004109083e515040704004080c030031403c0f100ba06c3d82003075013084141509445285110064414170740011244004528500d089118076031044907605a654003131000c1282146481c071200c040844903010713050020010036480946002200e14034554400c244080104015582210301c0b4600d009500810040c0002054140c040440040c4600340c406044c18420041b03030b000495800070b41c910015128006203450300000a1402a4003007044452520081c41c001440041c2c122500e41c1d0100e6581c14865400d4000c100500e0360442040100402c96141c482c812039030030701184c060000340c1c4001420500111845242c94121069149200c3d50618040009549400602136135105080004a00e0f02020f015480740201105d420002d0204203080e0600e0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 978707122 1250 978705872 978705887
    0x50625050a1d0a0e0a020c07320604050910030507080c030304170a020d120905180f040204060b0a0c1101033c24060503010f0e0c040e0f04050712020a0b1810 69
    0x2500018851018045030441c80380c44143c01d41c2d09a42c103c2a10340c01900316011000c00c9032781205400040c00c1001240726100c003445584680d000c10f101c118079901e586041b51070854240e002224070b410000840003c0d5a0120840c1c045600c0f07240b403440c1141444200130b04101603144000d41c060711b28910041000050282c01c080c01205449502032a541d403030610020056035548d074010440342c0300026807208038044000390005e00240c0005840d03174a0b0300b40a03001c1c2d8480c1c41c2513404111005601e008014052180660b59007080c41c0600220900010030801c52083c01001c01c00c1c04001c95107013082100880d905840c2d40c103228018807920050b22003080d00d00324010951007060a4844010a025000f103040701d048880700100140142c1c5414000110700b0405808442a14010040095101c50501300b00d8011090700200d041182883d103055071400f500c13a448890307038280c034108010140e80e656142c4009c0f03c24a0340083c2c3c4d10041d04005080032030402910550001c4034120206141e40e10145 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 978708372 1250 978707122 978707137
    0x30b13090212030c071d06010807270b040e01090902030d050a020a0c1202030606030a080f0f0409020d06170604080f0a0513060806030f03030114040216050625050a1d0a0e0a02 77
    0xe001101403100c5107407606c20345040f1084c0e4042007140c4080b60466102d02c0302c101d8651040c1c0e0002c03c904d00f902c241c02c105d030304482e13000c500c9401d0301140910442d04504107242c010440310104004a015682c0800d40703070904030040000303001c1d021843c005c50500900c2000540d0b5800140001d031546c441d40c1030520002e40b8035040e0700900c100c0c40041e10606001840000c0326420000440c148180c603d03044640341d0041c4090900154180000600c550386400a070074910f4141c8401f00d441401c0c0609910710095070b110074030300b5902c51014440461414003c664410210f03625240d600c1d80e1045040c3c130346110b15a00000206e0540d98001541a81f0075103042c01034100300c1c10343e02c0386a20350303e4141c1d82e0f01007030196031041c1854001400962400f40d004080fa542904188203507441c10351141400c240044501c3ca1a10400500d01c0d0300c0101c80703200e0003e440d595410042e0403c0310f404d40c010100071055000c05034103107a40416440d983d481d422080014207055030021241e1800f0101c0d81c01a421509 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 978709622 1250 978708372 978708389
    0x15090212042003060f06060904060906060311040e04080a030b030f07030b060402180d2609030c01080f070806150403050102091309020d060f110301090912030b13090212030c07 77
    0x2801d05042d024010b2890280c100003d0040030300781c0358036030001451000501080d50081d0104800182c60f01c441c040d0030010030145000050703e47c03402c90003074140e90100000383c0040b20308100134099110300d400c40e00e8016400c00d5006481c2c03c0402c40950080c0801c802e1141e0520500044642602000607a10141c9204402d1001e25888bd00240320036401004405100081b0113a54040341c1d042c500074020065000b00801d07038414a030111205502c0e1044070000030362100004403410710741410801c0ac80d50150a107810119440c10603102c0046480140040c1c1c00c110020010845a5840007101c0141c80007600415654569a240090003584004140c5020305015a0341c08071018140c451903b1241d006001c0c00c0600700d4640e42c00c00203040244035030441d66a54041070070042c10b08005036000c2c11030168001103031170f00d90500222610100c3d0710360040500303241981a160b25280c2030100100b01210012a21441e944001222078990703d03804101c910000c1543d254a08000480904403080e14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 978710872 1250 978709622 978709643
    0x604020f070f030f090f030f0f0206120103030206100605030f07111c0905030309061c0f1509050907180b0a0b0325021c0c050a02090103080c01111306031509021204 72
    0x4130070307100c410f150b00c6105070480c4580003c00c0030846104107620500e22400c04104c0d029100d82c000b036400d030007203c0e40a941c6142100144100754040150300e401410919804030305a04d803940c014502d02c0014069100000c0f09000b080429000d0070000310501140d03402c0e10340c0c0c12441e401e80c0c2c00201080d01080e0024917180c10004d014100413007201c0f00258082e100e9443c220300382c03054100394500c40c17441c980603942d1100040703030000c0e03180b25140804007484e204000743e0303281089290540340d000d0080f03400b60700401410031840d131460074a1040084000000708100b81208001400031842c4e9004c4c0800301000420031030708410844a4444032000b405420640342440d5004a07034422051502c0310844c2e822881810b1002d002d209030310012440b074402c4402ca04229400308180480a0f40b080b01c2e80c50700861100f036120028025200031110743c03400a0b08281010044599003440d0b4843e0109043e034428841d403c5446002500c0007400e015807095540d80084058107c1400c0c0031a81551000d0300d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 978712122 1250 978710872 978710897
    0x150c0f08130609050312070c080d0507303c110f07140d23012d0c05090901150e0409020603061504170609010b060405060d050604020f070f03 62
    0x410003d4140c3e480940240044810010300c0d90f4581e00c00d03e41510b495041410000d20407000700a0200007294581c0c81e16101d076903e2401d01c0310b6000303902c10603100904000c000302e01c0e401019a189007940e450325000c181401302c60940309019244020a99000b0a0842585c16a0382c00300c0c646a441030103642c400501c080f80055142e21000c0407031420320300d50003a24042161f1211043c4440c40300d40e00420482550815958107940c0b0307820a134030842100c4c2800d01d40109468203100d6200e4040700214030004881e1451614a540d41b16101288425540c640d011800c0501c244260388802c04007510301e0700656114041c51441c01c802d1400c4000241090801d100c0b281440d0083c0c0d200709030b02a200604640312032041001282620b80400812101404009600810f4800009000300c0700700c0607000c00e041c0070b0601802d40e0b0301c0c01e540c280181e404000c200126202c80e411680100c55000000545c1d84070500058040d2140c1b5650b00d1000c1c0c4041040402e00400fa41d401385c40b14030a403a01c034030302d201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 978713372 1250 978712122 978712127
    0xd031407050703050d0e100f0c031b230d090305070615051c06201201050d080304031107081204080d03050907090e10050a09140a0507150c0f081306 65
    0x5002d0004000400a1142c0c1154244c16085004091402c0c07080c0c03404c58000c000750108407081c2c110401030840d10b6101c010071858061080c00e0f01485840001d911800a82c21301506104010102000c02c0722004004c0b803100b2007607400e0300c0f41d84105210070b0103400c003a400c0041040d004205c044e0303001440c1407201001500624450812a10302503c070021003078901c240da50002138140419100292140e00040400e01e042d040c11841c070154115098450b8904020054101c0c0f05030400350103600840380100100340a6010b681d0310503410b16044210311040d94006080031240d134041d8800e40304182c00610941100005001520034950807517003201c107242030450540300d00b5154126140c01450081c03001d08103581061130444103035011510390b24807110a010403601d045400400301d035506c1051800b001842d05c0d0450010b11007a00030600040f00b5210f031520750071f152003500103e9000707100c0703080154050001d003002e56400131800501100182400d0409174002c82c1c55094092420341c0107e403007030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 978714622 1250 978713372 978713377
    0x3030603060a02040501080411010234080606090c090a08100c0f0c02090106182c010609230a08010507030f0506150316021f060303020105060d0206030403031a030d03140705 76
    0xc01c16550b50440340c856072108400005502d103914114018031080c142c2c05a400d0f142e40710170307000303840500f1003420ce4aa6208003162042d00f10a0031500b029051106a030341e548a41a00105420245c0399070f09889000904030b9a150303403040c2c55030300a81c0040b0f019054030f903200031062210345d12143d40c0074244d100116009028100004c0d488064140180f1074984165100403c00d4120b001030481c140d1900300b0f110300708148140400881144d07810001c0307003d00c4500c400b17005007400d0411a4a49080c40c4030190000b01c089948500d10518041e2142c49a407210300e46801031003050001c1150781801c00d00200a0001c207030480000c1810304000c40daa0781817480207000c500d0402d0b4142401e607125003109006030346131158030900718070600081305e410b981c14940304039000c80da298001801341d04e10300d0042c1c25500700403d120320650346c1c0c4c419034000da11a141180c1e8055410310307001a021010341c1854400d00000411507405225150341310b1902d80c1c160303001c400b107241000c62450250760b03010021a12403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 978715872 1250 978714622 978714629
    0x30912030c14070f0f050315010605071103160e040b06092403010b031617120f0c011508030a0212130e1506030403031a1f0f09030b0903030603060a0204 67
    0x180380a0050300400ca002c001e20702c410100d641640d903100d0b558040100707050701a412484d07400030f00c4807041065240411812040601000122840303615000d8050518026840080d000b81c3c072001804059690910225160712410442e80c016541ca0b032030908900c1c40c040f54100e03400054200400d4851400f4180075104800504030340400e014407150354440129031411441d09076403035048072685a84c05008440034810015404001c1510300214200d000320050b031001003640100d24080f9070b07400c0030400c0314041200825820ba03241103034500c40d4010030349031800d034001c0800140c000c11001c0000c4000d00e4064955806c803145000c1d24200c240c0c0f2845a502c4400c10045101c0d8104100117414910300e03840198004c100c3c15803980030010501c5a40201c5003100025a910010781c80c0031400b41d1002c0842c20180c0750724000504aa4440c0c811140c1b5049040130310824001c1039550502c2010b2840c080c40d40051180128200340d010365035260826a10b080c402d000e864001502e02e0b5442c8241c40c01ca = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 978717122 1250 978715872 978715877
    0x7050613030f03110a030e1614090a0515010819060303090f050f13050c2b05280e010213030f06140405031204030c02120c0310020c120d0617070303091203 68
    0x1845c09002044d0700910351032040c241e50f400b5003e4165a5a0100c0011000406190103060418014101000b4046400500000c2051314150512444600300c0720044082803003800c1c44000c50b1a240000b0480d0140c111002c445507041200100c100b50b0f001000000f1100422031401d0101d440300100b01102180d281c00c00d42185030705104c0480071500fa000f0540103d0440310300e61034824800c800900c1916841141c044100c1c0150500b50414101d1196a500943d0500c0d001e43e1141020001503403c1030a651083c0c030940c4030741003030140d0300742075046568a18040b10f080700410b41da8605050f214601810503200e642c50074440311080c0303c40424152145501c03001962070101003542c1001d141e400680150704101020381041d0040e2107550600c803140da5023800034207004070950201481c0c04150481000c0e15801030240102178a00001c505401c2080d19200c983c6980300c1011410080c0b070b9560184801d5079030b050000b100030300c000c02e151080d01d000b80d0f20814180e844140c0b04ca0100584a0000c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 978718372 1250 978717122 978717127
    0xe092508030913020405102f0c010c1b1d0a1107030c15060e1005041104030201030905030d1b0e03190305070c0f1815081507020307050613030f0311 65
    0x1991810b098080c10f90920140014103040e100c001003248640da42ca15000816000d403081503003400c010f0713070070b21360301d420b90b00540e4079402d040c0c1020351114640c801240c140310100070900b00f0060324440303412080c030a807881c094040d90303100741c0d10a11002003000c40d1181c0405030049108882d0380c2c010980c0d0044041c4581d45042401e80e021510000b19080907552220b294900f290000c0e445c0c002d0f54020100b8486840f224204100d0360b810300801940003601c5103141c02c000b2080c034040b40040e10304407a0242800034444072181031150071481181d40401e9410b14264008850ba00c03070760642c90720300d030a41d52100c5c40c1c3c0d9414020b0507603882c00c00c6101c1d00200603013405500042c3c0b00b2802442600c0c0301e9108612400e9607920443d9403040189c000a5903000702035907420184e003440c41104d180b12210040074501c0392501389116155201145c05c44034070503200c0c00151455000708210345400741c0c458216034051500d5108181c051240c0c0e202100060582e20051708014400d004d2901700720201c1c2902403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 978719622 1250 978718372 978718387
    0x2220303080712140c04170d09050f180f071b02010909050a0e0f010614060f04090903110303010f150f02060106050901020a0602030a051b04080601050f04060e09250803 74
    0x5440100f0350364800d00250f01e03250511402c10b0000200c2d4000c070152440b5a888030708041507003030040390100c014500740d84441d000384200c2d5400801c410071140305070f960780c41094818001ca81c9164144052005a01c0c0800501c903001640301191485042c07150b6480760080c40011401d201e880c2c004102038006909000c003407061055503849076400440c2031100181501117085600c2c2843d100c1916151b40342d6686d00c080045085854000050480403110a440c2140d00c3c940400c1e580910302580000f5a80c03079030940308150003000700791010790f00601100c0e180e43c0d6980300d60b81c1513610b90040d8020510500c000c525040d0007600041d40401158000d00100d07070828008a8194200342000c83c1107106500b070740703404a003551000794010220442c004c6500d00e46000c170310b9900c100360001c070742001d070b410407080118036004107086064450803034940b440d00085c4d0b40050007603d210f420102000b801541030101d000c2d40001c80020412980c40c2c468503049421409102409080c802d0303881c41d41041001d43d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 978720872 1250 978719622 978719627
    0x25a0607050f190e0d0c03030206010b0f04030809030312190b0d08090d0206090d0b01050f0f22110a050c010b0f0d0b0a060f0602100b041e0504020f040c03022203030807 74
    0x3100c21565440c1c1100c03c46180e02c00030705c105281c1d01302560458148001401031543c1400b0980c090400e03e090285050540c2d0204d00d410322035884003a101540200717012076a50340500c02c480b40162603000710700407400c11180b40c00658940720110b03610603160040b0700120741801c0a920707602d01d0308107000a00308040c46041c81a50f00c085041240d10060401000da034554800350b01004031401104074400540c10700c401c0c400000c0121540074400c40e0b214000c484266140d020a4000e0075032a030003800030388040c6440f02c0242070900140b03501c0c0c0314042a00007003c3e038408003500750942c3c803000a000c840400000d0054006406020a82202d000218000459202c1002c0750700b01420488c0040c2d401d0f9190040751108030241c002c0c100503007201040d0014000207000b602c0546400312420001000c201d000b144030703034140081030447e01740c64100140035903036010304c102182d000162090000318a0000020025800995103940d1600d1501d150341011041e00d1006042d0f95140c0c4030242940c403581d405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 978722122 1250 978720872 978720907
    0x2a130216021507063e070609080c0c04090b0711100504050616030c0207061b0203010e0d12020301120318030f0503040e07025a0607050f 60
    0x40361a0300164211006072200b9100031540440c505210f512808280703807a40c16107039134070150143c07220082d05030300900280c3c0b000301c070800c0f460b49001108218010003150850003201d00240c262890403851400f48440305001700701d00561582950704000001003044100c40848402402a40c02000000c0c00301d801042c403083c002c0d005400b150a44060891200c1c10384d0011a070850392508030b001801710f141c410807403801107901d0b182014416814142802550707141d50f40320b44000c214500a540802d00c540c80b541c4088250041e000340604002d00d841e45541c3c4906528840c0028880b500e103080e00e003003520903641612140103401c6020321558608031485500e10a81902c0c090068070b0000003d030761400c4c082d12a40c032400195854602c0d2500030151050020f1091040d50041c0b20800004600d04c0d6414801540c00b00841c00d100101d000c00004072500500d0000821108080301800c070700b006058100c24410920881c0d5956561f40e408880f81d00426030000750310700d4240511a07411150345e48 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 978723372 1250 978722122 978722137
    0x2503210510050f0a03140d080c0f0a081b13081c09090f020c060901091203050105100f090b180a0605040602060a20040b120a050714070516082a1302 65
    0x444c8040c80d200d45a100c1314011841c41d242941d84601c4288110381d0b0080e241035801a64098518285a03900b8101e52040c403965401c0c1c02046043e200240604c911008110801105040d0054583c070900900024069150064501c0d80c490f50130360b1030441c410f0012641c49400c4030355402e1506072030304030ba0101900c1c0041030010f800b0307028422421640020052244903a182e14008260301e011340c24174500d001e10f984541002c040c10940148001c0c0c540da44030000401d010f1506c480d007880d000104442520581e0099100600c000551442c0c00d00014007119091354200d483e08565995071000741c840d4850f03031081d1001f5801c6000000c6101003940d1159410b100c60240714034210302c1c0c101229000780c0c4290004000c8800105402030440740e01204c04d6440511000104041d007080c481c0540320380322012030081c1c2ca05000500004000e0107003c1c41040000940d00d0134440e5480e8262962036090124407081010320071150720b00355500001c0800342000c0c0203004d526141c411004044040d6001d1003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 978724622 1250 978723372 978723379
    0x30714030c030307030f030b0603160e010c150606090806151011100618050903160203010e0d020604051b01080a0c03090f150b04110901052503210510050f 68
    0x101c00c0285601c0900041070030505c2aa640c1c60b950b91002005412117580401185c0200401d10800000e0720f01b4020b1030b2500f4441d800c102540800d1040122541c05010100800400f0800202d4400c44440d40016040e20b2064441d03030421500c40b100c5036035549040302c0410034200a0002c0185504222103083c402c180130745081d803203030001001c806241100c80e07180011607a03910401004910407070000b2001242c02c046041c4498104041200da0b03a00440003100109a030303d114a80856400354403010020f149801030b0390b00580500760107034031480111001d440d0381c042c442400c0c00388140004860f0402c00c0507101c4c0c4a950b110141c0b10002042c8844806080c5941c52003100c001c03c0d20703030a08403201c0d441000d182c1c802195078200034040d55005402e51340200d003003040712079402c0622020f6840c0c0328400e2801c00d4560307481c4001c1400400b0286a00710300d5803900c401d03c0e000e141d03015554800b116014520501000d181030214005c599040b506407452444014003440f081c6041e40b02000c001c503004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 978725872 1250 978724622 978724633
    0x4120c0f08181c241404060204050f09040c0e0a1d0c030d03060605091e180601031b121a030d05180604030201051c0612051b060903071403 61
    0x2541c40036403590025890030302d90000304500000c103140c042e00307030040c1c890b02e103140406000143c0e813450070440100c001030790ba407081003080302c2482401d40e2145040d099030440300390281c1050700780b11000b5072060103141d010799002090401c290500942c0180960b40c80f140c0c3e10350152171b080d0a08a081400751070460070703a846900100540c562081c40044400c81c1d20080c10a01000e1070826140c100c02c501d0300e0080c5428035000300907441c3c001c0d0540d4803101c820340788042a420440c010041c0d440c0c50303040441d03014203207044030000d02c100c1c1d44c4018441d020a072030822040118038500e184000440b403c039000243e00d980e61203010b454a400602008000c1000e0169042c0382d00c000034146811440b6a00000344d0103d0781860074070710134440042c200e10130f40c2d001c0d14250031030300000c14030b22031155041c510302d84103908408440100d070700540081083c89070f0451150641d240c00b5440d144510003607007071600719403d61601860a20102d81a000009004080e10362421608180f01d061000b0b2056150048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 978727122 1250 978725872 978725903
    0xf020112090501150e0114090c12040b0a230402060705070510050a0909020921070b1809070305090c0409021908070807120c06080a0f0609050a060e04120c 68
    0x114020701105621030400490100d0003030181c612280800e40c8003000c80106200104924410300c005005002e0094440c00119940c110514000c2c0c40f84030000030b19085a5030420007400bc0b02040180580601070081c01484110340342520013245041841c4400780b441408100103243c64030090200c60301c40d200f610441c680d03c00018554441c00d4640001040e000601e1810712035200d402d940142070042811401d000f0100046250303000030b032841d44404000c0da5030b00301c3c410b0400c00450700205000c500c590364418070010421040b42150300801d00035114003000c5040c0078000d0090360310488411000b000307500810300400c0050586403100746c1c3c1100c03901c80030160004d826a510380180c20050010b151072494040365074a4000c01c0e80c070403100c0f458450a0203001a1890400a003100c83c0b620345600341c1c0e12481080801410050841d048161420500140803562034000c1445011401c10800100e941c64698080004040710010310100ca41c180c61188140203907581003490b4020140c80112022 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 978728372 1250 978727122 978727157
    0x20a0e15100f1218020d03110d090f080c03100506040231051005030601081e0a0606020601060504030c0b03101a041e2303010b0d06051e010b070f0201 66
    0x44009400004480c030702c4206641e42c2090318000c50f48512102001841e91095032010203115600340240b0a011101c420403c3c14880d41c030000d0001c000c00709844c01c80c0c2e14100050b028103808d04c144084011203000003d0751950229840d020b64401601601714128445881c10090800a144951150b424010b070000544681c132504086d48102129001482c070b901420b00f40301c05164812031040c0c08540d0140c81040e03000003a41d0b0080703000c1c04c0c600a152500045a00f5031000c1c10075000c041e21014080003502e8a446e0098001c0719455000d80708a46d8031030300103c501e841140400387c8034010907002001000c1c00f031002140c2c402c540c5034a01d900c00351070b0b1134580224507a910a80341400808901400320400c09150b0341c0d818412003070080c00c9203140c4035158003042c4c4034202e50461000f0160014500d40c80a40000f901c0c15001064032000050610344400100401d84141504001121903554803140003030341d19040c0e84400e241a0704115080da2043c1800396002012410011204441c0000c4203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 978729622 1250 978728372 978728389
    0x90a1e050618120d06050a0e070203040b032208090103060803091e12070b0d0e0109021003020c010605120a05010e06071403090313030c061209021e030304051f1b020a0e15 75
    0x801e904c00810114034000401c1202080b84d00700f1007000c01c802c014064104d40010841d4100c0b41e40b01c94036910703035a402c0e0030705a038115480788100ca60170300920004100110f00e030051102c010243c80c1080129200c2442e03e54900422043c5604142c1401c000d102c50003500c841c1842c9914014408141c12900d100d505003003e0040d8407581000c44041065201c2111600400c10a02c4840c03000f00201001600024000c100048c407080502d50300007413100301d4150a40241c005020098040d48081c40e10084941d610802d4070810f41c0e05529240007d2445140819403c0c025034480d0f40d0300c00c070703d1408105501c10764405042e8005030b100401000d02403d10110000740154000c541040e8020b2400c10040d09101d02d5104440c0c4035440c126406005940e06aa100d9881c01c420503400784040640e4086403031817046800081d40450003559900d6254112441d01e02422042d0381e52503840454004141d00040c803c00700294000c0500310207120340c600c01076071594480304045c80111007160711400b050006 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 978730872 1250 978729622 978729637
    0x60706021c060f1e090504050c041e060906030b0106050c0313060f0e091315092f030f15100b070f030801061809110909090a1e05061812 60
    0x71030b11110100840003c92000c80c008000da1107040040500ea00d482241c50b21041c002c00458a9680010500b4800c003005501902074020f041040070044103510030030f0400f00c4040100000e41460702c0071640d0803e07801400c04407648000705004507401c01300d00740c981d5000b0000c44599440103001da030340220103000d5284000c080680707400510030031100005280300c48002e607441c0100d419605125100811440d59420542c021042200440821038100050038208201030605111015190f43c00b41400f0304140100140141200c2e0346100c00c01415241c00e50200401c08940000008846581040c0c0751141d0010149401000f41c58031909114040d410004040d6a0351460b124400d00301034200d1201e50144c49141841c4241c01c0c8449945480d01d0011301034036880c0b946031011038416001c0781013a0707441c05030002d1a10f0214502480207581c1d40346d452070181d600940c00042101c40000004051990940010190540e503840100804902422010b00350705441040745224800070960090183d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 978732122 1250 978730872 978730927
    0x30712090e07031b121b0503090f060108030706020a02010908160312061a0904091a150d0309140a380405010207030b0705190801082a06070602 63
    0x940d0a101407000188001052001818a4004035040519080442400c02c414510b08000100b8002003400007401988040f2030520781c01240000c002508140554422000342c1c084401c1070440940140d80c60901303224200054004000400204405800034011907003140000f0a038001c242c0d682510b03507808514a0a010801c401e0300c58200355000c6079501c054240d5900501105041c03071031008540085503c5034100450020708e42c000c644cd15042819500d8200410100307194000c17043e0484079508880305100103c0068084c1031034074101604072a0181c0582e2034180241c10040c104141014409a4079402034400300002001c00d800104043d4070801c01c03c1028400d20041d06510030480e10a000c81d0114006000901403640d00142880072641c00646001d502c0d15484000d03201131090005d82e80e1050b01038081100a60f800807200c40c122031900080b070305030300503100019580361101100e0007480144807000003114503000001d00340e50b03030003603800524085480c90002c2c0c40b5407030704040c0e918 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 978733372 1250 978732122 978732137
    0xb0307030b0618040302071e090608071e0e0c09010c052d0a2a0801020403080403110d0506060405190603050708070602030301060e0d030e2205091b12030712 69
    0x140c6042030b8080c9040c3d010494800ca10906151380c01a4036070400b8018100200c000001c6508042004900b40d4001c000c0440204401501d413403850303880e070b0724900501c40356200b841401d81000100001481c21581070a600c83c00d951941c0711841d940742d000001c00c60401074110f43c9400418070a101d01d404e00303490b2284080d8016a800340b084c2c140c405400c0900d03e0340e0041e4101102160140d080b051520620150300740050500440140c400c02c60b54001211070b61020402004209500300103105803070185400c4a1130940450401080045151004013030b6040034011035440d060a400c4140c1010750a00f0100b004440d0000d040d0494038260310a0f04c0d154001c2004008456040c45881d006c0c08040c80510320755030404c00042c00b200301880d88039000740e14070000c03001854450399041c0c0c1110390041440c0041407451166041a040001058003118504404210241c40018860b8400c51405581c0985610700d6000c0010000100e030015007140001c12800f80020310b507003201610511240c44814 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 978734622 1250 978733372 978733381
    0xb0a0b160611122208070b01061205070c11030c15090a1508041b05180702100c1b080d0e030a080a0209090610091703090f10051c0b0307030b 62
    0x15580340031a903001c126002c10000100f01003a501440d440150140a600e0300e00040000d0990300d01050760240090b20f0101d10101003041442c03540e4121143c9a40b40d00c4801c1034803909104a078000c1e81d40001091a032051400007a655454091342c3c00390007815108001d505030b01040381b03541910500d008003400000c91503514504820300078050300d444100e01040b9080d0745400f42040030041d001620b04120110525044013040709090080c100c06440c44c114050358140442001400382c0b541000f5025007070101101010030311680c3c050490301d903030340501140c4e2408044015940c012055a07200e00400c4410714034a11405600710001813500110796440755081c1c02800301d040604141509401044150b0843c4d69110289030442c00c200d90b500b46140400b41c00b900c0c0d002642d4400c42140701c040c0301410004c0310110250102070001d0f184880c043d5a0b4804000c250703085e0901080100d001405414010007210f862148901d40e4058002001040d0200080c80c100442e40f040303400d0b418a20801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 978735872 1250 978734622 978734633
    0x90304050901090b061b0705060a1d010804083c13060e0a03080a0e0406061d0103061505070c1706011412060106033201030201030c0503090d030b0a0b16 67
    0x203004003c0c0510070082601c2d0903000603182e00c00c10004c004141c96082103c034100b00103002c100001c01c4020301030303980c8000e403820240520f0700e10040c64000090810040b0819401450710f0f62185034407805181c075284c0340d000b41003000d1a4000840004204401e800ca0218244a465151210205202c02d880e140c010100204940c1c02e50840010411585941d18550702c54001c5101544e5000955039210040340d141150b420003100012a44a401c04100042c516005040740602c920203600514005041c140190b068031058031800030051a0708480e0b04005128201410541d44192018400d060356036004c10f0340b03140c880036140101d03000000104038800c142c0105454003071068620541c04080c545039543c50700e005104000038180c8807207805082440c1c8001d000e03020b04d04280f034040518405111203031060400d0204034042484c4c800803904160040382078921400b01c42c0300a10745240440c004a0180c44525181b54010000b02d001003907024010340a0804000c1d0f081c880c3d00b1180446c01d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 978737122 1250 978735872 978735889
    0x3140313080409152c0a0b0d0f210801030b0702030c030a090e1003030509090415020d0f0b0102010905191505092433060301120605060a0b090d1a09030405 68
    0x206030b400b000f05d4607040c1e40400000050750885805090400d69a82484602a0005104899001203040100c4042050800700d81202a002d241004003a502c2d0441d10808140801d01e00e00114581400401c00165000c001d280e1040703141c130540e8182104e480400f491904071090980114045050a21018021881a540c062400100e031444280341d601c0140c56441200701c52406001e0350400941800b412070f0507140e419607514000c540d10102070600400030802d0002c591003450411401460310741c414015000001e8009020341455071400300300b1040c1c07000c1018101c2d00070600c83c0440c1400c28079407003250701c69880a40540b481c0300c200d100c0e409200e6403d5043c031400c250305030300303010582c03900c0500e40300d0110b6115601403c454450290211510354140c1a41c2d101c0000030011441c40c0081c881d903100c0501c2190240a6a100c3e03004111400c141c40c044d001c41a4018000c145080c94141c500c080c000d4002d02e00e809500c40c00c610300d40c4940504680320320071640001401c0020341440d608 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 978738372 1250 978737122 978737129
    0xe01110d11072003010b03031309050f010f05090a0b040c090e06030607120b010e040c09030b01120b0a020f09030f06062d04020906041203030b09010b070314031308040915 75
    0x80034680714440c0e80d07080d4030051114035180d41c07140d20840300341c03e51001d41c40b5900b071107402412243c95844201c0341c071a006150380284400d260420011895060056095905a810118803c000e881c141000e103c55094010406010340da01c0300280f40e000e4aa80c4074824000c032142d541d00c5580b0f42440000541120058140d90180d8410002c00000584c0164401030300714a0020101d019010350004036145a0400e000170ba12911381060302c1d07078494000401d0001c89204410300c0304140c0c0d8440d03240064181c40300015100700000800030b5200e00c0300e82e00a028006c04001610308044504011920303041102c019000c030350b80034405008582c0383c1811485007a11221070900c0c484050081d240d1100c24006040e00d0045402268040d401e0f40c1d19400d480252042c0180c1041c01841410000c0c0034000041c84503001d441c00c0000800c0a4140c0b038200c030714054045c1c039401e4200d00d0043c648030b907580c0014501c03011011110b1040000410a400810051441000100311568100c0b802d041e0b2126560 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 978739622 1250 978738372 978738401
    0x20f04090c0f1d2d040c021218130509010504032a020f010c05030d0501090c140a0c080c03040803090a05100813050c1c0b06090c1b010e01110d 63
    0x10b14003000368021007000c1c0c03040d2866800012041000046451440c0322044040ea1205040361503500c10824000c000700f20000725020720034800b07000b0051762541c11498000b080920208803401d0300204155034520307882d8006e8007a080c00320040e04a07c04450742500c0804441c1d440748140810301d0350003510a00200c0745004c01c10ba039112008004c0e252590b40c0e820082c05000084148822a80525502040030383c000043e2a5107507a05000040180401d00034021654074003036a083c0024844d984070061011144282445c3c05444d0348191038000c14800200c4054908000214000d03406001a000400780200215100c403c01420003008807419080300d8021402c000030422030a6006280d80d4020340618500000d0101e681403080c2851141f064080e000041c088284c8052540b90681580d0680641c0c00c50700b00352180010032408000540709a8000001405264140702911440c90b25059012000184800d080143c041c29180c6c101d114074040c900200b451074034092039010341d0b401003c901 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 978740872 1250 978739622 978739637
    0x30506010e0a0f060e04240824070507051f06031a070f120f0c1205091c18050a030305030610050f031302040b03062508012610020f04090c 61
    0x4002e83c0040c05907100304c8082002d0f226640480d80c407180d1041c12003840300e19407020282402100001d4094480c403034038a152048000100d00c0c40740341d12a02402050034560101c4580750945d0132101d030703049244107541c0f074002c45500fa0003260340b4801883c1894114240402c01500c2c50800500c480c1025005002c0c000d904010031441c107030b2021071607101b01d8040c1030180d080c9405254000007000c802241300581840c04070104101038000c05021aa000c4104003400559500e2003030a840d80305542c02506074503514142c40c456140100281c00310031400444907400f6599820008440c501c03541d00a4020400000074088981481c08401070001e180741005450300008500070341081c40002d164001c0384804408140c115551500074200d08440182128620f080c4646030080c102c02021505800e00c0c80d202003520103d01a0920604a5410320700f0710f1461840e004840c101c00b02c4a408a1015000e602c403854025143c6101810321070004e050074544407402c065001d0200c2e18024015810300000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 978742122 1250 978740872 978740879
    0x6030b030c060703050d020d02071103010c1d0310060b071e0b0a230411010806041a0907180603020a020d0302181e0d0f021f020d08150d03030506010e0a 67
    0xc0340d0420103015140e0710b07540c46035810110b0317050140c0c01002c030303110740000b4540080a055070068240d860003000b0790101110841c00705400c90704140d1105000c6402c2c895034402c0c00c02100d8202d04c001501505403140da0701d9003142041150240e42105d4022a00412000140034011030a0111100c4070311082c00d42d501552281360300300100410801038503072111220304420540500a0488900c9411a14400e04041c5020b41c04d2000c1810301e00c0c0001c4804002441e6464280140d03444c0f048c007040305100d440d00318424802444d500911031421310142151102003001200a22001810603641c0142c48030001c2e10004d041202d0180c1d044205401071240c501d1030020082400d02c0350303000701d0382c48848041c015040a802040799000992003804500d4040600c42a01c2c0301441c424802c40380c0400b801485106035651111455880e00183d028000b00c0b4082409440c81c55005441c41c029015003410b00d41c002004001e044c98228002901e0b003007400110f50704003401c0c510f507400841d04410358030306 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 978743372 1250 978742122 978742129
    0xe030c0106031b08120a050f030103050d1d10260f040c1512021605060106120e0f0303060112110d06090b010816180e04050a020a0e25051b0c0a06030b 66
    0x4050b00e910101020018019105902031800c8402208c80320410b9a120340e9a41041d44d122180325000e10085024607032142400700000300d1079090284e00a0a440b010700c0e070401c08680f060301504030211041e492501d0314440017040003c451084680922140841c42d080c80c0c0740c22801d07181d601c41e52191364a9014030078401e410018410623548078410050311011142c410114040c5144000b400c60301480c0c0c004200283d0081007000d00c0c54842d40c2c14400481c260300229600e50182550f50019041400410755540c840d441d042c1c4040144c80000c0b42c0b0610208100c49164080360710380d000980d40d0801004000c50a0180302c2481009003090300d0189403601400292000c0b44038100c1c10413020070020901081c106440030301034280c802c256130041c50300f464030b699500c602e01c00076881881602c00c000303400003500480920902d100180011442441c12400e61210314042e1090b040c01001e020301400030311083d80c00d510700c8045400400184c5000d00500200300c3c901d4124004050810a1103519902c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 978744622 1250 978743372 978743383
    0xd12030c050d18141b2e0e040b0109080c011407050102031e070c05060a021e0c0c03060c03040f0209061323010f08250f03060509060a090b0f04060e030c0106031b08 72
    0x2081600c24940080645401406c80103840c0b820b595140308007000c20790801d610080e904442c0310242e50030005581864019100302c0b15030b100e8640c1a502503100c840c01c55120302503814403070003d0b400d494101051940d40ca03082ea00103c40c1c000e070442c0024602015903801c95403050300020a400e00c1c084101190300c8007070b101e5000400b0011070ba50001041915803866003204049071522105a54445459100540d260030006404c1e510a10a5202003110309558200300e0b802554030218802070309225500b0701c26059001400540c0c800c15030000e100c9030068500a400c94503e001a1815083c0c82a0081c41540e10040c0c02005840100c1070f0300340203866001800d00c5000e415560010740ba1480844800f044403002d80010800640b607407070010810556410141c0543c400744140d64040d907842c2244801c4030011000500030a0720000072a2050001140440d01f0038000c00004c44c00b202d100181c58070315400000704000f541e40d9008200b0902040c1c503151a001c0e03402502802d08603252a007000e5881 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 978745872 1250 978744622 978744673
    0x30a0213050906030a1b15020703023c0a0e040308090d0516060504061d030307080906100311011403011403011a01090e0705160303020a08060d12030c050d1814 70
    0x2030f01150349034403440d0346c079249980003040c42111000c05442e883c1002900d445103888124042c52860400d030780c00c20209500b01c07110b88000310400882440c10500d400c42c1031241d6240d150003c0707419501103400041d9a0034548140e019032540b004504111081c50314200260307500b1401c000d820702911601d158101c45a51100350800c001140d103445500323101009040410a200e800b030920805401c10f03c2001c00554030900f242d40320b48405560310490035884981c100c076014070400400340d0620005011f007080c880364002c107240c030414610352840049503990080c2c0001003003401842d041c0f00b252034240103c042c507840d80301c614a1010038140000c0d0959490340501090350b0f41000004801d58030030010f5070300c00b80e091600004076032070604010b002540007004510005080000040081c2000603036194a964480500c10701c10a981030114010201c00e6469400c0220801940c1044212400ba4001b01e40007142c0c0705404100c145000c140600c042e00105040341c00c0071481541c1241c0001100004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 978747122 1250 978745872 978745883
    0x301090b011206080304120204060b030103120f0801291209031c02040e15031f090201030627021608120a06230f010c020414061c0c090c05090303030a0213050906030a 73
    0x1f603002d144000380281003503400500003800040000018401c002d4140c20441d600742d194184120503259048406200902031141c0920896407080b80850381c00380103460040103000001d00b0a007100c820400003c0e02038540322740c241d0002c929070f1080010b40120311107420b40103030114a490302e094000c108e11400104055522010001c0002d480c0c2c60501c0f0084a0b68011800c11400b4086125500000d2040e8181a400603142142c040b4030070b100ba10400d501000f5201c0040c13041c1d54259000d402a52103042c0c0d500182c10700d000c242c2c001801c424064401c0039801c06840005251200d5104110b500a9010590302244c802c890903506c0c452074009018680d06980e510b01200003000140c48a90100380d0094229181c4404009446000c502140c0958011030701d03401034130100b03901c1b49000c000e82d00c400350030020021401c2040712a158000f841d02441800c009040c900d03414002400e6420841d001020550001101500e5098203a000320107818120b50358005410b103800800c0c1d8811003040024103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 978748372 1250 978747122 978747149
    0x10b1c0e0c0a0303120b01090315270606140102120a030c02070e0f070905031b0d021521010504020a0c02100c050102030108010e0f06090c06030a060b0301090b011206080304 76
    0x28201400d00000001501c00b0709404001540c0f880c0082c224090b041404916501c2c005c3c200e2110345c4900131030003c481c1c108140306400300c1c000220788002d05500e01510b0200282d000c05012014065480c606418090180041c400380380c00302c014001040900801c0c11904640b8455903100c4010081d0b8000e1002498000340394408488141d241c01800e4001c1c0341da4007143c1c81004081c00c00f5002040c46a180c5903550007600d41c1e164289651403141e40d0440062200400055410341420310124410341e000810105c4403842460700c181a5600c907003076040300c0c15100461500c6100070550351340d004042c1600d0071031420740c142038000c1c2420301c5080000e200f04c6d4006620628548501e4031442d207030740c00c1383c001c568035607503241094024010b0348070020245c080c00a4400410401186c014030640442e00a403c0040c070312740800240750300080042101540c3c03000c0205030a000e990286004c0c2c07034040d0000079807800d034030005000720700030821070780b002030034202c0034096039802200781c40495041002400c0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 978749622 1250 978748372 978748391
    0x1703030106050a0e0a0f0302490b1602071a07080307030e1c02070f0b090105071b030f03110d090b090103111926071808190b010b1c 58
    0x11002c3c540601d144ea800030540002194843c039040113a01140e2003120fa5460a41d5400042c503690644ca80543c155507000c4c12000b118141d101c4410b0344041640b8400070003100070b40d44c038171680607000d460016800035444010001c040d010403840c00901078800145403516001f6142d00d10f03900c184030b0000d240090100c040b031034241c040c2e0001044183c00c2030a0351450b040458000b401215803402003401840344550008461303c2001d01c2d00d0540d030160306000e2405800c5401580c0561080d54115040c83c2400c41e820505c0c000001d143c00a18400d4086030a803504a09000303000d802c204d00e0740d0030303941c02c00400c41c40026080300104007142d18001136991100508070050b0010441450030402c14034001441e441500e64071042502c0c224481d40f00c8800700c03208090803003000910000704000221008010034201d500900b944082e110005030240c81c0c1c40d031901c00c02e40c100942030058149418501440c0b00402c052040540d0141c00140c50440c10304145103c81c50303000309a80081903c081d81c03000c0c42e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 978750872 1250 978749622 978749627
    0x25060516021905031c09060509030307021c1a09010b180f0c0c0a080405090c040608130602090406090c03050c0307210207171c02071a25020d091703030106050a 70
    0x1030000c0900030159805d48002c060f0400d880c1c80900c05080c0001c50040b4081000d50081e03081d0740758004050b0041d13080c814039500f4442c404071031340900d514154401250724000b410303070b0810b40349450172011444101e0418000b220f09407481c0c144018802d070b0301d0300440c255241c4030034086036000b48203044005070398a810880d469184207081c1d01c0b2020340510101502484031840082c002c0754000e071040d03404e60342da00c0610050703401180507400006880101090528210150701e200e400d010703101c0186000c0c56080010308a8031254082e00f030040d1a003043e10b0320150148220b80d80b01036100b942d01d165180c071000081000c0002c2e1400c9072070b100690000d808064555040c0e030101503110810201545410b8a40161a04000c0e4a10601c42050a54242d461070346c0c0203440040341e010401c02c41c080b803441c3c51040c1f4000018007004010300d05855003d01d03c6281d00c44080c1c0e00c611a0060300c1d440c0810b400040080105401105801440700c035420b10584c00003049a0440320240340954944400321402c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 978752122 1250 978750872 978750919
    0xf0c09042d03140909060d1713030c0e25111c0201290111010906090506040b0907081c02100501030308150a0311060f04080105040c0e0a1a10020309032506051602 71
    0x9064240700e004c40e101b2219080300154004ada801804403280059581d00f001540300c008940585045000c0316100d0318a040241c55249403042c903080122040c03140030700c014988440004044c20840c4e443d619400201d4080c0b00e4091201c1c2c841d0801160100c0c06603407203140c80c401140302410060382010903201c4000c00c1d0704c509001e50340110244040c69150415a40c0c030070040c1c8081c0c07250942d00d004600c940d100081c26004840c0d10b00060182e030080d020600d030300300a0003504402580145003168084604500c1a140690312a031101d0400307092035002c0103d480c4080d01d101e8060080e10006002007195030303c8040783c5a078122612a652070003088285118001c6600400c5550b08050522040114046400b800c2c1d070207140c0341c103466640740d2000b8010f80d805c1034140c2c5404030346d004550400d07061260300c031100c6045a004480c80c0850701800f2a260032016440010141000e50103030f5510041482c01800601e0103140007410149089001011031400c458003d1140240035214880d40300301c241d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 978753372 1250 978752122 978752153
    0xa0f1101050d050f0103020109080f10050711060a1505150409050c04050a0603050a0c0c030e0d06060b0f071511040603021c09030f020f0f0c09042d03140909060d 71
    0x40500242c00c01c0c05904e130b6026001c0c00201d0100301d00920208910303000003140148840c889009050074000c168484c4008d110140207070041104941c03000d542000d04010841c0280d94985000507045c2c01e080030254404026040103100707031100150103c1e00802d0009540683c8c02c403030000182c9442d0f080380040c452059610594002822600c006a0160140e000c00c0c42441e4410042c02003006040c000c452031007203a800140172510450043e1190b082607203c3c00784440c407400700024400e846014440c0950000b03140c2d01802c080c0058900c042180002c804852902d4004050088400345135440c0e00e00e00950040300c003015400300742c0c0cc04c4002c0030181114400400d10003005044200c1c107005148505110004002d03209030010320184560000d030b10300d030701303a10351014182c45505a410485030a001a00688000c64a005146503070888194051030550a101c520381e240b40462401418803070106000c0c4c48140c40a1054041e0741d250b05180d80d0340804110340030311070f0310001e08e010070107081d5034036 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 978754622 1250 978753372 978753397
    0xd031d030a030215130807081c0501270603171602060403060b040b0306220302031908062704080c151f0b160201110f030c0109030f020a0f110105 64
    0x1c03220038180c022034070644281000402e0311596480c482c15118441e1081c000810200c420000440440e011b480984840310210441004039401040708501b514802e801c010390b5403003480350b00e44155481d2041c1003131048140d0001d00002d8655118903000c03440c40c040501c44036000155200c59006102d402400c460360040075145c8554132400d02100602c42c00c0d4055004500c1c11041444519001800360711408030881c8400341003403101603003603111090b6a4110203621003404403110f1024580c0c2100c1613095a075450040034035011041108100340c1440f02d100f40209007408528003000c190b40c403070744180c1009400d681c4030440e00c00c0c41d2826120b030f4804503100890038203120650071201d1180c1e0000c051a00d1161500d42c43d440502d4840c801c0c8545d036142d0030b070780d080c0c0000103502810851880c1c01800090703600c1101480031a41c02d65000c07140c03850913650365075030311410103411191070482043c03984002c01070b410041e910610716461004024003414001d00c0b44c2c030a107a01c548210340b001c0641c072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 978755872 1250 978754622 978754633
    0xf01030905030d0507090e0a180305090a090f020306030115081207031e031e06050d110f060a020c041a060d050c0d060801060f1e03200909100b010e0d031d03 69
    0x5c90001c0c1644614041d00801405010204030b00e80d54a0143e0b4800340921000c07003640c2c10300f40d5819245640000d4009400a012460004113400c462041011600c1440d4015070350703141c420101400c584004040e080303030140c1c10b1824403500b1000100c401d00001c0c00c1c4091a80d8002030304003134841d07058104030190100c40314a42c4110090745600111503802262031085042c40c050301c81c1d801915114000d160700400712550308400300c4d640b0941c2c40900c0c0d00203040415004c04600100340035520001d15900503070311642506030541094460b0380e0042e900c5492840190300c00700d0001d500391142d000c900e4800c584031008109000041c2045a10203401003008100d582da0398880207020780118403a89035403080002000620425507000c0006101c400003180c01e4990469684800c1c040c007040301a00e801511000e450999282c01401354006d404001c000c09011170707000a6001601e511500300350400150175140803c0b502c07002e1090408070b41c9418a4402c2d03040320b080404c041d080134100c541d40762060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 978757122 1250 978755872 978755881
    0x100308030a090809041812030c05180d02123007020402130f0f0f0803030906070c0c0e040f0506071d101103040e01180606021f0b0915011106060f01030905030d05 71
    0x1410b8844685880750700c7d0aa11031220003029002c80d0182071008001c14020030a880c4c4a8100644c04600040028040c905980041d008948c0e650b50401c042240742c0e10a0f074004800e83e0316502d040f224070064041521311604080c207401c0070f80c040d8000003070041d5008a25407410900c4081c0020241c10549091411583c0d6100d8035601c1450910a81c403000008035808226800e012044a108001e214000d00d42a00c81d81d00c12984051403410544515440c90000b00e02a0290302c00280914002c201c0d580138035076070b0b090242c181400035008400b03211580c500261034441c0c0100760300c40c024080b00c501c3d02c42449020103480740b00000202008601000402040e540b0388050306d00e042c1e4180442c0780080e81c0344012110700b202e00ca400342c103015a000d241d44030000500103810a801c96480d11020072441e14501c00324038070390700a943c0c40200b000f1485c404007280d64001e0100601da21300600812150405402180303084010314032207410503480380032544c01c0c0003007002210f02c000031000040206140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 978758372 1250 978757122 978757151
    0xc090306050415141902041409100f0810110c07061d060d0c0807090303080406110906070c0303030f0207020919020f0a0503100b0702010f0e040b030f060a05100308030a09080904 78
    0x181203c0714000c00700070385c0c0300c24055810791084d030307040d20202d50300c0c5805840040200407080000520809071031540b003c010410104280721078009100c11401080b02c0300c0440c144200390f820b220144150f4007414040144900800202da4040b502c160821001e512005140355070f400400051594001d40d00103000350403492240d01c0311050b000c00e9981c0040c251180034007114951194400500015919408100444d00c141d2001403900700e414038141c585020000402c1300c0e0f40040c0e02c1a11424a20031080040c1a05801b401d8922168420110b20382591940096603407040984101c0e40c408213140c3d1030340515010b50442e1544040c5148a41e21030034000300092a0741d008403403402215500410015000b0a528140d504440c0d0584511f540c01c865944125000518140000e40c030076100c0881410684050195080d400c032041c0180c9136a10340003002005650000d01401e81e00c3d500101c082001c55a0881500e4000b0034800000c104018141040201c600541340e0751580945400340c43c01580a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 978759622 1250 978758372 978758411
    0x9051f17041b030507170723030307021c051615050906090d150c09061d0321070317091f0f02030c0405030c010e010e1011031210090c090306050415 65
    0x104070282c0e480d01d408501120380c0e11501c6c00d2003511441190060109100c480c231032070310000b00c580601142d051205907000601d109005040100144403902001d0302400800e00c44007140c2e590081c000c02115292107400004802207050b03100400001040714020340ea143c0e0100c3e00402c40c001c000c00011286030418450595047d0722494040f407800c0300c00e07007105000301c100104444864648401020060899140ac2e1030000720640d803600506d64801c410100e0600361704a1602021501c5031610b20902c1c019103501030b84059500c183c205641080300c45c2400080d46504190b442290740008040101000e01800240c1c05081c00f290000c8100000203040c08042c02c100c690450484220111000043d14000c01e480c1e0b40d640008d8103003000c0b1400d802e083d141014444454540110405910b16410b070440e00800000d40d402c03018101440340c50701004402d8405050b400c0c01c1041075403c0208080c14880351071200a001d01d481e000081d090160030814000b43d500f4480c070901400a0100b2078440d80c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 978760872 1250 978759622 978759629
    0x50a0917011d060402100507060b131d0622140307050c012c1002030d0f020a0e010801081c1b06090201021b0a1809050d09051f17041b030507 62
    0x1450b00d480403081e094000280036020741c1d000342540607071802001c0c044540341d00080c400c1d540c8a80360710a840f241e84500700d401121041c001000074421080c000a641844000048410a5484113050040d0741010302c4400c0425107950781c0c04541c0392040d00d030840030380128440c2c00010307010114400040c820040b070102e40da95802da1f10b0a05000b1002020580328460b04000f15840c5a8207030164142d0070301c6035202c0c803052480d0048909001040d4114070540d100a0501910103401207941101d45810103032462821109082c1500d00b90306228515503140030b1203440e1441944940c506131491809040c0156403030710704c0c85c0951078000313450420340003030134070356400302d0041c400c031a1800c200c1c0b0b00e901c00e01e1050341f5004080052035480d0003014802400840c00c4a0040ca80c3c0300030900001d00c1c200500d0200401d00c3c1c4801040c1440d00c400c010070300c12041d85003016440c024040b5078181e588641030080c109401c034180072071601d460030019407490368402002c02c3d1016081d03001c0140100082c4c1395045 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 978762122 1250 978760872 978760901
    0x210702160b09190e131113060305010f09050307030302030618041412091c0219080d020d0f050304120c05030f040512010b1f260f06041a01050a091701 66
    0x36402e0400110343c020b90600c564402654202c01003441c030441801e003115120b0080084541e030414074400280c4c0311544400c01d42140d81e9585c0c04004000c0280600c0102540841e0104035110541d00d50949a2292210007003c1650000000d0740d5942c074241070385030074480080c2c11201403900e8a0702c9080e88100445801c030b54851044554800c0724400200e0310030f0f001c00303003102c0f840c0003007614805007407170034040c080342d00400440c1f118070400c010780c41c0c0c1802022114000d007240703070381410042c1c2440c071005040405c110458840c000d2b00754005e07046903002030744030181d0002c040441358129100b00328038030300500d80c0c0400103d502d078079a240000f42c0b00f9520200c81c603c5a00d01c502c8061800c940d08a5403031340d001030b03400505150941c0b0340f051002100210741445100380340703104d00740103124500c42d5038245610580307000c1c44550282d0f4950164000b03401d84040221403034140304010130b03d4286902604102c800204110990310502e0703110001c0154415a440b030b208001c04207800380c003440014845 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 978763372 1250 978762122 978762139
    0x40b090f0a23030906181f0c080903011b05041d01030b0103080a02190302010204032d3801030b070f050406031808030708010614210702160b09 63
    0x102a04080355100e942680701101036480d903000d200c5080072851802c0d03a80d0305408180503014490700c51000a011a500000c42c5a042c01c2e90301040090030340440c050160410000c002c80181180c10a60550440d500010f0060b2601c65a40c0040d002d0075401d41c4050f413482c80c0701ca07102000354000d001740003036401c0100140f400e21485850103000c41001d1101404c900c50f0b4400400100302070400030001060749105582d1541402c031050050700c500c2500c2140140c3d0300207010004d00440541c1c015010001d145000802c803400c13450400101c442020261224190140d41906d61a0788100d425041d00302c030485040401d0891203401102c0b0003403000b5144040070400240405200e80904220401e158071042d06240c02c240040b0010034110400d1403454030481c20081c08500d4082c00303588124455541c042107907050032002042c0740700b0110103144040c1c0600c1080030258107090710820709000892585800d94510070200d140c58503090340048084c05a100220700204110010310a48000396500035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 978764622 1250 978763372 978763393
    0xd0e120a020114030a110c0a0c0f0b181314010e0a0e030304060c020304180518010209031209130c020708151315110a09240e0112020d05040b09 63
    0x1500d4066625000340090340500500031402200006150401900000042c0f80a48803800c8009603200070b02d0440b86900441e00001040f00401166016144140411550074900b241081181c05045a4240e506509a409821903100c1540502c0c0750b0394407042c10302c40d803c60300007100c41e03140080c007030b00c2a00044031000612060050084e090706010b0308000350300d923503260b0316810002d000e145105011804104000655148060125900c036204410000740c64140503814000400c088070715800c00f44d00601c20040d640e43d002c5601c10500512503d801e07035603513988000800410300111000c002a00c1c000c000300400d54001614010761b5030f84021180c505503004103818403982c085414400200030403680e0790015030207070200c041002c5003041c0481c21084418041115130018003c9500085802d401040204802e000340708000d40d143c828105641e50004005245109401c1c026050002c0c1003c15035540f080307581200c9210381c1c036440401c420b0a0134a891549044c0a94035484544a62400e84 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 978765872 1250 978764622 978764659
    0x2001110d0c0e0402041223010c03060627060f09050a09090203060a090c14060909040b0601140309030405120a0b040b0f18060f070e090108030304030201060608070807030f0b030d0e 79
    0x2942512195404024030030002d03034030f040180442c005051a6441031f2099000303500024010109004d80c1030b1008144541014002070000c520340015054034107040c1e0a00301d045194282d4801910158039103030461004a941c155681002544450b401880001000a080001d40d100903840d82c801c40c19180300d0745600000c1c00c10f136500700c0001b42c038008035504104001001c4081001414030060603190034011050001005c685e0f00321003d48000728410100181c5691204002c018582d00403101d90039420203c075501c3d600c1c001c40c000c071401403560030143c4200301020450000c155a00155801c0c052800d45448440660f0645040c1400300c812408a038122600c4070a4060181034200101029541c00e80605100500548030009021f2200c4c455036140c1c40e80c03202903018041600c0119540c0c00c0031b150090031a400340c3d012204001811003445050baa01803c4a90840307001d16010804035404d007669070048c802011a241d25216001140711004d40000d03021070b2903c4100c92600c01d41c00f44c202c05 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 978767122 1250 978765872 978765877
    0x180a0801091a0907210b1f050303070c12050c2d0a060c0b15060a020c1306050d0f020a230a06111203090705031203090c0109062001110d0c0e0402 64
    0x1030f80d0f816044804207100317180391034603c0740041111952184a4071720548601d01562411ba5882c1c040d040c1e03038080c07030a41640c1c0380003460003013006400651410f52951100002e5103064043c40f134055803416078003c1070060821091100a100420744140303400c01005021580024141d01556a49224400a62803402002000440e032035a210344030079031143e0381c2d100f000201c001c3c103a000500d0740c4c00803c0207036110740c805000300c01448d030000c019540c0741404002c0c0407035125012040060521005001c6c944421710050603042c2d104412460401d06480020b5181c11030b0340095480500e03481400c4120101c0701e4011a1007101035901001f115283c500446410540c0002e480c0c03154890b044290783d9900500056601c00000c0c6c0980e8046600d07003002078180f0403079102c840c8031400c000c400e0022411090062842070042400c221075074034038114018001008414156a952940407000c401000f02034100720105429210095602d00600d00340340001c1c10010070840020742a200078103000e08140c803c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 978768372 1250 978767122 978767131
    0x303030103150c0c060e0307060506041b11010b0924030610180b090a0501170601051008070c06090b18010e070311030a0803101805060d08180a0801091a 67
    0xc00750302d10514115030382c0140c080030b602d00c001c00c101c0d204c0300c01c0824018480e1125a0410201466030780d441800c0503800c0d00d0000d41590700c03440c60000d020900420304407904040303400c40e08003003000c44100b846050040544d49001504066a5400c004c4840c8080f016144004524812410101a13990074196901821100c1d200e0a1245120900c2207449480502c148414a10004641e03481510302042c042941951345a40441d01c810042c094400501020192039040400400896142000040460b00c090707280d1003e00c981940440c203014440c5850104223500050700f845007140700d10b452104d1420440d5401c03046410038240c80500201801220941c10400d0001e00ae074a0840d01c451926040d250640c0d68235120b16403040b0001118a800b46204480c0c0403000000945030465000c0d042d40c2a95507018040e00e050304003d5580d441d002e010107159041004640c903041c9460700100c104542c2610a41d001c0594800000c6c5404150052042c2d140300d00742070b449142d044008174209600554 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 978769622 1250 978768372 978768383
    0xa0b04210c091e0504020d06380a060f020a08030618090f1014060f03160e0115050f03070c060e0703140d08010506031906090c0c120807051806070b190b0303030103 72
    0x2800d40000c644030781c110f02d090241d001c24402754030260030014000d5140e019441c03440c800c0e03400740030000303440d100080e41c000340064240107058100500c0003d4864800c0031000703240e20303030100100c0ea07282c8884080b04604160103100603281d040c105103440d510086106001030070310a0f8800390b03407d03550901900345603040142c81250a41c50710000c11154842c1c03071007110303018840e6092000c00128650520001080710107a08140b0354141100d0910f24140c0e00100c100f03104e000c020100fa4a40f041044a901c0100f500c0c006d100d4003010b14003030014001201c10545244a034040200c1030013416035000441c41800e10841f0b03032b203652020040d10300705424894141c0c400c20900c002102480154034a444040c1e83c860006103140c0c86150200c2280e2444200f00002000300040c5030801c02080d0101a06007000e0a1451452a225400400360b02c1071815200d6407019201c42d02456840c3d1100b52220180c0c440c8410401e0300d4100c00011900c5421030750f9008003810f184184500b4103011003103d05998022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 978770872 1250 978769622 978769639
    0x1050c0a14010b090f100605031510110d0f0306140109030f03050c0a0b0f0750091c0b2212031a0a0b04210c091e050402 53
    0xc0c0c40e440c51800c21091800c220b9501e503401648a992046212407080301c031303810b80501c9401e000c00d940140d06915042007003404006c02c18883c232202200510704042c0d07811148a216120032080c215111500c84000d9189032141c0c11014603119041059021001c07400e5404000950b56407002809240b030690805010884004051001c0740e40302e100c0424117400390410620b0300b0000780800c2d00c0c10324885001d40c0c40109003418000100441420103411259924140c0182d03c2e514205404050351010a44031807d2000c202e2410031292100e01c2c200751005003100094001040000d401551188036100e104044101d1840e14114000c80c0c0386400a800a5220171030341e50700c502250020301c07081e6042e24481c210080031000503002e03044414242c030f815030b00803410696000e0100d20003525088140d1186000d4032080c001426070703d06a504503411009152004000514451011200303008082e0507007000320008101c0c180260030680c042040c58114400248a00d4a0502124403d980095105810 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 978772122 1250 978770872 978770893
    0x30b010e0c0f07080405011d0a060f09030c08063c04080409090f1401061202061e03070207030b0604050601170603030c01020a171308040905090309060a0c06060501050c 74
    0x100003816486440001c4031881d040c86110036000e00d4201c00e0088904180001c0c0034002568413000350000c05070040c00c00302aa005240000d005603026010f19010020850480013040344640d00401c01035800c21100043c1e152108042a2182000c0754006800c4d12003154042d942c00d1360f80c615070603141c1d550f40c10901180d9440e8951610510241003513401351024403010034401624802c028010384030307800031035035415540f4001d48004e1008402c03c165074549601000034205007005809003d60496a40c1d80d40d4440a500c40070f46141101400024a00401000300c09a000980311003501d0044400300c4d059958402084290303041201c000c0d0002c0c1d561a0800b59200e8841c0c00e0b90b8020000505880c10446211400c81c03c83e0016a05100007504c002003071a56141c62414050300f20345811062400301da000e844041c120f101e5482110449a0f8481c0003a40d012030a0043e00c42411004200603a15203c1520040903618911307029a18940b4007600054158040c4044031411420b200c06003011141 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 978773372 1250 978772122 978772139
    0x1509090504030c0b010602061803090f090a0f090803010e09030f0a051c18020f0301051608100503190b06011e0e030c04020705010e06011d04020f01020f060114010e030304030b01 78
    0x40948110140f01e024510800041e001850326806040142c6c01000c0524201840c0c03049202000c420a1542c0c1040003681c1082e19004003c10301c4820075542d80145480e0703170550300020040543c5040500b446e00c5d85907800c200c0450004d504980c000041040035803a2468516140c0c440c1400540201604100918000c0d0084015240031214403121801100e801216441a101c0c181101d502015075104050700f1490a0f8400340704541b010380c005c201d50f140024410f400b0307040300e10080b010301510340001082104080070f0100581000740985403800c545401442d002c0782008030403680c002540c0d001400350351288480c200c03d2040001810b6071005006801d07628202c4451140381c150140102c80845621140000c00c0380d41c0c802d4000003880c0d00c03514603190030484103804c181c00c1e01c0442c01a003040b00301da1a510a42064044402c116800d2001e00142d1030200c43c90000302c2d4901070f0000008070001b00c22680b000c80042a290a0711118524040584034855400001e15000d40000103000011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 978774622 1250 978773372 978773381
    0x60a053f07031409071a030f0f09120a0c020103050a0b0901090c0207080714090105011d15160b0604060803120406020a020c031c0905490b01030c150909 67
    0xa01ca040c001039038200ca0310301d031081d82c40840301391466500c02e038010042d801405980d000b032420018181804e500f400c403142039881e940980421511020840812a0904140310001c41d500c400c1c0001c6540300c21804004d4480b007050744007a4042442c0c01c0c00070707080c0b031003a000d41882c161009140241d6a03003880c00c488018212018214114480c4000100e80c04108100c0030016100c006004042e0b02844c00400c41440c81c140c1040741000210004817a260854034130407074042e2821607004503a00c02d4a07401c02c805002c0c030702e070300c1c240c21290a0421046c80002c1d00300c1400fa0001341c40601c071641d2180411540c070301c51444440c202c1440074000402195180c0e0242107144c165105a80504228800080c07078400390441c00401055040207200d8080c4e004611500100b00030780707000b241551030300d10700782d283d00322a18034810a4103007440f0f2520501c00c0360003a0340c0711480c2100210300d90140d42884a800380c2c090204840c0640c2d078030b5012885200400c819109243c3c259100c00686040507455000780 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 978775872 1250 978774622 978774631
    0xb09070c051c051308150a09020d0206041707080304320a030b100501140d1a1309110306060a062d050307020d09030804090c0509060a053f 61
    0x34010030160510b4040c1c201058410070b801c5a40e0b40342c4548240341001159186a4401d998030f5018029404521091640040e40f20380c0100b00050800491b00202c5e10001060078020f42c410310000d80030441800848100a114254804030b8440c191101c0e00c8a41c0c2e44224022415075075a04801150220710210002403002941303038800480718014000700e4075030302c417580048034a004040301308901d8a022407146002010f00b482c110151080e401821403280c03207444c5d9202c0e00140ca8000b030f101d8112501c012018840300c0a4161580c04041034030520080c004880b080f11101c4040207010480d14000843c10700802c0018070645110740340160503541c00c1200f02c0c528021070b07a003c90340c2c0740110001411108046203901c84035500e181c0480001d040c40f000d2101001802240f47c014070100e08040140c40550f802c07400c00040b82c0d120381e001905c00b4004c0d13043d406e510800016288491941c0007004e802c0b40713800c103030044000380a003c2060310860040310030f6841c48040d022504000c81d500c0040b07142c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 978776978 1106 978775872 978775883
    0x9160807031d06150f04050123030a0f05030405210703080d020408071e1a03070f0507050a050601320d08120a0507120b09070c 56
    0x4020303184800301640c1c0d9440c455161140d64103541612411001c441c100d02c0d00d0141030303150103141300da010302aa102d40d507580040d00f01401018140d80820459030b0b040c0e5080c2000c01040340c110815954140f01e501034007000705040c0c0304502503050180018640d00c034200410720003100c160b01c0f107010400040003503046070f690b408103c00c801d0340d81c0310380503c6ea54001003503100d001c1c1c0641e03080380c14240034490340000c8844a40801e0750302201035081c020001551810444030110000310300343c1d5030840410001d41603d11800400200c403045040c942d06180407611140e00d858511f850460359584100c0060280e062007014101d031180300210a4082d40d250340c1c0108413103107400c11025005192119041003044080d80c00c0e0b4054005010301d203d13491922541007009001c05444507008105202caa10f02401624004c010002d000a001d0301656120550101d41d03c0c1d280ca0b1781945c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 978597122 978776978 := by
  have h0 := BRFrame.cov_init 978597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 978597122 ≤ n) (h2 : n < 978776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
