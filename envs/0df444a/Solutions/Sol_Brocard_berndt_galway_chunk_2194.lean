-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2194
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:57:14.977369+00:00
-- url     : https://prove2.me/submissions/66d24124-0427-4003-b179-df190c9de5cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 394424460 ≤ n < 394604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 394425710 1250 394424460 394424473
    0xe1521010c0f05040b131806030210020d090b09011e0206091203060a031e060e010c08090a03020d030216021f1419121b0c0c08011e020a2102071a0108 66
    0x40c500c01180d0710107843c400a1684451b00412006070441080c989010800c00c0018541c1c02c41c414042a000c0341c0d90301106660024007040f807050350140c003003801e036601500f00c607031592800c00c0160342e5110400c14403d0740b240100c1c0941e10f000d82c00949148240003000032612609281d00e1030490034801074610302e8000314038040c2071020a0110314150300407181c8d5046405a2025500d856086450300c06020a0b5651a0110051120b6100c0b00c860b400c034401c0d1000c2c11142e220344d036000e07543c0c01e4180707851810315401241c28502c081007a0b00045d03c99401601c0108501e4205c200551500c600714003003808607418010302d0610a07101800c3c0c90f00072311141840042003c01c40747c142c888005001151074000e484500607411103503c00c103a152613002545890120385054517060031139078400d0b0080713045a0f14041481035850100e81d6919002217001800581d1502028011030714031034100310b001d07090b0182e940c00707038001a110303401403840c10700403100c0e051703e000c456024003103200080c400d40c00d140c0c1c041d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 394426960 1250 394425710 394425719
    0x260f0a150b12040f0803011202040b151b1c0201060905090304050901030b0a0204050409060504020405060f0a061b06020a0f02011b0503040311010e1c020c03060408040e1521010c0f0504 81
    0x800881d400c1400313401544a030184907929201c07254400d8109601d000da21440c10811801c250245d10510032007115401102e103000c2030810b05600031405031b48160904100e903480e5848003400441d05d15941c5800740f842000c55098003901a040500c103500400e803500300000c1000702c0200a0302c0588900400304201a440c64641c5025810040d01418406a007080000703656038517442003c6095100300408500c07850a401008125903009080c60302031040e5004007003043d40d50b14640801d03100701e4144100121000001c1e8120007100c0f0750002c0820b80b000079819440b80d0808035040308514241e00a02c40700155922080010b0549403481020410520100303000070b0160240d4481a400800001074010100d080e041c508040741c841015150504610002141da0503c01c590f88000250020515402c207640e4070b5084c1d10a034880c0ad030301181d41c4000b05440001d000384101d4003d6000702114039021140ea40e0360214103254488a0581d8a01051188800d0041200608070b420540b105814107140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 394428210 1250 394426960 394426987
    0x803070b07051c2414060c010207020a120507060c0809040f0f0f061e08070b0313050a0803180f06010b0a03090b10050f030319260f0a150b 61
    0x2500c24030601c9000d200c04850742851040c00e81c4815002c40f001300300000e101101da4a010707a0f00d41884e82d501d040e40002e100302541c0300011895448240c45150b03031191220002c90090185540095004444010019009045644000700310307002e038041d200e0700c0d582c3d4001524509640d10380207000001c00c1c85041401d15050303001016001040002086104116440710304440314041c441c10080d540d007200380420a1560b1902059005410b85402c450341840710340c80d42c80c002c61180400c0f0400010000789050040400f00405542c000e0498501c40700e070349001001c50700200d40c640740c0c010b080210381380b0030b940019100a49201440141c4806d900348541d8024540c0412030f02020700d500c403e4404000b0308020201352040d41c50816074091541000104050401c0c0700700c149110758014401c011031151508000c242f0075045080c02c055081b4503a24041500108070020030508250b00100407480c1e40c4008820301c01c56445508105c035400e2002c103485140032500a031200d00c44244109402d00c40c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 394429460 1250 394428210 394428233
    0x60c0d030b010c050a0615120c090c1e0203040321200f0316020f0604030b0a09050109081903050106030e07091109091008010c1407020d0c15090503070f080307 70
    0x40c0341501054042c2e8131810b1504d115020100c40b02d0b0b41d41e40320562443c8140d611030014000350301a184c0c0c4120301380c480881c5003241e8000c1c3e110b0199516a2040002c1c095a003000d00c0d0030a076450000004151000a07441e604903110580f0341c0404c1c6a070100741c080b400410340541d040135440d003503a40000ca03040780d2a00c0c02a060840e081e48208262014542010400f40064601444011808d0045881031007100d0501400b90381c0107007402d01080c400100790800d09980f001c10a103001809908505019001d85035040c0c018001d01030000c4c10750301d0700a900200e61881e0306203480c14809071345e07103002c200c1c1268200031100d140764008130414412080301e80c0195244e20050f176280b070b04000c40c0c1c0c00040c811a8064450441d0f012007071070300b007103200000e004040628409007012040104000b103076842c6071060303800091190f101081c1c410100071a011126014000015220341d41034004e50024040c45101d01810340b00f4402e00341d00103030208072200c1c4034040d250008003940c01c0208a5441141580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 394430710 1250 394429460 394429481
    0x3507061115011d04050f03220503010e0c060a020a0c09060302190806070e010915080906100609060c050f060a02030108010f09020f0d0c0b030c0a0f020c0127030206070b0a0605060c0d03 81
    0x552a104c900c1c21b076041015051895511200084240e00c20003003903d0050140d1041c3d01990502d4044981c0c05e80124601c1d00c400d02c213480059881c000b500c41207090851621009046056241010030b100600750f1245054038403e0b50f6403c1380c4403008846060303d0300c09215054040c1d00c042e0004003154841d80490004000604080318103641701d40f482c40c5170008454204000a1050781003124140042107100d40048034110032880d59401c144004084003910302541050112002442080003810001c036160100180e05503805402c0c0b42482e60041d5100703220354402da608080d4440d490700c1942c03141041c901d40c000c1800c0c1220540744140841180020350070b40d0326400b0f03000d00080004c10340d4011071140031940306141d510790707410a015119544110507142150b0103a01c2c0c444950340c000210442100011240345500e030002e08140e0407540390f5400094100601081c1c107410400503800c41d5003d140000010b1281589907014440c4a00070043c441800d40d208000c00102c95000754030410600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 394431960 1250 394430710 394430713
    0x3060501061103180f0f0d050a021903030207050609150d1a2d06040509070201150e010b220503010c02010f0606031404081c050f04020405103507061115011d0405 71
    0x1303001c501d00041c07c00000c10410b07900c42e04445030007805c40c1340041400e9102015100c807036000e5030460300e00039903510090045900580c00050f00e0420b540c0d540b92801d9440c21801c111039a20310025203500082c001d41c020301c0d110100582d55202041c5400340708158a801d060b0b802c8030611459642d144822102c43d100745402039402c200104003a03c442420f1407042d60305400200c0c1003110200a00c456580c1d80e07000e22482c0e4a40001030120403107640c11075111a0090f100d004510107420001401c1d04c26540c0040d600d5803074580d40764070b6a9010f4111501001d503c680c10000a981c854099007078449520100031030400005c0060000703514480541701c01c803001180740b01428210700700701007142c50075141c9030401c64a4108020031807070203014031540030b10410410b0002c10300d0141001a001c01203800c60160001c0c3c21129002e0301450f01c0d0454408141e28101c441065559802030041494001c99206074000e80220801e03503640180c80340c0c100d07110081c80f4202d6010034001c902c00c80d02d024008031003d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 394433210 1250 394431960 394431979
    0x9010b04060f080c070b1e01090218040207060e01060617011403031e0c0304060905040b01020a17160c03230109020a050108060d020a1e0806040b1602100603060501061103180f 77
    0x3207441b5010f0907109141c1a2400010304100600700c4000200503845800b5060040106000121a81d000e071002501e0503280503807030303004600e0610080e04410083c04001c2d8689140026425130209179500c0d11420311080300c0c2140d03242c0158600324404a041290541d1003045405070b0b01c0c0803094103d801c0c140c14103c242c1071902400b161405d56001c1e602103030001d10241402c0c029841c0510400406c100240010240180182e80b124004400110300703d0b016040840d842605c120411258082c03241d0150401e605192603140c4040d0019100000f00714402703121403482d400210500c500c07020746400a003624200381c50403004584c03c110003084241c214851201810040e25581c4114003e80034044154400d02000310510100419503804150607500000c140004940d4180c003280d04091104c2d000548440120805c1e45095900b810091010785841c0000042c440796601c80f070f060302d80a41e5030504200710440e00b550b07a4054083e2500f9102c0004c1d441028500d03061908001c40d800c0505020003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 394434460 1250 394433210 394433213
    0x91d0c0c0610060306051008071d030703050604050f0a0b0a1509150e0c1e0d020f0c070303080c0304080307030c0306051c02030607090b2710020c09010b04060f080c07 73
    0x41040035a58615502d541810500246416020380805030100303452400d0560301400b8024103d2501a0081c028414a45a107a010b003a2260102d800b03408050100c410b03281d0380b450065916442250155581e0081162003118520041000c12095820901d60007964860901200c020303d00c1e4107103c0501503c080300020840c7c201d000702c0742c0104040003603003c10391034900d841c02280802002100400c9041005840c441410885101025507111000c0e849105401c26030009114620914800b0030020542c518080800261310300ac5da4802c0d91110204d072511401d40300c05e40000d44000f401c01e4810f01c0003401d024426400410040f20314074001c20303a156214003150380e01c10380000e40151040b4030240081582000c000454000140e8074185401c03070310700100070443d4010b0b401080c020306048000d00c03e0341815072680783c0c0e50321002400300540c40d8082401960b514130305000c0d01d0086109500008404c400e15040d101118402d440d001d0112801690440d05014018101b56148605000f20700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 394435710 1250 394434460 394434463
    0x5090106120b030a120e030d141c090204050f10120201120c03060e24030c01020c06030901060504050c07060b19060311040306061d13081206011b050105070f091d0c0c 73
    0xc4044842c1d071180400c0c8141c62050604117071703092300303044140f00080401c9507c07442d084003254034004100440300d5460000c65203450190060700c80c00387d130141c100000d1010b0440792200300c9010f4401541c214080c25650241c01d00071587c22b2a001c3c3c041000e00c1090a50302d04203402185c0d00341158900080c41503203c0420f5104071405503516507000c4a0a01d1040f0b1146552551150000c4c00310001c046c00400c0a0000b07564030340e1210440e01500e00480801c09000c400d401520180100a1003486289440044030010790890003044e14014200340e2055800e0402043c8c3c072020242144050130b07541c0c20900254007510700c41c0d00020107100100300c0080411210f100341c5e4081c0045050581c485801c0e00314000c9101c1d0090100180794002e4004074000800d02d10850b49000502d08141d9207540e54840140c420001611000d01e07280020340340c2c14100401176128910a03643d0f174554080052070544121150102c9004070408201c200340d03030b42d19050004001c17030b512200c038420461914080003a00d6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 394436960 1250 394435710 394435733
    0x1217070f1202010218010305132303070f151401030b0709031a041a012301030e010c030e1e0a080304080f0406080403080a051e060f150d0605090106120b030a 69
    0x601c0141d50114080405540040c1101071a100c240b900340403e0424a503000440d0f202840024448003610b0b500b200070091601401d9a02007405040d030ba11000a0300301030302e24038100001101c00313200c18076190000c04082e00c00c2400741c0c400581e0314500c0703a0a5550300c0e190164090184070034820a05c00c00400108401744a860b8803030f50511030075890030f092a0040340c1d817440580d298446042000140a000303800c1c0c420060102c8009061007000b106500168010124402ea103403a0354240380d06441100d8158108507000c1040b101210f0740c0454021070f5050a40c00d5251031a04c030741181e00c110010071092000f554010780200e0031145030180320404286070f5405580201c01240200d020481856082800d4940c0810414028042440c120324280d80d0b110900340550710726070290700440d0140d100c81400d0f8000d144050003610040c030540508a61540000c0580003007076040c001d002c601c1c3d00300044030354125001611035821a8042d0144d501c003902a448010380c140c4600d9034418082001131180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 394438210 1250 394436960 394436993
    0xa0203160c0c0b181c170a211a1e0105220e090706081302090709051e04050112051207030c0501050106201b0d06060e070f091217070f 59
    0x1510295200c60605c00d20100c40c1041054000130310740a480032812a594100310f10b1038a2003025134806940780283c0380a51001c01e503c002d900c40584280c00892070740d00542c0800c3c2c04c101a180307424002c2c810000c1ca0750061341c422624162031044125654001d40107800d28440c2c100c50a4071103400002c10301200c1c503660740001c0715584240f043c04440b000c00d0104602819070f038640918146010100702204e000b211900a001307444c1c420000c0c40700c610547e03062001d49001400c100503045d0081c8420b0940303056640441c1b0032031408000082e414003c02492003119800400341c40b800c54101d10f00d03c92508104015414480c10020315000244284a1240a00200d0301ca0140d164426000400030108804c1100c029a024921034007140a0442d622242114100c3d90a009855a894440081c01c80b0ba4400c08590005ca0240700d040d40d002450041041655500c2d20103440c0e503490403105031095140c010300451a12106190300c030b09070354003c0901d94010320204480141503901d130310412003d08203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 394439460 1250 394438210 394438237
    0xc060f070b010608010e1302061b010e25031b0306020a020106060f170c0c0a1407080d090b03011203030905100501090b06091e0f03071403060a0203160c0c0b 69
    0x2419010007551251050243c00315140403640ca41c1030a01890410102900301c0300c500010a02d5042195030302003c40e4404419520314030303080c4d90301c0c10055000e400003c2015002e4010500089981100c90249240748a00b01c00c5d03200c2c00501d0764135051000303d240116541c074013014010100106405000134607400005034000a180e9207040b400410400e807600e140700130000ca00d91401c10703000401e007030325420140007802c040e03a40d162952082c2c80c28071015001091142c60500c01d07200300b003001c10b0b0501214000000e030b91011104150840c1d0040941c02000451201800103014803650700b404030000c42c0c0b180c00e00003504009030f2501850b201c4c050004d144616250f0300140446407440c090f121882d04299080c905010716035001070200a400860103046040300c8104091540d51406511001480941560002c94481f1705000c4080c1c4a0341c4280e00a20a070000b141d007890b070a00c201c0c1e1141c01d120910400014140e00c04071142c80000750261109122038001140b1030304040000e00c030342c0c1c680d82c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 394440710 1250 394439460 394439467
    0x2100e090906070e040605030309010f051608070203010507110d0c020d080301140a1a070b0c070f140114100b0c0f0f01020705070f05150c01020c0102040306050f0f060a090c020c060f 80
    0xf540148003840c9048814000d5003081000c00440e14000103844e00c0c0c15007400c1900b81d0300b250744800c55440c0525602204400100706901c400d001e51800285000c500981c02030200ea50b1300d47d403d640c2040e81e01e201a903d0381c85010719103030840c070078244100c00c10700c018102030099a840c1c480c41d09136042a0060500b2059008081c00d00d85400c0c240d8200528801c0e800854003034501801801c2401100c0c8090992001e03903000401e40d13000d1300d086450680d0301c11481c515500072030034103803600343c002d05240c50203601c0e2110914000a1a00d1910300c102c0c0050070102d840e6041c0201d00b400d94118008036025881600964091188144020700e80449040001a120b0b400307428454a4514603502038941e151140c0801d01182d03c1c3c403260400d84440064442ea56402020a0300d802441501705130400341d440130501000708501ca4000500a0051000c03800550b10f408070303182c4101000380c860651040c07000300708101d080baa940000c5082136090054072540500d50003c10301d65404056112244103000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 394441960 1250 394440710 394440721
    0xd030e0405070c0b1909120c1703060609060702040e07080d020c0103150519030b07020c0901090228020304080601030f0209010b0c06060d061e150503030a0c02100e090906 75
    0x1d20a40e603015103245030032241c0802d1038540e15222a005040490030240c0c856100c0054003032600401030301c540c481605207a003408401d004044441030300040341c4025544c9950340d0401d880034150f9005045c002e06580c507080742c41c42000015413190034103e800c1a103070384040007250340501c03112004205540c00340c00710303407410030000741480495120780e8103062910b131210940000c0e9034280016a207003900e4440949419a40d2070302e10b0302a5500c0103042d0500314040001d8503501190414003650241c690800030b90701d83d0b116170300703a008105001c14003440e8a10100d000d180d0884400000304101e006aa141548400c600b9082220980094039900344040c0800c08500307161800500500003208581d0800302c0d00070405803120809403902d44140e5000c002e060600405500140418644c10a610112000034600070050405e4040000004d5008030000404c1d0030040202c1d20194481e03500d00c00d030034401d58201700a11401210f00301c100400b00109800d42d460306412140102841002050b2601d0603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 394443210 1250 394441960 394441969
    0xf12060a0e01020a08010e060a0b0a030204140a03080d11040906230405010602060c09031204060e0114040501090303081f031a091606031a0603010b0c0601141507060b0d030e 76
    0x9410081d030580c4100b00840b40c240c2d12042503819030b941074442c51001e4480e1800604100407640026811f070100043e0010b816804d0f50040c4103d613240404032080c110240100400c0402d01d00c4050610b9a0030060215418034030b42c40070071210001201641031546640800c011912150415498142d00300a10ba6010f000c140410a1900c403c86090100e5810000c00035117995002d01070304036101d800300d90400c2599003444010240c40351441101c0e10340740e50b80c200030000101c0300328950110b6401d122022500e22400100d40607070300c040c9c40c0c01c0790980c0f9555040b00d0302c04004164114140410100c82d121340c0e80e1200d200000c501408501320020303000e44901c0d0380d244015260b400144d001c1c8800d0200780384800e1350341040311010f050014642c0210500c0d1605000399001c1c250380054000008100c1c000c245d005440e00c1c01821040700d03140e80c3c80d594110344820b007480b41c2651212040d0032001920811340006d00940f84141c0c03011030514000700100300d0304d0505140840109440040784c1030541403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 394444460 1250 394443210 394443221
    0x30b0106200d090608100f060c0305090603070305150a080607050a0e0d06061e060804110105070b01081c0e0f061c0612110105071a07020717030c0f0622020f12060a 72
    0x516040d1b24501c1c52802c50b6020b00708590f44075801c28880ca5205603803c0c035000c0c1d0259044c0315401707814940d030391401040c02002800200c2e5540c0c0074050030125000d250a2000a11060703c6107500244000d440300c1c0415241034024079074031402c102d0105412500c42d2543d15072101861700c20000840c0c0c8906240c140405440081c2070100da0204c0e0701400c120050780407180c03d0f0401c1d044055160089921801265140b1500501400c083da11000008a04400080c1e40b0441071682603020425001418210303181c01c09408129844240c034040c1803140c0c0b03010744c0242859450402d200c004020203000e10001c1d11b00e1540703e1042440e2140014081c048400d10400040400740307020b40c42c01c01709030790b05240300141c81c41864541034031100003a182c5d4000c02840000d012100c0c0100b49040803441500d41d81c1e07100003400700d058040c45010b19040c03040040c030340d80030b203039201c3c400c040c001c004174038100d070208807448140e074400d0722150800110344550801d184100c80383c0d400b40c0700d9454400c0d510704c165030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 394445710 1250 394444460 394444471
    0x515120724090b070c050301020c0607020111041a0c010917091c0f0605041b0806100801050603030d05040611030c1b0601060c020418170304030e030304030b0106200d090608 76
    0xd820031035081e91a07845480303441980c0e161510151621241e040c21004429103030841c0b0307019840051448c00c1e85100140a07817103203040d90300a101c10100300c048010180520b12038407000111640401c1808526503015010110401e0f00000703c095007038450220f45010400b60b44030f040c01c00100403103181070210300100c864076240340c0c011810103940c5c0c40e0f040794072031105d02512559540010038100000d0795541101018204c000d00c2440d5201c156480d25481c0684540c2508403440000007108501070103280c2c45951700a01075402d04640745100d8002e031030014011141030307554805070854044030340c0c099030040684d04d40454031900c0c8194409034986081110103400d0340100700401103942d100442c00405179040c1c60115220b0002c4058a8a090f041c0100805542c0c64a031580038590413040554070884c0255141c2c1091601031080c141c40f485a0300014100c003820000501040d400703000011200d20305051410381c055000b19a0904003200341000b940040c100c0d010400c5829400508150400c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 394446960 1250 394445710 394445759
    0x303040f050715090e1305010501060207050901152a020a0e0a050a05010f050409030c050d11060a050f040b092b03060b040810110f030906070f030903020d0305151207 73
    0x14003a83d1010308030039101d21400e80802c1315030001a402000c1038420b56403241d40304000748029616080d0194590f90755004107400781101c500001b959a2501c1031050350300f4219100c0458500514026070006c09600e01c00e03038410310307440c882c0320016107a50050030001c11208103a95000c0c1031280f081800c2e640c1c090000c170005030500005004500d0312010300350440301d0807a030001d64149a854140e551b4034003a0300240c0705010b03a01032300d80166000403c00d00302c49640303001c5e0b4400365204020700085030410b03900102c0e4810b01400103400640098480350b00310800d6070403120b6484951849072200320043e01c880480810307289581220682501440015024807003c15040904208007940d95042003031400c0d01c61600c4440180c1c082e080c00d03044885192500100b250303640350007500c1a903208400d0362044001040c000701c0c3c104907446032240711440c0f64103a001d00368501400c10120301400002c2c103c4114846200000c0030150f035142038055004650344003401e05146411640081d03200ca6903200303c141c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 394448210 1250 394446960 394446989
    0x907090c02151f0b0d020a0915020d1209020616050c041a060a031503120206060103020307081501140d09060e0a02010f111c0e15090d230303040f0507 66
    0xb0440469112540700201e40c03c5009050b108150140c1841c0803a403001c2002c0700001a0400c08000075001050b140710f00c1d48070448000d54405410043c1d00900c0d01c0640140c0104d0074040400313214000c6541c02c483c486c8004151420941c001942d82d03030024050b84400b00000481d0303c100301060100003504041110100300d8100e0554070240328101102c000f5101351400100080c1540c0a070b40b10780801c036502d0303000c0d6203807a80782e02d042040d03a049001000054413803107000a0540d0310030300032644100c0c506c0e60b03140740989802d84a010707805000b07904241030102000d508a400031662001d00b4080310040d4022a1072074403805d01c1401c48480810b0035995070484294140540d8100c80c00d0030301c5900c02e140c00103941c85c00c4244a400c0501181c030381c2d030704182d2520784030b030000b64031402c0c0d0760b5814001c80f000c0701200d86003a1009124418502219003080d10388031041d0124126040c074458506e07070040320540d84180600e0250455004071400c64426604c080c0c8542801800c105e114040c28000d00035a01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 394449460 1250 394448210 394448233
    0x60e0102090a080d0210051e090303040c091a0d0c350102030c070b180303071d040b01021903032307090801020307050316020c03060114040e1209060f0c060907090c02 73
    0x494410314040d8140307054851003c140040048c180c49080c2c0b0512001c0e941c084c0c01e0000005480e0b07402a42c00362030f402c007540c030003040c1411244101c886401c2000c1c40c50380d0090341c85081c0411608200c800352181130342d01c0300001300844100060740c1440b449030a001c0d003107203019a1103160f1101c03e40300c03103440b13038410303c02c0280c2e05903400103c42c400303608440064119502d80c0f62440d003000c4401d90341c420320b000110500000350340021240030400961008080b0710306124080c00700300d0f00307840c0d281401a40007509404e0440340401e021240300d0702070310303010684d025500c407170103281040030740f01522220310681000f01d4140c1c0600044040d0065000a6107542441080200280030180c50241e11155042c81c10300801d00811001c10fa1000c0070303050320010769541992101148414000034003075420b00ad9a00025000452400c01e29804005964100011002840020f41111941c00b244d440e00704400010100200701c107030300c501c004400030304049080041c0ca10a0f0394030a00d40c0015948030408925 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 394450710 1250 394449460 394449463
    0x6031404150506060c010c0305060f0d0201020d110c04110d050912030103080f09030a050a03031d0703060c3c0309081e13031b12081213060e0102090a080d02 69
    0x1c1011040c003184a8030b90400040c454807900f03e040e0450341c0390003505130f4500d4054000c0c0b4420481100e40904c804204402d2024941d03030307a080280143c000040c0f0340b500d00c2c0215003c0110803400c0c01181e00054000e008030302121104188402240b201050942800e44240aa2075001085c6800f500b204482401080c03254041804000d08100c0c001c2240d0440009010545a030604010216104858141400c2d034542800305130135000641001c005010300d020000350039454030320110003044064515103814004003c80c804110402216440003000b0a001c1500c605103180c4000110081005202c2e5007080815000c640c0b1042c54100703145a00442d5051054a5018900200c4041d103030080480440740c92190400c000758603040c5c5040030042c402c450b00d040c0bd049000c150001c40e03072a101c1c4900c41c44000d100134002d1024404200c417044540d40b1001c082c1d088581642e4210300003c450740c03084291520750000001a83d4007007807071743d402e1520708820401001114098010070b506204000e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 394451960 1250 394450710 394450733
    0x50a180305091302270108060607060f150e07020118150f110c160503030313020d08040308030c1c060812070f0b04031106070e1c020d050d080106031404 67
    0x601400004207010042d625054014821204001400c41d03607030780d2401c0404201456561485108490a140c4090a5001d00c00e0785008403402808241003003810b40d15031f009030120f81c0c407009070145c6036554444044020812040a071062500804052a01020003401c40d004030282c24481104006040040381e81150700c0d944d0500c0c03040000c1000c0c642d2001d5200a0f1418045204d40044001042100124041410940c8186801761440c0d2150340708209a640d0100f51101220102c028824400500c0d0120140c0120340c4141c82143c00c0c140c0d60b4941c034005420440e981c080d01100054894404025400354018901245508000f01810f18646942d110141c407101d03103070b0f64030015000f000d120803c0c4d29910125803000394110305140c640740040c00100810384070036081c411240451156400340b400c80c00c0d098000341c090800700c40715980b0442040001c050aa8000c080810f6080105105104800540f851901c41c0724665242000040841d84481e2282e0b2030644a50144000601d0f0038012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 394453210 1250 394451960 394451963
    0x1410060608072006090102130509040c0b0c1c0315060f120e01090203160e1b030613140a0b01260a0213081605010314040302031902030915030901050a18 67
    0xb410503540d0b041c0e0680c1100600300040100344c800d00040001c14181500201003038142405940207403a0340b101804a50300069400038002d44144409205289010010f02445d100352400c4800807040020001058880c114032100003945400900c101e404242c108003000b4011440d100260902c0040c0082c000c61290100140071601c0c2c048001c070241003500318460741c80c3c00500b40e6405070039540c1c82c0c0d011403c2e90b208400e81803e80400240c04901e404003000105071039101220300d10740d41c1c0c10030448040e4007095204c50040d56001220052050743c440709110321a00c003000601550440009080c0400c260106032041620300307040b894810515184e9074004540441c003580b80c60900b10b072400e0a00320ba80000607180318120143c000d40c07080c800c5010840d03400386c0781080310031000c031100d2580304422100640540d00c10081c00c10f4a0300302980a141940103441500d08110740c8400182c0c0b00301d5208824580d0340408818081405000c0c0300d12500402440410081c04003203c5081455400d200e00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 394454460 1250 394453210 394453217
    0x1e140d1e0212030a05040e10080a030f0212030406230702070501110f060c0a0e03010207020603010b0304060914030d050c181210142203080a09150603141006060807 72
    0x40e040031034845260718494203510b041903945800e40c0160080480e0050320401d6203050551000c54840342d0804000006e5403550005040d90000c0e985054400112607000b94045100796a10050030170b11000186008900c10301c004a038070380c29254040b1003c86c0000e900b029105c41a030034041d889800142c607204451003801e152607580750418a441c20030fa40c420204029010300070820040080803002003080f01a15207a21854800c1301040c58204c0c01340c0e0740c00035002101040144804110000a5a40315104031008038240c2c066903545141c0c000751620042440d8408179148818001303a00410b41d0004100e1249030400407104081c00401240742e1a2501030071007094405003640c41031145d0030b001e503602d4106020007070505110300802e0604883e600c800081e80b0f40545199405403604255081e016580d00c1d416440341215080202800e440880b402c16240440000d9942c0700c2c003c600045028034041c820f5159a50000780c00c1030b003071a540c025003500c0c0c442d080c000b5a8110841c103400885519 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 394455710 1250 394454460 394454513
    0x150406030f051519110d020a020c030d0203030105150306030307060f050a0605060c070303050703020a060c021c0203031905070e0d080406030501170304140a12120f0504060c080a091e140d 82
    0x40658217248100c08200c101e403400010415074144d0000744241045c2c400740d040780d83d41a501d42d4101d8490000f030050651011804115014032071030758010b140c101d100107090b40c0c64008540c5e6a1802c84541c03c40d000202074a030420481098003602c11007004000c29529145022102850f1640b10a0140001020300001203501014184200312010781d41c0c0c0d001e4020403903001c42c103d007c1e5803080790f102d20108a000900780c0404d042d20204c2524082c41d841c0340100c440e480ca592000c00605801040c440800ca0035400d2809191b40c0c402007d06e450b4000da507055540c034184603000b401d45005030071112804007200340200415030300004031021981100044c009480300d0600040000407503612030407000365540000301c244034016400c0044010309440b82d414024980c1d5041c0c0d81c90103144100004941000d40d100301107002d81c40240900e076130303501e0440e0400d9104c1041c2c861003070070f0110203010351001410500c41d03003284a0384007034040c030203c03104c50940c0b0346541e4103a40845080c4944005141c2070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 394456960 1250 394455710 394455731
    0xa0b030a02070f11090c070803072d0e0f0406050102030f0a0c0c0602010b030105061c150f0e030307090602010501050d081303080d091e050a0209150406030f051519 72
    0x507416550101c1c0e01000740201e240ca07a00b4040007800803610614465210070010425000600d8215845e00c0c0c5c5c0f14404500790f42d2002d0054840d01c0c140009814106006001510501595614403085070002c0d1601569040101e080c00420840d21540501883c500b03030b810b008680e000801e689480d414840100e030351b6145500201c51104400e0002400840c088601286254064000049054058008100c599100410410031056032a40a00c5018501100e4008141140c2041210210484010031512154441e103c22038164001105280e00003000b40800c1980c0302e842c44008220703a1000340034550401002524000e41a84004e00035400010158003d0701c007050558000d54100e0a500d496099218440e405082134401c21035500306e4041c01c00c42c5c64000c50801d0300c002502b0800030018003030168248030000e00041c0c914400484151700d10b500e40d0391540222006140b24140310442c0207042d02e000d525000040c0340c619030407400003080080545140140c248000305290307000c00e507540c18 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 394458210 1250 394456960 394456981
    0x101509050115172d040b0a0504020603070e031f05071b030f05030403111002030106032406140d060b301b04030228080703080f0a2a0b060307050a0b03 66
    0x30400800040701d0510422600c010134400a03032241d40034a44500036a600c02007010100d0f48212402544858140007290b140c40c4141c803503800184004c1c1c116000d021600c1180803804035480450840e02e03480e44c0c10090020b0340b151015040c1d2845010507100100c480d07801a2001500e00c1440701088404000201032500c034100d00c9840c181d203c03083e514120740132000030001c1d50090242c1c1c0c022074204103d000715803041025684000b0000c00135913805c03a040103000c50f6038080d4000d400441100034801103525a42034403412000340701035a003003551129240328158904000c1e005e0804d401e40024000d4040130903041c285c50b030140700092103900030751080c407007948180501d80020f90045490911012141707ca070b40c10b181d602491001580209a43c8e14a180e512100c50000600480c41440000c2c020610300340540641c01c107a0400f01040d180c14a45101001c3d200c60407510b082071110030103000d002c049124145c0044d0164054100c05082034042036030320032184140340c1c0c42d10000000078241d400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 394459460 1250 394458210 394458241
    0xc0a020d080d050f07092c0a06050a0806190c08060f2b020406090216140114070f091505040e0408090607050d02190f0204020c10150905011517 63
    0x200000030405130800400344041c4007402c41c0c801c000315500c0000807030000602062201010840b643c20030034641e500c2e1455010410240c03640c880152540d10100d02d135550201d4142c007828001000781454980407480d003840079844c00145082c01d180045030071403d81c2c041e0080c1d51048040d01c8104401c002d0002080214847c20040c00311410202c0300044a5230300200140141c1d4000c840078001541c59182c09012403142e48041403402d6500c900540010321800140c50313209050100021302e00084d10344120641c80100c4060000442c0b402c0c554090f00c1d005006100a07080e17083e81404003110300440940244954000e100c01d4100600002c0c1c20810340900315407240c5d074003800076a15608281f5020f556985442284d03005401001c51000d03142c50400c8080f0300031900310424504400c055020f0000a62003881800401d0081e440b640242da00507009000520310350704480f40e0780510f4810b10b00304994040e08240d05621403a030f4440c20850348901146510350110f82c14070b02c503464041d000c52400e103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 394460710 1250 394459460 394459477
    0x1b060501090617031305090903160f140f1b0301021b0718050f07030216061d070b0f0306091008071e080307021e01090b0721050c0a020d08 61
    0x281480000315480956070803040c21901c202100c44006425610010307183e01801c20140c00081d8041400c000c18138150708896040040542600d2501d01d1071040e10500f80380c1c5080a030383c070702e64089500b01003122800740300c04c3c19a0340070040d1030540700c84c0f070040f500c40e0074080c604000d01100500c01c0700a90307402e504039003e85e0480c20440c0680e6100c06045030720b03005217203c1d8420b00381803a00c0490500200f40246486031007010380d41d5113166503040c0290f009400407a1030380281c0f521140c921000542922980000d084401c40743e00c0420003401c0b2103880c00715150070042540c681445004004040c4c501501e0700080f0032103011406684414205c00303030760300690144000303219240001a9144c1d071208100301002c2003005808101d500c42410a503640301d010300003500000c00100390141702c1c100c03051030050048145451001c84c1d64802d01e94446803c6a00f090f205490200d0b190040054400324041d2103a445013400d904050110910076217518000101a0250f840004076404101c0100c00312004413 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 394461960 1250 394460710 394460723
    0xb0301090c02010509150106050a1e030603020307060203071707021504090f05100303050a0c050c21010e070e130302210307080c0f0403060213150f0906050f0301061b 73
    0x9680d9404810064401ca000e0840594079040101d03005040108030b014820f000c515844c0d00c40e07441c10100310351692090994404004003440c021580c0120791000040e940282c1e500481d80c00e0560041504200c0268000015503000300100400505a0080221145484079049032a85200d00224108100201d507240c0303d40c1d4001004540071081d5405040304200e10041004030b80e0310b500d606001c1383d03c54080a008200203100e8218000d114006408155103e4420364203230319901e0700820b5620307503d000004640314007034018959119003407251010b58001e4000901c4034030314150104c000c02c48003420b04e07420081c500d00100d040c1402040700381c000b05624001183e941d400d40e244220b00740c00507103c2000140341d00380890354090390030301070341c2446034000318052034989117542d803d00070346c010307a0303a488400341140c0002810b4640b8000d000150507245c44080d001109604018200da0190300070100740681400b5940d919150802564151102030400040e0160040800401000c00400c000c040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 394463210 1250 394461960 394461967
    0x180b21041a2a04050a050d0c051c150507050313030c0c0b1215011b0c05030307240e0c0609040921030b01020f0a0f0f06090c050901051905010f03060b 66
    0x545503444aa070000c0c4035403600b410742c4010341c1c80c402c1c10b50f8411403040c0ca901c501000d030140f0807031400b141b41d91210b622034504812450380e200301241e1907005408032900e003130f44541030307a1040c02900340e4031002a02e031994040200e03190a4601815600020300383c115034a41880c010300030140114402004613400c105090000c3c1d695811241071544802c0e65821103000401c04140b54000544583c0d0900105858405a1080280701024070a0f4141004c0c0e481c060308180c0020070341c509000520f00c0341e001d1051500e0080d2000c2e09249082030708010316400da450300c54100885000480c1000c503204085502c0340c0c0d101c15840000b800b0b08840c1c00003a0400c03100c0d12003594880350090404803202242e40701881960210001640c503020407040d100c4642d04030084010001e0403c2c4d8294120900c104500343c500f101503151402203815540040300e040c1001c0030180800c1c54034428190062904441601d03c04110a8054142502d1481558140000c0d90b000c500171900a4000300302030444031807002c0d00d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 394464460 1250 394463210 394463221
    0x1407080c01020d060618171e0a1e05060604092f01020d14040b0c150901050405150903270d0308010e1305060705160204050106180b21041a 61
    0x70743c012001d04203000c2c070300b910004089000d0a0701815083e000b407042014103141034510040ca03010f015540c02c035070007298487c070504811a203899482c0e20900d0010000300321980707421183c036080354082c0c800151110342103c1c00613100141d00e0b40d01c4041135030003103071401c130914020207084181d030000c0050301401c800b02281e51034082130b40110350600760308848051107490310660700300f540c0c1600c007194200c0802c030a200b9880198014185c2d440381504448044a0501c0c4400038084103035560080f694540e42884280107040200c51f00200d1100c00d40b07562410948110340c1d0f0303071141c14500841c2d8042d01394001e0380e904980d02d07808444003020b8004170030f40105141c02040c9820074010500c2c14142070001c50102c2e107031309043d1208142e000d40104141d4646d100140c070150400c4050441020040c0116001611580100d500800340fa0322070040c0c20150120260201c0d0a6401403d6180414042d6800d501c101d5044003028034230020f50b0010986950610074001d56943d80301000b80160b03607040c001d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 394465710 1250 394464460 394464463
    0x303030f09062d0203060a03080c03090303310e130c05090703090b0906072001150b030402011b02010518030c06040b040f12030c020405190e0607180302101407080c 72
    0x10402402e03508882c00c12843d840d0369400f2404240c032015049103100c2c9003803000503503503c010000c1d0380007142260308124180e1700091659004048401d20000e50201c030480742051035044010720001e640c825800305090140c036680f6090010500501b0070003404502c414040034103140000741c0005404c105d0032346400400070f009845d030036004881103c44d0f40c00080400c0e002207000c0e0300078a030a6540300409020f00424001e403c2c0c0c2e480810320350355600c424031400300c0c0111020400030216205059280e10b4540005003070b148200c100c150085000d805c410b00180c0e80312088441041004071101086036a01010030318140080c0c00f0180c004000044c0810f042008102910450784402c40217140280c0715504100040234008008010406001482c0c00500e07060f0045030340400006014240c3c070840b005004140d413652018844960040018080349941c04545101041c542c00c44042c080c1c0d20310340c040745415034200106020840c140d40782900d2a68403100b191142604079400c2c0303490b10b40590009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 394466960 1250 394465710 394465751
    0x40f0f0b3303090f030703120b0f0d0b0a0608100b1207030b07080a2a090603060803071e02120106050a050a06020c0d0224030a1a0a0303030f0906 64
    0x12840707400c080407006040c9560310106207400411201c803400e0100c58030030301100d030742014000c08010701031969542241c80e070030009004014040d56030043c07044482c070100402c40e060242040d004100b90b82c0b040140f621760110318641a5400f00c16050030396113620944000701059000041c0c10700500300d202c7e00d8110143c01070115031500b143c24405e00c05047e1080c0d0f50714201448010300001060340015600307800303020b40d01d074411724860020a29590340c10710f0074064916107080c1c3c6034000c0320a0f40000c0d80e070340c0078204d00d015010300d003820842a8100000940e40303000c0c404005000941c0c5043c40040c124005d402c070070f070035580506103003d415610382044d03000e0700c9540205400398071101d5002403245403c4800d03030b0440b00c20360003400d241e40e59541030200700c882c07460050343c0145003000200c403c2e1f00d20004418102c507501c0207080c0c480c2441c0b42145c06442d080751900910350b1607403807224020b5940384102001c0341d9060400084540b00421300c0809000341a102a240f03c2c50001c42c2c003020000347c4c004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 394468210 1250 394466960 394466981
    0x30d060e0603060a05041e1b0801020c06180316050304050d05060411040b01050703030b150d0b010806030708060718090c0c05061e01140a030602040609030c0e010e0a0506040f0f 78
    0x1d8a00340c1d0744800180d0111501124040e241f60b07029820f01d003085440780c0d000c40350f440c0524074082d1010385030109492403030241d07481580c085c0c1d4006026461b101007804150b401640703018030154030710080c2e190b56a4900600b08520b0b028210281860100304c4208121401000060480c000d40e04650a05c20b40fa050200d500b60f44420b05082d85942a282c144a41080780405031150381c140604c07a04c045004245000c400398100140a06809010500c1e05c09401e98015654000c24050840c500040030150060452030082c1e1000f1814000c4030408104154040c11624141030800b460711018580054603a000402c1d040c50700660429450344040d801151700d02a2085071440c0d161041b10301e070683d00d030b0482e08241c1c1e18000f0042c442c2c0d0503074121091090300c0007400964107684a85552007260b0155002c40007007610b05904000304180c4040c200c000b0544c01c10103007020b615000e00100f021000900a03c0603696a0001032000d548580c030282040d44010410849820001c444c43d0040c0040b11a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 394469460 1250 394468210 394468213
    0x201140a140106050403031d3012120103030305061f020c18130636050c090717040312050f07121a0910051e1512041202030d060e0603 59
    0xf09415000d482103400300e0340d05665540b164260390341710030702c0da9902c688080c1d40081100c901c0301c140500000b07a400e08680b41101c00111619040ba0b19207081d484c000800908a011710041c80070320b035502310f202c0c11a03400d8140841d4560b03449000809501580818100100781000042100c55001401d07418124059608150780580040c024091103400c503000140192005581000a2880d4002160814051482400c0303004c81d001c010000070040c10350356440a89400c60351090000400040300d0301d500c269000031007400c2c80300d0003d1500d070104155041300c110f047c010404041c032629202d81603030305a036010000da080c440d01c031100400c4141d820100060349020070144140c1180316490350f60080f5507401c1c80a881c8503080c06400751001b004c81a2190605400081c187c41c0c1c1000d1803061034070040b2000d400d4210400b0450750075081042042a074200340b100c030301240402900703603400c95002449980540e82150b0103c0c503620521601485290a141000a0381d003030b481c1182d401342e0002c80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 394470710 1250 394469460 394469501
    0x3070c0507051509101803060b04050a050f0112030e060409051005010e0d0f0809060a0504091104030b070c140d0207081c0507020105131208190c05060c0a0201140a 72
    0x1000400c01c040e03c1500c0c01c4079001c1115040700d01e4104d1141c5006400fa0030b01c3c1c0c3c05517440c85c440c0120900150302c150788494803120b1305105c03850305100c0c00c1d6100a6002c0b0070007042c00c000d1800203a000d014001c0802d89440d402c00101454011100c401c00b22100078149a6030300c2d00d03010030401074042580e080d20724085034500403c2644c000c0c1c2e40703206002c034041c24680d801c44440e140e01d50300c18806c020550300c0c600304000c181c505490352801814a0501510b90300c0e5034624002560041340d000e0f140100b5100350500c01800003ca0801d2296000b80403450900e46156203800e090211031400002141d081c171a04401c203880e16000b08002045807030032416101180310300c3d044038140440b0600c820002800811104005600820140c1030105c1207003180f1401640f600348044010246000540701d410303000c00c080c04070030509408040118100e18080554021556442c0d0380d50750040c1c04108034070004141c4a4400c0d00c04d40c40594003c2050803150040d0420079034410040c1030746501800e0050029 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 394471960 1250 394470710 394470719
    0x7180603030f3209030106030b06090a050415020307031b02060105190810020f040f03031d120a080d090f080a1418010e010c050a061b030902180603070b03070c0507 72
    0x80700d03214800001503040407001088092034a2181c400f4101c0305034040010302120500781c8091142c0f0000d14403444102c12982408810810010b1006045402ea10701301001c110019410800383c0130b441500341d40c096120b8079036040a0780500b480b6100011820000c155051145038009503440c1291426500884801240c0e076803c0002040c600a100c3c0d541d0140051100113109907000300401000c2501c1941446d890390758401c114085d03030b80281c0c00250030f40c01003000884410590007007040101c0f2200b2905403200900c03620380d034031680d0280c42c1c44004207020b201c2e01d2041d0069190280c0c424600608464180360a40e901e030040c054540009a80702082410b034400340e42240c2051008002c0d82c0c120760704107801110341c0d46448240c0e504000580d00800b001890030400070b80e5180c1302e04c1e8042051804030700d05504119540c02e42000301810040a0009030b16462071020359000e50141c0086a6900c0402192804510341d200b020005400820414041d0740b14000c03101c0701e84510207030b80c4d403580e55 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 394473210 1250 394471960 394471967
    0xf03030506040b010c120203070b07020303011a040e070e0402091203070b060108010302030a170f0f0703030f15091d0303011d0108061009050910050a0603140d1403070207180603030f 80
    0x10b440040d4045808113020002040c40400311501200d1b00703104513403a00c0002d64078000b90900c00c0d03500d600581d1010006000100e544004110001d1003940002d0900703207094282c01d2040806402c00c02800030100342c0100d0741d243c5404a51030100c001c2c1036040b0240a00320019500e9020b050203413818004417001c1050740d84210110381c12260000d004020a01d0300f503c0e8820040804621005031400410a40f00010098000303003c804182e0306216403101d0381400c014080d650700401500009107820f0300300009840740c1d4400000da800042c03001406500110012942e48099000b044161102000000e01070080f0907140001e001c1050404803642d0f130354002d43d5a1034400b518000d88040c0c201d6414408520158001c44d030010b044400c541a01c418034a40008455050710b074050801c4e00e1f142d003801480001940308000d0002c02008041014010a004003952011052014000c40010105220700d10070460170b809000903542120301c00440554020060000307200443c08a4030050003000120301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 394474460 1250 394473210 394473221
    0x70b07020a170a260612010b1305041203060e1303090504020301030822080309270903031e1003110105040305010204060503181b0405180609030a0201050105100215060f0405040f0303050604 83
    0x1440c07040105038030f99104118060745c03112044a001c1d90380301d2320303018550b07603c0008980000f507503440001c0c1800e040c284801000c0082c03400700c1c1850708244003041034100c0c204c4107c0c5e001c00d00c624181c0300740100d480e0803104c41c04240d0043c0c0c0e004d40048008001e0112403402441c44800920340703100045440b0403003099940c0c543c23203080c08640040c081c0c0309075400d1031840c2100348210801003442480c625500c44007101d20a0300c030074110b07900200c1000301440c200720300c0310300300c01105203100070b00e107400300460421031114040102205a80048c129585e405001554003645d40315000759111901c07944010044d0708105c480c1280280310a5025a40c000c0c086191011101440883d030101c0300c0700d4081c04040e2002a03c0d00012100000c0c032400003107402e01440b400387c03880340040d641d201c40700c1034000e0940304183c001600c03c200c0500c0c1602c0403070b00000c07000d172005000c2480910329940c583c00203a040300014030365a0803504000c00c21041000003041d0341c400b90700c6510200074940b6524140b02c1100d0303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 394475710 1250 394474460 394474517
    0x30a0509190210050d020d0501061115011502030c030408030705011a06030403111c020f070e090607031a0d05010207020301050f19020d060b07030503070908030f070b07020a170a 78
    0x200300c00e44040c0581401480c00303c4030300d140d040c424038000340050b4a84c2207038003a901403448181d0f03e0f00140070b0a9845405200400c4400c0300078401c203003500b0f60051050302c042c4a168541d010520b0002200c03402401500d581740f42031400d4a48540e034502d98a5201d40c420041100d040d440c012104005554440880c02409400703004c181c115a40c69906403100401d28180604c144628994004855114543d4400b40c08456000d0000c10034050401072500040740c100c1c04090b00c250003040805070340012102c0d8010540d18000c1200406210110303082800c1141e081e0304401c03c1a190b02c02d11805400802100c4c6c400c0c0c0082001d0b80d601c054039a0501c0040d5a004891681c1e400c01c03c80c0c90300c4caa0050903208e150383e40009103683d03031034045a8480d407107544120003103a004002c0101e1260041d1007c0020705180c40a5868040c0915106180b48a8810014070101003400400d42c0c17184200180c4c41c005070b001180c80e20b0342c42503030305600300c5400c00020000001c07026100c40c40078902000403260b840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 394476960 1250 394475710 394475743
    0x3040e0702060c040303080711010617010213090b09070f03090209010e0f1e0a0e01061d04020a06030608031b0c030d18050312071118150901060c0308070e0a0504020f030a0509 77
    0x3911422021074040449101f80303542c41d90bc800c008070720207401c02c0300700061800f034400059a41d011002841800c4103150f012074034103460082e550140c2d072640008254095100d1410381001c40310cc0900f50010300700340c000a9089034000002064800b20180d40c01e0140400b0031010615070b440e0f06140031001e4407240d644001201001c0400c0c45510070303030000c14201c1c02c1b50f4008a0341588880b1280440034000c600c030702645d24103e0501c019030401107103910190140707103018450300d810034110681da8881c04a100d44c4450000304038040d10b00050000c240c040c0c1004060310064940d9600062080c04001c00c1ea003210049054006258900000c0f9183c40c840c0aa80b541d0912415454407013510740140b100d80e800100c803641c4035404801c41c01e9a1445a2440610307015030000c0b80d4144200c030001608040180700100074442c000c0390f001500f85600031903030315019802c414808003081c4050881c0d40034580050000c95039000e100e0035540510300c240035510040126595050240e0303903c02c540344001a1a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 394478210 1250 394476960 394476977
    0x20a030b1c020a2105030f09180c0a0c060b04020a02010b040506010e0306010b030a06121a1303050909041106070525030308151c0b040606060905061c0e03040e0702060c040303 77
    0x410440b0403110f60110f6501d202c0d5a21031403143c031417504590104001014280700003521548902d804c04845a00e440d101d038004c0d00e0303407030219aa0544d600c01c000c450404d200902008200300890341d0495031100b94042c001f9916100704460290180c042d10403100d20460030040003540d254401d407020600c120f40140200600d0f440d000e140403131540b01800040d80d02c1d448140100b41c050340b8041312400144100303180c1007513100c042c0041804c184081c1c0700322048100c52141101003903002090740c1105404580c452030315200c900c0c00680c0e050448105035001100400c2810a0020214030003208950380b04240c80c0801e004085c2500800043c0400bc0c040344040010911130321072039010407060100542083d03100c20550b510415160b06108040342e0060016040004004d0580901c00083c041c600b0000e540302d0070040011801e003c0c03980720303013404100789100300c44200e065000840410303007680039656030f20340f246000640130340122800c030098456800480c9103150741404540c00c50390181d541c000b1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 394479460 1250 394478210 394478219
    0x3020906040906120b1501090311130606050403230d0804140307060e19020609240f0304050601060c03090306050606091306090c11070b07020a09020a030b1c020a 71
    0x290054605150421801d00011902941c00c2c410100540480c600002010341c0d01c2c6000989018010003052085181c0703140c0490a98002201da82501c4d8003042c0d00c03039010003610109121003162000c0d004058200743c00010141c3e0040010029a070180500212040d0351a0039244002d5a00f40021496031250a043c410544901c2e0a56000b42c4a001304031075105900e428189150840c075010341c0c0303055403400f80140b400320400000450701000f54582d01010030b680c000a4860084460050088507400c10b084001c049081c0c16204511090f1f50042c7c40786051001c1442581044a00700c030207220b408000701d55240500c1d038409803190300da038501500b14110303038034140600300c09071895402c6241842140c4490f0384000500c681c2000c81800098424640090101510b451038040b40a0092440e1102c05200b000b01d1450700f65010782d0070455450381c8500c00305200040a03440703103200c188003248a004c06540740c0c0201c854030500b180d504000300349080c0316107450124180020340c0309448100c10030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 394480710 1250 394479460 394479467
    0x12070804081207120b010206090c0103050a14011401030506010c081603050909090607081308030f2208040810022b0f020c210a020d1812030c02120c030a03 68
    0x6501500c90990241844076030480114920025600f0b1000b14011861200f0030551078424401746601c2480200503604000d51101e44903440790b440d8a0405440c2c00024950f41c010390440b00100746a4100307283d940d80e4945c0444520074222038070900103400e040120707141d0b62190030600d02064100156a2070034440202c001032046550000324240602030045440701d55401041c03500c10f403005005041e0328509a0350003032060400510b07180315182d002c0045000300301c03204280c95022100f400c1c0829151910001c100c41c000c1060034280f840321419450030108000200035004850a020071922003415540080c400d034010210746036000d00a0380380000b58503000c51044a04540f02c1e010005100c0a01c1c4c0886060f64803009099206038000f25080c11049180a8403a0380f8154000243d401e00603080402501c4510b03c081d20001c00c441c66424405100792200707290024440c07150f060341020903502d00a004035003401c505910407110041c641004070341c007050406003201c0040180c02d0001c580d65003035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 394481960 1250 394480710 394480727
    0xc1203320315130203040b04230309091e071e0e060f0a0c020a08011e02070b01051203090409030806030f0705060405100e040204032d1e06021909060201060602031207 73
    0x9507011026030920f02c010182c41c030080d4045c0e401583d41a2039880d0504000d2881803034803201c0c1c1e00200d0700c0d0303000d806e181e0000310030784110144c02c90f1100420344400b00307100c45000d0030035000d610300c83c0c2aa040c04001d036007020f152203092080d610004000844a075040e0b801d24003840704180c10000410241c105071420758020a001c5200d41002c19010340345d900495070500c180c1e00540220783d50344207508001c0780305c0303900c80220702d074078170f0082d07180601036501c035a4092018403480380502280b441c0e28003014020310035118200740140c02041303503078824103004240580a5800074003d010b001261000e51201240950a90390007821061500d0710745001d20603c044d000103500d04110b03400381107401690b03c0380000c1000794001c602543c1075404032041400c85071241e201446070740fa4802d036000001801d455145d12800c4103140d000700c000040c0c1c1001c20180c032a412540315448008032100044c0e9400c80750020640b40c0c0c41e8003c00c107482d283c01c8180d80d20301c2420700c009060741252001501d51403061442d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 394483210 1250 394481960 394482001
    0xa080703030e0a060c2a060e101a152109190b0402010f090e06041d1501171f02030406020702060d020403031404120f0c12033203 57
    0x180e00c03105803142c0c81c1080310f101004c482c03203911415a01e03521a445010a80c11403c02c084482ca10081031400c110700b24010704005000a07150002c40e00305035014030807189048440102401409110f030681c08503070071142c05a501c40c100090105445500617020b031101541d05801c43d02007642c01031000c41d44080300800b006101d108501d1035201d41036080350500342280c8582026134103820988005822110703003103140c800b0090580020011800c0b0311601e00c3e000a016a00054074046506044100c44001036201030540718103040410710b03d460f0400541242c0070780c48a00c507124100b040480e00c640f294050124052580d890b50440e98200758000d5070840e108080051801011390302080540d001726414420301a40403900304140f541042000d0b00210a82800c0c034a40f40c02c09482078410000d8a4003e800c4007181030546040000191a880c060304824800706a4940315190041c00c400401c00100e100750b142c090000204000340b1703040016001c951120506642c0ca03a594030508100c580603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 394484460 1250 394483210 394483217
    0x2090708011413150807090c05210a14010b0702100e01200a0f0c060e030a121206080609031c060302010e010807020106031a0702010b010216090b040e0d1701080f0a080703 75
    0x200443d04101820281c01001010060542c0a1070407c103442100c1442c002c600510008021740d8031108420310911909a601c5202c1c9000341d03d4000c0210f001304060041c240502101b034001003020304025001d442200c0c800c4a01119080e4080300c1128043c256010b840e010805039110f01c1c2c0c5120000300c1d000392107c0b842c012100502181d0700d4904141d02007082c03d564020340110140005680150151910b0718198000e000c0e4084907600c1c0c9a0580c4000c038045c4c2003040014484c003071114503400c940d00401c1d480084602078182205920b4480d0300085028840201c0f41341c0c0c2174001c100500070300d000c60380c058503400c00c056000d40041d030300d040000342003c00b195a00c403400300c0015800d140300d0590340c1c81048600d949241101001c0d08560b80c4195003819944000007048003881d448a105064403810907010580b180d481011030050020700003420210700440c0c1000104036841003141c1100707020704140040e580d0761040c00c640c803020150212900c0307401c030302240300100d1406802814041e00c00e1030f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 394485710 1250 394484460 394484471
    0x19090b0f040c050417030712030209240406030c17010e0612010504050a0c091e020a02070f2c0103030f0503060a03050d09320d0f05030f0702090708011413 68
    0xc0004040316a5401d40001154000ca13007840040220704145100041c030400035443c04d207840d110114101240c0b46c1840806400054907403142c0c980800c0481032103456002021a000581d0202c40c0b0394209004a130000703881c2c43c1800c0341c0d00340300d120030081c0c1000e607a02c4003000e6401c101810720f013000000d01523a00003803808008038041400f40704061081e070080014005000305494807980001807a807200c06e569003030100c1440703010140f0044139894800941c0059960410140503070030300ca40c90703002c03810b100342031100010a104070000e43e40382c40c051000c22240300c015400e00c030100380c0002c0c04003600140700244103c07003e41c019001903800c1100103044410180c5c1e00c0d0b444c180351040d0910b6007800200c01d0350f82080700031101c4803105642c65081b940880640e04c0001e510b102d08001315450340c4245c5400c1c4042090101c030b1440f0380807054110083c8c13075442c040008030100740d501418089005119007000144858400c1c184c0905030346918000c80c218403a030030108103109454410044141d075540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 394486960 1250 394485710 394485739
    0x33305090111031005010201060506030c12181e0106050118030b101203110f03180105070602040e130c0b04050907051b0714030f0a11191a0c010b19090b 67
    0x60003d035208a000f00d480400c1141090002801c0d41c60b80c0d0300050040106000b8484003000040603501d8079040c0c0d00607a1040d994102410082c04c51030701d0034100f10b000e0010308108050b000b0802c80d403450100c00c002e01007559030717000440b03405041062419481c00206070502c00501c401502c0c581110b101c003590342006442d0511200c4203000b003981180402c00c42160324280c8001480303004484220305001c3d50401c000d03442c603c2003a0450b8101d0030704000d00040d4405c02c01c18250f0695024110000d10b10945240c1040c00c1d204610b01e52100fa14410020380001425580c001d0445068076030140c83e12040e6110380c441582c15410400905100a20000e500c0d69000d00420801005001c0e0340310b440b0304814000c00f0302d0f00781214142d280310980c200e09140d10108500d200c2e451516001590100b0901c00c0307141d2a880486031503080205000b2100ca140b1009101c1e003005002c20400c3d0000030009280b040d810402d8000301c0d10381c10000134015042c100310a040582c003990843d103003e00901021002d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 394488210 1250 394486960 394486991
    0x11010b06040b0705150105031009150207030305041a0c0405011101020702090f060a08010506030a03050a0c0c0810050702010c12020901170a0608060603030a05030610030b030a06060333050901 84
    0x42e800050201d00085070200a01208200c0c200d01c4242e05a0150015414030713020a440d000340e0b044450701c2039100e110141c10080c500c62000c02e10400c0d05421901d030f16003450024041d040954068807209811103900112882c600c000c0c80c010407c0106480c07400780341900644a000680184010715582801072001503100c940c0b5840c850841200c12107000e14158042242d450480e8014288503850a001c00006417000255011503c0e01814140d4032500001c03811103d030050f0300001003d64905680000b09a0301c002040f041c1c0440c0e584003881240d8920b1340407800c03903000369081d40025002c0780800e803903100780e54000d01c8450310615010019110007081c04403030b200d0135141c4da080300c0c0d42c0d6074040241c0e0500744403150b00000c044019511741014003200910b64003001e400a8494940d05884404590017603010324506a03003e4151100c1420a04120004103510310080e60f41001ca200c0e040b610034001500510021f60740e2207094210319666068400500e001410040c1e0366589410310804080c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 394489460 1250 394488210 394488217
    0x90f060403060f0b090108011112061f0c02031b0f010c050319051801050708040e060402120414060a0606050d0911030303010b04091a06040302040509070515090321030711010b06 78
    0x2a0f10102007203004a0000703105203c02c0503800034056915280f00d049088041d40100d03440e60604410440582d10b605000030384240030303981d0031081c0c0307074601600528042d0001e0109078024001c80550750841c004030100081031028614090348040b61142c1600290b0080c1c2c4000c0c0c030203025004607400d101d80c4400e10501f10300303030f00507130703c04501c1c041035882003184800740c0c851402a0030328001d414258141d0301d5003602c5c01039000d100c51020510b0001429910b440d0305450005696442030041d0741818207000b01075088661a41000307005040015082c00c4403030181c0d1045845503170310320f4542000031306c05400500c0e410401b1240c00d0443c14040416680400295010740503600c050b079500c61600900104440344800c5080c043d84201254625581d01c14055404903034043e10b001c906541c600d102981055000d40207154000f84840100030380c040e01c4400350408000c15011aa0303110b9040050368030303440d010300b0490904403080002455003407242c1184030b47c0b20301040c0003003000c9024200081042c0c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 394490710 1250 394489460 394489481
    0xe0412020a082b060812031308040605180301060608010b0702010e0d0308240603220507090b15071509031709210313112b03091a090f06040306 63
    0x503034458600f00100c1100a01c000388101c25001080b070719207050f814645071a80b84905100b0054003100041d802c80d52110203207009903018080680e40e80c2c4500000d0b040760050104032180e18002d80c200045402c0510903031042c0e80040d243c003140c03686442140d0036107074085403040341008200407c140040d2203139140d03140e03000d1294440d8034162400302201c1580250111400b142d0b00b90707802d00c400c0c030741e281c0001300c81c0c015145140484450b52002c0060442007400ca500401500c00c42100203170310f0b101c40d1b00000b0f500008850300c251745003000c44008050302560301d000c2d090303420070712a0488545096000c804824070a040400c1c0340032000e80c0c102d8401078126008181c0c4d03000303c660080c09210004030812041c40501c03950781541020380c1200314411240da00209503940c45030b4072203d5a40ca6040c4541018000b101050810728600650030544011803c114046032024a000c10340d203404400360141e80c0d0040c0761032414252500c040044003004a03500c02e800103410440400440d5146c06282c2109 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 394491960 1250 394490710 394490737
    0x12030a021608190c120f092310090503150612060103120f09030803061302040b04030c03060b0616060b0402040b161109061302090307051f17010e0412020a08 69
    0x40704000054401e00f50141c0b10708081000000003200011620309070322100120034030f450301c401a10117200703443c000710030b41002400ca0b20b4100d20300484460845c605000000585800c40c2d141d004000644455180b03000d40c551640020003400080184c100d2002d502050051005029078020304c501424400e080c1c006840c900c0c0030640014000b6044610a441d1641518018000600d180c56621307850101601061060307107100b40f4028022402d4050300e0161920b0001942c0d00c3e0b6a902c0c1400e240d4140b40300886009041466180c0305152403000d544020b04900f81283d011111580c030701d8003e210402d00c2552003a428070010811101c4000a801d0b070030b24800c222000208113003050468400210300852061400c0c0341000340c035494001c000340e40c0c540c4040e009a11940040006400c014054000070303000904088645000440e5401c00c41001d00d264503070064949800c188600541401d004005441021002180004072140200b846521301403055905d08001356881e50b40540c41610780350401d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 394493210 1250 394491960 394491967
    0x71a010305060f010b13180e160f0e07080c07050304120305091207050f0f030a08071b06030e0a121b050303150904021c140102040816061112030a021608 67
    0x3883c1030381a5060140000c000c00c9411302a01d8111180d078a24680518014800ca08030301c5044c0a040f42c00c07940d801607810041d00c82c003080c03a0b18051300b001c40a104000081c6060100056640304604515004e19902d5a48442c1552000f01840c8540c2c05684d04031107910040200041c11030750b0303d1000500781c0c840e54809503922454800c010720003801140180311070b0004c0004000035aa5000042100c99095605268020b0404d00107802c0002600c4003034683c3d0000244c1030100900030740d02981100344090090903541e2516005c404642e07190455040c95844030780c8000c0440d4412a0070b02c3d10001616007103c0900039a5030200e0071025030320b400c941c0d0350310200600086a084601d04444110700f07a464000d10f00e850b40004405d100f4203011283c021b83c1c2c07006c1c804107201d9011201225103c42c0f4000b5965680d0307a203950740e940d68030010b01c1c0c00004402d400c0800c00d203103d40e88801e41002000d004044030a001e600003240f65001901801341c9540c00c1014150300c103407076640c9210305c900810040381c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 394494460 1250 394493210 394493221
    0x1020c030a030b0306090a0209090705150a0f0c120c1104020c0c03060604020a05180105040e070801050117040803040b0703021312020a0b07081e120432070605071a01030506 76
    0xa90f405121100c0c46a040082000400301d80040d0000842d0340440c1c21a080d0f0325031465043c10b00400c2e400050304800c084540030206140c100c010113500190750b40d00c402c84926954100c803840724240c4000c1c4042c203030101481d2554495080c10400d1406032100007010f10b07001e4001340c02c0743d004e0703400f4008940003169041458902070101662202c01510b040d45070558840300185548a0240105d0081403c40c2110301180d100344140c5014003040d9440e074405040c480d0003d440e814091090034001129444019a60b6102e4042c0d03d0050741d0205165041d51580d99402c810a4001000e03001059400d100307200702d24241035440f8004140800079201c01003201e0040c466614142d800190f20804204568030009a9101c11203514903130b8a400b116003440d13815440c0700b040c810302c075000c00e10701c040740103200070b2000d10500462640500300741d0300709080340f200c40340b1403c040d80441d80d0b02ca508000703c01c00c00300c0c1c0150700500c40300f0f10070f48035810380c0028046003043e441000c4c0c000b80c0c0c65078060410483c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 394495710 1250 394494460 394494467
    0x40b01090b030304030201110c04050118051b2a0601092a050403021504050409060e1b09010501230c0c01021603150207060e1246020f01020c030a 64
    0x50140c0014401445850000c1c0c02182d500c3c400c0c1c1c407000b4108042c8006403202480d0500c5070703041c1c1d464010014005940d460710444081030751020781c50011440c110100d2035810140e225402d0085032000c070a030a0201009440300404e401140c20745044900a290b40c0c0e004405111041c0681015013000801004542c1201464454030b01d0f815100c2801060042240c3c0e00002a5000c90f0f50443d40384040e0b0300c1303d8031403a18500480d8841608603040600c400100b00d2035410a8000c1c650f544200d8465411001640c102c818200f115240c00508080052000d54840c00302850191224818000c42004401c13044402e60300441c82038615400401140703409603410b01c05201c0030b13111040c0c1040314504548880e001c5060807889040003035400a210010080c041d0800d40014a00e8800da80061650f82e4070310b9102c0d030002e580702e80c1c0300d000150302030035040281c0600c0b15170100840401c03850070100b050f040440c80d661502141540f0840c400c0c2d0301380300302c01d00003428240f00040185d41c86810461019 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 394496960 1250 394495710 394495733
    0x90207020609102006040b0f1f030c0501031a0f0411071b0e0705071502180d030909180803040215070b010609030c06090602060f07051308070323030f03071e0804 71
    0x100c0c941d4100005000101c7d154010769a0020200c065541650b101c0a1090514800c0c03029001016a8032120000c1403054003403c48040391020307242480208030240d02d600c0c40600d641c0606034009601c04050721a4181a88504071184180b01001c3c900041c0b602c481c440520b41001d0001050388610080c4100130010742099001400b07030404c50b05040d140e80d80d0403040c0b400c100001c1c000c40e6011551409542d84161810703c1d49401600b20603c001c1d15080040c50f0b0001c82c041c2450260818180c4285082c0030b007003298145800c0030a1074107607200e0ba402c1001600358008850801041400381c0004141c92001c1c040c001d0000d03485080e617042c03540c5030460014560f03610480c280304240408104054012400310b500c4040148980d903244d4820405a58038000c84182e03080362042450080755403000000c144081d070303018240d9100d14031000c10712140c10244528202940e908180071460540565401654201c419824240c40c00f9400448590910850800310400034103c0700902c03040c00103000c001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 394498210 1250 394496960 394497017
    0x612080d060b0301050303030c090a0312050307030615050901210e070305010f02071505040f080a0302220501091818111e030c131401091b0f0909020702060910 70
    0x1024291343c50a00081c3d03c82c003000380300c0a0a8a4009200109a0740f0001d08001541c0d21078600700500801c900c0003040740e00121205070120b031501a011505082ca0030729000c8140d40d03a074500380f50511540c0110740310031070140004003a04200b69032000e200024010002c0103501e402c028012140745042c07450a6a07080300d941030901b03204000110208010a0030484a003012404c042216201c600d461000340306000b0024140c1a004240c0c07400080c1c1c107070001c1030800c08203d1010440d54490081142d50b60b01e5114080c0411581c5000f0010035510302e030300507074080c2401d5000407124811502a41240300c010400c9500a02c02c0c000661a442c3c407280800c01c4080c2c02c480e0280c02940b030400310341d42d270f030302441458072034141d1050038506080c40350801540203402541107002c65035280c801401130401141003044590b0485052084948941d814050000c050360320500c2003881e016560009501840ac140d030000d0041244400d1503e4031090300651a0f081d03a109654031100e10013030410701e11076051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 394499460 1250 394498210 394498229
    0x10903020c032103060904030c12020123061008060102160b03011a090d020f1302070b0702070e0709140a080607020a0201031a0f101803050c0a0603050105090a0c030612080d06 77
    0x1014804020383c2001e60364004000c0c0d07030710758881d11a4101603415400d241002400c3c80700c220081c06a4541c107410140412201c0c0c941124010a041848200034030300711500c4d42c01c54801c0794080701140c45100748540054043c015500426100740c1c0b03403051000d29420003860141e0000040000c10103417621607004141c15910941042c01c9400022983d130b04182001e1f00c00c4101011154959035220001412074000380e200b1552104145000314480740d084840001601500340002401e004a10380d480c8035100716a2050070441c2007140c11142c400041001c981c2140c0d10080118101e40c00300403003030141125070001d000958041c030004055441081c20204d240080318a040481d498007034400d10710400071103500c0c92511102800701c900c400e0f02044809110f420503c0001440004182c851000f0410703140f10100c1516040140c003681d400b8411690886035800000f450400f40da88081c501601a2401150705079036140c5030b000051a240d01521010400160342c0e581056500c00c0784002d115000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 394500710 1250 394499460 394499503
    0x1b1d04060303021905102c030703020703030c0f0f261306031a190e06100804080c10061403100e1519050a1a150405040c020f010903020c03 61
    0x2d4000303440340c00c0d041a2030151a50701500c00704001060110381d04800141404204c1c1c62154120030079520307980e20000c0d42e020440264212090004002c96074500c0e0540c0061524526542e0708407000710792a81c00b070340d440400e0315000300041d00e80e5030003980d41c0d409120950b0b2b0041e40c45140100f20a9250030b41d002290040004191708034900c1100d50444207542000100b0a0b810b001c4500e15440030410154802814602614804c6030759103200c09031081e08818a600f651054144581b40400317592000c00315041c078000800107092080200301380c2084806031404400800c4880041e81c94540100e5507072a10b10429000702c0c1400c10160101c80120316080c1305104004100315200c400002d2002d045140f06000541040c0c1d101c1c1c1d0031250003011702010080b6141c00c80301e203001401c080c0a241c8220603032440c113020ba450114140040c0440c0007116a182510740801c200081101926031006d43c014000710001e00c030401e00c158002107020350040d01f032910102c2c0800d424011507200c860342c014242c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 394501960 1250 394500710 394500713
    0x5031c050f06150c03040b0f1e030f061c050d020607020d17070f05070b0a0b0a090b0f09100521070602120703120b130e060a140a0504061b1d040603 65
    0xf110280201d03030986010a030380e41c4011803d141184078a402c0082c02160000314600068200d41c000d100d22a06c01c5d0030450400000f52400945e448103540b1303451801082c0020880c00c0c42d081250000c03c58095070740b1210b10b41e50b0344d90a0f0900011042e01009a0403031010000e4058050140c1200030781d141c41c6c8000410f6400510541c0745401620039000c11495944000d100341c06001140c14442c1c1010000c0301c02d251401a00f0090700492014030b014aa40e810300154121840c00754254921009100c620b41402400510038584030040c1510074005140000003030940303d00040f9036003c2e1810a651884149042005190100b00c1e84035a0440d8403407050b400001c100b070000e0303504441e45803400e8100048a108100c0c05000407120040d4805000c01094103466001d500c00200410007009560981d40c8a105a1080392400407100321540c080d800046c1810381c9580c00260321134440d00000950840c10030380b28040d440102110004101c90760825042005141c8801054103000c40d003d10005045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 394503210 1250 394501960 394501969
    0x90f0603060c0509030312070504030b010b04050a05040b010f030b0103060510080103110105030f011202030106030c14010f020304050315060406150503070806041a060d14151503040c0b0309070305031c050f06 91
    0x4407500090843c01c88004a803200c0d01c07274001c8400543e001901d510003543c4910984800368058840c080c4102c400b40800600c07410a801070880c00715050711341c045590302054050f0050040a00c1580c1003590341d40d00410a0341c2c0b80c4002d06c00f45081e07603a5600041d0304624058180c071202006040c1480400c0c01001104a42e403800e4505407204000320000a001ca84040380c05000f035600002c003080541c1e000451142c0302a942c0d840c4000b0243c0e5400310402c0501c40a076100e20079402426015040b415050344d0618103194801d400c54070207000080e409580e00000e1005409032022400050741c00014494419800101585c2001088400f003001b00c4184208003000c951031031000b0f00410012800700c04881c0381da800031030850854160a0704515000d442d1000381d0860b004010710801040800384215000d01c0c00762071259a002500c10051820540168030b00d400080c00740b170041c4607048002c4001003042c07001e071070800385405040c1c0f199034064140c60203aa1008002982d0100107100300040c40c0d44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 394504460 1250 394503210 394503217
    0xb150a08070504202a0a030309020f0103060f140604050a09091b060c02090a09140c011206141203041e050414190506010c050a0f1103060112030315090f0603060c05090303 75
    0x2c05007884680c003505c045c40b0390b000c015000180038540540e1504a05047e01600701c81d0044d8800c031140002d1a2440c001501102c2460052020101035040c0070300c00300c454041e41d10544080203100780e050568031070000302161450782040388800d480d8154181044023403800908407a020408040b9028101031008201c4680184042d20503062500031070f11404095019588043c0c200c2d08400c042000001c5030b0781c0e900c40c1743c0580c0d400280d40201001743d0b498144103e10030b8441d420001c08014032001c1c00c0040c00103c0c0e000d45a5135010070000002c940303401c0b90304034107129843c1c0d40c591f0b2038511700401c0204945200d42d207890250028010000a020310003c91004080078020000e0651215401210040881c98000344507100e90640030041c8580c01c2e02800344031b8814143c008856601d0400e141c1c4680003845040305034003802020b000024025040000c40c43d81101503140070503690070b11381d0709882070903c007912420384d110014020b00025000701400507500e0b0411528100c4039001081d520310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 394505710 1250 394504460 394504477
    0x40504060b0109060507030e010305180f2d1f020c0303150a12030807180f090f0506010c0804180f0203130201141e03060303190f021510030b150a0807050420 69
    0x42c0d9034000142c00607c0880b121210cc00b03140100c0e500140e000301d44559031340c4121100340710803a5940c0c40d0b446140c12404100310140880002d80510500e00700b80c44040f8004c21503070011240c081c049a44841801c10146106e80603c01000c030589946a062046109164100d000081104000207012a0b08000b0103608000985002d4a0301948601000e400c0c035040e8124416104602c0d400191003002030b017140f000202c00c10020841d0352038020064a0101c00c050000301046000d1004101d047c01d9086048404d8480080c003260310300c02c004d00e0303a0803a0702c100c510500722802d0306245020f41d68400c015007014102030000501e814500c400e204204803414000310301c0d00c94000002240758505009a41603010803a0008000720f203001d0300070f0002205000d040307005210794284090841c000c031126a000741131f05c3d05003010b51800d5803605910f4440091103e0238484046520106984503a00804028109030024200791030900342004141d8856411027860b80c0401d028106202110008807808031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 394506960 1250 394505710 394505717
    0x50618070f060e030106050603070203120a2d15030b01181a06160215031f03020f0108060301090c032102010e071205100e1f140420040504060b0109060507030e01 71
    0x80351000d0001c0c5c05040f0542126812403404014007980710740000c00760885001c905001206640d82c44581c400f16056a2541c5552030f4040c030010510401600d22345200020292020415062100091413a00010742c0111520300a40c0c004100d8250b00c0404e61002203580d03102440512021200003840c41c1341108071030321902c0e0000703400783c0020341035604c0b4103500e82c090001c0d8400c20454440100079001100c664544a00c0181c0082e070f103039552001001602e50051400192103c500d00444454030300805c0b103501996904a00390114891200200085100d80c05040004005d40d2654030001002100c00c819607051000c12465101d011600a041d40d0b4095136550114405003001071602c030040020040d1035203042500740c40003d001c9961401080d04021940f080051003000004503260000c806400e60480d4000c1400035103007410b1030340c0b02103030114061100902140011304980050300c0441d45150760354009841540c21200d800001d02c1e0314100305041541c076450180451f0311804205041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 394508210 1250 394506960 394506977
    0x703110102030615030c0705070e0103020307060809150411130912141b0304180603050105070503071e02120a02010b040b060918060406150201330b07050a0609050618070f06 76
    0x46c1c4981e0000c0e24007098010b0101c5119a41d10b6090010080003800280c0c02030040250104103940034002144c05002c1b800c3c0100800614851039032084a0003401c00c0b01c0310209103031f09091956510104031600d00d4400d500090400a9141508144205048500c140450000d00c4003880c580001542c806c1c0d17800119240551a0300000141544955085101108a003101608142080740e0014040c1c0b480741008000c02c1d15a02816200781c003044992000240e90340d5480342d880b10b983e13440d40000040f84c1c01211007400c01c11030100c21a42180c80c80304e0050b95204040308151900b4091108184401d80d13f1901c2d0610410105441804500f01f911030f542d50030700400c0351030f10b4a500500003040c980d0800c0620040c42003000740078000c1440402e42d15081a45201da101c011128220841d0344000e1200d00580d140c2200090503811189040d83c0c00e0040c0308403c00814058001c00c800684150082d01341843c002c0112010400300d80c488050030341c015401849850303210b2440c04196507050410144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 394509460 1250 394508210 394508221
    0x3090901090c051602060409060b2706092e1205060a0302060708130e04081207020115090e011d010c02150c03010501111c02030306011d09042a0b070311010203061503 73
    0x41c00c0c440c681c801c54a2307500e45080010411008030151003020107256000c0b1001554404810385c070680726440b65401032003006403031020300e0a9107008420741a580c140002d030b201c240102121083d600030301d040100d202020310b141c02030b007148515580b000c000c4828456550840d00454503902400200800c80c000004070142c0c810700ca41140d0380140050711120381c013807404c0d241c0001140c00040c5000b041060300c2000c506080d006000f02050108151402d203145032411042c8401740c2000c0700008025540c481c19201c10f42da030308404040889243c80003164035035801070028585109003d0341140e0808940c24000e00407640012241125001d1030608120f001c41c0c000e8900b08041c000c1408008141001ca042002c0d030084091403050009807207400400d65030309000f840c17505000c4000347d0702c03490321070029000440c0072141c21003080101d14104103564050034030071100025170b00721002100300410560105944400180f14504075100254250f00304100400e401c00c1c80d00140b03c1ca1423401100150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 394510710 1250 394509460 394509469
    0xf0b040302091f0602100f090521040504091b05010207180203181b03060601020d140a230d060f12060b060904060618090905190609120203090901090c051602 69
    0xd2544104810607608036a2684e02a545007845105045501d0070141940c1100405202d034129694000000d8103078071000700141400360259404180c0940001d103c081a691600c2c450700b010303203100d90b0b110f042c848843d0b4000c034841081a8081c904541c0514002d008034128450384014000d961030001d6141d0f1a0000000c684c031801d400004184d00c101308094800c0d580324107010040c0e100603810380d41c20303840e00c0004980301c1a04030316650104481c86d1207244400c5041c0000d00d00003c551401c820001c00c03201c4d05003010000200450403a0f200824408403044861160300d00134482e100080400c5d0b49010125401c400f900d0b0300140c1400d030780b803031803190300d486000841e075614400400800c01551521000340c44041400c404198000c0c181201241d003c12a00c01c6070541a00321000302400f40020f0051800c2242c8030f0750031034001341c0380d104060004400d0030700710381305c1e494a130041c5860b41402d0003030000c0001d050380300c2c000c52410007540344690b0360000226010600c40c405289880364550004c034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 394511960 1250 394510710 394510741
    0x18060105310911150c1506121905010e0c0f010e010e040501171908121e0403030f0c02070f050d06090f050c1302030609060108040f2004060f0b04030209 67
    0x100c580c94181418001007040620850f03580000490300790a482c1c0c40c09190200901039504030041035806a18001042c1c02ca140740d441c1e100c80d000302680c0001001454082c20002240640004090b00040003010800d083c02641d400781403c000030b00b5410303440400a02d1000c0400c04240c14400030603202449039220ba04c0d014802607000d4802c1c800d550f0f54060105e0100442401c661060141003071314403111159115180c122901701000d242041d01c4600c455084840207070107459191020241c801c8043c109100041c402d0313000e910001411003240c0c00e0725003030300c85903060f000c1190400c00e01403002030701e0940c40c4025604140c2e0444485a04c524210005001404003d4840ca044401d030030200180010204091030017030f03030060480640d00380300380b040e800251002039001c140000024540e52251107861b9210b03000d5040c1d00c20404590b11a8007074000c1c1c0b602c0040400000c1d050360001030401d80101001400e802e2001400d052504201046030301036800001c0c45541c522010420301030b5180c030007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 394513210 1250 394511960 394512049
    0xc0a0603090c0b21011e060c08030609061f05130e27071e030201030b1c030305130204090501060f0617010504330e010e0c070b04061b0818060105 64
    0x11302d12a51311004005003030703000c030041c00d001c450750800086051442076424044c0542c3c058885d5003191101020000340e40350040070590446070205003010034180140070003589489a85515642d10202c1a40f0340c031a140c5900a03071141c0003420240804042202958114031b41c0304200311003204d441a02d26410009181d010300ca01a40b110342c0310322510315010046d070850703100b6241040b00c0c1c8241c400380442d40c0311040509000e00030f4806000c0129009410880d480b00c1555281030030f4003030350790000301211606c80058075030780c1d03641c4001d221440030704010710050865824141200300010814120070340e814040c0a009644481e00b0a01d403651000c01228010600c0b145010500380b50f00803001e00b030704240310710850840c0718800041e0035546100c110303004441440500c1d10300380329620340309070911020f007046402c0c55031420b61000004074200c941841c0b00e45961001880d0500e400c181c0d51440c1058422348482c1c02c4540100101c0e0389420f0721840b41c1e045000388600c11958042c026104500f00400b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 394514460 1250 394513210 394513267
    0xb0406050312130e01080a030819060e06090a02090d060b13050708070201050c0a091401200304080f010b09041211191a09030d0b040b0409050c0a0603090c0b 69
    0x22100d03911403254000e80109034001d407000d00f00666600603102065030030300c40c2000e00e4001c50003803000300e40310341c0a65a00c00201c2c14104407108168408100311400c6a000042c40750091050004e13500d0410030080d00300300003a90030350500ca9001700090018110090051a0b40d90302d203000c40f901c0d25980c000308040c2c3e00e00d510030085d03480c10b144050000c0e8000c85402005500e8000011414001c0005545a107292a9140c0000074140b0102c1c03003000c0c41c23070001c081c18020140032040031007041102020728648500007950f19980f40c42c000d64a07100e0b106500c2a405e074140036039080d564a90020940e03226820150001250107404000d0300c0090500d101c0303403298000c43d2400d0445036903070804013111602c04c100040200d610006681c110a9045e030300f02c00a500204960003100066420411035000001e20001d513a0308080001002c843c04444105d9440c1c0058024441519019804100078801414288031214450303503034901d020000d00034182c44c85008a00c006080014034082000840b20a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 394515710 1250 394514460 394514473
    0x120923030a050d03200c07031101020f0109060b10050c03121b04091d0f0606010509010905180601200304060305041e03020a0b070f09090b061e03090606040c0c060b04060503 76
    0x100c004000d4009100c2445c1070711454591000e40000030f404544101e80c89202a01d0100e003903944840c42c401d6403112032811441010244044c190003031003050701407845501c00040300150181444680148820400203001d014040d10824640c044110b0f13098451100038840380360394191420010112000d1011003a00c0d0101e80450444020b511541384005101c10440c0728006520160340d0f0743e011a0381c45000317034100d6030101e21a9405107000e044c442005062194416880d04007084a030040c0b010b1000c13424224000384803055030054141900f80c0c0e00540c02a250349458040d082ea203118a106000c10940d4034070002d4144000000608100788141d4020150340300b66050096032140200b60a44010036010f009c548010302811620010626035101d040b00c0a1038039184100034100c1c0316200381c201c0b400708181c40c05005601d4562806802520510303407282400aa818070703001008102c1d40c025450106d1600c40141c003c40f011032030a6100001140c0c00d845440802d014104036840190148070390b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 394516960 1250 394515710 394515733
    0x60a1b050414041103090705012a030c0c121104050106030905070e04110d03080402010f050a0905090903250c0803071e1703010801091109010e06010c0c0b0313120923030a05 76
    0x116051023203804c240c1e034030081d8000e410010360203841580c10016002d02c8810300c0800103070083e104540e1043c01840c0300300426640350300645c07441015001c2245c005205c01c124201510f001d11815024104601e000c000b440c0d140daa800d50f0b114605d000e030008102200c4001020400001c0000c1c845450203081e000110f5042e00d400f41030f03003c050f18120b01007107500050301c00140c407840907070384410641c1d540c141a4918240c00d0040180d00600964800d0004010113100040c0c0e0302070980c44950000d071900c000f0f0000d0704200048500076089100b440e00304111003800700f4071000d005209250070542d2880d009a0614001d40e40b00151400c010b5080c80110000840e02030641c0030f070710f0721405000100e9640882c101041b0a2040c00d002c0d20340381c0e4050780c1c00300d00301e54420303440d00600510906020800a865130315000b060340044039840e240ba50750803007050412105d0b1441200014660504846481c02d180d09501c0d00012840084050130100f403007403203039275001c015a2640304c0d00328080c0c078000c081c40c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 394518210 1250 394516960 394516963
    0x111040e01050906090610030902060f04140102100207050c1e130605040f020c0a0609020a030c0b042d090e01060f0905010f05010207060503060103090c05030f060a1b05041404110309 80
    0x91040512654040300091501e0070404600e906c9204000e050a05903100c16400f03600801482e507050741c010106209845000e10100c000b04007030100307081166401e07503102000916000f446c2c01c1c01003105005126000005d480000c0441043d001180c4034005402c3c4080b5100740b068031640701560210445a40a4a03201542e000c2015591301340c1e02480b92551520a10f000d03403041002402041d400091540302003041a44580c00c3e03213100038a20f00c229552515019603800003900140b10701c0d200003a04002102c0d8031480900750601050b130700c005020110b420704102d89424860010345a84860710710311030403802e50046002d000040c0302e02c807030745465807c248002d00007405241035940f1504008500c660001030440111a1035650f00f40c9965519070046014100481c8111544e8241000c007040c550b070244000c50044c150324008080c5440c040c0340300d8041d9040549411000e815000410012660000440341942c4100e40f41012241900e00400c0040c508075590022221002c030600c000b5040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 394519460 1250 394518210 394518239
    0xa02010e0619080f0601030c05071b03051204060f17070804020619020f0706030b100c020423061f120e070b0a0c0b010501020c060403150b040e07090e0303130b09011104 74
    0x3042003041c1325566400c401501280c0000c0191004647d05000c030301c0020303102d41e66071095101040070300c0e050759690742d4520f0b2409d490220f50b11145003000c40c00340041c9070301040c00d02e039200c007501d844046103001c020303001701c0b06001514400421280740d00080c150346074007080318011106105211003041700d588000752580c844d061707144103a010399000001c4a40c0b2a00602c0c010384d00042139032003c281900f40603552000161740032a0081c1d201e03511541e00d0b4417503034680c00f0381c00c4a28007121301d146084010444020941560483c103240300d036095201d155404000c60588013100302000841c01400070035686000c905a02640302150000b07010b054941c6d0000070a001079100e09180400e5989400040ea00c4000d2610104c0d0072000902040003c030b610f540c01c034001800c19034000165441804040b038140c5011607845012a4003180040000d2582c501c40c42ca25500c44074095400e6090800913078010450140d030241c41400618003140c1449002c0d880010304c241c4207030704203a0f00c55440040110001c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 394520710 1250 394519460 394519471
    0x209031204140918030a111f02030106120c200c09010b12010f05090a090f02031e070905040203030a050a1e08070f08070c0305030a1104030c150507050a02010e061908 73
    0x1e0082010800e00d0900c3d98983c0c4030313641c6000186040880400c0100ea4030100303907001000900c150402d06201503058030f250030034241c1420b4007690702c2d81001c0e00075200c0502c0d020348008080c9440e15194400c1d038000720020316100300864454180d0500c00c4040e1501040071002036002c00650700000b503801e40c00c4001c6c5080704503c1101c0920b6a41d40c0300369068981188221030300010b4010001300011013640c0305c0780001d0f108000d050010b410540200c3e143c40e04521031514103001c044c1c004041070310100901740082c030a804003400306242c03960210f5201c4c006c2d80e1400d020703c60b0101d404400306000307102040882e00d145401740c11a0107025001800618141c607210b010458501058004a20a464180c0704200e80e80314032088078820790303044910740c2c0014015051150f440441c00e400307414520003000114002c0709000300f11402c01c20581c1841c004500707040140b01c810414400040d0004c5801d003150740c0c0900f8440d081480c45808101c481c41004040403170b00c051202003555040d0800390050091 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 394521960 1250 394520710 394520719
    0x6180a0c08060d05210c100c020106290d0207080c010212100b070f03111204030b100303200a1a0a0c090506071401090c080319090513020903120414 65
    0x5480b0801400710700d818110b409040ba41281c075001c000c44203a615001c010704d114160301881c01c013049100fa1b003030000e0604032070f40311a2216582424640c0c240107020180c000188623600010b500f1400740c5410302984111801040d010590100c11041075058441a903000a900341d40c0d00940a84107000394001e44030032000507a100086050040076412501c16500304449080c9480001d8a9030b660315420b91702c003141003041a0001c00044001489103034a00c401c80d0801d503895500b540b03419507090390010889205520030640410200360f006843e80e5424402202284440a480c1c4503941001900340c0e01502081c1c0c10f003c00b200004180e80c889102e0101c88104100d00e040300325040b1400d00d800d11906500602c10321003031020504081c20018114440300000801d003d00c0d5540402d03181c0254001140c41c0c001095504e80c880c140b4420180003002403901e601e400e41004002141039000c080b04626241e03001c2141c4c1c5042d02c00b000030460034807100c0101078603aa50f640b14601c02c1c007090100355000d03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 394523210 1250 394521960 394521977
    0x5040803011e05060301090e010b1011011a0307030210032009040518060612191a0702120d020a021905010509010b010309110f060d0204060503010501110319030506180a0c 75
    0x120340d03880401010f480e0000c1c00c4902d10303468020400d0140c948281c00c50034956039403004429642e100c21410a0560f1a40c44912945025910341070841c0d82600c243d825032042d02401410594000c654641900d50481d241c0031030300550801100149640c10511507001d605200401c660b40c014000f40c441340508503000d020540d0703001e0410f00ea2410400c01204ca66010f00301041117490021004066100c4074421229a0f106440640c1c40c1d880001506440003140d00d11070007010a03044289079880350301c0c1c2c00100b006154418488020744644c0c428203480035408111802c40d180b0900443c204940000c1e2690018407050030418000d013002e071040d180715860040d0040295000e07000d0070f007280d500030ba88002c1d40511103060040e428a107007115039210200304004402d400e003a10150000e0000da40e80c294403903041400260181260190900841c2c2c02804840610440f0800500341c0304524078010070716803594800325060704010510b950100746980304204d01d0b001c80c0d0307000b0030025170503545030040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 394524460 1250 394523210 394523249
    0x10090c06020d0e0402030c070b01090b100c050c040207031205070917070e0c030402031c0806030105070504081b0103110408030c0c06090a2907030f110607050904090f05010504080301 80
    0x240e42c26007a6900001c614200c000c210145402d5000d0742e840250111854506007556588024080c4260841002641d41e11103080b214141520504a48010b605018042c56566204c55035075450b2601c846210300d80000d00d50b81014410000c80c0222010100b09005500b00300f8805081000540100c5100d000030802d561142080000e11030b0441b01c6480288040f41c884108064041d400140240c0c4c0501c14070454600d001d40d03a00d6045000d005541e40c0301c2c0705e402e1890405095036800b4003007000300b100a2000340002400400c51181d0300e4180a040101c0407164401a009050b5514000c0c0c100c00000c60001540b00000c0010241c002450090b00d1040c0240001c01c41a0b0254103041034001890301c6050002c040d500800000c841c01c200c0b80c0815020f0080b604004640c0840821400070b400003562800464004050041d15050700016240c140b82c40d10b4010074500450009d10320843d1500181c0b01400510b145080171260004000d100794a840c3c00c02441650081c4500200c51703000b94146003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 394525710 1250 394524460 394524463
    0x1b010203060a050f1206071709060f0a05040303090b1303020609031806030415060914130308060d0309031208091c0801030f110a0f06030c0903020d02120f10090c0602 73
    0x2440748100814400c000b03401e04090040010100c04580d800515034070741140d5648040252600c03c0019a446000d4003004a107200218800940460290341c058024440b00c00e140c44d500b980d010b961494009656555418210f001d00140d9170081e100005d8041442841c0036a804500b920394040d400b00c84064403104c441994900c1819500c000114440010f0307962850140b00454106001d9500035041c00391101703481084511a501c14242250345051310720020400d40c2050b540061140c085503d00b50380c035240940407403402820309100b804004d0907282011301a4440c80701443d0030081d204c10901c4107042c041e2490200f666003800e0386c0f02d44551030800150075030415060f805142e484141591850703449140b0b024044008980c40b440400703881000d600d0b0000d090b0000c00d050710070b040b089841c042019040751860540715040050403031050002d40c5402c84003680c515815603004010702052448170307007002c000b110400c030a0300030b80e03d44011510f102d030002c808060081001815032a96241e099 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 394526960 1250 394525710 394525717
    0x303080a0b1807031518020a0e060306010e0f030a1707051c0207140d08120708010618050607060b09040606030c0b0418110c0f10050c09010c0f03030b040507051b0102 73
    0x1590b8004610001d85014400d811a4900a00b04588044215218412010241c2100d20001c00040e40400c0090500307030322400940b110001541c9051450600c1000285a861007100f160700410182a25403c00d0314100000b103071380e50300b03e41e154444400390310045407144d200400650b4144690790400d1401508402140e01c00a129002041c840e440c0094003109116055003003030744515451340030ba001c954000004d004040660644440354038003158094542801a0044410410000d4007141c804078800c0c09002555802c8400300e848050b10301e48080504030740e0720f03115040703200e04080c0400c00209400c031009031b900ca030100040e280d449603c000b00340e004034030540b0760940f240c840e40030321042c03903900407000a07040c10700301c616142c44d0000300e6107099003030358264500b40d001c844041e041a45503c00c071078020105100041c5442c4c1c030500020719222114201a0203d50b255646101700f40c066406042203000180042c421480d11310005003603178010b00c2100c20200080e2040c440103036018400c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 394528210 1250 394526960 394526989
    0x10b040b060304060506191203080a05010b1b03070602040308130e0705070f14010c210606020a120306080601170d0f02190f0c08030301150806030709020c15010303080a0b 75
    0x98034110f90b92070b10703010080c00e0b0141010f03030444003020759480b01007403640c4504041d104450091280765071a2600400040c0010301500000c1d29000060010880e110110382242400c541d64a44441e00d44000350306511400d0401402c092001900200300607c00001c0c0a81007000184140295607519031503100900c121010800284100800320009105503034001c0003e004525040c25802c159261500711511652404003280c26000c1c8240c00c0160b00340340001089109005202007458440c020796600544000144060152a501c85c1a00e04c6940282d0080400004075119541d44500e00e01064a610802c0700b12405903c507198590350041c16443c1c0000032550041c00360341c035605c9041441e40007411084605d600548803610209403800e8070300000d48040d001035650703540340000201083d1004200007051011080400c816070b50041580800c4540c2d800000da80d506003e6a1107041000402c500801c4038090790001c0705050348018414805e184407002003083c1612081085003041101d450b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 394529460 1250 394528210 394528219
    0x80c0306010c1202030705010504060b03070f1d071107090504060605090609160203090612010f0f033f03090314070506011202120d0806130605034803010b040b 70
    0x100b4500158902c2240b151040740380c0305480c02c203e141d58440703082d42c50541e07060b1141900c038649a140f9140500c2007500a0140d50034561180b0720b8100f03d00c0681e828414940d030500240d03c0003034602c2c0d00810783c110740103260f07400382d9a50f99240c448030b4000384010303501079950900e0107001141901703043d448140a07000c010039480381541d4600f140c1740e020800b044602c013140001d1101801c0c90725aa8054801c5075442c2141001640c10b114150403801040d50000b801c15155032800c0011480107004802c0c41d100604800101040300041441690602e0004411000002c0d1064200c9641640501000ca11903520b002003617120b1001c103495801003035000340c042e40141004012010744032844045040c030152030380c030f0f0381ca103030f05031180c00c09000c0c00c3c101001caaa8030003080154074104010802c601c40c071007000c028032418440440c2da60201d028501001150800e06142c0d500484aa0540849000105020b20307403240c3d001c0404845005034618025801c000c0e180310369140c940101c207002c0342c0140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 394530710 1250 394529460 394529477
    0x50d080714040b120405010f020c03030f1303050d15030c0806060f030d090605090f101106130308010e13050d050a02010b0a0509070507060605040612150b03060c0d110403060c080c030601 82
    0x4c01e0308110080075000700c84170745d69481110103040c910700250803071383c07060386c017868591400d510f045051250003031007800c0c072883d20184903002903080415100f0211555600159100318600d000314041416040a003044148060004818000103180d602c504401e0380c045500034918005d05545219040d05807020405444040c80360301c0c41800588845900140740014612200e00413682d0714050b03804030400113035041c4c03901c410b003403080004c19041151109419200d1409880083c031500041c000d0b5030f5060240030104940f00180704030703003000c1508201910089428210040c009500c84090f1002550a0134145c22040c58070440c1401200c402a09000e100d81d14a0001c980e183c0c0041001c03030fa0aa038030400880c3d25100d0317200d40c501400051402c0d59451125051104c00c1a9081803c003021074100700c6041350a0718080341e100e401c800301743c030001c1c1c6807059050800050a048402400d0401005c140002840700c541c2203121928825129004a6260b084050080d4403003181c540c0d0125a420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 394531960 1250 394530710 394530727
    0x5030307031a060c0105040b01120f1104020c0105010806011701110406030203061206043c03031a03060907060906050a020c010516150e010b22050a0603050d080714040b 74
    0x250494000314290250212071000d0b036a0018249801040980c00c00d695904108800c01000c080380c0c5000d000c0003000380c105080d07141c0e1140c00000c150200100404240c0400b06d0070350311141c0540d98102180002070080d07603114440c3c29a255400d01c90074108600f81d00c480e0070308003c10310030010070b031004a619514103070418070700f6006507101400080d004070500003000445d92081c0580d0f406103104219040c440c00200c0d2007011600c0008a03411801f911407034402800c3c19142c14050b0166034035007404642802211042070350604034102854150090b002001842c900114416007030f0784481e02e5400405485030b01c1101c2500990440c400568011800d03242d6035801b171405410404140c42e0b001111078055a904405040e05172041c9040503162101000121002c5c0114140c00f0403d441264001c04048500004031120322030785010305544202040f0b80e03040e145c118a01450308001114500a15071400500c00b58048907c0e0340040d00079040040c40c40480800c54049811a100090401d002d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 394533210 1250 394531960 394531967
    0x1050909130308450601060f09230f010e1009030b09060403091701270515130b130501020301060c150b01080408180a0602010905060105180c0f0706050a0b180405030307 74
    0x1800e074504d54a0201484403001e80801c002d0b441c081c10080d82c400b00782001d07818001d005000729070000c004888102218006148503103020303030301c281d0f400c83e040a0b01e244014010703200c6803a203110582d0002403140700c0c15101a0000030b4841128401c0d854907885030383d2441c0c503a44a1000fa20010002004d100c0200a10300c410000c2c8a0695a070200000e500e500c40380007180060000c0030010180c91110705100107000781030040449109200885440900d0406216009500102c100811b81d0b00e5400c003150f01c2c480d035a4407680406174040e00866407542c41d4040904103020400c0c00300d8034884a403074040e01d2500d9501842c210b810041c0c495540c5a1241da46d11845a00110f4680c650000445105c0c0c2066072481e01140050409400000706101a424411300704401604401d020745101e000744501c0f03050b0710541d50740c000f50004d45e4944817603401d2000d004503c2a030401410040c1010103010b00e10b03a169100924440302201c90701e24102d450711868002080484025084d03400504c00070301060701 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 394534460 1250 394533210 394533301
    0x6150304080d020903011a0319030f03110408060408131502120a02100504080405120705030c100908060109020318060610031a090406060303111903050901050909130308 74
    0xc2c00d000d4145000f900200e421600020000b0f40b00141c042211515030030b09004044403140c1043c82c44103003c0150324040c160722210565082019520391850315840c220b1030a482c00b030096101962000c1c00c080c10f00041a801040082e0101128104001500950700d92070744010011500a4804001440c0b1542007580018004034258024440240e4680015100d01849503210b556119100c034140b10502081c40c11400d01e000351603110101c203000070340d00001c00b080c62850444e9500107000c59510708841122296002c401c240c42035500208052185801451240301c0003140070308805540c2e207001e90f680301c050318019003207c54031300c6c4051064480d8111a07400c9509074040c0880c0d29401c80811030064084a0a9a0540e40c2c0c140a10802d54800030b9520041c00e44001480895030b200f514420030480c0d440010b0a010740001d52016a034010313400c0d10304403a0010030f8800c042c9090040d0555402d070b10081240028015070010f2040240c0400301082c0343d0103065541c0d114040503c40301c2d040701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 394535710 1250 394534460 394534477
    0xf05070f05010509010e0c04090302070b28120b011e120e031611010207050612090705092d10030609141e1501060f051308030414090615030408 63
    0x500c0030500201054003406514003a1031181e000240080252108074280701703415010900c00c0d814032049102183d0300040f44415a0f02c0c49407042c2d61200345491403440d40300c070b0001c8064202c2c2c020324418001504484c90419440e000030042c450b40c107045004482c2c0050689216040030340d100300142c040e51080203d00980b181c00f600c0001e1b0810112103080ca1900b1624103900821528403d500c00c01001a403c80c1d9940001c0c00140509418907000036018058098815107a08601c00000c040c95000c22a40b0000c004c00f45c101e02c21810a003c2040e044002d240c00ca041c01e0b9010358202d1980c01210750740ca440f80140103650301e015030031a515500034084000c0b0a40306042d4078015090500d42c00c0c40f00a40c0c60000c00c071303050f120007500c00582d820701a0240c1884228148035004000721608207038203030000001ea02d800f6a8844495030780e6041200c040e00140054480890b020401c00e141c85052213041500711841e68007035a03a0070411180e0540e1645030420f000050001c9800105500040e00384030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 394536960 1250 394535710 394535723
    0x2b0212120402010e28050306010501050a14271206071d030c090703020915040305030d020d0e061602010b0a080703020103020924040303110a1115041e080f07060f0507 73
    0x200c0e440000810745d90b451104c2e149441008901000c42a8070600b86000400054000e080340358584000a4500c3c001e502c0d84109000d26070742c41d421468a070800701e50124041d0200aca401ea0070b842d03421030704400c0da11402d034082e0000740c542e00000d00780010350510400342c030b640c2e01c60201d401040c115800e820959130307581c151140c5141c01d00309903038000a492040e00c45a44c01078540107003804009921503220407025500c07200300414404500f000c030031642c50000d0300e030000d0796405c1890030b50401004845800440390042c2020f20120641c00d1070421010122940207000d18134601c0708220607104c40e403141002681c084201000107501035005001c02c20b4005164560100704000403840e450308001e21841c002d58001020300416801002c84180082014010101c5a24980c3c82040d00203c00104d24072400310401c100b01d414840104a40203006451086100707540043d06400611009004514060040c4840114120340c0005d44400711001c81da0307000002c442c3c00b842950158000d040c2510711 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 394538210 1250 394536960 394536977
    0x10050f010323040c0506040812031306050405060711070501020606151605030903150c070204110d0f02090411070b04060c0504091d06010f0807091109032b021212040201 74
    0x421140036035042d0b00c400c000740b8120991400349407520034200d507a0411391103010284001d100a5200041c80e900030301003440b501c0c2d40c80e2580e04040604803d1a1402000f090a16041004001011803401e00030010740d220500c02c04842e2020070748451490181c82c0c0142d05c610b00050712468007056107888000d0407100c0381d240801d12050012001014503080e91a42e200003800c1e006400d0402480c02d94061950340500d503400c05510300e100d2403158000103031080341c40701c04501214401c07100f218081c0303419160810419510141020194100c160450311440c44e0a4080101004100441d4541540a02180c1ea107546a0f9070355802081a15041410887e00348404aa04203c5100e0200c8585e66800c00d145c0820240080619041058020025442010301c00300103041d40040c0d0203050311343d014404968107400c00c0951105001e42c04130f0560620406034100203c2162900e64140801c204400c40c1c00040d01007416641c9030400c003402c007400007040103020742100f4100b42403a000340c81403425003907 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 394539460 1250 394538210 394538231
    0x18030c0b0f4326010e0a02090f09010f030b0603070308030c070c030b0a02030a0c1e350609011707090c1b0302031914040e041b08032110050f0103 64
    0x1a410b50040d1401140601007040b00015050041e004490700d0780c1400c101c41e604010301c150031083c0141c45034808540100c5d1a0003135135110a503680b18a60040c00210403585e41c1d40ba0205c074660a48400e845034424880400c14608000c202c0c2400c0d40d811494252540d00c441d0380e01c2000b0760040d0403d81d12803030100e002000080d411100c482c010003820f900586c490800b02c031600115410405c1080501c848080e040540d0f41da0701e4080c010101280c1820004c0c2014140915109881441c1e048038040c0320044ca035071280b0002e01d24901403002950241d8a603030b21400104000d0305004000302940d27000a004000d244034135007085401001074644250200d2a011281c0903203121b80f0b204501507040131441d10002014846a40644603841c688100940c0ca40b8a04880b10f204601030700710b051b801c07980010180502e030610b1154104403000c03040d22030340da00d40700140c0b40d03045011140c1e0030841d0603495409928a0702c070114000d41d00040d802204600d4401009442052190741605050311400ca160 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 394540710 1250 394539460 394539571
    0x2010c0507090203070e101716050d0f091406250504080a140c1c06020a05190305010513110d1a0607030804050606030604050d05030a18030c0b0f 64
    0x5000c5c61150301c07901900401c500802404005420481007003001c805a011032030714024240d20f800010300c210010500d0300c4900122445c0c4203075003903010224186422112403c1559118840082c014401c9819800b0704204003600c5402c11340e812076110014400d46142c203100406200940382150500b04e103400e90f220703035481c00c02100f00f43c15100283e040005400d2500140054552031808448081c5184811f20041405110058024107140c1d030100c1c803054902d00a00460b03036111401043d600a14041c480c0c0103010381400d0040340d0049840c000040803090720f50043c1500000c075440424100758440c044000140142d65080d9588605400c0e00c040a031182001814481e0190351000d0b25417402c2d003052440c01c0c10140505010b540b000341084041540801d04000140b803d01c0c4c4990380c0c4d1280e0711200c0140003245002030401101c0400d4200709a08110307008a0140f1400b00740b80190340380d10102d0003d40b006c41c3c041044d035035065801204d40c0010f84100c1c584450049120b0344c680295100308 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 394541960 1250 394540710 394540717
    0x12050d090b0a181203210203090d050c0f070b0315030303060a0902090f040f0b0103060b030f061005071a09100905120921150a09020a12051e0105070e0405060d02010c05070902 77
    0x1640425400f03000e280c070103201b02d41014400b60348210190318605094501c5942c440310f054001d010040040750105c08401c090140c840e07200040c2d4200e07444140ca4050402d0b640d4800e440c9100f603549040c0100d51542004400d40e4490040140a81001442c04c1c10000181d4040380c1070680c040350341d410341d0903165107030b201c0c49400d8121214006005001c032000903003107942c9074201380e54281042c410420114655084603a100606a500c0034000d141d01c8020741d00d9000e1104d00820050200421501d90a0400718080c07180e1000002c0760000c14055001c0350480341c3d1514013520740d1b00103200d500000c0440c01d004260600010b403500c40a11030b401e561020340400c007042c0600300d40000c0d42081074144180602038204101c1c0d2070400401140360300081d0006468414441c1110080d01c85a091110510601010714403030381c0c4680121040f5001540200b00841c0c0e0000810144200c2d2611402d040c41968804d1402030403c9101e4001034006442011090784110340a02c100140818142b443e40040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 394543210 1250 394541960 394541963
    0x1050703030f09120e06040b03010918060903030506010e01111c120e0f060f010806040b13140d090f030b2e03080909060d052109040612050d090b0a1812 67
    0x10b10325a92040f0011700900148a2080c071600b02881305015a400000c101ea044464820380080d070300700b2040018110303100c42c01002d0505882e1661140078160140c01c01449810240e0f81e0a00414100e0015038222510b65205c500c260b01c4941c103450308001c0c2003286d8642d0406400d00e0b07a42d135076400e18130400b62000c48040e007030326811041503440200000c000c0d0a4100441550741085903042c0030046903603010007071019084800d5000413640c50042c6807881765100e500b008904141d2998102010f41d01c445408034500045d12242c80003031001a00c0c188842a258441c14100c0103803981d00307030403101e070450300004104404901c641a0340001004c40d040300070f612550303196032601c0001040242d084001042d81d8002c0c49002680800114082601015038520200c58108214080200c000c180580310099802a20b0214045641d0740e0010420010310b124000f25058200c4400c4100c542c415144070359130000720107000c19814a40034081e1829100224a1804801e5544015105002030302840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 394544460 1250 394543210 394543223
    0x70f020f060a050403230307060c03110c030307092103031e05070f030506010905060a12110c1e0102130314030f030a050402190f18140103110907020a02010e01050703030f09 76
    0x1c0410420112000d4250203d50100b800786c404004041c0035510b030703c15040010a01070380d649417024450300982c80980741d114826480d81d1a0b02c20f60104656030f41c4107031200400704808001c005515416002120725102c0d002403007200e103200c0e0341e40690280c00000f0000f03d00e261401104118440700340301d010b03c0ba0a1566071080e00c5150801c0c0a4202c5002510b0f040c10484c075141c061089449100440d41e11021614066210b510231003814401801d90294100c100c046c0050501d02080b000144180c0c4100030540c3c8680200d21503440300d080740f14031106000440e98554042000c03c0d0b40d009889c082d0850030b030a6924140120109803515482100e90900b41642c5206200545c200300d003005000c050001c00500780c81d400d1a079549030038041c620400034844e0141c07040000b07c0c4c40d103801c40c40740840014000400c03542c40b840e1060500003000b44a50007146013100140702c061000611f81c1d00d20780c06071540d07203400015400440c0c150740114020740502d9203601d0149072003840c40c8211605a0300480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 394545710 1250 394544460 394544467
    0x206010302090f090d050d1b030c090b0c06040b04050a0c1d07050705070b030c040504050a1d0d09050d030507020904030c0b0903090108131703131205070503070f020f060a05 76
    0x810030605002c00380c28070390083d1141c0108080902d00240446209509003442c64448000f0b070384a030090715004441c2001908440c290040890b0990004501803002e600e54400c0d1544843c00504030b40107165804100740d100d41c02180100b01e084003142e821038003500c01c2d680366540c10346400c1411080c680c00941440603106038003003d038440c058001c1e044040340c030b030447c54001d0030340b1010342c0e52803140203601c58524000042041e581c1c540d000c071001404050000e10051804071400001020081c20340340c1c1e090011810500d20520104038444801d480d5150411101e0034002480030800303da0300220180f0004211030000360350b51680480c40b90f88a5504e5104c4041030340f9090103040e10142800c0da243c0e009110f0010303c0c0ea0409800740d405010042c40961100131428184c01c0d032003040607440c41e60800001400b080451003002181c0083c0100c020403003841c2c20807400c0b5160302c9400c0000c4d1503504140020000513190803110078400340000d083c030890070040000160540c2c081c01d920380100c0c1000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 394546960 1250 394545710 394545713
    0x20f10090516181407021b0f0d1b090b0d030e040f09050c0f030304120b0c0d0c0f0215010608010b0d1401150e040b0d030f0210050412180302130213090c02060103 71
    0x2070244035121003444c010040780e0b040a0790302035544e84900c0ca800b0070140315010208102e8407a0307004030301c14080041c00d060b14200141021003000c0c107030042000c440e201311600410803c54030f026a004204000c0c054680040041e1400c542c00f064441405a0041c0c075900c001c2800e007050302038087c10034081e0000e0b1040b400c2d41c0c0204001569402903950094005210820101007072520300e40d11503800080c0c01550f90343c0d600f2281180d05c01d0305400c0d00d2710791400f90113007401030b440361003a51400700980848a00072034820400d10000c409114140c0000c03400f0005010544514024003841116140b011401e4216a15004101102600180015980800c407104560386c00380700c80b484c0c0f11041d90101300b4000c141c0e000c1040314081050207003d200b03010b040820340c28401c010920568086c0d200400840c206403030079040100c0340d485041d00149218025107103100500c0c061004403030b40101000704c481004041395002c2e403c41801c3d00406010b40d10700054100881c050320328681c440d94003034852907065 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 394548210 1250 394546960 394547009
    0x903170405011b0b060d02010302070203150103030207090501210302010902090406020d06090608071e090e07051315090b06070209010f081207031d220903020706020f10090516 77
    0x6020700c45583c5092845000081003402d580340d074000b001a2510052040c44e400103034040d11451900a42510170700e14410111203410340d04a040ea4030076801c2d0360600c0c0e59034003114203a0741c083c01410003945000c0c1000c0311104003008807156581c442c0c0000300b01c0b03080c00d80003c0c450900071103068841580004a0a0030070390307680708010103001d0040040103e0350070541c01e00e40c2c0f0005806401110b20907204480044005507a09900601202009102c000690101d0300e07101d040521416002d140046508002e0044502034243c840c4403140d860886189000b401c44080e242d06480207401031000c108030800350f100c004949001c3c0803040d40326048640751204141c03030f00d10303117106007041514180f1007a00001d80c8610f01c142003144002d00c0340800510743d000038058200c01d0010044801203100900c220959a402842c94540203409913921195623000903a1208020391060072075401800c103500c3c0700d40b11a840118954003c04c01c4442c091051500b841e082900741c0c0100d031507012120041c101c0e0450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 394549460 1250 394548210 394548227
    0x90e010605030f07060210020d1d071505040302030c01121e05062b08090301150303030e0c03070b120a020904110d0b030a03050405210d09030303110301031a07090317040501 76
    0x191003004000b885d00c0d0000c029121181007044500d819000541e21f01920802c0e000403000c504680c4140145d81001518150b6941c42031241443c06007211100d0600d03a40100152011260050060592190491700440b4821401c804581d22207a4444004011009020310082c614a2081c00065182044010016111000f2802000c0d8200740801c2203840c00310b6005881d400d5038443c10b12a103c003528000240544001039068048040c40e040c0001407590503086800b01310425000d54001d04044814540c482129001da8000c4040410544403800c582111443d80010002c80042c02c00c4143d40c0000e058602d45041c07051018000301e00c03038108606030f10801030462002c4005100014450794050024011440741070b05c140020703026100052103103c0091030340201e80c0145c1e80c8400352250040d00f40412030109800007840d14080c400c0d02d0081c0c408680c11b0341d410001e031a441e4015000004604000108810100082c400700040054072600d04005810007542c649910b5600b4540010850381 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 394550710 1250 394549460 394549483
    0x31c0f0905040e07151101050c03070e0a0f0515090a08030912060601080a0b01050c070612060e0f0a0914060f1909020a3c0e0c070c060810090e01060503 67
    0x83c5050020580000d00040500848500e0300705082d80700d480402c01e0b44c90900941007110030b0b50130841048207608910008503c1044141c4944520340007a03010b110519180b07000390142030a04400a1040b0700c0d0000f012100d416401c14172500d01103202d0046030740b50f0450f600020850b0f001164074009850712008103003c44449100802952800c0000240040c00240c101c901080c2d6a405441699200704226800310718004101ca070999039138070f4010904080c140d01c030100c00c0d107410310101e07601109055090003034110f081c0d62039040d00c8044112006121642e0f04640d00032500c0401051244284200c40c8510105201030400d450483c10703842c10f071820000400011072406020344010303075036001c0100644031038002c00078a03181e2601566a03c0c001c0c0101014150401202062207c2102d401003c20b0300c9145501c80099142c00d19001d105016890004010a00551007406110b102d50030866001d0580d1400b01b20a076513964490781144c01c41c86640c0e500f40d444075414026410204400300552 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 394551960 1250 394550710 394550719
    0x313020a0e04030201270b06060f1303021003090c03021203090909010207060516020d080c04091503021003020f031b0f0c0109060606050903031e19080109060b130e06031c0f0905 78
    0x11002804064507604000e50000d001460707d5008c03800a48603501526070360803011a10994450345000003071280d001501c0124400c03540e8800d047e2006210b0b00407442900e80c044e0440c42080d0a41d801c0160309074941c00e00c0c1c803940c0310038050305444740c1e1042072040c041c032800000141d4540003400c1480c2554001045062140d8496584d0303410a580090562845c608525004145446a103140e41c6c80d40710b01c0d8021035045081080a0404d12280c4082d001201c1c4200d030402800f4442402c19010f07802000c0c0d09cbd0032400010300009840d6240305004507285000d0143c058a0111809280609500980c0c042d040c9a035660000004000c0144580e402502080c20314605110150001940d28402c409844050050f01d1201c3c600144014007034600007070b0f007030a000481c654100d600404252092040d00c2c4001c1c10010005000961b041c11500c03805c20010340c0714003160400002d10500d01d40a0001905071084003042c402c6951501d404032040d61556607051441001120b00500c498225002a07115 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 394553210 1250 394551960 394552001
    0x15021e22120606081f052526060105030403050a0504180504021e0303180a0305031b070f060f1d2d0303161b080303010801050109060611070b0313020a0e04030201 71
    0x210100e05460043c21170700e00004585540e50380c21102e64003004607101d51420556600d010102c0b50001e076140e880764030100d00340c0201040a580e54481c03080580344640400c0c002c0012501107403203440140304810845c10090714060b44c2d820822800303000c4a00140344190345a06000440c41c203a07405145034240d04007038000d517017006000203031244590309080c51103d001400f0018142c450209107402550428142c940302d45c1400602c64020169812425181c000e1600104000c00b400100c0300541d0b2180c0e98a103c1912102c205554802d0068000801c4100b050200000e41d83d4a4115000c0c809a51000c005041c140040503c000d0352503005003440fa82082c40044205a178100c0071f001400d82000ca22421072084030021009692160032012841c0400400402c0489054001034120751000f802001415036640c412145070620f507000e2046504412001c1000380754401c081c503040f48180b0b00500c1c08100a0b40050000b401d2580300c4031450600d1070410041c5078080c40f0b080314030350040341000c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 394554460 1250 394553210 394553233
    0x91c02030a140903101a0405070804050d080a0e0d0306031b120605060f090f01060206060a05010f030b0a051c0203070501110d1b1a0415021e2212060608 67
    0x7440040c0c2c440b100c0414404220000140e5041012403c0080240c80400000c404928224900541c03030407000e01580c00c100202d08104c0c82040d0782d900c2150480c0180c009160000f004841d00750002e400d00c0c2a898483c1e080c9441c12909110b0540f410381c40717840c002039051545c54002d07a1203412895081003034400e0f010400541c4504c503011020030b80d01040c0002e883e43c070100015560b0380c100c003030103411061940401098010300500c981c1601d240ea0201caa00382d4540e400c011480045008850001e03201c90704c0d18062a02a070081010100e000b05944846915200820b54074085101c1c003100518403141c9020940c101400407101400702840c000c80d0024070f076007007159905207041c00d02041256806000310442388601d1060300b0305501114541c0900c4e03d4007210052000305803025242900c4c034800c1c0781a5110f05200301c910901b28600200300c10350540c0b0150210b84c226400d007102824500d94001d5442099528402c043c00b40c01c04400c1052005080a400301e40d0a03400c0a8101d6201615051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 394555710 1250 394554460 394554467
    0x1401090614040b07060204080601030c0e0603031806030901110c0714030f0d1209150e06070c0209060409050c09040b1603020c07090207030c051006092a05070206070b091c02030a 78
    0x900f55490042000da45500c180362100003482182d000c109240582d0001208001301c40500108582e1503101400440d2110401c040c1c41b4850300c3d069804070003115000c8004c03420910080c1d6441a410000060040d403940403c104940c0700340965038003031300a40d9092002c070307a1018541030440d0080c0e0040804112113000e543c0d464981106001c01e010030302d0150349505100341c0003244c42603840f01044484c0c41c614108400540f6106218003601d000c0c140002c0c3c0039a1049201c4517649400030b100c1c540649441c0305104c024a881c06058501d400740c41c8580310191145903d4034081c62040c40c2000c65440d08100041c29000d00d00d4201003014010030a00100002c00203401041c3c3e1412400141c0d6568130b4941902c0c2c0808003207004206028101c4201e1448a0580c0281e040301c1c0341102c240017485014212101583c2c5c1c02c0d14600703010003000c10880103640702d40090b1000307900c080c3c803440ca4510b81fa01e82490100b42150034200e59401440310502c0f400150310b403000c1e442c0c1d9500045040c400d5440024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 394556960 1250 394555710 394555717
    0x1f0302090105040e16060c020901060e09041b0e0408220e070e120109200103060302090c0c01090c300503120a0f02040e15180c0a090504061401090614 66
    0x1184110380304c3c510019000790610074443c042e0040000005010307524480070f00210f207440342c1684034602c400000680b050086804c07214608008028040564840d40d42c0015140043c0c02c1c84e8036441c2c4000d010800e14411103400d13000d98010042c0c2c5894601d0403134082030008040c07500c881d06c00e100c00c200700061491000359642011250900c100444c1e68180840e24210962416030401d6081c0f103a0030043c0300e2800484074400c400100000c0200500100541c2a1381081c40002c3d04040013030300251403c20030b08007524040341440004100945151a603030241115038220f180e200c009507012905a40740c802c1c00500040c025403d0300e24540c07103a15a03a03100c0c011618803095141403c4001040b2804a074824404064044000c40d1165140c00c10020101e20889050713064441d003c504440c0c0340f44c50845000502c4001c0d0011041e95140391710400d840d00072280c15410700c40036001c041001e580b24080d0001825003840c02c0c0314501140d00004040c0142c0e940048280704c030381080c0400b00d43d50303e0f045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 394558210 1250 394556960 394556969
    0x1d07090608040821040f20010512060a050402030c030a0605030c060a0f0207080f0102040f120f02010c0f080304080903150124020304030c08031c020c030405010c08070212061f03020901 81
    0x1c2c141c40e011001d0f10340e0071340300790b4020305520100d4007803c22040100500242601601a42c12804076507020080581d421880e080c029000c51001d00442c072080c044081e40d04c2e40058080d241d000b0b2550358502080603600280c8001070680400310400ca60300030140700d684001e081c101c0c000d0401103840c402248051090025480801c1111503a088800d40204140f000030714400e02114080e03900000024000d4100b0300545075040742c1d18800259140a956420640c990010070f07001b07880c202e542c01903801c1203c07060b0464119040c8907402010485000c06180f249018408682d03403038041704d040505203640204001e0005584070014855140c00f008000185c1c4d08288104444040b014002e92840c06168001032010400301c202294205000c0b000e40103a03108041e25408107172420320380d4010b9002e0708110440690091008020030342c07051004500081c014070f10141b40c00da5540220f9050080c0518000f502c2c1c0c41181031101e40885100d0301c459004440103140c2049007540d00040380c24106210703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 394559460 1250 394558210 394558223
    0x60f01030f0803070e1008150d0b0a18060c0c030906051207030f020d09060b120f1f0b060a021b040903020303130227010602060703180f08040801061d0709060804 71
    0xe244a4058201780e641c0d5880208404803096218000030402c20049890308190a441508841700e402c00540d42d42c0300c1c5600c50007400745642e8032880c000041a400810840007441c00284002080040c0305c1c0f52010704007030707807a607800b8245401d01410390041a03001c0380410a00700900c00340d0b481315180345600030403d0b1401156001e04186210080e005105400c10300714039100f825410444103600c1200d240c403058a331b02c0710501c02c09002544649046071600c0071038010501c1110411011143d0700d2030707400f07101000505c04078140003041c881d0301b00e208080003591292144050803000480515004407040b1014030812035180d600a44900001e041c1ca11031608040300340046558681c6d9008150080c400c400600146624958400410a100318400341c05500301140c0d000d803003030044840c0d8100e00c0c80c182c460a640e075594910148052101034444610034480450a08801c0c041c00001b0003058905031007010884170b0f00418410040d0500081c44410482040003c0c0c01c4000c183d4440e07000207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 394560710 1250 394559460 394559467
    0x203041a0705070327080a050d1707080c120703021b01150e100308031608062e170c0c100605010c020910030602030703020d0c032c280203060f01030f08 67
    0x30f01440d1540f10b00000e4050400194a01080030341b8001000503500c0e002d2022161240e105c00010b0f11701d40300341001b003030b5214041000110300a0040035042c0e004681802c20529000000c5502d0b94043e10640780640040e40001c5c0b5080005010020a081841a10000c100c0c00301800e880e4008149a44504c014250703014000a114000301c0010034002d507001310010b41e4130310f4090201c00d812004c08901c4800b182030003000c103034107041100700040201d1810883d110141170341150007505400500759441040080c81c070000b800001d081150f0b0140c07003001c1a0944071444131104c0d40c00d01586d0f01c100000503107446810000380e0391041001c03080c81c1d015215515542c5030000c0303400790300c0310700e0f00040c150740d00010a102c100e551550003800400031240f4200310358044107000300c0c107454400c0400e0310001e800b000248107195805c4000b02c0345107000d000b01d130a81d80a40ca80710007051110310701c20822503002c03c0e501007036003028040d49901031200100d6050b95811552031941e00350b0300d001d02902085010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 394561960 1250 394560710 394560737
    0x510170c090907211a030106080307050709060b03040807143f04060f0908010c09061704052e09080c061e01060c081c0b040b03070e0402090603070302060408010203041a07050703 78
    0xc4c07011105d0004064001d21400e52514180d0750b99601001080f6100c2c0f00d000000254605103110304070985040c503e900d450764071903440c0c14019800540381964015071070241e480503440c0800011801c40360104600c4480101d41c00c84a642040301000444981c40091b2450741001c240c004031001e0350300340d0800d503040054407801121112055000f4444942c03810703003140e44054000300604112005030388d40000c50380d05540300d2600a40103540042c19a440320b208103408540038a080980340c920082c517034455200041c5c3c44425150190702c10303598070340c00041c540501c0c2e000b403106aa002c2134030780300041a8001c5140a6440ca02c0500c02c02d0300f00010314090b0800c10484004413108141010401e20030241d00314814402440c0c010070351032180785041c114907894140882c1c810202c1e14950000421590740345c080c00030800008000031b0713142c09030420100050b9122400382007c1c0688000041c2c03a4942450905410079030040c0c19a0610001d0007008800c07076010044a18050341841c0005820494 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 394563210 1250 394561960 394561991
    0x9051e01260307081201050d150b040e0a0b06041401060816090b0c1b0f0f010e030f06090d0305011d28020f0d23010510170c09090721 59
    0x4400141c45404005070f0a424400310602401c80c44180c0c1e0b120000c5a40c3c0d443c100103c00d160720f00d00070584101031540c14041041580000b001da0809400421800328280020b42003450000f82242d4050114040c40524182480f69241070200120040030799410458040c0c00704000038010580d900300000c0c0b48028a104400e18001440d0209110b625012040703401608e454003060f0785c10040f407400007515140e2416180c1034032000ba003d000041c80c40098030046483c0012380c1215038162082c4908034040d03040c00c000c030320f125109000c090107020214032001130a81300c0c1a0f01c03000500c030a9181c0400d080e103500c02010b03081800900d2111020f045410028111908035a58202503880468500740040300c0344002d214030782400310200600743c1e82c0b075001e080c0070741180c42407505480c2690041c4203e0034503941106046806090815102014041940719200111000d62003418040340011142c00c2c01c002d495008032071818010001d49505042031041220010b14281013070700c07211b01c43c042c00034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 394564460 1250 394563210 394563269
    0x60b0310030f1407150e0a0b090409080c0a05033105040f0b10050d0c030608061506040f03030c0209010e04051506150318070e0702120a09050603090709051e01 70
    0x41c0d0030f091302e14031696100d4040c1a04107908107103002c0743d80944501c1403481d09565a1082d03c0350317a01d025003404901c10502c001041031400860325480100305100c1c4c030781d4040191b80c0c0c810b44900c00442d40e0385d5000b40c0807070004655005140304084071200c60404180000100e1041e00c0d01983c0005841c400380e528403015006080200d48c0204031484480d603403da000000b800c60060760a4180040b0860200807022a0494400da602c1a08590701248491940f00c120445a680051159080ca81c0f1080c85d00e4048060f1341c405c8000c104258a00380850611180ca40e0042401e14902c0c080ba10303180e200c4684614417206448420070b00507000410366500e0b103050905002c881c02c1610703124541000d074400c620602c101085241d01c2940030000d032800c000744450384138406c00c0d4080c003003c01881002c44481c1d0401c584231704c10b1240c00c0d00003150548170361001d10310845013140103201c01450211808100c0e60003030040d408400c40c058203889070140c218203050450b03020500c451200e001d5800045000075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 394565710 1250 394564460 394564493
    0x60f03070c150903020604060e0f1213030b0a02090a0609080a030305040c2c09010e12070515150109050a050612090f0d0c050f0c01090e130c0612060b0310030f 70
    0x20f00c0c25003420207050740010301074803807413007a14100601440074416550310b5401c1045c8000f00c0d40304d21488610390308407c0c003800702100c021030321191064582c3d91310180c500c07080706c2000030540c0c04141c100842c42c081046800520090030030800702820031641c10b840e01c04905016062549034000b044c01c01000c0b400000042240040030030425401200084401007003862141d06884002c01191044030103100c1c1c0302c44880100000c0c141c040c1020f074011001c1c0c0202000b92000d002d601d202c1008420500d4103548200c9030001c1c450810f00d0210009802d03080680c201d2400744468401c10b00c01620b0354821940703042038511241006a583c50580b914018261100c40418000c0c000ba6661407134005010070f8015210700240e0f01d01518001d6036aa4070045c404210340001d810883c100040703510008002e070414108141c5001c40b178100d403105601c0e919031b6480140040c07440000c0d03500702c680a10881f4003500ca40020245542003050304c500c412941e5000290012031000c160004100001d200207003441e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 394566960 1250 394565710 394565753
    0x150507021f0509040e0309060331030f1701060e06090d05122104030203030a0c1115070e040e0a0b06030a0b010902120108030a1d032118060f03070c 65
    0x901407900010080d8000300c641c2809141050301307108402e8408000c4e680c041102a000300d09560300e514002140c840702240040e500e00307650030080032048980c40140b403258020f40b0b5403030844200c140001c055850098070b400186440380018080940d00c01c04200e0050b100300c54031a110b800120000c0c041000c6800001d269211700c480100a120820024101050f00c1c21780e400c82c0b031004441488010242150000c0068000304000784d80103c00703510210300103d880c43c0007142c00d420480d65078a02040054000c000001003000c001d400c660150400c105c45109503814850680c8039601181d4840101a0091154003902c00040e05c5440802000022603005072045003156034400c4403100961100c0365100180400c1c400101d4a032000200301c2d180c0c0d0003a40d0343c07401c03808109607030310202c0410b0143c401d502d802011150210421800d011780c10140b6490b100540d5245811130080319040b80035801030051609002c01a9809041400d03207512100900700051700c1c14940c40e146480ca00c1c00c9c80e07000001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 394568210 1250 394566960 394567009
    0x901021b07080f0610090908090301141602010e0309090c0915040816060c0b040204020d0c050309060702161401020109150905060f010807090e0a020604120b06090115050702 76
    0x18000014070340048070700200a55810001e480c000b030b5201c800460724601182d1400e601009001600c1d40b11101d03403030007940342c18180b00d090340010742907484a00c00141000d0409044c0900c580a141690790900300300d00003004101c1440c1803494a174003504042d13500c5100301070000349032080c0c2d0790100c414501c00102072251901060369004c4aa800c680100c0f262482100c0513109010b0f84540c6110948041b5182e01040300102c2d038502005910081049810640901030680344008a00640001e02406e4540d1500d900e00610003914107000188a50119072007000442a200f01030851842540d45a0410000554003240180d014169003100100561410f030102c44a0510f158429110b079803040040e80c03a59207400f82094a4101d00380218100c03034120810400808400d540140c0c1e0007140351042d03c02c01000c0c0c0c1c002410642090b0301440386464a121901c0800011582442e4821401c460303104955042c2410003071011345040801040c8400042d400d8107558903141c80a0089400c1c034400f0b105c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 394569460 1250 394568210 394568257
    0x302160605090d1d010c020d061e0902091311060d0b0d15141902130308040305010501211104050606070f0c0f0501020f0c041d03040806060f060901020601030b090102 73
    0x70f4481e1116031201c00070700c0f000d8850050140800400495020581d51a01e4602e4250204001c0075080141145c50582d5501240980141d6140c04c03200a0582c4800090820a034014401c0d00c0c0c10080c005840400c2c0851540d00242203510310400301c1c60140c6441b500c031010342805100410048050780e6000098100c03100070003240114240c0000d000c0f100500c0b80490b20150348d421088152010400e4803080030000c20880c98990140003c2c2c40c25100c154941645c90711021040d03409504242c403d40d44610041c8056500481c200002010300d05c10380001980945801419804001d0020721843d103400104c0c42d0b55582c0400d81c0c04158000d0030244c90b181c1545402034040d0243c2c481c4550342211484006810760010810311024030208001d004680480d10401c0000c19460305141d114401c0c0044050310500100040c0001d03111042c0103002608119003001451401c0712080da2296108112085299902044203030441e41d00068107940364481550441c064003034001580c02c0d1600c1d0645444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 394570710 1250 394569460 394569463
    0xc0a06110702040b0913170d061805010e01060c0b061215070e0d0213020306040207080708070507120206190225050a090c3615080a020910030216060509 67
    0x180c820300c01c0314100800400c000078465180012030303440010500520100011800450a06e00d480c1107141e87d152818002d86a16030440b0090741100700c5119440d1420075112403140f0499000d800941d002004541c54a03000801c5140c1e000e0004110351080c0d00407420790740320002c42e9400c024002c81502e41400b0942d0741ca03070304041d0481c0c284000481c0d51400e60030600341a441c1c0b0803000c0e005440004088143e0040c440a50300c041c2041350442e40c01c1006501084851002d0305042d407045d085c03207070b0b105000d0500921304003003908040d0307045d4414001c02c40103a0707400007150f28091442c8024801038030240e5082e8100303800c525031183c15160008085408204201c0140262101120540c520a031542c0b00001240c0281c0a1600454044001529800c50081030f440842d02c544c040e071201038141c41581b00c0e020502d90310407a0a02e600100401c3e11581288040f6405500701d0300460901d50010000356141d2141595803041c160300007050040800d440c1244600260003000501c0f031802e021a856 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 394571960 1250 394570710 394570717
    0x50c0d0e01090b0336100b03120c06010602100c051602031e010b090a050c073807030b010e030c010507020604050a030807050616090b0903011515021005010803030c0c0a0611 76
    0x1a9450982e160a4001303509040c800909810045c018600342c401255800e004290600d0102d0741841100c40300c1000c210210010010b030f500c5400500750b1940340040c00303498028400103020030241440381c0360241540c030100381c8003041810300c0005001c11090000c28244100452841e6400e000729900c118550f905401100d102c41302031380c800301a0b94840c04018100c032000c1c1d80c600048803080007400c01146900341c01c0b6041d0410354a843d51100c201114031501c910240c1c100816400c000c004208501341c2510402960314003e0810070030b20130f4500d0000340c039440040481c60512201084100c107649540003135401034074003c3e0990000700e48070304000d0070507048160212514400c030800110760000101200c003640e691a2038045200f400e0100360300b5140c0140b141c0507010343d03980d4000b107210041601384d40c000301103080807c4a8140d11500080c103000c140500450520304040040040382000801c8942c0400c2e2203038440d0315281448003290500a00d0203015082c50705020f580307031406207142c008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 394573210 1250 394571960 394572001
    0x4050124090e16051213120503070c06050702031b070305061008100908070204151707081b0d0803070305010f0504050402010f0315080717010c050c0d0e01090b03 71
    0x3a090110620400c81e0300d2541401801680324a94000c55901d01c1001c240c1c40e0b0030030303050401d6070400a06014000060302c00302da40142030f08078910703440284000001500b036803007814944030307140d0324000d4409000000c00044c014403c43e910800660081d1082c420355150f03031900140d882c040f15200c0e43c600c1e594640340c042582d15000c0c100c04182005081444d600880d00840c025052040c0f048001c4401032208070000c1d16101401c210b5400180c0d03492160503035024041200841440c10000750032400151030210301c0720360740000c4051180110020b000c55040ba00ca141c40300d1108500004182c40724582000106002c1c404814810502c0d0103810842c141e800d0402d590302034036a64020401560340070b50340603001c10a10005100d03901d01c80c0e04044e25543c646104405030bd84e03600d09840c603113100707036204159030b080714130b0010300482080c0540802011946052400e20f04500c040c0e68580c406c0203108800d100518101c940d240c0d001398071b407a0041265461241d04e914100c607505c0f0352020702034030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 394574460 1250 394573210 394573259
    0xa0b0619200f0606030c0a030f17040308180906010c0f05210a0206130305120619090207020411180d150606050d0b010804031b0f080301060f0206131e11040501 70
    0x14071203050003d81b213610340ca07005115504007072564480481060f840b01c010341e8642150002514007000140040000f140719542040d5038404103050b004050424000c03e030320a4048105000352a03902c140740900840e0000018103034502107190441c03506820902d10910018080940428000000c0141c08810301c1e40e002d03240e042e40c40d254081100c0c4081040180480c030103224410b001d401c171004256022001400c0404460141e800c40000049150701c980c0d175568000820004600f800e01504005190004441d810041da40214043c52580e14618601a4205400c01400d00c440616a5800e59590441c10424aa03c03540010f00c254018500c8078251420702c000c09003194820380d191441590180d50300094840340d0541d022503080c54030401c1d104414900c0c4c0440104503400300949c000c103107a4482e0380c5121186880641081d60050401c0800c18448502c1c0d0045a499075084d9048109440011032106052602c4072081e100004d00720f400c01e18100000c59414649460310122803880d50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 394575710 1250 394574460 394574473
    0x306010f0903410115060e0a17030d02030906071e0e090703060503070e0f0609070801140d0506102909040e0a020607030905090a0b0619200f 62
    0xa01078592846900c0000c1616400001d5070380ca103151122400c030407a80041040c80c42d0001149064080551a510091180d550300c10300000c5801d10740c0900c0080043d410100c1072031030000c00044419089100d00ca10041c00042c2042d0032007024000c071140300f40480030443d264240bc1d410340c0d0b6942811220710012801000003d0b22150f00700517004540131540d070310b0406941c1404284101c801020701100189921680c0c04035241c0d0f406d11101021300807200146c0d40c1464407071220000700d100036059a0107860711a05205101d81c0c8843c607141590920300d1403d000b24524000310f42030001c400c070050480e0142e2010702110000703d00d4100c0c220346181c0906a0031410582c0ba072103c403030b10a501103001e00c10400020300d40303080076007000e2420305444040e03d409204030703008070701d0f194428103045002445210007800b06240108103c0e40181c0411003c1201202250100b10309210b551411205440d8000c0003044035480f45804020b4214a010ba4101d8201000107181c0d41d00318140c8000e880e4082d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 394576960 1250 394575710 394575737
    0x3090b1815042303092d0103060315020f1e07060b0604050a03021507140d120501030f0f0c0312020c090f0f0c030703020c0610030212010506010e04020d061802030601 73
    0x5910842c0580e8003c6020394030380c01412032004034215054402000c60100744445003443d0340d220000441c4100703a2403401d0019a021107200944014441c084c0d044c5440c00c03500f400441e441400c1c1408004140304010b17a124411006202c40340140341c204441b9243c0c001c07009050703480d010080c0034902e200c0d210501003d492042004202d00490041c1a0041003000040000d4a07206070600340c180c1d52420a186801070544a94400c080d90425840c696401034446a107079544c06115100341d0002101c04111039410365841841409584101a01d5041a00342c040148007044040c200210703401504004030315170281d0081c1d224114104d81c43e1203003412100069001f022403000c14800d500c012184402c69890107101100d980025007140c041681c01c1c410200e15030010044503004405210b492003c00d03103184100320044071486d076000301a03410700d000d01000c0c0c1d03080076050242c8401228056240c00c0110601c2005103031552281d0307411050915001c5034401207500441c0030309001c1c0e0340c1c01d9804480c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 394578210 1250 394576960 394576993
    0x40b1908180d030b04110d09030216030b01261b0a0f030c03021009091e2703120f0207060203040b0702030703020316021c14010b010e0f040c03090b18 66
    0x640441840d5500300b50032031a80c4501c00c0d800180e00702002072002850070400e0900c111355800400c0fa10818940ea4424601170507010045205012040c400c010200c2d4107607618032058100612038402001800211102c0311020f540d030385401006e0340c008480080140c02d0240c51a221b01e04c3c80b1a019a41c401808110241030080c200b003600e4025007695070051031942405020968003801d01c0c100003020f800070662075982d01441621010f40d0406c6540c0501c501c1c0600e007102c0b6240c5407148600b020500004468041a0750f501a8a4060030030381400038125a503500a802030202801750103200150007010422913a004e58040c601400e08000c40b0364489500741e0340c0c2d1003050360180160b0b02c14080c0d60120000d55070b00f005005d2015280c0c4c1e4014180001c130f102c5030b130b001000445001d54540404070036079000b441012070f480c0702460300103080003241021800030703070540c61514041e5448842e130515683c0a60426030900d070744406030754094a08100805203005c03103c14403204500400640707291072580f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 394579460 1250 394578210 394578241
    0xb1302030d09050f270705090901060305010321020d0c061506080103170a2114040302010c0e0a44070806070819020a090306050907050312030f010b030c040b1908 71
    0x200341c80441c091060a170501844080010107031070800c83d0420221055480c0c41040c607001b8919a14041025411450310707150101e100e0307410170001c1441c00c50340c848050b400104d032116994503040c0040105e00900780003010784130f003401c003880c50110ae80300028443e40c400f0f00c0f41d040700c2c0600c1030f40c10070b0710603070903c0601445080d501c400010403a011345505401647c130142d5540205000002d582d109000c0d80224030b580c100e4042e80980d42d11a00d045819401c1068589801001c03a225501c817030524803e00b48000030030302102c04076048080c06080d0301ca09030048a030b03c0140e468480c1e1003e02003482450b40c071039003806060741d1400740c8004124400d014441c0107000b66a60060304c2141d44140740d00300000e400102800e030803c445008000045035031886914090591000a000d5127401d00e428180341c185503080f2011460010010028850b035006086410b4800252820307907a5111241540010300440c6c01803150214000781c080c80040504e5a01c0d8501d10503a1560100e03a900c61b01c081c1d0102c0c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 394580710 1250 394579460 394579489
    0x6120313050a050d050c060f090307030c050f040b36041119060504120602070b0a1b050316180e07030f05060f0f060c03070c1701060e0907030b1302030d09050f 70
    0x1b0710004d0031900c5490040043d107030700c0c20040e00751030501440b800002e150000903801612108040b290034405800c0030714580c2238141c0243c400b03000000c40c250120b01c0c030706010418001c9010110340c001a01c070040c3c0740b14521110142490b03907201c0c11305052044110402840b0584503040316a803905000c0c01201e032402c1122100d464441c02d26281c101c10300e0400c0e9030f50034100c1340300d50b08204080004242d401e800f801400c40c0100080c114203604019040d14030342c2c2c2120424040e003402042007035030b02c1030f00da0342001056181c0903248003c030050f8030303880a000d60007a4100260721402c012103298587d01880b8184078218007409183c0f506010f10240d441c0d41c50180750007041c80c20120b1403505203c001041e060501004403407409001d603ea0610440003034000c0703182c03916864030ba145802400d00076080a8984003442c003c4034141414003580da6885840020103100f461130005150040c49441e040d41c0783c1e009000e81d48450030340f0f58018140142802050b11601c81c1a668603498204102c0681300e64 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 394581960 1250 394580710 394580713
    0xe070c050712080403231e07050f030718020909012301030908040503010207030c02090106032d02040308030f0a06060e013e0a171602040506120313050a050d05 70
    0x240c0c02e01540d082012000d0806440141c81000000005561056558111440d0760b905014071504d09200ba400d0440e0080003c40103000c00b02ca1600914000c40c42504071a0b00700e911708020b104040201c0e042040552064891070b920098010300000c0c550020880548102e0b40071100e6a201d06260001d080a1460141e041c3c242c00f89510795035000381d0008180a0041240a040c580c0c1c0300e001a007a80c0c00b0070421000103900c03030369000860800d0062540500280c0c10107020203010482070b1083c80f1361501503001c20200000e0403109088070755040310003554001c49410b0743d92030b06d85840b00c003003035040d18043c080d140350200c0001c80d81d02c1903103a2406078905a540c0034220b04400d41420b03400c845402d0403809443d0728000003074101c0411855940c0c041d41c3c00c01a00902055081c0420400041c1910b0120076904009040c2c059825a60400420f41d0403900010780d500c40001103080a0076002801c08980300001e02c802c4401015807802c401c50388101c400705002503c80e014031005060311500100315 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 394583210 1250 394581960 394581973
    0xb2a0a051b010b030633010509060f040504021612030c0e1318050105040c0b090a05120313031103120f0702040b011e0302030f0702012f0c070f0e070c05 67
    0x19540c41d041079001a504a0000c40c2d03d5202c1400681404001c0c1c8889103c0504800d42244103104048080110070b0403254051a402511001800324403801ea4440e2055100080d04114000f032541170742c0c050324015204548810b031980703c440807554600720544010b00c0389807010014610034020b0805000f400d944101c5002001c2040c0700664644292150302d01e610b40000f41c00110f40300c0c011400d850f00540011800d4142800c1100446400790810000304030308020b881100d4441600d51070841e00d0981304020a00d120044490860094000c2c00b46161040040001800ba40b04081d0908078800ca06540c2101c00e146e0150210f44110307049c90308031000900448000d4a002d80c0103008494041c189501041c505003100c540d0b0350100c5d0600c0000c42d40c007101b40810b0f1003101081c5540466540000c215001e00b000807048145414843d10341502404134503e02d04002c04002d03075150011080450703560540300e009000140c41ca5000300d401140740700001030305c01c3d403089840c459000d821402400300e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 394584460 1250 394583210 394583227
    0x6070c03150b03030f09011b17130b031302040608030702150901031e060303170c0304240c0801140603040803011208160302060f060a1409060d0b2a0a05 67
    0x429094145400441c0d40c0c410008260342c409000600039403003d030405a80c1c51110000240085251440140700040c014400350005601802e0984131a9103e610140e01d4070340c1806a00c0c488075064201d0420190040140700044c0340103218018014802c95007030000711744030050b450381d902441401940c40905200f50006040c0b91400402d001a410324010541c00c100f83c681416000d102100300762202e96404080046c507034001c03407640c10890102c4c003204c61400c204050320075500015002800d00e1188043c240071030842400703882e070010f14000703090042c1210401c01801c00802440790811904488001031500d00e441e10440b48a25803041003a411350342410301902201c0c44c45201211418801c01540e20309894500800d001944258000d007040d01c2c142d80031840c040e10180a450191500701403d02103601040580700040307405136031398011540da0500003401445840009040309803000184881c0100448200c403501c942114003c110b0601290b0308400361196000e00400107030705016004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 394585710 1250 394584460 394584473
    0x406080115140a09110c061e060415050a080102040e0a0c091e0f0e010303020f0a0c050d150c0201022d030f0a0209031005070210060e0403051614030d0b06070c03 71
    0x4400346006803241c3c0a050326050020110b40180181040c000c5000c281c800c00d44804101e003a500080d82c00b40344d2801e0344c030300f814000c088101400a86c851900c5180b0b040c010b0242028042c01007000800c0704443c15a03071110795000b076006016008032a05e001001900c0c0c0e100600804a02468507501c2d42080761a02040015607030864081d28882040741c6000254081804008005401400b00002c99035145280180c640135591002d00c41e550461002d800109000315445001c44505840194a0104901e00b0703c0d00c145100c0012880c5030302e031100d100e803120ba055000e080d005000a1160202200c0344203808400ea0161944448100c0200b0025003c03072040ba6115800039411403002d8201240c8000003414141d29554642e981503a403020411070756410003100400b05d6000800304105801c1c4000c11007038040c01040601440400541d6100c2c000441e14541d626540211034101c45010591011340c590380086005e40c07a044c1000c00010180c0340040c200e4544590181d03500c1e80b403e10315070703c0b070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 394586960 1250 394585710 394585739
    0xf08060a1a0409020711040b010827010920030607180915080a030804050d03021809060f0303071101080708070e04050c09030102040605070204110a0f080408040518060406080115 78
    0x1840090001e01002034030003c28000b0b464418498400408850b4134001800704440c0c4800c070290410030900240920340b1282c0c2900100301d49800d11103601124400c5015016108909000b4800c18055140785151900e03814001c070502d800300d0681d0071035166814121400d02482c62402d901300c00c0a039040142d0b17006e036842000030742020010f042034a66948a6581050354483c401e601181c034038001c001c1007140601c00d240e900381c0c95040c2107007042c42c03003040503100b9a89a59894007601403600400e0742a5031380c400911003440c005044075550001840d1080c1c0a00c1c0b18103128ac0840c0c010400300318070320300684034184544210b58850246100c0c0c0000c00003d404040d002c404175900400000b00030380c0302800100301130210b6403161940c5800b13074418081162032203200d0f54407200040c481c003800340c0d500603111200a0090320702180703162190704010313403640300b254003ca60003030803400f00640a403401440d1901c5088215801c029050707895001c035080c0c65800840b4010700480c24400d0049038140c4448 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 394588210 1250 394586960 394586999
    0x90b010f0813020a06020102071103031602040207060b09130521030a1829010504020c03090d03030b0301090b010e0609010302150a020a06060608042108060405090109020d080a0f08060a 81
    0x100038546403d802107061150a17410034070040c2d4000400704140140500488140c0c034003500218a403251090110320800d00b40c0c03200070f10030740e000503400301884040d0300980b0410100404509907424074039100e221010101c03900700d8081c050960201c425020316443d46400040703000c040c2e46181d0318104032000810304046142d100c032a018024402082a016400050714855000700160306208600203c09120591000b44aa03004000c000001031005c81920703a0b520042d0340c21002e003090740c03034150050060300d5011a050342c81c04175031078140020110824120341c3c0203101101140ca440d4107004803524240806034204810124000900d610383c002400003a101d4416603100c000542e0340c820546055600040004010205000500078080c07070441c80e26440c0e80d0391b003011512850000e81814401841c203449580e5400018080e103c0a400964825130b0080c000312040c4114076051060360030041122000402c10100a80358a024401d85409454002d01c0f031071400d032411110304036041000c03c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 394589460 1250 394588210 394588231
    0x317090a0e071e03150b0c0307080a022a0f0103021e03130209010e070f0521060111010e011a0415031124091f050910180915090b010f08 60
    0x311143c5000d43c42c425046040e000b0f50b00421500c61102100b29028171a41000c84580020051126846000411501d92580c00740e01c4507100c44030b8000a90a0182c0380303070342810074114480c03100100c07400c54243c1c803541007040301c03402c2c3c180c040500110200d0084400c801d8240c4605416403080c4904000550307030000c0c41e4010042017501d694003184100b102130340009140300e1004140302c0450f80180b04541c2d154114603004d400d1541c400030f184081e000c05010710808102400c04200035901c80c41d894001024040024440654183e145034020000c080c0348a000c2221039914000070303d0325020340840012000131041c0c010707007541c4900c080e4070300a01d4a140d00034181041202520140380e0021001d00903528040c0d1901c0f00c040520484c07600c4503444020f81c80d408041c2c0054180c000042c0c8204650a88556002e8207210078162584e07080031a901d030013486104400540c03000290000c5906101c500ca80c05000c41d910a5134000b0b5448003403c15011605403403102038202d01c141981e5901503070144 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 394590710 1250 394589460 394589477
    0xb0a08040611130311040e03030708130602030117061005131104080a03120c020303060a270203150111030309191e03030b0f03061b07080903010c090317090a0e07 71
    0x140c140c64207a1281c00004841001c60f01c1c10000d0148810203030303100c0b840c03d0300d090190344200720b003054503440028802824010f032140480c80c03080f04c0c400d9000300c280c0c1c4608215a0b07940c44510456a09440f2580c14815201c1e08000400d07003140e0148c0c5108440c005445481c112403101c1403d000381083c5902c400c1c01e000b040c0000a0200700801082c4244e43c0640c440c207524210380d00c1c8201c10398000488803801c4d54010401e100c80303500d40c0070408044420341e2120361b040400e9020a0b6090f0920110121301d664000f0090188201840c41c03849280902625008060780c0c104064613202d0008a42080160700481002400c21401d004441207280c031a41001e41261241001c8804111882400781e00003550381c00b9841950901e00ea5401008030308070010440ca2819040304400c21044281c0e01400b07010114942c03040125410549000000080013405000400b400c01480c40440344800d8509856000c140f0b11200b50348004c48010000c081c20b5210f205d410010036400710368002e80038004010251 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 394591960 1250 394590710 394590731
    0x30503030c0d0207081305090a380405150f120316020a03050a060203060f030f070b0c01020d060e0601031514150702040203040c0f0b0c1903020f0d080403090e010b0a080406 76
    0x21802041000368100c1c01203081b90803e41400840000104805019860f100e10f0710301c1d00c01441c4240d41c003494050710412b0685480351001590f260784466103500541840c0c184094680107410f400d00c000070684031000d51900a200f0412403003070860840b4045c1d0030401c4403c0a13554038601040c081c41c0050464803c0f41d94a64810f071038030035030800030307980f656002c008d000841c40c14190660705031034110024914000b40c0071005888510303038824074003032420018040802040a4054401e98002a0001c120103580e600061010306000c40744240024541a0b41001840080e88c8079016500d07910078010007100083d05000a107031001012203002e110500040005903900c0c0000c0d845144142c00f01c61030103150421351101c545040c0c00140002d881407081c2090440c0010710070107115181c0103044503006807400c0c140d052040e410f11050180c01441043c220007a0046000ca01a0788241d4910100c00d546e544c12214a12081c00b507400c090100f00100300a0070310544196030006d000300303800035829511 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 394593210 1250 394591960 394591973
    0x42103020d17041226010e0c191d21010b0102070312052214131a0d0204020405060304051e0a0b0f07171302010809012d020405031006080c0a030503030c0d0207 70
    0x585594080c1000014020032501000403604105040c101d00e0500002003002040e06010302403550400540d40780481b00003400241121a540010b0300581d2f104504508074070509220703040e4040c0da50b0a090328040c5079403000810350116500407051030004104091308554940c002c0130000003e01c0040d8040d00081070200d0044020004042c450540007a1101402941106180781440c4a0719001d401c4201e44102c0380b0300c80c1c410f001282c404031040784a20000340240110340006401001c0881040104280019100b504181a080d0b44116100341d8850301c3c0e0380c00e525a0b000b8005405038010a0744002d030281010341100e9141030100200e00c440000d9001c2101c02c5941c8200d004a048001c019540c000c2c034a0ba4001d80100024040c80480080c5500010341c1401543c1c40b401501c1c50401800510340d055401510005041c0d546a0078410300500c064072290096400c00e0240800002151809000381001c60354820055401c540d00c042906405030400c5030000c144540800c81070300050f04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 394594460 1250 394593210 394593257
    0x2603070903030807020106180e0a080a0201050105130e0c060d021216090e0105100c05120a0c140a0f03030c020708100c030b1009090b0402042103020d170412 69
    0x10955800541a2031414000e00416021300701e202564504001405030403109a016150721685600100e084508605041d14201d181e0201824001c0007140c0680b00c00e5040d00002c2c101d40084500303818095a003282d1100700c50394801940359640c04802c040c00c0a041240192904420001005060009000c100e420300041180c070401c8103960712600c040701c43d030848401e10140111102c02e103030742c0d070401c400f0a001d0188001c071017082c40102803800c010041c0800681400305c03420b20100d901c51a14120180c01980705110032180801d0b0b54039180c2209800050b508919a042409045054031030344003a4001c0c1100c0139241e085004044012400c02c00401010300884e9440800107140038048100808846a00d103495100d40c0e80b47c0c6054040c1580128408140c1381c1c1503000241c60640c110015000744540e0b40918203c001c10715854240444100d516413040340280c0994003c14903011048510242800c4410a01e51100c4041004503010408110302c030301150400c006d585420541e101c0c010710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 394595710 1250 394594460 394594471
    0x90f031219090f061b02071a0408250b191d0616050c01020f0601090507090e0a02210601171b0c0a03090506040b120730050f090a2603 59
    0x248075000c0c03c115441c805c3da54040c040d0401c2e980003680c0194003c1d107454062140001c40304068107400000a4043d04440c000c1a041080760080710403008010004d00035800007941c40c4500700b10004107843d812045406000306040001c80440ca084810346034a0049807154807544000c0450070190788841303004041040c01d80c100c54050f00451f10f48945007e000b0358800c0d0454000c0202034401d0200002d010b4107592540380e01003031a5545a50484011445521240511902c20203000d010801940144041d94203d0341c101240130311a01041c2d5100d109544c120300240c03850144004900c003a07440341307401a248680520b05a640760703080030390035004450307501e07c1904040142805c00d5040000940201030a503402c03030401e81390101c0c000c0c0c81e0281401e0540344418250010700300500c11203801003640b0301400c009501c45158010008110f05810810019a01e040081590380d520103140500c9008844020014014940d40310240041010115884c00445020524000510902031442030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 394596960 1250 394595710 394595723
    0xe0d031701060525210c0506040f05061b04061d030102071103061003080a0f0c0b0f0109110301030f032709051012020a1406040b030a050906090f03121909 68
    0x5944062441d0701504a5803419105203408440c0300d40040e104038060701201d9014a182d2400d800082c2d03082c2c2d40d0b5481c800c1b00601d030703000d1141007000700401a502c000341280500200c8130316a580d6070700c4900e207004035030191600907400e00c0100100303480380c2d07410100d200021100c3c110500c43c3c100441d080e6004040216440c2c911003134070344401d08040196691040c01706510303000301c031714580780d0760124171807800761800700495203000f4950240151008007420b40d10800c941a94900701d2900780e030350f6400f0301170f43d14414144540b8840707880d009010b90307059a4201b48a09a00205960140c42414099031140034000034180c020174102c1c001054a8001d01401802107101d141c405030000c00c0c50101d03046440c051800e48141c40158895408c85401d8074468000844058032210005070740780196400f0444400000081104070b10007508a18000c01c0c01108440807070705c0303c90001742c982c41c100100500d554000d0020f00088105556035503089640c070050003104602608801082e2807a0000c2912003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 394598210 1250 394596960 394596967
    0x906080601050f010203040f05040207110319051009080d0c1b0f020301050f0c090d06020c0a060204030c06080c071104020403120804170f2d031303080a020a0e0d0317010605 76
    0xb103041c903540c2c12035154424070240d40b9060070010100007180c5103015081c041d41d400316080040101d0070309206040d84004049522044002c00101070348003031f02000715100c2c001c8141d80e00b0955128021004560390100c819400c0a820006d0b010080652206e401c0410a0b00c0d1500041c040c25400000c0d18180280254143c405c880c2c0181820b6031301c081e01800d103680c40da108002c42c2060060a4030040d4204881c1248401c0aa05118029000b120360203c440d0003101341035070070800203038010401c9912800041d92202d9444400b80d4840f44102e8001d0341c41c4204101504c0010104400e00030503290060005090503142d8851100800d117440901c400301d135505050000303001c00704901d111b40c20040c40d400303498111506c6036542e0900410041402d01403062107507028041c21140c0c40141c482c5d0a42d0340b6a1280741503010004818042d203000d4010442e181d0100b201b881e0203008940408101d0f4550101c00303c6d0120a200a030f03a140c0405174100001c034110350000b0001c00700000e000f0015690380a49 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 394599460 1250 394598210 394598219
    0x70c060c1208070f300609050a090201020a120311070b18072303011404060b180f04022b0602132306160602070c17060405060606090301060906080601 66
    0x1190200014882804038880c200003c1d0303940040c005500d440d5070301e001401c0c60f809980505000b8510040c48003d8800041156000c401d9503101804a0b031030800c050000d40c8503444403104540b20f0483c081e0041e0055943c42c0e02240d15502010200c003864a000100410030464030004d641140904a648604010034000c075070101091482c0ea0441c14005041044d00c1c01e040e520112030f00640271421429681e0b1301041a40c0c0c294881002c0d01a014600b0700300340752034070b0002e004110f000c5020344100400d8010003004800c001c4100c0c400c00c40901d1000b95501c840d02040f01f804000e007058842410311010028100200d80c92041c54a0700c50352015031035589841c3e01e041641510b801c132040c0c0710500040a030202045003140e03045800151013983e61650380c1c881c612554480c1610140c01c203400061502c0800460001703035800c50f0041c0c02e10b400d481c18140d206648900c4196000361103544900c01060f11450200010800c0da40c1c02800080c1207652214074a040d18200d0b40a2061500040010007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 394600710 1250 394599460 394599473
    0x804180903110105150405180f0f0105100f09051b37081f0f08030702010e0d0809011116080c030c0405161101020405040f090c150215060402070c060c 66
    0x10010080b00e00a014903e003550544e0340c0c0500800b41144640d84a901040c2c24441020012034541c4503a4150350b903071601d801c1c503566900c03d94000504650b2a020005030100601190368041d210244c8c165504d0501d454400d001602c00907003001e00ba03120b291000e0080c01c1424005281603001d50395030184104211000940d4418005644940c11704150340c030b51800c641c400b02d0303d944143c0c40c541c0510007a00030240c403034160300756403c07207100030700b64400210b50741c14004064061640b00340d9034014640d070a4024880911020b1000500c0c0400500c560000341d0b00034070411070a0010b00046455608a4092030080760106920001e0380703400199a02d00d05c0e00b028000d42500d8101590103020500f0b10040075180f02480e4003810040040c1d030186502c00020a404490050000a00512000c0034000c640d070000c01450504545109012000050300c15860000f103680602e0784c0c01902ca29448403200c1d0b08183d90040a1076071042e03081142c000094440848a8003400c210740d102041d091640c50942c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 394601960 1250 394600710 394600727
    0x120106180509090a1e02030f06010915060905040903171806181c090816050102010c02070311150f070c060f1701121407090c090605090f0603040804180903 68
    0x114026010001003010f1010700166071004150b02c0240000c5980103442040010012a64002c2d03060055500d48071401a00042041c140d4401403410003080106080801c1c040710b461181001058106100b040145016801144400c2c01f034180881030b500141c0302990149001c4414040c034144401c01c45031501c1c410840d01e03601c1500b051203a500c59180496031540e031281c0d420000c0c0c04212040c10344006912551981004140c2c0500b143e031115034481507218540c9150090b180150b03e08070404449a1000070100c0460b6000242c0d540c84950400600901251200354003401031401c10002c104d003000e0400410385070380141a510345441c104103004000e00081d001110401040d401030728070001407040c01d5411503144a101c0a401c3c1a07a00d03011440b030421400d004100d0152060008044005410100806001d6030707130381c0a04c40c0c0f282002d4925004030303141c01d034001119034401c8000d810400015034101e0301503a40f09040555641800801c2d400010012084603100c80c0600100360f007050340c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 394603210 1250 394601960 394601969
    0x100501030c140307031a2502070e0924060103020903070305010e011d120318010504060606260117210706140108030702040f0204050d03081f081f0212010618 69
    0x1d013405500d141c4130084840c40303540402807400c0e19400825500300348000c603405444041d1a8030404042d11042c0691510000e00c5003541c0b0185010004d0403114001c122080581c00c00d9100000c100780c06a0210032203100180405e05041c0d0030040380010390b40c100030400003140308200104c1c00c0e80c00e2250f910300b561081400e001d0418452050904211000301e684500c0307465070000c4503141d0799060703001c14048403148034800c0c9651800040c8001d0206580080050300c40316140e11100c205040d0110b404000040d01c5da51850841c10018008041348554001800c03190704125425000044680c20882510000d0300700c00b00f0001668808121090051190011850700c90311001e600d0256100e48074407580800030710070380d03403000c150f40865500d81c181c802419011348404484240c0e03280140040400f91912082d03032420402c0d07070441d108480354000a4400c15000761542d080764400300644e4141400591402c59000d001100044c0700c04541c0c14001c00301661040f203140000400a4411070580e0131 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 394604316 1106 394603210 394603213
    0x10f05040803100501020f0d08090f03040b030901060b070c05010806040906450212070b0a03020712170c0c07080d0e030d031803050c100501030c1403 66
    0x1461203400340e03510f4480680d40b80e40059a503011564041000f0358044000c1320b00c000c1c03080c10643e8005072010200c2e805c880d040040c070750a42c1c009070404401900044108600310f03009009190062680403202d45c030b0301000383c0310124400700078000c4030f060181001c085201c58590b9031201e10450341160301080214900c60740c1119013a9040c203018034600744040103208268080c100f00096841c05041c149a518045d428030100e4100c640c1303240c00a000b100b2000036031110840081c060002613a500503510701c80c0f468080c004040651180007041409000c0d03d01c3c0c8209101c02c0c0d07400217652070203da140d03001031080f00d290a4694000800074050f8107084405c4640100540c030010700120103071010002041c1044040f58800d1081000d500c80144081d8040780c011002005000d8000c0180c401171ba0301c1d8036909040d540203900480707501000080c00c0006034042080c06400050490 = true := by decide +kernel

theorem cover : BRFrame.Cov 394424460 394604316 := by
  have h0 := BRFrame.cov_init 394424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 394424460 ≤ n) (h2 : n < 394604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
