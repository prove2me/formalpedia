-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2362
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:28:51.629495+00:00
-- url     : https://prove2.me/submissions/d0a3a6c2-40a2-467b-8428-219b3848a0ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 424640287 ≤ n < 424820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 424641537 1250 424640287 424640303
    0xa2001090f03033018021005040b03010e06061209100b06090a0e0a021b07150c241103010801061a0310050904030e0a0b0a17041101050a031401030803060306090609060103 75
    0x3020b03a10800f01c00b408a0a114440305020b03641588000c08941402c217001244100f4a049085551511500039a0700ba80c040c6034029241d03900705140c1c6505c01c0ca00408180e4481c40401808030090b822044090003000c0d10b10050896115840d2180f060781e0140d07414500450081c480c5890719583c0d0400300c1d00700c1d22120150301e8030b0f40700d41e1885406071050590441c00c4589851140c1e00b489000030b4010102d40e03000c0484000012060002c071a00d2000100c0074092542e043c000c440300f050b224011540320804403000007880c041e401842c1c0d0154109038450000d50f591a40c04103d03554031501c20400c0a040c6940c07051071460b00c0403c010300401503016280c05103103504005810140a400a513800002c01010b500585a65000881e141d920035031004001648c50401521010302071a10203028640c40030f00c00e00030700c40c0300c030044030280c0001c10504101600d81d00703d44203000f0001900b83c00f8501440031b00d5600e00d0990140740c606034000d400152a94010000c115203240d011030b0080c1901d50090789 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 424642787 1250 424641537 424641587
    0xe210c0402070c0e0709031a06061921060503280f0302030c030f27031b040b09180d0804050d050703031119020f030f03060d050a2001090f0303 63
    0x44080d01d204241c1042c04113042c1001032200c0660040525001c5034422010000c40c649000148501c0c40d100713030f4041e60041028007008043c0c0001c009014001107444c9030030340400e010700c4280c46a02d0703042084010400da032100244002e05061011504c081d17004d541c5083c020301c000320880b0f00b1100103e0041c242c00240d503130710360415109104583c40c00c40e0000440361071311070f0700c401145203a104811004d80c401810480051079a806c18072100a401c1c000c001d80203205000900184128040c82c3c441c0d80150340744503034416036a8800d070340c3d800380814241c48040d0071640804240f414a0840c0807109005c219020003000410004070429041d00901d00940c80d00d203d4681907002c2c1c0a950050602e180012607205540031001142c5c90f605141c41c0e0032201590186680b0380e40b244610421020000e000700001449820150740c6c04403900c1c8590112200d0100d0754135009415010703042c1c0035003045a128494000c3d581e000c0c0d21b120140485450f580301d01c61542d86d0251807140228a0600c000700c070208 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 424644037 1250 424642787 424642793
    0x31906210803100e161d0303190e030f030c0c2b030c0b0412120c0527090f040c0f05090a0e161d0108030a05070f170a0e210c040207 58
    0x84494024101e484401107117092811641d00035880700c8015500040008900707411359001c0005c02d5290090207400345140140c084461075500c4010f4180c0c0050152181180110341c5040109600c0c1c0150a009151030794080d05640d814140541c00d510300c2a03a442e400c4040d110480000290440428003000c2c185010620b030a40d400403c400000c0c107282800d001304000c0c0a8110140255420306a5031400d070001544c0c0070341c2c2100c1014150000142080c001821580c45022910740074441690322403440c222080001070040b42c0440d20385414407142d10134041080b00b0409a24003400001c6030340c80c06e00b030800c40401c520100041641e00358030380340c8500c204006014080e40c104a0b0001000d10304460300c0750385c42050702c0d651a017041402d0710303180000214900f002c420f540c1c0081403595420b203420b020b030304c4584040c000d640050710b5070700c002e451021254150340c000385900d00c41364035a02d520000c0c1004002501a280801c42041c03100088003034103150001c0754400108504450041e1100b090341 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 424645287 1250 424644037 424644061
    0x50a110705180a151403151603230406140711060a051f0303080105030c030f15072115060201140714370f020c012003031906210803 58
    0x210501c401c0609100005c43c0c8110390b900800803422003a02140c40480c4010320203a1180c03c00c0b5501012010203401c8a80854426088400d50b201000d26414254090612a1940d40780540707040740c840380d0300e940810080c84800c10741a07201e1000d05160103000742000707500b80c0314007006005150403903644002480341559120420550010a1610100c154691034080c00b4140c1c20300030140b00c1c1c8240303040c8480c68074000074070440003034840018210000309801ca0302421707440602281c1c00c1c001d0f52003000802d06210240e034042c28201c3c100101e11340d030070300e04e00c1808248160400c80459050a0804144002c4009099003005442c5401007510851070005100f60050140400c069080008480da00d54180b09540c48020032000d010b400441b600030f41600c5c40c0f04500118005a00820701140c05980280c1c150740c1c802c1355920461a107448100700f00ca00350343c800c640499101088850103030011000d445201c1c06400d0306512699080c0390b04080300c00c105804e20000742410000000645002000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 424646537 1250 424645287 424645301
    0x170103030503010e2d01030201200703171603020a030e040c05180103020405060a020c04050108010b0112020a0c0f0803040605090d0e13020c0105130605090d0c030302090d02030d050a110705180a 85
    0xa041c403402001c4614454507a85d03402c2c4820380c000399a00b2004481c50007500300004580c1c0c4408010302400e85155500706400412241d0461800810308c40000006d103403c106c0c4000c288254050710f07034030700f4501d0b0242020300c82000f140d0041d441c00e2040400b868010701259040c0503080041d5400d06c012100482c0a8865604419000400070074020000354000802e00c910300070031036040c0311503a201c0c60414200c418090305140010403203840c01d640a00e00d5030040110052500e40300c0e43c6440309481e01c02c1040c3c400c00040b582c3c0c40000003044144a110710500c0d400000f4000076000b4960900001005050040b0711b44d84224000c01071403a2006003581100e00c1c000e4800003e0129182c850300c040e082c0080c80e04195585818030000481c0450003084180c401c54641d240c040706004aa00c044000303400c054041904840780654103c05603804128062021019540d1b4640d9403100c00c070300038a4040b078420b0300c08080d40301840a00895a8101d00b0215268080c21041069079800c2200c0c8060080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 424647787 1250 424646537 424646581
    0xc180c0504061d03250b0a09060f030b0631050a1e0e0703021306050a0203030703050a14040b06040e190b0702070f03061b1b150906140403170103030503010e 69
    0x45c296580740103011207107028100e154510f00c0c14942a40c2c40140a41c1ea12410298500050b8290130502032140220300142c2020600e03c0c001810402d040b021400c03d5110302c01c2e030184160300e00845202c044a0b40101c0b28450b4a105010032058544404515425070a00942d0040000a0740b0038440e842d007290020010484a403440402e030605500140c006e60003170071a00d51012030b4442c003017a200d025038121000c2c2212a802546144d07100e0600b140109409003511000c6601ca28401e81d100285904003800ba0b030003000800c400d030400c1c0e81080110f460100c0100000d4004500451140c0303c00d104d400407140d0450071200460b900c0b50400c03030815842c0c3cac005282401c854031010007400700c1684004511141c0b90050311084103040d43c00e03903084c080e280040a250500948600018010841064400c0501640415902c8190f034031481034a4103e90201c02ca069618100818194000007581d03649001d018940010750443d1001021488140101900350b85908081340082d5040e070480148050303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 424649037 1250 424647787 424647793
    0x1e0b12151810150f0e01060513080a0302060a050a1109040e0c1c052e0e01200306150a080403180e09010504050c040c090501030e070b03040c180c0504061d03 69
    0x40d600c0018030080020f003180c02528481d1920100304000300c901d98500351900c040210320305a00e40301045409501c10381c091b12510000c900c0000d242da004201a1800a200341c01510507454000510411078400400b49030700c00c1d00340611a081280c01200315299213405030b0b40444d00e1007a0140c900d14080b886003c1d10307000900c0c00030300485042c1032483d01003854070030800c0c0c50000101c1100c0e010526000105081c0300b19080031884e00c5258940c1c0710800c0404120008103144002c500420008028400807021504c0c0000800800d407502c9035032107501e14031222a5900b00140094002c1405400400080c24050281c00480e518403105080c071000b000c2c83c0705054000e1404040c00b9020344002d0b1811209849010362402c120700e098054882120016501c0101c020b10b00b0004601815910320754003058001d001020406000d03690007140305901a100d0550118540180440c0a841d0b0300440d907809481c240c03200c44d085601c54101c8040700c8680c40d020800c081c04100d652081c200ca01f1815501d44 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 424650287 1250 424649037 424649053
    0x50d0206090909100b01020d0e010e01032009040f02190809070305030d020a0e0102070b030c0a09240f030908041521050105100c0c09020c0304091e0b121518 69
    0x35000040d41c0452135641071051051800410059a68641c245602c502040b40241480c500c0d5100f11302010380b1100515002c10000c060740c28060031a07009090000c10840009400d0305681400d0240c0e10160b105098214908403141a902907101181c0100204000c100408112045002c0080c0c0f4003540e00901680d45c0d9443c0108144c009600040c4c0c90b6001c170380c410300700200c15800804c0700c9045485021341c803491079039071403c12009507000e4604241032014510001c1003040c400c1140b0920144910300b906804110b050000c2c0540764910302c2c0404044c21b02d40340d403001540f40f01c00d4800302d400c00b2085001960f02c486003501d48180301c001c003000704001c04010960480d00f5400a50407540c09a50b41081d41c926507008640030103225a01a00586a49a040040000b5a4001c102200e1070300140d905164a03042c015044d194121080f400f00454420004a2801544100c400d00782003190025015203003000c1054403400100000f8007054145400190380041a416440b0300032002c00680d0928 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 424651537 1250 424650287 424650301
    0x8070e0a0504030c080f0904060918060e0f1f0510080c010c140105070c0b06010504060509060d090f05010e0c060a2111040e0f07020102030c1801050702090f18030f04050d02060909 79
    0x91f00b0240049105d2800c000001641401c0d602c6100c20405d00440c58042742002d6807203502c007404508003103080070310410140c410411000d00031600a846404030b032040303400c0440b0944056650181c082d00721109100400c00105000140004c4407120a00b84003000760428180b81d094000b19025030503076075003402e0400a9140c2e0001076160001d109280c02841c0b9180ea1004680341c6c000c5001d500c0101340f00300320410300c0c1c0c034000004e004601400000411102081e030b8130481d1000e0390700c1c412101e43c0e441da501081c006409008d1128400b40607200f00d414902c01c0314005102907441d080e400d02a95503413131800c01080301c64114280c0040c0e05c9491030b5071540daa07041d0f174184034412030b40b10603c100c0300700c049010725206000712405012800189410424812027100301c01c00d2110405050003c100010301c01a05d44940061194225800e08410340c940f080084008134019100100c444d001009038104040320701d81583d0981d030f016101b51040e54107510110355984200c0c0e0381d4070f900c0180c5008211107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 424652787 1250 424651537 424651567
    0x521031308030910021609050c0f1606060e0402010e19090e07050906090c040b030702030903160503010c181e1e080d050909010b03060105070f0302011508070e0a0504030c08 76
    0x1540c8055800c5003200c014814100c2c1c0f0740c0c1c176a06e0343c50045490000c0400030107100d40c02c420740011400e403445140042540c800070b030720f0b0300880c00311542c6104003446505101c102c0c824180145030708030241e50685403aa00003050300031750302c2005105141642c1c0040d46460a1034140000c0c0c41d0700c0b0400c0144d0705921030a59600c0800348101481951000005a1681421140c2500035181003642c43d081a0600c8404000c60300028100e004500c000e01c0481c5159604111010000070000c80f03000c521424081410f003540c5221413810300380051040041540e24041c0605c1c0304481500d00d28020b24507445807207a0300c40040c5c0d8070a00c0080040011540303203580c038544200440f0012401c9a00c441d0030b00e88169841e024208000740d016000400420004d8458001594030200502d0600d18003101d40d640d45810080e040010b40040c0e41d9480da00e0b44140507689a0320203411801c0040500c18a801c050b00b144a1004000102032910389000c541014021b805480c80182c0c800e07101c54460003070304103102d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 424654037 1250 424652787 424652797
    0x5070c080304090c1b020111030706050112230d0e0a0314030c0118200d080c1e01290f0d1121060615160602031b04052103130803 57
    0xc4402d00d400b0300400d8441c045c01500e51410003040300741c41d0310015034006694000d0310030500c2c0454002006400002450b03807003107601802d6a108075960712951801c00700341c0c9080301c91440c0c1185c034141030381c401e02d20030001c1c20016001c2240741c0041856000800b08800c0c000325400244070810455007002d40141c0031020309511030143d0000c21221034000fa00049282615201401079003440c3e1100e032440203100c002d0314150001a00441080b109582e8030b03c00d5a102031140c105075006201c05a003000d4420038441c64088000c40288001084180c0324460f40b400c1d1005082c20001c8a29488072a1711104901d00302050010302e1614403a055043c02e440135003003200750030310500000c00d1550980d444540c400c43c07132921020061482e5a0303044207002443c60307030480c51074217181c05110301042c100704c603869003101074070035a005603e81c10201103083c00911900d07150703011000280420301054585826000c84081c081b9400026040f08420b044c0c190300c19108a103074461003a00c004140d1010010040c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 424655287 1250 424654037 424654049
    0x120402090609070903080322051f2315030a05030a030c05030124090b0d0902011b1e030e0a06030501051f0210150906080a02011b0203060f0705070c080304 68
    0x100941e49800030489114411a000004542c90240034800b18107481c016580c007000c02da80140c40c0c103114100c00580740e0261802290300d41e0241900007007050b1440007501d100e43d9550014802c0c143c90303070386918810884840800742150707050300083c0c400103003a0925400e0a4042d0664004c00a2402d200707460b5400950701d000402d04015068440c0c510070b0341164100c601030b100e56403c03000b8518200b04480d082c58258010018452008103146500400800c0250401000051b009026100152148000ca48012159002e6288030400f2840b040401d03201903604092803500c1108500c1c042d150400c1321040170360010780b50100469000d8160380040d0607240100ca08042699202c100110403401040030f070801a0860718818202c2c0c07105802240a103034102c0803007e400d0341c03111b840c0300458255600c03948495001100d11025540c00c0244150303043c5043c0009141c407046d503008603594500181070403116150200025510038454401c2e540c070135034852800c4500c107603510a040e540703800a006003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 424656537 1250 424655287 424655299
    0x6030705090a15120b041e050a110733050109050a050a05041110090b070c06110a030f050306060405030d020a060b010203160206090339040204080a060e12120402 71
    0x403c0000c140c480b9030303000700c1e0903550381a609071540c500c00d406403103109540750701b050311840d450b0903240c45070700c1510781011142d04c0007405150500b0301d0000d540a94010752000c42040040c5030203c0c00302c0340c401e5803201c407010200d240d483c44c040c210044029180048074090303203044008501c14030f05400107400303000714280900842e210819a2030443e1416100104400c01402e849140c1c2d04220f01d25840a08050034940d82495550031004202d610a110881c0c10004000d01444100d400c00c040d4042c80f500d01c001040ca200040c2d4016003a0b81d0244c2003c024440080001403042d0765000496001d49806070030b55080081a0340003030b41c0c80c0724900d400c40e402c03400c007150840d903944004281e629000c000413044200d13068030740900134203a00c020203280e054041c02d0071001741034441c20404082810b5080110300e0404089407030301c4400c4140003c651046004100800c0031541c0052595000c5810840005100301c80c04901c628102110403905142c0c48041482ca407841440b44500d44114025640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 424657787 1250 424656537 424656539
    0x30c090f0402120a0b030102044b03030e0d141b1e010c11030105040c0303090e0c04060815030d05040f0e0f010605030a14100602010c1e030f0204030206030705090a 72
    0x10007050740511003000201010440004103400201d4000342140100074000500d000c0d11201041041740b90081800300502400400010028070219001400c0b007807510146040d0340d200300396140340c2c040d62201504121503018220425602c1221a900140e840031115812090248410f5228190035070001250090021408000c1c1400c44040d590a03062501c01600b00c800c00006480b107426041c1c040c3c0c0c0b180921241c0f100681ca00b482103500441c054441e05500074610725000b0416142c50300804260804941840b80f1b441154041e14242e42c520f007400d610b141e845042c24005000d002502c1a4180b180850380c2081640000040095441c60701c142c50034652640d2000d407241d1011380f600181c0c2850b03140100001d9108102454010b03082003c0850a280d00c218030b0810380e00b05485e0b16900c070140000401105409104491125500d41490a0520300404030303140603605001c03240052607258821280305030303069411034015540c010501a241e00700240010440e1b004401e10b540280c2c00610 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 424659037 1250 424657787 424657789
    0x1f150809010507141c061211090a0b010f0c02010c02031e16030c090203191a09090d0915020f0f0610050d05060c07170c0105092e0504110303030c090f 66
    0x554a41c800d407113041060b1a00c0d5503581d02c0c00300e5502036491807204039622240811800d100700510301ca924020510002c01d90707440701c20007403480c0002e0480e2000da85050711820090340c10401030180c9070f07624102000313516514001a9841da898100095040c00346d44020480d9411a4070b4050300221010200c1d001480502102203100b1801d01016203580000035040285180c19002194801005400b00c086001103000c12015186840050041d0020602c4007089a0504000e130540c4500920001e11200c80030303003c0a8501e0459024480101710f40e041d0b120304a9008010071003113000642d0881e0b20002c6e80312003007034542c1c2007aa090114403680301c0740040c03d8501b0401d5205c403030b90080050039042d203a0720480c090550110714101d4407821111a60321540100c00301402486d48900c7c0046014540203070080d0030203501e00404a5035402c5551b205d1401003000040b0012442208070010f070941310742c1424030303503400b0400300a50325210000421101c5c01100000d8010a40300380d500130241d22404c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 424660287 1250 424659037 424659047
    0x10b0d0503030f090a02060708030114090421111e1203220f0209040f03090b0a09090e0102070f03110f0105070f200105101e0501081f150809010507 65
    0x2501034000d51040c008075200c00030402c0c0040d00100d8400403545074002a60101707070b0580088d101500c4401010004000303100002d007415050302000c4074500c11910b0660341d20114800325036800444031500650a4021038010b1040e4240d0f03d4080c03046808646e4410000348901485408076a0305004d19924205034084220a9030b000b01e40b599940c26550054550705d0324407801c0190142d400a00d001d4114026845030200c0741e014a00030010384281d1000c508000e402074031154020544544200041030b942c1d0380c016404c8064440300c603800b0581c03d6004140a02a01075064090600c3c0700d1080c01304109900040b1823441c00c83c0c80001c0e2018040010a000d00b00c807411550381b80800d05c03005a07000c503c0c3c0718006229481e1482c0c1204070b00301003600f010b10300b190012104241c08101208050100c4903111281c140700848001c82000d0942c10100002c045410140091103500081c0540c06500151402e4900140007240811198003050a100070321854054403502983d501c1c01c8080380e0514490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 424661537 1250 424660287 424660309
    0x4090c27020a0e2e05090f01090308090607020607081305090717040f06020c010e032d12090304030b0a0504022805120c03030c0307030801050132090603070201090302010b 75
    0x250f00c4004003407040c00305110b0303a107100c00d0604500c1650f03d810080c0700028280e203144800180d0b45c41c507448100074020f100300700450308540750504c100380d6405c00004848404848051509480a9484220364801b0072400d00804800810890010806047c08098003003920300b11038040312282e0241e01d0340e15041ea40c011055000005c2c0d0040302e0000b80c003054030b5128480600c0d2107034800600c1d1000c0d0816040c01c40c0d040408050882d000054402d9440302054403512511429940500251041c11004110361040ca84074040c519140c0e400035104400a200303440056820a00003072140c600403030a0360041500b00c0d400c0744503404401ca400044000d910140e090b084075054a640e01070f0400c00bc01600381034401c00814203114a071888840381d2410b00150030044e490000540d251000751602138410b40050704100d04200c491407811400b0b40c404850007500024610b40c0c08861038164941c0360840c030640040fa034002400205004510b0b605500005146001c0d40c02080701038140170800a8480c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 424662787 1250 424661537 424661557
    0x140f0904050d030228080601090503030a050d0b010203040b031e0a090302190203011b0804021806030607051303020a06050d110a0c150b0a08030c010e03090a1404090c2702 75
    0x1203249090b460b18020703402052036010704040400007441d41000305802285186098001400c0501801138558014121401503c0214061400c20f40e290b403000307003980203101403003101507101c48903484140d0082c0200e6014241080c01c2d9a6030380b4045010b000c1c6102d0380c8001108402c0c0a10004065604522401c4140340e8164003400c5941070b10f00c0100320100100c40160381c035558442a51000b5148000c140c02401003944400920385000d004100303c0c812594071400340030410b0010010207560229415912400500308030345c85007200c0549401e1002c0350740000350011106040031510725003110103400c6400c08004c042c41015450340c90700e07696000c1ca00951011a8904035501c00040c0107414400108800000010310703428200c000541d0001150b12201181d04000740c0000543c0f401c0c0242d40031020301c007004514020303c9034086580580e45d0700c11400002d1b450b6100b01510740c1c90790408032519400040000695131140c0140d40d541000307240c0c0c40c00443d28609410b880c4051402500c85d9489 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 424664037 1250 424662787 424662793
    0x13081606030506210703050f0a110105030a021201060305180a1502091210151710020a030b03060703060501030609050103201c0f020901170a17040906140f090405 71
    0x45002015070203800c000c3e02d141d0340003000c0810074140d49080c0da15000c00c0700c411802080a5844e604100342490001040d114060704141c00c4403000c540c51203900f2122010030318089a90f50741d0641010b00901907681f2100c0d4401300c0c90b00000b991903064102034007a04482002d6a9020350001030a541c40704d080324001e04c1429004da03602e034a4000c036405010300102c041c104005050f020203232642880c85003c00141c07242e60701d004446010302a071402c1006841c00e103289103002c640c2040f06680e038218004405500715000180d140300345111340c00c160410080a400c403011410f00c901c020300982018001d4a001070710348100016003d480e030044034103da4101e00404075030410f0401d9403681040c9461215005103103003603590724000401c03902001c1c440c000c580207000d0380614030400030b0050069000031409080501d91552020740802d0081d038256100381510800c81030110101d0560013a548034040c01d502c0c0c554001035401980da440c20750040203d4010601d514081f042280d824020349001c1c00300d038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 424665287 1250 424664037 424664039
    0xa090207050606040b06040305011503110306040c05040c12090c030212070b090607110a03062c030306100201110f0c0706030e1c090b07142a01081902030408130816 72
    0x400e099020038003070780d80607040c0c6c3e15094407600c0d6107003926800100d0125101c0c08032020014030040c1d9040c0c2522500c01c4014190504250705c0d4002221201c1c0070f07840c80380d95034210b400200790040144d15807000c1d40341401c0c0b109076034031b003054a0054000e21060f801360242060031139405102150351400d540d4600e412900309880c8605105d85a0440039040358481020700340d120f019554840000001c511401c1c01003081e2280700301034070764807040391030042118050b400c07000740c1c44001000382e9034006820356114000200100040340500521603440804800000b0062180c41e81c48008000190700007080b18061760391114110126143c031b90012900b900000d8203020314050710564040002070341c0c9001c4030102e40b62145c241c200d521070f420440b1700d51000a200d020a64052144003020f8000c90f061031503e1840c3d00010b40d0a10203542007030304018201000840c1c1c1c81501e200301c5416048014115220326140c601585641d011168030300e05610150030015038401c0c0010004d6000c120416007005071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 424666537 1250 424665287 424665289
    0x10e1807080906070c0f0510060f080f0607050306060702131b020c0d0b010303210c030c080702011a040b0301090602130509010b1314030102090409030f0f08060603040803130c060e0a090207050606 86
    0x1c861000100c4513400341c4c045082c41d02c0624001c1c8000b4003a4002b030300051501c0d044600745841c00100241849802000c1081840380d00b26050366031140065621550741c00300c44c40002c034141055203440c12010301e480761602000381c840300700380c45040d016000c441094000c24100709510610389001400c4070742250042c000603100c0c001450040d6140408000c030110901c4000c02910104e80c06c1100027a621011442041d030300407070082c1c00413a9400200891f00f1142c500d40304050300c03554014040c42c0c8641c1c00b44c0081d10258032401c121500400215180c8801c0348842126030f5092094a00c101549000400ca608a2804441a0600d1480c01003403042c90003019517908460307007604a0303143d542032060040c00d861740e02403c840705102c2d0340c81612952b58030301c02400c03031648003858008121440381001002e07100d12080f02d80058000f801562640c0e6a85110b0f52403840680004203a0b55210310005002608554000c0c2004002c0304c59420b09900c812000c030880c014204098513950084e408500c43d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 424667787 1250 424666537 424666553
    0x1c020702010c21090b0c1c0509031009061d03180406120609050d050f0418061d01090b0607050a020405071209080423010804060b010e1807080906070c 66
    0x9414410b052803000c006454981c52049856203541c0b00e819051900010f20a03580720b000300c00508256101641030040703844041382e9034182e1078080c0c000380c41c120190102550198041d01d41e0120001c0c1201d13141c482c145441805420380d02400c071080d40c202800800781140d00204070b9801c514070f100650810b4048a841b04452981542d42c0d5000740c0c1d0340340c0c046202024840b00021490040c0c00c0070698207154a00f4a1820034090245410000103100c4120641440340c2103400321b0700c0440d50410145100390031280103240941c003501030040700351201d08000c0b680d40c4809040703820000b03007000074a80b010188281c0d44295840201950008143c1500600c1c05600140e0413200c145042e04611601001035030480d18181410b44000d080407070100840c542c207811801c6c3c0d1301c409000801c89481100000f074003818014100400880e11007103094070300e034450001c00008100040c01100d41c8450300341340c3c25401c48103548401c00240b00000203203803a0390005500b801849240c1c0c903d00d1070650f940350f20725 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 424669037 1250 424667787 424667797
    0x4030c0f0204020c03090907030605010203070b15090403090609050307030b0c0a020a0506090a0b0907120305180612060f04050408041a09060406020124031104050711010c0818031c02 80
    0x1030340005a100810160b00c640c03002d412200b00c4480155503074145001040b90514004024204060410005001d030341d82c003005840140740c3c0042c00c10803a44a03103140c0c4801c03000181050344c120440404201c00e15521286460440d101a210f0039452a10f400030705465010781c0c00701402a51a44000c00d008880201c020540c440441c13050311142e15141c5e031401e080c240e0a603080040c07035100030070741028407203401c1480da003007100c0c000200002450300c0c1040d040750713035200405000d00001048401d070050301e1852a01e8a048020f014941c0e82d079242d5000368400c202950307603a000c0c0c510341d0320b042c142e400c00f842928041c075080300350760307040c00c0c9004640c40c000001c4602c00500f02c501801b148001e5181c07000540003408103038001081b24424005000941420048801a110b0214404001080302f0700940c0c11031800c292800300301d82d0b440300d8090720803080584640600f580f904002c40402588003842c2030050030101d458800720316070300304510340e24020981242c0e030040d0944641d5680b0001c0f680144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 424670287 1250 424669037 424669043
    0x27050906060901020f0106030309080d020a0f02010305060a030c03030903061b0c080310030c0b09120a0803060103050c0c0a120206070306030c180608070f1a03070206070804140d030204081b010804030c 88
    0x5d000b0141c0c0a00f80d90a40301c00d03500841c0840c17020003080c0806007040c0007507102d562143c4000c00c14003020361650f50035444d0017a0080d05040ea60750104440c1d0301d509032000701840d085030907501d40e10703541d107001482007070907100580e00c040c41d2071115503d111062503107040513081035407100b00d020010340702d0300002e5101030803410300c0b00448070780000011002015a002040d03111040ca40381e0650384144200d445141044890340e402403402a40007491001c29030350010420301e000201c0b555201440b11592003000c019000a10482303104100304826600f0001603c01c01d0743c00d5501c1c54650781801d8081c0e403510300004040104808040c040f105004802d82c0b90310213000e030081078681e03952101d141086c905400441d8240c0e490709007440007005800c181a83d48580c00c1c4424030798a00040c0c0207481d80c00c0584140e040085500c00304044c085510114103050300e103903041d108010403801000d4000d50041c496480d860143c40341e228814411401c1c0e0300c00c0c100068450b13504030b6032550340445440070480c3c421 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 424671537 1250 424670287 424670293
    0x6020f07140f040509031c0219090e0a150314030a02011401050d0b090124140612011403012913050106300606031a0d03090b16050a032705090606090102 67
    0xf4100303c00e4520305002044085c0c040107a80701d1400502c50040c1c035145d909c000c1402104041000001c00c0340c00300c0b5a0002d102240003402480d4440810481002948098004c00031508040101c0c1000300043c000180150001c00ad00040383c0c81d241e010941c244100303a4000011035045003c00c1c0030300c1400390310140f54800001c1d00c0309480d44843ca1a9081000400520300c014402c5c003002c07032050301c440e1140500b00c81c46030034408000c1024a00c000c05002d050000c0040c0503460646490035085440d06228100c0c1c10385011611446170340c040300003100070a00ca0400d00035072a000501d60b200700d038141c60059848055100032240c2c0c174000030651981064400099140020030081c692196a024084950f80400c180c0c54441d02260755011220120344940151200302000980101d20503080340d07080b207050390310b801003d1901c402c0d21411749009401800350800a008040c0d0010800e9501086140070203a8419540840c100c80901c901030f0907041a8100b002c41c01c10700d451006804650014811 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 424672787 1250 424671537 424671547
    0x903170714070602030307091e170a0b0108010b13270f06050108030418020c06070f0e0405010b070209070908150a060b120105130e120705150106020f07140f04050903 73
    0x1e85091000d43c803482c01a0404018001c910354001c503911b000340400c030100c05141140b0f001c00400c0108921031070b0060b000e00f8090000d10002404020072558001d01e44160540c3c0d10307032200340079004849a2900c039401040040c1c040000d248180c901948141101170003c3e420284016030780b03020000281c80d058010542100002d44e14010b540c082d04000c07004e1a261450100e075000f004000741d6401903450300501000300044000240c05030f0260452608a100e00034500c0f05844481119003401d030014103190000c140c1c809001c00504141d0300c2a150a0580d9440c52412251095540070b078130615000b00c1d4001030452003010015070801c0440e100011410703500e130210400c80d40120400110f05451400401c010b1400100c40b100c03800d9002e10034045101d000007882c3c0c907440442e02403003070010085400800e0010030003078283e420500c200300c0152540c4031000070755174240e15201520584207503140420854200c0040d82c0824030040c0120034000e94140c100030182c800141201150712062003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 424674037 1250 424672787 424672823
    0xd0201030e030a03020a0206011d190b040e0109020f0604082e06090b09101a0705010207171e16030318170903060906090307030f03090b07080a050709031707 69
    0x20080c0210320f00c0d6240165a50900840a803c0030760591142c07a400c800300b4401e400b80074600a62550054081002e00e6000c41c00c0508007000300901c46109400602c2e016081052800540c020000702d802226a4403403c80c006040041d18440ea0007000c000380c03c000c8440c03008170314250a0b012000100d000d4400008410103402d011980035a1203a01d100d41c440101c01d860781007401b00d0f0758021800701c0d4240c40082c1800100c007000880c0403001d414441d00010184144602035060b00d00c907650080007100580c7c49203641c5101c81d04008034445007080b0420340020014250303030403245d40b89868003010b02c0703061040e03d0980050103041080113650702e480c5a60300006030140b500012140100760026101d580c4841490b1074808024107854490f031042081c4408004000159100603500d4078002d448945440c000310080c00c00c01b01c00910121043c800c6c8249a90448a0301d4401c03401d60400700b085540d03450302251608460710000c1d004c010511a20405d65141030010103605014402a0080200c001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 424675287 1250 424674037 424674043
    0xb0d020d0606050603160e101b0503070503031005130e0601090c120e070812090a0b0703050708030709031205030f01142d040506030a0510020711040e0703020306091b0d0201030e 78
    0x8031600321503e446c2001c2c800d0140c03c101c1c91042200d0503100c07100c1c04000d102001d043e01103607511414019501c0c40c551010031204004032500903500000fa82d032a0b0801000060350034100b40101480bd0412098403180780c00c1e58030a00b01d01084c0c440040141c1d03464000607000401070012042c0800441d030315078070000e0f991030045645a140381c1004010651a01111034109a00c2c2c031a00c0c501c004040008903202e13550b0502e4030b0b060710020a940c9a0350503180c07900b41c6041c0301d5118000c1c0001004000c1200076034011007a4005c0f64040d2038420280910080b0032075461000720b424038036814407040140450307031041c7d0001d800d010b405019188645111095080c0e82d4000ca144481a01402d035520342e07035402c01d80605504076200390010901a003056503801e03182e4104541500c0340315808128082444000700d5440c10211000c2c004000c191004040b540d1905030901003a0700922419002c10b11300742c000100415801c103e92103500c2120000810400f0314100c1500a0b41050785800003460121014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 424676537 1250 424675287 424675291
    0x3070905031b0f0d0b0a0c020a0c24110618010f1802040605030f070308090f1f0f020d021e03070501061e0b030106140304050f0f1f0b0d020d0606050603 67
    0x8490003400d042d40d03070b200b00810481c07107502d224020500740f800c0341c000036202d0901c1900b104529902088030402c82c00c049207014080d00c0003900c0e036078200c607000403650b065010b1100440c0030386001a4104022480c1030b210000d280036082100c2e03004a00145040d10041c01015682c91024004100d201d4600e1401c0300740c502e000107084104c445141340d201146403e103e0750000b0601030300036288650701108070380d4582ca20b0307100141c0495000502540144d48200c0c1903114401c3c000c2180c41081d21340305c500c80c074105030420008040307084400c83c0104280000b0701100e6614079078ac020000a85201024448030044100a6026100503c10000020000c0c0243c20240850780386420403101d01490103221000b0940c00701c00360100420040c400141e0001c4000d401810030b4408aa5988a51030807a180c10409445450540140c0000d40c0e845440031404060482c003162400701c40350031740c0c0100403c807030740d00001030746c050f02040038a401401c1600408182d14040e030400900740f9600c1e070225480b0303801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 424677787 1250 424676537 424676563
    0x60a0906080f060610021c03090204060306020c10050f150d0c080d0f080405060601032403061b1e031e0216020a0603090222061815170a080307090503 66
    0x1d09110642d0070300c108a207a50049044840804200030400d01035112001e00b01240d00382c1081440342100607009800070b04000d03501510400041e42e407030418034003d401001462000d801849149904c2d012035008080c081c5075500309600035500ca82c0c030928009000400842d401c00545000040810390b0040707100014104240903014804011100030038003401410b031582405641d00500002c05c0300050150707070029081c24002561040c1c0003100107032030b9000104a810300c41c4910040204491360700804061f030304071659800388110041d030988000011101001100417134600604005210350000d40d818a01c0c1d5210700003146140010704160303440816000015482d000c03200045040c60030144000305201c0c51308028462041c2d0004201900100d084220100d004c2d19035007064000754090801066030b03000c1410301c11520903820001d0001186c8007001c20504445c0040c2d0706241014040d0f84007201070280c10300360701e250f89407603071a08042d0a8004002540c400458030342c0b0108030070651005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 424679037 1250 424677787 424677793
    0x7020a0b0103050c0a0510020c10140a17060301062d03050a1202070603020306031917161a07050304080c070b0c0618030a09060c08070f08041802090109030b060a090608 74
    0x2001e1000d1005c0400f00358001c600900020810324107165000c40e1180300707650111030103003968000510440702c040500400c980c1110f4001141d074960303074100c0360380d1485507000303004c105899942400305402c0f1990307072150b1000e0100d07281a50310541d1510451145003044800c1000c18280c882c1c803058a0142e541404844114801d00c10b40c00d0316070100034100040c043c40c0703415855450640046a00c4000102442c004087c8901e080d80810600c03a501c1c9515920310202140c82e41c240b4940c14012040c00501550028000c00b401902d460714905510f216801c242c0b074480c61a152951400f9840e03101c0c1b101100c0e80d000e01d0001280800004000301009001d0b000201308908100790714035241004468641000c1d8010841c0810690f0452046400c81e00241042000c00c3ca1b2400c1603251407150500040900c0403401e030680070401c540000d401500c1c15028804072441c00450781400f07d1040904103400b080d40b8100400000300e0001322254040006820400b0351a40c404112041d2030445e000440150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 424680287 1250 424679037 424679053
    0xe07020703150603110111150718140105121302031b011d030c010c110607030c0b070216030602030c190509040c02071a1b030a0e101d0907020a0b010305 67
    0x10840d246a8a4030821150040003c01d185940704a80b80b0082211541841036416154440030000d0203c400f000f5000d100c8540180b400440050030702000b0301c07450301700ba450403001140d01600c202684c26001c0044e19000d10741503240720041000c02c0000c119408a07010030a0368070060301d00307200007288200d2718040440e8508410b8009450248000004074000080c900b00c5042903a0001e10b44501038001e08290101500900f404503074120307003504050300310200240b078108041c0d202d186650750502403069440c0603122508102e0310f500070305d092100010a020410300201d1307125401140c110071070206040c6411703186144004503c505415000c0860004129030000d802c25014440460359030307201400c1c880d400d090050354650a41c015404502c180400e1025000c20304e41d85580301040c004086070f86507004404000c0000c0c50424071075000300243c1944d5500c560054007601c650300f01a070301281d00c00a460040c1f01514000410030380441c030a00350300c4d001082810390014040e500a1307010381405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 424681537 1250 424680287 424680293
    0x121f090510090b010f0806010905030708071703040e07030b0f0d060617122502030a060204030309060507080a030c05090d05150f06060301030f0c0509090d11071811040e07020703 78
    0x1e010030303030041e040c00e820200350040c81e07a404144156905800d00b000c64854a5000040750b0004040d040706806104500703010a6440001808104842e5404e42040b054892803000c1a200c2c0900e100f114503121810340401d0b080390280d08014082d8030083c21001301602803000103900e909400348203850143d07440500703110080e0303940804401c04000b82e000f000100784d100c50310482c3c0c1c801c0504000f13401c890402805d15080000340300b0300250350020b0423180a00010708040009501c548001c5000c601d40c43c0c030004a0b18011010303140060f401c0303084131f400c15a0145060300600004001c441c00c20504100d00411980e480e1480c09003540500c1c0101480c00014101410128010f00b041d41955a4602049220b6880714100c81c15654800074a0a20120320314004150b01c1050700b1556000b0100340811a12000000f041088001c9550354038101c0010100140d4407034915006140c4508003000c45270040ca407003a0411189a21040c05143c80c0555034084500c8a082c1034403c0d0005030000c2c0010414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 424682787 1250 424681537 424681561
    0x10e041b17010b0406060e0103112811150a0207050c0402030106090f05030601050a15090902030406050a20220503070b130e01050603040f061503112103121f0905 71
    0x2030841550704100b40350500380003500c024200d074002410144c0b50a00040801c0c0508152070180b42f02207801c00002c21100842d1101126001d030711000100041c600d003041d9840003038681d0040b00513811011160721030005010107035104500958940c41260800341c2030b511517200860081485030755041c03038141001c0700c030215131140e0ba0003240b10760f1000005000a0351900308010445507804416000e0707041c090000e0b28108032547c807030351826101004010030f000240d00500c0c841c09403e80e040000c00d4903503030030452003624511001c02001080c8400c01c0d6840c0428502409801c000890b20f04682d071302e8000074a00358041c0c01003401180c011600711508003050b00c040f00a051441680a000c1d030500012802c00d000c000c01c041c00842100c40820107000c8a544078800310b801d07440d071030013403c3e4890601d20035684d6041c0526000d00c0c4800824006c1ca45205482012071101070061441c040f050100708840100c058150030100c014880ca0502d90500b03034120100401900e00c001c6075900d009108109 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 424684037 1250 424682787 424682801
    0x40b010906060e211603032607020a060c020a0b0a06080717030706110d0e0606030709020906090d210810050d0807020415080102070b16090806010e041b1701 69
    0x5001104406950594401003801300744201070608400c44044000081d15001400980540c0d041290b4004018164043c00c140103410f080a488180c2c010394100c10b5044400c02c81d140d20040c0c11032200e40c4005005134002020350b403414030407100681240c2d1030302440c04002b80da01102141e40d40300300300b009201c20703c20440200030308d903c0b800740c01c48249040c54680c4070b07040009000c01d07a0782c540c0d02000841441a16031781912070504000401d605642c3d607603071300b00594100d4464801c0e9080010004418021105680c0300130302001c0c20100500c09000d05071020718811102c403052390401507078800d14840d21002c3c03100e0381d9413030182c181060202003101c1d402981009024400341000c10000c40c0c1400c00b00c0d00041c0d8151800240044592281c410b10f401c150003030055540002040814814001400c40c010106040c2030304500101c601c017941e8083c12446081c100b038105400400c49114500000360744140601d10480c0d01d54803000166558041d1500020b0900e04444030841c1002024803840d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 424685287 1250 424684037 424684049
    0x9030d03290a0e090114010603021b0106140d021203281701030b270703030905040b0f010815031006030b09012009030a060501060206060111010501060804021512040b010906 76
    0x10301036000000854810651401204083c40021011502000c400d5001101011182151820070f58540d80020041d502c00c0141c143e145607404585640040180320392800c540c9890011001d900b0b800091000340c0544660590f48200d4020780160309950500080c1001400d10809080340c2ca41340520071040c2c40003c0d5103100b0440b075411100135107550b0390199030641c1d8103c14240d95565a0021858440d07600c00741240c0c510195600c1f0b402c14605c006444c4007680d120b0b498584215844e04140022542888400c070780c03140e04554200285e50044540c2904082084c500f130158800243c046494120449100e00c45a55601e00030010300a1070040304d40c0040c6894000e000148503207503000f0301d181402d104405080300018407402d45603410040b02ea840b9611060900c0341d507a440030040e407561170071a100da02280c280c2c0c0ba40b14061006200d40ca044e10066140c0c203c064455070240000c008480081d541241c40400c41c082c00c1101c100d0010348104d03c1040010502d40c140f024103402d44c0c41a90041d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 424686537 1250 424685287 424685351
    0x314030903100e0c15130b090d020d0302030d051311100801031b0306050a0f050c07030801150c0203060f07021209030606270903070219050d0605090309030d03 70
    0x4100356a004103042ca40401c042e4000b256150a101416040000030914650f0110404013000c13100300f4840c0240c00c0c45601c116240840d9075a8110710b21251289005c03403548184c1c40c82c406001403502d480c180b03103814000e204580c1016507100218045403007d5909580d00c1072121810400c004e1440b42100040700155004801e8071a9600c1c003422003101804002e01e141c040014400e041080d00004100840d0401e40030310290420803170010040c000505000b20306030520700000c08126a840468004a505540e6445641e02e08440ca44004802829042c03c0042070410100035a8040000034080c8280c44040c09a50414410283c586280160443c40d80e10091003101c107140d4000c00e14942c044030a0b00c4011846030f5a2659800c955071155181c0012002181070000c01e1400002400c42c00c0d00c20b031403000407120301340d500c0e100320011403098a41c850200c40d2070300000f48072908199044140e001c01c50703040c24100030010f424a40c00001940000b80d595120303040c042ea90405084110a200c004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 424687787 1250 424686537 424686547
    0x10f0e15060306042f041e0305030a0e130c02010213090615120b030102131503061401030c1707020c04060b07030c021c051e0d0e011d01030609020d06031403 69
    0xc81c615000050020344141c0d03a404082120400089900c590b403999039010002032000020700300c41c560040d004030940e14080303511454107400c111122070180c2350444021f509000041d02c0840742d994011300f0345600400c00120065410015014601c21000d40b03070005619402c081044c11440f0b460f642c0a050a14248642080146041401212442440d2801c0c82d412003c420401d0007904102a8103905913100003a001a019001903c10050310704241e88103102e00d8101c03404500b5501c0c5406609503020034910401c00d99802540400740902e1038ac02c000942040288075401d00b4403080314220050380241c5504d100c80e281c64410a07002d060202d07481030074004079407001404c4c2c48155000a004603101c0d10301920300c1c0c10040d01040d8155208044900c4107615034030035458251054200c06103413081c1c0c04040c041c20f01420840444943c1071352550104043c03680024200d42d04035030b0302810f00d40d9884005c2100c501500090414000c01100406c0d114070b5072608940b0000312125400c9180c2040c08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 424689037 1250 424687787 424687789
    0x90803011814070f030e0c0a150809120301090522060b0f01050f040302090711060901020a030e371a06030f06070503070e0a090c0c05060a1a0621010f0e15 68
    0xd69072605400c4d40340000d10722440c203602514103515132130301b940d00803025100052641100210a00714540d02e980c2c580507038035a80402aa52030000d15084c40350b210600061001d200f60707030702c4107900c9660316a002805145412045002070034924040e620280c4800d82d8118070b0078a0103001c40500028a0001e180c140300500754a00b90040e07000080c412030503000826a2039220743c800466050684081c0d607168101200058000e60005040b0340100e401c18006541000300400e80c0e0b41c2c488020030301013880e210070310541f82c015034040b00d50700810b0103c84000808034200400b501020b496100da042c0c0135080250805144c07011504030708150354028000c00000d03e910505407900100b0500f04011007100b000000f4852505d03640203004900e1500c4865814940d000e000c0070041d600440c01d031404c94aa046441d801c0e6010a48504445403598404500d6070410b80001c10080d4900c41120540400c100c004144402003a841b0400d810008201030104e0b0148107c441d40054903a007000c1c2d01c1116408c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 424690287 1250 424689037 424689047
    0x607020d110402040b04121205090609040903031104170f011b080709030803040f0b011a0a050705030409140f15010c030c0c03050607170109051302090a09080301181407 74
    0x86001000d6406041114074261641c1e015200a011513000007601ea580307400110001d0828100c09a55030320011412a0149020f042141c005450140003e0304e0300142c6001c2c4406407892070012010180d42d82d600c180040840c101a001a00040c1d21400c640411101110f1500d00b07401d054203280c2c0d00d0101c95030181119a5840c0e095819235080c9414103540742d0703000351613048003944090802040082080f00700004079032100d054030302c154003420660362504d4208022019554010b00780500400000e5091805540a040403e115400b100e2070582c40381007160603940e10b0502c0303210350742501d0305025155036100120342d484640c00a124804004c0180001c0c98001c4404001d0180030b0403102803028410b890038898055a041400c560040c180010010483c0020340c00c86113981c210340c000840d002545000e05400f17000603428007682c4240603000c104800340d003d4100450190780d001d0860018004001944c000d2030450704030b480b100420340d00c403010748000049040100040300c1c20000003a80007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 424691537 1250 424690287 424690309
    0xb04030515090a02100e03060a0b040c1806030911040c0e01081e070f02010207050f03180a03081b0f070810061401080f0903090306160314130f11180f06060702 70
    0x40b9014884c004005c50180d51038552092241d0b01405010104098072003d6000fa60078004165420021608482c5048640740c0b0740740694046851070b0081041602c2c0b09800c40a980c600a12240401030700d600700050407660700200100208030740450852540d81c1041c50a60b01181248085100c3c400c2047d00c8882400c0003080702080c804440080005103100b517055401c0142c1c824100c5200031443d41700c0c255030740c002030611610310600d0307044211182081c2c05042c048a80c82020f61381002c94401441c84000c1b02100e5115142c400d503c450740c9295420002007004042441c050640c44e00403078102002d40d504c2e40c020302d40341d14621110154070b0341e00c0411203600c038400a0041119440e0a00d5070b904600c40c014105a00d849440180102000080b00502c0c01002c1601c0c200100500310481d1400110102d4038408441000c0c1c540c5008039107920300707407203001e4825501c844140c5e000c8000601e0040320f091014408180f04010041c41d55040c1030700c15000f6504541e010b040c00581d6000500503490 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 424692787 1250 424691537 424691539
    0x50609100b0d090b0703060806060102120313031e120515010c030804060f060b0310090e1e071505070203010c051608090d050a1202100204180b01180b04030515090a02 73
    0x1407055803081050f4803001040f039108200c4100d508200c0c0c0300801500d014090a6058002d01c80070565660000501035441620301404a085603249900d0305400002a60190180410710042d00a50010809022034581c0241c40b0f20140385100c045050454000404030060590005401e80385680c010000301c0d5400c3d450b1500400e191f40c0c502d80400900400c40241083c5400c010307022682001c080d0103103204054480900d81d403a9540c41204059540100c0b00e020301d900320f00b141d8603074941054441c00700060240112506d29035103220810b1110304400e200c0c0300240010540900314078003806502500e0f082c1e8503019043c926000c0c0d456241d0441818002c1003110005050140c035210110560903031a005400d80300c40c020307141800300303076020700303c03901c0b401401001141214104144283d4095603034200e003260000c0b1030104000c00404040e58007031305204480c55202800010505500003400074102d0103621030f46903141051416907024001d5006103141d004001e00e5500000f10768044c076030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 424694037 1250 424692787 424692809
    0x60b0c060a023c0309010902040e010504031e0903052a10090b0d06080f0604031101050f0703020c010f0f06060f050306091314030d0c090b0a080a0507030e01020705010c0305060910 79
    0x150258070041d50000392070741d483c640794002c4100600e100e4103510920b0114000d4500344508244005028226841200c00801203188012100d18400b10340a03030007801000b5051000f0400d0304c81e100c851030141013050b003901817031206140c0c3c40200c20040c600c69031040162000c85190b000481c002c0c2c00010140a00c3c001035102080804807055103400c0a0300401e000c500351070020381801e040d903490301001c813030980116102c0d4001c1c43c02c0303500500c1410300c50345038000c6654440e1a84101103002c3c3d80002d000d5a182d40d240d143c01105501680b00309a6003008844000070b12500d0203d001c2c100d421024409800d2003814020032810380c030344020142d40001046c13610300340c40845d403804000202a401903240c10703103c0400c1c40e0f184c00481390300c692603481242e12030350951540c039404010300344900d58465000902c407102042241c013080e004103401c4590350070701007020444440e04600f260090341040c2c82c0c43e07441d83c4010021507014403480343c00620a40e00c0184078540b015401a18104503c0795404031781c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 424695287 1250 424694037 424694107
    0x8061803120f061513052e0309140105180609010b030601030f080f120a0f020403031d0406120606030c0509010605040b070804030b040b0a0b090907060c0c09060b0c060a02 75
    0x9520000d00600144d800d0701426100c0c0c01150710404504005d00070720340503c1c06d66032031161082c4110721301c107080d41484192101071189450200e0180004a0701216455140e42480141000a01880344681c180c14140e000c040e0f14444414a401300140c55203800e030340b6004100d40c29480c0480c18605403030300a092500005082c1c0746c070380e5861160380074072244a2004103a0b440d5912280f51203e00a00a0032000c4c80342c0c0802c10a208201c3c031031480024081403040b03400c400d03580142150f01244110040c0002100c559603031165a00081401c01125400e03950003042c82001118aa140082c0c8800d4801c141c0c5981800805030443c42140142051800c001c40e1017000c010100d03003140c001e144d0103566401c01d0b042c04d14100980786030686244d2074083c104454030703003a030402400c0395114002c001c0c010900c1514005041c0c62554142109441d042083c8501042403061801a1002407400c0c45003245c0c0c1c0c035114181c2600340305000d00450300301401006401000303500560740e051000b21034810540f08c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 424696537 1250 424695287 424695289
    0xf0b030d0e0d05030c030403050c0103050f0f1b04150210110a0c0809060714010b010e210724110c01210e0a0501021306081003060c050c0708061803120f06 68
    0x40e40c2c1950000304180320000300c48140700d00c00b002801c2100e10803000c5600c001650001502550411182d8040b508080c0d40020074251006840070f4115940714010381d50742c0710300180c8084c6940180c202050081c52800000310540d410022142a011220b20800a03801900d481141c50b100d0b00007640c040212032140304040c410303144202d40d40101c0060106946010500d001c0d0340c0d60ba20941c4844480d440c2c4952440741d075005040005202000920b010962201d0f036822807242500380c0c03451f0103c4c0c41800004a03e00711440c01080d1a221445c90b0800760001011340100208e100050f00b51080e00401440c04203640c00011402c20a44040140040080c2000b805002009000980059071080400762014400c06500400842d81800d040442d03079502c54000f91070b0b040050380e0780028541070384010008140980c0c8002c414a4140c582585441c00f400000d514040d02a04904502d80080e82445092101861000184203034840034500b466040c84089113042c00c01051148042c28840004030a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 424697787 1250 424696537 424696549
    0xf0b0304080d051905180c13060801140a0e07031104051e0709080c010905010504050904110a08030a08012411030c161e080706030f09020a12060f0b030d0e 68
    0x11840b40100f0003403868141103d1500c8508101c28500451a2201042c0f0004407126050704880d0b10100610010700382c50184016854505011590340756561404584610300b8014000005031006040c089401e01c1c1c1c0c0c8c24000c4414089104210364441c0f02d0400000d10012000407a03164110b4000802c3c0e52105951281d038240d10715080035082090b000c02c980b06801036002030581c0c0d41c8108603141030809a0041d50a00000d01803607000c0b0780d05100411440c90001481680544650701c43c2d440950b940340400d01c000c046400c02c40f0f00d60008202c444800354440c2c0c0090040000820505004000f0403000c031003c06405404002c00040518000f146902007040790503907440302d4201d503640e8007100d000082c007903414003446050182400b0505405010350075004251198a0050a2420300d04181907009110240d240301415842e203120201695400b84904000c0054410768a0300f40b0b010b190005c00c58040324030202c4d0b620310f0100380d4040348d10700042d880385960150500e418200c50701000149 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 424699037 1250 424697787 424697797
    0x1603020a03060504080f0a080f0109150b3f0601020a110405100e0709030201031803140c0a1703040b1803030721050702011e110f070f050a0803061305010f0b030408 72
    0x2240c04005202c0301c7e00c551000100d48504601c40c1846030598850658100340c0d041041406036400380a50b040c400c664031030008003119851000760030030b0000c1400d01c4c280003038685201d0040104440b1f240321150303445d00078003e52100e024070250081580e0741c0d840001040c000c403102800303940e41d400014642201e002040010b810900c0c14800145804140202102402c2c0012800642000e903915110107580361960382e01b942c59211042c00740d0040d49146400c3e0082c0340e10118610603100d190011030250400008511070036072010b91b603071500c2d050200c0075620140000c0414140b43c0140304200d44007006503600a4807d28015221951440101c1c44105ca203400d00ad019903c0d01050224103501503002a2000806103e14101410705184041c00c440e170b80d1018081e03000041151210841c0c191000b004030740d00c5242003a00c10030030380d2955440d12810040403070b40340400206006032440c0c90f0120802803602d02d6004e11456041008a0030300c002c00d80300d00010340d80c02001140c200007020003610 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 424700287 1250 424699037 424699057
    0x30c050309090a0510090204120f1e05070905010509041104020903030702120106060e10020a0b04020604080609280c140109081204060e121510090c0804051603020a0306050408 77
    0x2d100d9041c04140140140400e0360b401c00e05405519000800f01c0060003910111244510404054800ba0300c403078007c0400f01c5c00442c2c3d040b0703c040700c40c17040b08001c18201c2410350096005013800ea0401d100141250070603040f05106510440030040010010044401d0541d0709440c05030301c0d0f21710600031a145010300d640082d07005100e07a21454079080e055000a0072160300d50f58084600b17001205200c00075002c103a003480160071200c580720114210070348464000b0701c050001481e06903260602c1d0700313201054600c0c1d401030f0407003031505100c64030103401d0840500b250446c5104100380c99840043c1c0020710321070620044c1000d03201e00340301d038090703298000142024400e0b9150105044208205980b00780941d0012480c8400540f805040450008007400a80d200404100d05603140710300c8030610060040040d04129140824046890b01440001c060a40c981a0090a1502c1c05038184007980303440040c81a01042c0400c05030780c0d00b5100c1d50860b60400301c00034054480e1b040c0700d0f0841c030800e2842 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 424701537 1250 424700287 424700299
    0x9070c0c050d06290108010b07020303040909050105091b0d0b1005040207141b1c110406060306060e030a0809010f030b06070f0219051003020a03060305060114090708090a030c050309 80
    0x7003014412140c00c400000100078a0130407040414540d03c1c2900c40c20700f01d2135800107003408014480400707100020101140010112428295612892002c0d1440183c0444180c1d440340144400c1d07100c20466460908000442d1103a07494003100070130f0001c010b0703010190200482d0808600034244454000c005410050415560340409040107403154540c2e0310203a00c42d114281d0215485160281c014881580c0180984040d4903101d0105503081c03081c41e019030340c1c01c01c140520002644c4a1048800801c0d071a140851007078074100740901401c0c10900b985000b60440f003014400206003208170303815050309080c4902c081080f050304034000c0101c031541d00d802140004480c402d202d1500350400b0481d108550140c481c40c00540c2c224071010841c401e081e0011400c580b00010715020b80c001c2c0c0f400510f50f00d0300203403182d07580d11500d19140084e8005031001c10501307007201c850f0504004c403642c8141181000d45c0a800c00b034046a683c0e09084078080c3c1040f008419006c10403000f802100c0300d80b4002401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 424702787 1250 424701537 424701559
    0x30d020d06050316260d14091f0e030307020a030308090a0c030510060b120a0b06160b04030305090303151909020309060907060c080f1b03030c030708010f0509070c0c05 74
    0x151001c0c0e240c90300555050110180c00c0110301c40010201c44030241c0b40c0c401500401030031500c1503e80620702001c12008000520030f0f0f0240b61207927030441d680c090010441d0303100240307540800351490031556800ca000782c204000130409600c4800f00c1074100d99040c0340c842400c0e0340301250541031080d0b0002c0200702032020b480c00000d002e0f001895454840306080e00f0044547d58030400c82a900c2809184002d5500050000e01250425801411040c50143c07080740b9001281d50440350300001c90401300d86040203003050004ac075a143c85140d9005401d440254030b181004504824980b1078003520310f00c00c8030208a8002c00e54054003002004011040095440b41016403410344c03a10000c840d1885a0700c00c0c444002000c600c6550720440640c0c01041513843c2401c9400080352682c050803520714480c81064610007452400c10095215a40e044c6c18180c580c20104401442c445040c1c0c0101d00c0800003030001d00c0103903110105a0b030010306c50704040c07219059619005015680b540d00059000940030301d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 424704037 1250 424702787 424702813
    0x5031c0501031707031e120204170114011d040807140d080928020301020403020904080403150605090109090c0314070e0c0a050306060f0d0c050d150602030d020d060503 74
    0x1581620b21515243d00490862401c2d00c6040c014888090300040c0700b1811850306001658561084e0303402494003005488200e001031090f0380c450780c00004a444280032650301d0a000303110b1100e035200020b03980d00352545061000404d0602104100c00f050f880100402e0403c1521400c842c485680884446e6100b2103450601c1d840e0807110340d105010440400c002452402d0104050184002c00c4204e0a00d000d407134041030300405030b1354400320303010b40d820000400585c0c0c68840d030b980b142c1c1c8907021195807607003903207488101384c0f480c010821082070400354140456610310707081e54107540103101d0014040c881820001000c00321a0310140c0b5003100c03113010399051000400c0c00401d40700b18501e042e20980307440c050043d1034400d1002e1314002035801e10202e0050701d014001040d1112800024500b00f0040c0100c180031a01251401400700b0300001e40d9510b4051140100d515201c04110340805051074002c0c00380d228810b820340d40072035580c0000d912060580a600caa0050080541121120790281c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 424705287 1250 424704037 424704041
    0x9100f232a0403120e01020601301b061b0308060d02041a010f05070b01061b1502091509090f0c070b0f0a0b150d020708120403020703021003020f090d05031c 69
    0xc0800c1c4c401400d0007400c00080750050035201042c031010790081009030300c1d020740c1c4410035540d0310050844809401c0e049805403895140c0c0b00f1964010b48101c4c0c403100d81010440b901c482c0c254811801c1c4000269010303056505103090700780854150070085400e959500010f0304982c007008009500c28a800201c4286190000c1e4160700740000f80c0b288000902c030f0b02070581d0036000f401c1004081000c1c81340140010342c03041c0b0000c2408099a00b100000028a40d1703252207020021021031011980821102a14a40700520700c05a110031030710300d89040064408200b40000007018207078400044404622030080400441e80b003507801862140450411038054490200180c6100f078441d400c0c01d04165032450840003440c914160051014500305240e030b127040194021001c2558523007020b1004111030480d07a030f01303207200c0c903c41e41c09040c059081d48100181e4203400f40086007010302c10321550a0b92001e01040350a00201102c1c1220081c069141180c903501c200d01c03100f0118144810301c07030f102415503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 424706537 1250 424705287 424705289
    0x50a1803090f06090803040311060c0d0201050403080c04030b0711030904061d06100801030b0a021e07060f0e030f0702190b0403060b03010b01080f060d0b09100f232a04 74
    0x680c5074081e69641d600c0f41142c00e8030090203050440e400801041000031107880d05d118031036401408550800d070700b214500d81802c04404410700582d440700b04020415a01c40d24003075100c90b5040001d0b0601f42141c0f140c50318090014100024403c3e203d91303c10a9410400c02d844803103030700a10a010507a00c90014a21403200c0c058204081d041100100700e0624148040008070b074000c0c1d458580607817841d01c6110700320740007070003c2001643c05c10100311a0300c0c0c0c1e05040403003060700201243c0e8840e03440c90100c017100c540c8036a452809140101e00c4c1c400302c0011007141c12a0070b60400d2291074210a000017600302d10f80f4941c1e690300e080f005500007100544013011304202c90260310200941c21000b42414240d0301d1090f01700340051403032030005071980c01640340542c014001034209460b080e090313034441d00c500d1403d88000c05940d0141e004081c844ca1a400b076507007003060116041c0207090041c984181108040c820003040c0c0180100016024000054040322181c03503480c0c000240c40c4081d0b1140480c1d401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 424707787 1250 424706537 424706549
    0xc0809121c0e13092402040308040306020301032009060d02040e100e070e01050102060123130209031e0303010303211107020405010603020a08011e080a11010816080a050a180309 78
    0x800340080091443d407060b82c1d80660440610401c00fa41c010320000355600101342031072410b0342030102001040701100940042e511442c00141d03a0350550401c0d84509200e200808000703201c0c0e000b642c815440d1540070b1608220241e840340241c091501c00900600200d118401c0140b0540da84101e00c1b5110b40c0180300141200c405507046640c5440c4184050542406401c0c0542e000d00010400140084444203920461041d0040b00d1400180013070040d50380c0c0c1e140d072b0301d41c0354000c00e07030400038901440b0200c440ca089102c43e400301015039422030b0700d038041403102809020003841d0702d0342e445909480e42c40700386504031420000801d5208d4401d0040c2c014090507401245080c00202d4072501031310031174045001d591500c490582ca001c018003c1c0070a0b80144254814090b640003035032240c100144101a84070340b100c030160300c0d0614001803642c1c40080c541001c0b1505060a500019007003074009401091400c80400ca07503580e10309810241104c00e560f00c0c100c00c4405207101c24954880c44407000e80f41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 424709037 1250 424707787 424707799
    0x70b03091213051908211606140901090209040807110d143c030415080901050703230702010603121101060509100e19021b0c010c0809121c0e 62
    0x200e0841e40300c2070744e080e034000d454803540041c01b243d541a6051008a01a05040200e245042e40300c0d03482c22121500c0c1402102c0481c0c0b104091099410100001c50b88010751030002c201003021900050740569010300b01501c40315001440e44140b00301d0514900043c4009001a404400035103040310300301c1c3d0315000004039030013810354a80d8018400c1014182e206411130001144044000c502005904603d51110440c40308100008240d800c103040030101c0450740d29844201d29000c035840303081d120000c1900742014908003203021901d0860703410418101d03260340918150b1341d50810507070042040c1e8001610203119078016a10b15980903c2d0140b04d50b858500a1004551f11014010386550540c0c59a861020003042840007003060740c0342036884541842c0d000319024191031804100d900c081d01a4008401e040c44085d0544410800c0c081c0c0c0a500380b91070900000f41d9214441e050050505aa1183d40d40015020031a10100001d0b9401d043c03060b1041c5508044540c01f030301c9a5000034020380510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 424710287 1250 424709037 424709059
    0xa0b0c0c0319030f09020f01050c071a070c05060306030307080706020f1b0d111207030212030a0209031606120c1e0201020307030608120d0e0a1205040e0c030405070b0309121305 78
    0x713946000d1400d0540d4080c1034019007070302a500541d00d83c7c00218103001d280c811030074009895054078000400340782070841803c0c0e60300c00034146019603101c035410507402103500308223010441d1000400c40b02c40f1a000700005459070f4151800201034881d0240240f529200466444a648a105000c50119007128202d07003406491800aa42050701031440b80c1154000a000782c034415052001405120312034410b94069218007840840b4a03002038961744242a40403441035884c2c1008c2120000306444207801e002020f2070820020000c0c07480a45088040d901c070700a032100c6034080c064049162000005290b40b151054800a000703410460301100003d05000c400204804c0120304106040344003002c2c517103000a40e0911501030407024071076620398402d43d01084040f6921442c041501d82083d5245603880340307010820740d40000c0103071040440700403c00c10300000800001e0b140c0c0450b526620450780740e0740e0f042100d80c00c140600d01140c4426a0001e02c8030180111401d04c0c40c00d680c01290385900701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 424711537 1250 424710287 424710311
    0x4080f0a09230a0603020c0a1e0c06140f210a0b041505031c1e08071808031606060b0c070e0a020304050607081003200916020a0b0c0c031903 62
    0x1031024003600b10703048243c01d0001c0c800f0b07038800c2c0c004040d02c0700c410007220500a0190745600e0602c03415a2404000721150301c00c8802c00c6000302521005003054070b440000e100c0000581005407281d99900c03001d1010014401d548040c0c0741741035000c0c0c0d004040c2e540c0000d02d450303408000906080c1400b584101e1030280b0b00085014031038221019a440030700140340d23200c0b007036009000303086083c2c00ca4005e0205042d20121149040300c01200100525690b042c4a0700305460060003614182e450301103038400c0300105121072a4000191a4240e100c0c840b43d40c200e864500b800d000510840d0001c4040260028860110000018102c41281c00041482000da6203200010041f070009640040c01600140c000c1481ca52052894642061280b0080c246095403951440c16030300051040c8040c00a054520441c1440c2c41400c040d801040104104101c00380311000075150301a1180c004c0844070000041005e80003000309079000002e0a008403030756045100c2041010f0030013443d0280010f41440c1d001044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 424712787 1250 424711537 424711589
    0xc062f0c01030c0813020105030a0b0a080f070501020a0b04030810080106060306081507210f050703060504050601231606150e181c030f090b150909031204080f0a09 72
    0x415245d2240101150080703a00440c1c0a500180035007080b02e4032012140c1c120b0740d43c400030070003c01810b00100103c14504000038140350380356110505540080034000003160700c01550aa00c0307030b07251400c20390a40e2195005402401140c11100d0fa41d881c0040202d480e6815501420540e2907840c2156140086201102c048000403682100060440f042001410b4060394015825918442000c52030f903503882d04003800c44100701c030700c0b9000a0b07d23400104a41c2c101480f405404c8502031803e404441d2101402d49102d003d0907040180c4100000384032010150100d01103410780780d0180e4180450300501032440c0c64840e070350140c0a09440000c01041c03a1801441228094210b070300c015010320348000c00411000361200c084402815114420b07003403910244d02c100c0c02c10510a01020505007004244100364042c804180b0b0f010f08107103030a014580d4000829030b41850000680343c805030340c96290154582c010a01075001414001c603540b03060755042291036054480d0b02034000c00214480d503444c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 424714037 1250 424712787 424712791
    0xf020313030309020d0510090c0b03040201080412090e271c0f0e091602070b07260c0f0607020c060702100305150d030909050703020301030c062f0c01030c08 69
    0x80c4036030980301500e002070b00a07005118410300040c04080803400d9600c4042c146000300c0541e508440e9547c03848001c00c15480500d80103022440c03602419464180c1c000f030000080a8030103000c44148a0038150703e98070071003004000c0c00b00c1c842c0300e02da541000c1c2d92014450364220341420403010180300701d003444900007606010300210f80c15405c18130500002c083d10100100821038007000316500c102d090b56100c02030030500815010449100070039407514000e00344500d542003d401701500300a000cac04150200747c0071040b107104050070798102504110620440c8242a0008106d000b0360342c1c000140c1c2c40220f00c46100d41b19640076103410b803041d07e0130850a0701c5206002035005000c0f1140e44d801511940c4910f07440b0a41ea220300380e100d80c030200020458070302e480c8202c0000307502003002d201581c101e000702500040c85046c15802c550441d80c6000c03842d07c0e14001c5008228460382c035084050a449500d918214490540c043c400010810683e01c80140b410090b001c28104151041d0381c622806400e4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 424715287 1250 424714037 424714051
    0x10305100905041703070e1302031005060f04092909040305180102070305120d150509010303110c040c0c110d030518120f1f0608102c0c01030f0203 65
    0x4621070070500303070701d004001c080e1060304c9401c0340d00480003062224070001d5004101545803e803a010301c21041020000e02995030008182c018010b1252004d0503032008402d584084400070340350994010b54800500031503005504c2541086840d4030b501306c0707003541054020001711114450510003400e001e01d0b03100c00d0350001e0002d07404001e031000d4400c000000c0f000c0848144143ca2406e60b880c1c075842d00c2d200716100100d032003280010b24001c0c9400103101c3c0000500700c0d0300d0328103042458000043c001e0401484040d05000c5280541802c901c020b000d45080003000410070411502c04a40007000c06641031000c9070280b81c00050029240340071000ca0881580c9030f65203520381041410100a400c481014894200d0851132540c000c0807010300990003010103010003810100049c01c03007440b4000b9000ca03005400b030b180141c00d02440380c0114071a1641c2440e40404107001311003015a04903110041d041c004418080800c4c100840404584a00c0350381007640c0a00070030040b45150022807100b91240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 424716537 1250 424715287 424715311
    0x203061914010807020f0f030307110a0f0303051f031101090503030c07031e060905010b030c19090b01050d0f0504150b0315090a0510020d1a0102030a08060f0d051b010305 75
    0x2401c40d031285202c642c4c40090352054071000c610201ca40c5140001d41d501045164002004101040d81e010050075402d103040402850884850b40314403d5490f04408050f04160302c403000525084c02a8080d041517036007081207420150764030300380100040078909043c0c0c0007c0e40e142000489180000984401c48541d07001341809034510b079500c0030740c4501c030600010b2101d0007420308404124584201e049490241c800070410076000420181440c101303d580e9880380074420700e400700c41c1417142544402d0303800003680001d0f80c0c0000c0006807902d00441108184050404510340c02c1d04c010750300900d000780d1241d04071442d072003045158042500c110070950b40d050703405038000c509295015140990000b19500039101035035003c0d2992810b1860b00e90003400c01c1a000500700201c11241e00c80d0700300d030a803990f000740310403e10100001e440340704540d51802001805008960310342c0e11040c5204142800401324850000a481c1c40b6031108039001050440c03020b088050b91041d4001c0c00780a2050118000c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 424717787 1250 424716537 424716569
    0xd03030e061303020601120b18100905031201330207181509050c07031d0603010303090e0105010201020a050906090f0406060e0405090a021c150c081807061b0305070c030602030619 79
    0xd0707440c440c62203113908274140315210070401a40b105201d14117900d03000f01c016543c1c9032608490303120980f80691040707031051083d4800b400d41890384a8070900d600d14030b0040581a404a100480c81e0070529085024000004030552103003c0203640701100141d920b107030b50b060040e507130310303c44007142c40864201011240801a1030000303445010303405081440000511407011100c0c003c01d450340c00c02d800031004140302420901882600e04c00b40d50052001344020740c0b80c0411610020058059a0310250103848045034004d85070390740d4030780850041000303803040012030385d60b00008010500d2102d166000741d00d40404030b14415000f1550f009174070380140903100d07214044400aa20310000c0c1c036090350304107050021480100c4450081c2c26160000307640302032660414020f0300c17034079004034950511180c0c00800c0402c90660041c0c4080c0d1003072140c1c41c1903112954075050946e250b104079280203004071030b000790100c1040010360286000b8141070f1802000c1290035803040c202243c403402001c03041d00741501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 424719037 1250 424717787 424717801
    0x507140a0c0303060b0c0a0302060f07021507120c080109060803040806060d08040b0a050403060b03012319060803180303070507050409062d0e0a0f020d03030e061303020601120b 78
    0x1003401c64188285400105295100b144146a400c82c00d00d60300f55400500c0d0030380c141641045540d030000c01108030010302d800c0c43e8901950310b51030381102250783c2c8010300c0050803070b500400c1c3c55000c202800405200c2071504c2c581c000c08004090050801c1540b420802040e01ca50002c140d07001d41c0c85ea0780040101c4e032100700400c450051254000c540c020020000450800d0301c0d480034010000842c0c5401c2c2e12a81140780280c159840329005034080c1c0e140c0120301d0302e0805200d4002201d50300440d40c290103034840b01092120300c2a8140c07045002030401e800002d50050000043c14000440f50f280103004e8840c000f01034892007092130181243c1d1162506002a10f01175128100300c920401d400511200b0a2208100c10100070412001508601410040d01000c41c0182500f84400704013910f07000006994001050712200300c060f001d9503440c403440c0105402980140d1358082401c0480c1c0c02880c10b00e07030151048003002c9088005000341c4000090345d0104500c9110001e61014a114440c1e41d40c03d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 424720287 1250 424719037 424719047
    0x6150608041407030804151704050a1202100903170f160e040603020405041a090705100819091407080712060e1c0309061406100c050a02030d0807030507140a 69
    0x298682e90035001e202800000104607400500c020a41001048084d04101101074100d1090f48825203000461208200000303501040c0d001c1c5141e44260483d00e041c8040b08100e00c0c084c642c010104515140100020605030411451109140c1d034040c03031103883c3d465010100307201206407400301002500203c500b003260701882d91240c000d440940b0009506a13603400140a5900a8500383d0301c01c1083c030b9011040c1c01d403c0c6181680310007807000800390640390402003103441107000104020081d1041c040307180580421410000404030785d00c148403450042c100320919902040c10b07003803184100d13500080d180358042204400c0f50010440000e0998a030f1715144003821510100300788070701030800c5400726030394212149030000e0318035a0006965801480d0520450f9a200c020984800c20002081030b9980c41d0480110030306820700d0302c01249003003440c00a142001d16440207506010700c0603c00b001c03c2e40440c01501c68106a9030611141d112000241c0f40140070800d07140c5000e0041200d12034260050b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 424721537 1250 424720287 424720313
    0x12020105091507120f030507030605130207020a03050a050706020d020d090b09180a1d0105060306041103030705060a02070c170c190b0c030405040c0504120209070e04050f040615060804 81
    0x403224603440c000050b503644610000c04130000000ca075150386411110765040c46442e5002110b4202003051a05001c006074256040000c042e0440d071300018801d0031510303100050001564002c04840603640c803480c2913900d40c01c59020b6440148102c00c3d604030518070004040e404e2000d82c1d154004983e0501126600039440600401e03045245000e840d014039054002162041030b14240000b48000120142c0d14a08041510080140c1c10501441203982e00072800c1c035005030340b00304000011180321010038254051228080c029004c2e26080003107004842c0c0081c40c20324031516194480e203407158071070290000000c2121200e5400350007124160308055000d074031003844080b40c0d40c40302c940e00c118684065000c0c000f004840d030408070f0b0412480c10140500c4a0501d0281040b40c03c141c03e107008000c1e43c644821000e481001240c010910300350003000d4403200c001c1c0c0607006200318904400e03440c81c040010348003210001d1410303c2080f060040da01030581950960742c1c42141a0300c841d1582c07080d02e00d40c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 424722787 1250 424721537 424721569
    0x3080c2e05040f0818010f1106010b03060f130b0f0406080613020105090301090c030611090916120c110c090702030a032c150a0504021c050106030c0b12011202010509 73
    0x240040001040e8090003601e41c13420009200f5160b0036171900018858644881004c0a000c0070001940511001003111411340b83c2c0d00d052151260b50300e00000b5090091241c5c0d60740c000765000ca400c5551681600201c0c1e41c3c00f000c1d62200d081c031124500344000c81302544079900c0c240d041038010a0841c420304401c8403100e401454000d081030341042c0000e0855140c0941114085540d10041042110354014400285006101a8200340c5140003040c00e940b401007048015440841e0400582070003002d0040e08070a940701d040100c40b2010354060168031403c0c4110303080303104503100407400b807500740841c6100b00110b5019608200d00c0190a602804a0402e18400f81141102485850030b800409aa4040e081ca0080c4003007802130b90800c0300810040c0041c5881d0303040908000150300d500d41c4100511b010507100c0e90040c0d0484c1815801004c05410084c07202c40080d0000407102c0007180a00003800901310001483d981e99900c5400b8880c020794024040351042c032440c002c078940303481c80c01c0d52014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 424724037 1250 424722787 424722803
    0x16121404033201020307033e0c1015090b1905010e06040314010c0f09031a09010b0d060f0b01020705210709110a090512060109150b0403080c2e0504 65
    0x149140b0942640c00407075446000035610a075149100d4960350009040c2546c41c03035444110750303000b100910501840c403401c28516500207085241814100100f2511100c6100c0c10888085030b0940420007200c1c62103000c8800782448100c02c01c40c50b080040c008940708461061042ca07140c00c00545501e881c0205665000c0801e00c0b00002280350062041c2c01d07044e100b0000035904248070340151030400305203001020000800010310029965824044007030341141c0c0c8011903542e0785149180504410004a508405c110000b281008129000840f072030704540d00c288603030250400126910045485000d80c842c041c1119180310104074440080360300c4e02c6c00162403065231929640c4061302c2402074484500c400001c1c200070a960b1000d0540d02070207084030100d20325003400b200380f0b507944018002c0d5420a03a886020b2800b0744460003400d001000184500e50315540c0d20700b0f126130190001030724005207000d131008541e403d0303611000d5a02d426007552034513a2030441e071611310300c014080103108503181c0c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 424725287 1250 424724037 424724123
    0x3040801020c0601260607081003120215180601030f02040902060403080904050604020a021e010b03101a01050f0706020d020d290306071d03031612140403 68
    0x400207000410140910b81d0080c59607500d0201c1c6410403c54a58404044040c514070840080c003020600b15044001480c0100c6151a00e10401c525240715a000521005030061065501500410301b1411051051400c1e41d0f2640c440c1e00400c221000307140c292989400280c010300014002c0026107055900250000a1031a6240e0124000da407050b0400e9841d84070209020b0f10b103150a0007041d5100000341c6e015420603199600203991218096107450604000942080c062802544011240c010040c1190381c0d20400001650040002e11403801c0c0c0701d4614003010005502032011246500341508440d480c200c00c641701e860082d0060110b440c55280c00700f203018507018442c02141161200e01c5010540c0b10358030404840d1a03441c92080c54000e1b080031042011841d00b182ca04203e001298031044020540400002c1c11480b031001c0828510550030848010701881c03142c403030000a03440d203440c4a85425410448003c1c0180e100040032038400320200264400c40f40c0c2c00c0707030a1050180d0304038440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 424726537 1250 424725287 424725299
    0x17010f120c03061103010317090604170a15140a06030308070507060b0306070302120901090b01121103060a090c06140406050c0c0a082d0c0108071b050a020901060206071e020304 78
    0x626413203680c10031646008001030007031088401a6102407905030000310314025948003c40c0c40d40c02a4441d0a100d035051039502550200c041c400c100b101640100c2240014248440c1d1000600502030b042542541c07560008802c200d15204031015203401d030b10b0740442c960f95040c003144e49500c403280443e4415260111a540b81e04c041000e917004010b640c038050307210400c1801d02e060b5010014034103500d684c14600903c4c00704030951615815104049400c0550b140c00f820304200d07403040c204040c0d0705803007048104001d404581d4001d40410748200032142050380e9421040303d0700b050b00420460b0488040004003d80c90180000b042085901810b4903003003c03040740080d025804580c170049042e004200b8035050b0515034003180003542110100500030440c808031440da0380155541c071605111a880c0840e1300e55003c2e441a004000c0c81c10056184541949071040d02c501c00800201d0140c001e070760021480900104019204100c1c90b0340f00f8481000744882200d84104401c900c0341580404c000110350703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 424727787 1250 424726537 424726541
    0x1050c011404060c021902060c0a08030a0204030c120b0705030402040612030801030c0b040b0d020306180405011a0103050c180a170c030f0708120f13140117010f120c0306 75
    0x203108404629141c20b060660566040d4944c040c2150410540c001c03495070441c4481700d04540594115072540c0f88405d50500d03082e0600009884040f0200401c103001c03107a038004105a03481604041041c560310f60f0700300b110300c54078030009001c0c034100b00014800b6840b0302c2c065035101e80014004268a59070744d2218554465064043d000940448014014088200364603001414943c0311140380c07600e445060041c1d80102c50328600816000000710342d103559035110506013481180658003180c2818a003d90003404440704d00e1002002800401c1055800380c4900b0f8868072443d003055107002030304103680b8075414841c1c2920740c1c864040d00020488100403001030142c24036030340091506880320020149005510030b4003900c581d000900034010b52401003031081c4045c0d81490065160300c0300001c01e038180c0c020780380300c40003007981c080001a40310742035040f2080307850b401e03200d5a0090743c500041440c001003d00a1099201003c1c80070040056050044440d860081c4c0d4502082902c0b5520307a01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 424729037 1250 424727787 424727801
    0x32a090e0309010f09051003110f0307121109090105040903091a0903060c0f041a04212306130812090109050f03030702060711011e1a06040f031101050c01 68
    0x108590020502e0b408650f000101d4041d48042800c01c0ba903010701c1c0100042003d80001d401e1010191109544502c0d5010207040d50040420b400440d038a03032070030010051580c000390000e00c00b403078101001070302d042411000b01c0c0e41403136001c0d042008587c204401d21000e410074030022004c10815001c0001d054224011030802802205551030743c0d0f411070000c040c40c20f40c7c050b0038142003d1041040218a1206004480440340070025041c80c90701d100100d44c42d54011984101c0d041c0e10049950750240940071080c1d41d4461052250308080c1c011840c148124690201407540705501900204100c1040111801c01e0b447c0b15440880ca4800d2104c2d002008020548100856a458081620801c00113001951564031050004c50a519180c20300079518180030300602c05004c001c0750303000d040c20000e4103c41c49044010300103000500c49000e10100070003030301c103a00380c41d40051500640395161103002c50301100d0183d50f030303460340c24155141c60b4188900c000c945418810104281c800e221001e02901e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 424730287 1250 424729037 424729061
    0x82701021b0607120e0a140607020409031808060f0a0507121a0d0803180303040c120c05040207050f010b01020a02060301180204030b0906191b0807020102041a04030c0609032a09 78
    0xb01960b10402413001d200d16076048201e948015100c942c3c2288c0741c80c010313201d40c0c60701182c01007000c00450506580c01e1260119031000481101c40c00320b14a9400280b0302d004841c4410300c000a5a280001001111000d8440c9000140405020108011140c10000d00096a580d2028680e0606000075400d100050001c480b0500040b0801c11b085024142401040d90800069031840c5025510b10452880c3c074080c920224141c01005418800f00520300c0340034103409081155209c015042032640c900c40b11030317220407940c2817007009a19035201080402c10a076000d00054116401c00320701482000001c020810312075420302c400804200001000d5018103d03050150240d4103000340c80c1460415140328982c0014209504490001d41d004000d84446000b80380c11078554a071103004038007a114541c000742e145030309080d005007001140c1006001710b07485006440d20be141d45130410b450350040d5100192072001110100d81030030840c01e4804000c549607200b0a02000c1e01c0d040184125506040c81c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 424731537 1250 424730287 424730297
    0x30203131e0f050105040b030a02041a03090705031603110409050a08030f0c09130c2c0a0e090303010b03070909060b1b0703020913020409020d082701021b060712 71
    0x3400c0c914107404060003900c54010491411414240040d20321300c2203204d00d01208000000007041c0740c490703a0648000d0000510000010303902c107020000640c0007134860f01100d001d07074a400152403500244140170b0507218002c40c80380900e903465810045010140300303500252601c0c2d801000a506021300100544074510f000e403242403a250015510074020900c414005080285117901d50701d000b44420302e4402d420b40410380403082901200c1080d2911100038907001010400201d506e940c0640543c0e00324107846075000140c0d1003500441225064504290a400800050210030148402158450380c1c5081c00c400071540c0384051000c95565034000d003460440440e031307180031190903c0c80d10a028224401071015904640000f81c41d400b0183c0444042e400800c03500003191034179003040100507001041555558201e007060741e9660304c80380c0110744410585030078824800805080d8040340a041c2e00821900116242d60b2501c6d0b1100b5955590050040c0035107000104012030300c00583c0c22951364 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 424732787 1250 424731537 424731569
    0x201090f1209090603020d022b080415050313030e150408010510060c03020d120f02030405060403080609040f0b0402010c05100b0a080c15090f1329011b03020313 71
    0x3800b0034400d4100440d81070030302500f000544d54181d001403050f5011a4200c031b40c1110a1040411042300300715458144072a500134000348500c2d8030261003111003080d00c050116803403107c21201403004541030051084859502ca010a101380c884010384100902a110042161030201c0c0a5030440d034070000540e03440b44200180d81c01c1e2002900c00400d40c0342011440082135030350194070340408a80398401c02030a01c1e800c4104c01695000020014a641c1c4115620304090a01f140c940c141110182c1c081044a00407030500d06107060424416034001c1c4400010340c034169510519500c0c0640180e0422a0704e004000c0880e6007480500c02414007031a000132456a84000d010f03500c200c9034028003098104c03020303100d40c6440b141d0b1035984202d80418840e0b40c80402d4800944d01100c0020455003266096480001002e411b0303111081454030042c1d41224800d0980d401401141c5080d5601d00107085c005500c050446400310a14020b8442d006403410f00c20702444201d09031045520510750245402c2c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 424734037 1250 424732787 424732823
    0x50d0605060f01110d030f061205060412080f041202013e0f04060305060303160302100e030901052205040507021e01150308130f090f15081009030201090f 68
    0x3080345a11842820a52100c030200100d081c0c8417400c0782c40c1542810745580c55500c0c6210f0662049000d0403034130403c11007444240c100319548601c101e90459011518101e02d4001a02070000240b00e09004545c11507160744551300c04e4640e01e1010309142c2990348600c40240205600c55140c00036540d00d01c8640b07114681a880c0d0000010420000f4240c00000c1003442100030b62030003114181d41d040e08000c44e140e100e81c40401d28610807801030321100c004440c0d1840070158082008003156054250078403480d4072086c10180c07244100180301d40450030400ca45c028034285a07440348504c0112001225006a40704081010342d0421070303140006800400c17030302cbc15070940c2d402890140c2c804038008120381c1102c0c407070f082c240c0d007207c0c040030300b8103040030514044001d030742544400501060034805100c103540b4174201004c1c2014591069007203041c0350703c41c000104001c0c1d0342c1c42294080002400001003020408000700072021040d000c40d526600e100c0081a02001c40a9510388165103881038402840 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 424735287 1250 424734037 424734049
    0xa050c0109080d0c0e0f1f09090f0e1b0307030b04030314011719050c150c070b09150304030e010503060607020612040c120c09110d050709051f0504090e0304050d060506 74
    0x101c1010b1203156440ea594415460b415088500d040100001c0741c0e1200d603454041c1d4003c903c8d0742c0402c440c0f60403c030007019050301e190040c1500302d0003c01203902c20005001d407c00d44c00080702e06c041d0103901415080011484054130306401034084e00700040c20a04030611a650f0364826082003d2400203140da81a083e002040448080b2080d0a120310305102c0c55030782c40d40c944500c03040032403042c18010300910340120540105c1c4d1a42c40644200d4402907aa05652941d60b0050444203128000382c0303030b20210070603119007106e1045a26603036513004080010b00540b60368202400032034220030140050001608c2d00001007030300301c2c000c2c1c2e11180c051405d4680340190221a411444c0c0403250910078070006122102c420301500c201e0036000c0340c1d40c01c80801c42c94840c000c906c44c0c21074030390800041c8030b940360f000301e40d030026071b0004d850b102c0c400900a00480b8449001210f06000944108020060380c800c541c480204120700e0019640707050307543c800042443d021403c0c295003080d83d40e030034021603241c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 424736537 1250 424735287 424735307
    0x160503190f1103030a02030c090915091303020c0907200718060303050a0e011e05030a05010602070f0311030307081b010c0c0f03050a1e092303030a050c0109080d0c 72
    0x20701d0b0001c24404160121a1a40000b0f00070032820383d00400400d14a2905505903028030740050214a058030b84103076010842045206d819002e00518008250002074182070441c5c4280c05030000c0c01809906403d0024869000b00090b04008080c0603a01c0c80030540302d2501300003000400244a0f0382c1c01e1114125040742407074281d02e002807408004200094110040c0c890301d240e1403c044601240d4000142c0340f030480440b0703007541c4202003141030140da5003000242d4020140d20104122503030301e812013640c0c2c9040f54050403e070807118150400002d1481da0b41c2400512000d0306403820502c180d6680541c5402c5003103006840720f000b024030b6103041c03000d10602d061000349103040d4031b5111440c3c40760480e5603080309010b8200100012840201c5016052540b12507201d40c0820a2216078600c00030600b0507540140d1078800e2244800000d003125415000c2c10342407009010b1403510348605429142580031b1070f2041d00342d540700c000c1c036004513000c0809440c28000800000c01c5d50150301c02c00501c0b12402d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 424737787 1250 424736537 424736567
    0xc0103050a02090901030b0c090604032d05120c0a06112107050f2104060509150405060609100b030a0b0a0b03070801031103010f18020a0f0b030c16050319 68
    0x2042c0010f1070582d461802c01e80c11030350000202c03200c2c0e031100070712920103115412100d41c00ae04005400401c11003810641100a140b1110317600700d100d04c15421140103440480040c100e98002c1c0c00f2650b404000c40010403880801c40129441c443da07580d03071801a5820800003505100c808035020200d0303004070b2641c01e20740101d14503070019440c4c80c050203401401041e000b52180d040100d41c441401401c020b021021104480008425241c00d10304034000e04011643d015950081c55410195101c1d0307000c056005991200242c8076a41c0c6540034008100c0c002015a000e80042d030100040e9406617000840c01000541c0d400701e181d84540d403d102c2c4c68241c550184219450800410075059409801c3c281900e600680050803001c02c070b00045d0242549035050801e461a100780402e075011001480481b00384245d4501c0d80540d51406000c207039184502c00c1040900040000803084a0401c0003407510f10550682d580362a6000c1d00c816295400007000b020f80c603070013a0a0305041c82d420401203420589 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 424739037 1250 424737787 424737791
    0xc1903051c14070f140705150906030c090415060f02161202130b0303040f09050106020316060b030a0c030302010203040302060907060504060e0411070803161b0f140106080c0103050a 80
    0x440340d10041c40c00c075003031242c000e85220218800e802c100482c103800384001c1c2c00840b50500740c0640007580d600c5505510409100d40040788920680d4000d08064a8100c2d80c0204010704565803882036200e103034026801c181c1d0007642e41c0ca02d1054444140b520300003074803142c1c0e18051190918a000b034608201e03d00b00200d0011480d0b42041155442020482c040f5810755044c0d02d0700c8487c0700c02e24007818215181e2641800017180100d03081c012220b0400c00c540100c0001d01c4640d03655141680c0724840d503003c0c0309030440c1c0d611100003c186035400580d0a08000750848a01e480f142c0c44555600100703400c1100141d4001044c801030507810040e46402c17a080b10b016106039890000050710754803a0740700b440180006d51101642650312030b880480e0f510030460b1410344c3c44100d40341c000c5050b401220444c5010000c18007000b02d0f144a040e4488804102920000c138a440c90b4541340c1e004141c00d034049820400d00211582000030a0140b94000c10b031480003010388040c40700001d070030796a000b01110500c80c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 424740287 1250 424739037 424739083
    0x18292a06060f0f0d08040603020702010e0a1a0f090a060e0306180c10020304050a03260304030507060f090501110c1203040203100e0a08070302060a0c03020c06010501030b01020c190305 81
    0xd078410291076254082203544941010103000480e4501e1201a03005d807040001060001e066501500207100c400d100740d8950315800403103010400c0144180c05131b4207400e86c142a81500ca940b000340244130301c00c02005080c1c00c0c03030600d4000500c4484560041c0c0e00041e6803100443c400c0c20b0420002d03800096841006d1048142c1501642d528503920602c64407130089041d85880c010300070300886000e41030252108000545909124880c4040d50003100c04120090b007500100c1400903003035a014541c142d86091815880707031a994040c2c440c410005003038950394007144000032024840c80041440305520726442e498400b02c0281064048802c28042d65803c01c1040010f0b90086032401000c101c0d400c2c00100d40112101030b6203089550b04004004400010703000d0301741500014810312410350b941c0c082c00034080c481320881c00d902508a801c4290381c0000c006000c2903009400a143d602010300c112100c42c4040c1000070755600d0b0000071600c421202100074005e100003849aa40806026111651a2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 424741537 1250 424740287 424740289
    0x11090622150b21060f04061d0f10060c060216030818030f030406050a09050d020f061513090201050d1509050a050f07080709031a07020d18292a0606 65
    0x1410f5a0b290003000383c000d0380000e40e03a503581c040f16160610014008109590305c80301c2ca04604040c04040840440203140040c0030081c8211006e8418002c00b5800d40a16241140c26984000c000004441071074080c00f0f0041011621044000c1d00d41c001d6a5040e5a07003000d00f40103151307901480351500d060700100300d80b80c59a46400e00701da8000d0780c0700c80000350359520741c40d9060040540d944000c006006a41d0101e41b1954002065101050306d1001e88900e0303250382d07911161303c1b0500720459800c060000342030340403408981e108566003401814407520340032540301e03241c0031140b0500d00324101d0024440305110141182c41a6644490707851800c11542c2056808606400d40042c41e060404c449113002501c1d00c0d2244100700000d65100e1000c1003000c01c0b1180380b01042034100c400e80d0043c81104151002c3c02d02ca14240f20b492500380d14a16034190410095080e03030003a00319103102e8190403d03c1549410a080c0c01452182c42980c0401001d4041d080402e00c02685406042403d074070550501240d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 424742787 1250 424741537 424741567
    0x11107080309120705031327020315030601120c120c0312050405060304030906081006050a0f030612210c15050a0e060405070f0b03010311090622150b 66
    0x8180c1111115840b40d0700c1c03031401c52411001a200d00140d00001c200700007004000005003000869000000341940d031954219210400040345004c010000908040c4d61500203900541e00041c01c1e01014101920100c082403500000b82e02903505c42201e042001309102000c5c3c180d4003d02800005910110503e44401c0340e008200c0c040a000400303000b01c0d00c100c85004000b100d00502000d45026141e07d05400d024001e001944034103000700703803008002016084d40701c4c0520300751401c03603c0316802d0050003d000c41d03141610642c0340043c960b40d42c1c00402e1040b18107408400c818481c11003410f0b00b948020501a02405078204101481001140c4038009080348550420f225110390b00010290396502800019210342204406180918414881800004100d09065440e03c81005e40007540d600c0f42003609120034031001e860041ca800c500202d0381781569104c1e030081d034000c4c0094070b04201a17481303445284400306500e034207a94510496451a084841c000014540e00a04909001caa115031980f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 424744037 1250 424742787 424742797
    0x9100e10060e1f0b0405061615021201170a15180609060c0525030302160c06031107031e0207030203030301140a05010f020a1112010e011a040654060501020111 70
    0x310642d4045460a90039038482c504111154009d41171404200d0388000040082d4400610690031014400000c107004210310618000d0742c01480c02441100b500e0703252400300c05004010642225210a518401e00b0340d120840f001141c081c000010b008040c900d0310070300700d800946005061080910401d1501140c80622902ca65007a0040c4003900403545801c40003032103103442900c8441075210141d0180441180c07030806407042da0b14204101c5007440c81c84940750007003802c0280007445451030181c003110301440419000382c040c0101c0d40c84580300c0d07000034110b8009801a0780704501d14440b0204900c0c10402820040c902800c1c140e07101500e1000083d15801049005001202c0034111010319807034400c8040d41c0146088001c00c800201101440c0c0a01340001120700068014001c0c41c020345464402c000403a91509508000c040d0014001c004446804c4094000708481c8001205031040494500041c105c1b403201399161404072008580c100c82c1503800c400e045a140500d00000031507100d040311 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 424745287 1250 424744037 424744039
    0x60b0a0f0828020c071e0b0d0b0d03050702030c01020304230607020913121803031b080c0307061a0904120c12080103021c0b0703020d020c1203190509100e10060e1f0b0405 75
    0x144e03a98004240a08c0a44009036805070803109110a05050550080c00340100510880580c1c0210260100482c2d8a020310300030020910b040b940320303c6000c00d07818841c1c400d800003e407845007400c0d9a0f40000e15403181c201c078900350245610110b0403c01110031025540401070781000139209203591014407803c10180802814403203100e0603000100f0b01c2603842c261042d400910ba6540d255070b001031a4582d0001901145d00905150844c8024030294003034000741d40014082600e140d80d1170b103075502c035036800c0c2c8000f03418009202455004514500c95841a0341119120030003039516610600c41000c108510400d1101644404100064220bc0005411042c10b14001d40c0b1070041d84e000f1002441000d01c0c09600384604403604040d503070481c000e10b100d007203c03d4525818404400c11007003681c008460540345900000058819000c8aa02c032020031001b103801c503112490500044c0084403002e40018050304605002c2203007810002e014003c1ca00306208006000a20f080100c40132030245005603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 424746537 1250 424745287 424745309
    0x50303390a110301091713270915020316200703200603093d15080a0c03200a0b0702060c07120303060b0a0f0828020c071e 54
    0x140c1c1035540c0c00d400c441032054000286d65180c0030040e5904034194041100c5200c50845401c0006030012910400325455202c1005074044840740c042079001030541113002c4ae103040070380580108011851024501c6001c000840442881c808500a0402400800003600e01c000765104050203075000708502048030f40c8056030400d065090069100024010400790750880ca0110810000000005156545060103a90100d0783c854600102e8a00c10b2a545a0724145403406580780c010007141e0300004c034540244002c9802640c403500039a0502e82125819220152851414802d1011210141806007241d681e03002030a8a6913000c00c07aa00194880c044100038089000419034071a00125482e00000d007055484050304e1f0700c0c41c011501e070140d81c240c001a1a02c04041100150345045900d4108940c41e040f003840e40c0448211840000105100b8101071032403469200400510b499420918060742c0140e00c90a030109410300d0b00441f5440706c2c1d0140025044120b20034030b0740028405035031030360501c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 424747787 1250 424746537 424746563
    0x6030c0504020f0d050a0f02070b0604050c040b07110a0902120a060e0105180c220816060503010905180105070c0308060411070201080406020c070e01030201120501050102030d15050303390a 83
    0x41b10000700340e24040c2212090000600c14100100803071501c2c4103120031541013019403034410003a003650166000310208030108004010204031030040c0c0102481c001010942c00039103840488060303070001c445d40c00303060a002d800d0098100c0c0b0b80c002e49024088005040c41e4540c03501e0009400305a224010341c0d50701c0302c0d007404135140ca40d9800443c8c5405a0003050a154445e4103043c80726101d0b210300c9001031b24000d03d00032034981004614150f044034010b40e21541113909081001c801003401400440500c0d4019900c07205880302030189030710554990300c642ca54001c503030501409048006104a100c3c900d400ca0034101c1c5032302e0400b80d8042c19020b19000e2030030b03543c900e40840284a155940407041c4958400000d500c0d04003006107068034400e030390700300c0303519083c2d84207000713aa03420302405026070820321003582d01c003400303034004501454007980d8240b420380d9400c0400c0c00c60b8044200e00e0f1280c0d201c0c0b90b4906c440c7e807070441645902e000c24040e1601c6041a40600b54a0341c82d40b2100a0247c1c2d44010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 424749037 1250 424747787 424747801
    0x1006050c16140306091507030b130e010b010e060c070303031d0a0c031103061005060d0609050c04031b03150203060d12030b030f12070209100e0a06030c0504020f0d05 73
    0x110400807450328065540003940c454070703604441c1801c032020341c1c0700b40b081c240010380c02403001c0740039807040b11200302a500039203420b0130a5001d040350140954200111402c40b17448030045014280111604000005645c1c040000041c10a03e0700d40d02240604820040f03a01c8500c0d00090345000c03280c0504c1c0000320301c03000c400515021280c040d901ca4840c0b0960182006020301c00c901e000071070f0301c650b00c0e030042401c400f01071503103c4c10304641a85088a081c0420845418040c3c002c0562445000001841a071140e200c94112001640d035000e40030400710b000d01c100101c9803d0300c1c0030001840d0318215102d20b9607448018900d9554509072400303802201040c4141c903000714240e00180d0010100c0000d0383d03440c2008000300300003070645110b44921034070305600b22030105141d1000782100c030443d841c00b107141c0c080c40307240d0300003900b030190034003800c00001900c07244080b40c58042e001080011603817a10b1410700403007819135034003c00e11030342c41000b4001c411510003048404c07802000c400480d081e5500f403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 424750287 1250 424749037 424749043
    0x50f0c0a120b010908120a021612150e100b210601091104090606020a03140405010c0f020a03050708060103060c05120a1a0301060603020c1203070e060c0c0307090203040b09061006050c 81
    0x1d44945c00e9889000b040c01d00c4165904080c1c4014161070342211604800804400700410740c5118000402c40459100c00c085950b040010081010490000c110221b4038880c8d645003c0741e40400815696803607469200d685480e031100c0e40d41910544100710b240c10800c1e440b0b6110703031040c41207000301039985030b40440c0c258156060310010a0007200420405681c1c04001c6e460360000c50b41100010051500f50f110b0b0350781c4505490681d20181d45d50003100c20039035078052045540d600c05030313840a444903002000420401018004c3d02d008000b0b08280d500d035142441c2959110060142444824003030780c03940d800d402c2011030340400103400c08241d40f402c0490340100c0202c0d5611058043d402c1200105100c6c0c0c0680080403038040510031a540c800e0380c610705030502d000980308000050070b0202c650849243c07039030182108041342001c0d02c4c40c05003420b00003440c040c02548a1180c041d004000c00c810f018003c4e00f490f03408480c11002d42018a802c52908010b94502d000e444140180420345540c407100030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 424751537 1250 424750287 424750289
    0x20303030f04050f160806130c21170415020303090a0209062409030c012604140109211d04050705090613080d050715020d090f06050f0c0a120b0109 65
    0x50041c5c445400c8200319203a0505594020701c0000d110304000319040c0003803c101e1450b0036412040b091501418001c27081c40344c80c0358504081d0085030455181011600000c1c44d0b41c000c080222510369181d1905d602c206040c901410180155013083c01005108440451940061581110440c02d140e582d5070021b40750160061150281418141610034409140001040b45036000c40c21a51003800d18001181d0130011003050352500c0035580940c02d007001440c01d00e04e0300544191502c0d5814490b00c1c9000b03013100c01d5000b081d0784081400c2080d1b21440d800c02e0101c40e503941685407461a0640e07190107100f615210b003d0f101c0c05a82d031180002c00091103001a224040c500510f0156180d0f90f803040a584405036000300601c500401d540341818038020800c58100550041c4100503d03480100e894000750845c2d50f00c030003004d841c1c0303009000280d0b00c03078030005071244228800229418a0707402c442051100138142d51141404216000c0c59035001401d021072004801c4000c20100c3c600c1c00100e9a210403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 424752787 1250 424751537 424751563
    0x5011e091e020d1d07080709181407050103050c04050f010c081b060603010c020f0d051c0f021804110f030405010b06030c0711040c0e0906031608010b010219020303030f0405 76
    0x40415403010741d00380f81c0c0146202042c5640d0f00001500e09200c4540c55981c144241000d550241b08100301109007501b112811500210006910924030b454800040c01d00f81400c540c0b40d00483c006008641c2c00d8400d00f41c11034018420b0500342428030012416020610362581d040c0030118802030104200740d411035106030b11071110b8a212406081f204c80d503440c030641e2201d11a500b08040180d64610004245040301d4581000781000c0400036410785840c1e00101c07403d1418100000803858020312fa000c0d001c8020121400144c0d03581000c0800c1d0104010440424402ca0403e414200b000c025401525421038009440743c1d40e90b100c03480c02038010109440200d411613004803c010002d803550b000340c107104c0c0c00f40700d1142c40c0d40500000c000485d003030b41c481c840202c0d411000c10001c0d0300305130f04503aa0220003d021144030002500e60300140040c45d501080720341e0b4551002c0c4545590501400116802c03210b8080c8400609900180d20303800024060042001d0440018083c09400c1101c98603c003c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 424754037 1250 424752787 424752791
    0x10f0b010e04090c051e040e01200a090e0f04060c080c0a11070e0a020a080a0b060f03041a04060b1002070b071e1a04020109140d080d090602190305011e091e 69
    0x154501c00103a4940030041c0c22071081f0311700941c10880140601404ac442c000100140d40740d03a002411000c415000700342814100b107110780300400d0b01c40d0900f2145010700111a54075406141a241c03003c2540c903048000401c00c130300c1609204840003101c060355180ca0b480d090646a00f0a01d0744801d140420503030100c003441c90443d00b400500042c0394002d0541c4081542c8102280ea01c0003420b5013958050561142c100c0b40820940d0300c09a800303070255410070311407082da0344080214849005e075820107403000d5410039070302c2040341d10510300400c1d0348814003854000742687d42d03d450031400d00c0b070098210103000282c3c10400c00100b03001c1c03000d071070f030702142d100046c0c3e000e800301c0d0038100c0c200003c00c031012408107600420109070f4485140410903100710085c104810103407150740e0f00b58035421442c12003905584900141c0001051800507041c1d0100307401d410392201002c1c10004060b584182c0c0b0040c25069030a4080b42103009968400303090741c12000e00030655101e801080e604078035001c17103c1f0803014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 424755287 1250 424754037 424754059
    0xd0501020d09110307080303271f051b041811031806010914040f03090f0e0906060f030a0b040201090306050a05100e1e0408040305030301080609010f0b010e04090c05 73
    0x8016544082c9400340955111080b146911040c5992048035000f180801d42c000e04c0002c600c02d05419498056103002d2a000d5040c0100701c0107186084c545504c1046245010b00b45090042c1092107031590041e04601c140c03007509200702da01203062289014001c0f420010001d04100d404158000914030840088600c1d564a0402a44150f003489a40e5100c001d000e2000000f4201045018902e0b20804590680307007c1d40b01c5a0390079000624030314007101800161003000580709415002c58008203044100d49065241102801e4101040240389502c40e22014840003602e403000601f07034100c19481410105691110b00040e510200755500c018081828101009801030450300030714010003d40c004c00400d6501c8110007080c1081c02c560f00240040202d403066800620010a80c1d006405881c1407031519440c0c4c3c035854210740c82608103245c2e5521010070b00284140134440c01900d030100040411082240f400005c3c16044810381c6c01d40300381d40314041784d400c2c00140c1d1001c100401c4000d1201d4100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 424756537 1250 424755287 424755307
    0x4140619060608060f0d0507051309050708060412080901020915040602010e0d050f13150306080706020304180203181006081203010f05042409050103141b01030b0d050102 75
    0xc00060280106500344000018110f00941d030721401280b006120069115080302446190070300010280c401d841040030014090300c1e1501250b1518000704004100501c160400764505240c560044180707034070100800c004075032420321007100240503140001454a9441c1e0050190140603c22580308012602c0c0845a1001e100140100c40158009000e2056441c1005845201d001c0300c0401213081009032a142d644000e0050111020040c40b44080a80340c880b0b2502d100c250300e25101c0402e80c1c1e10000e20000c0030420110006010520003036151034101140200700d0003040284001840d004000b1801d04000100799040003000c2004484155500c1240c81d4080c1425105983c03036406440c10302404c0c3c2c034800c000c40c0e040e5440d146d01c54075150b15080c2480010941d56003006c00603895000c0d0750303a8100c072250f010001400c13803540204095040d820320111181440101441c5584129041d1000f106915118010800b0034200003820440c0c02000c182c0400864600603c15440056801e0072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 424757787 1250 424756537 424756561
    0x90304060305010b0910180806010306140108031e07231b030d170705040b03040b06010f0804110136180b010203071502090603040b160e0117041406 65
    0x12035a1036a02032045998640c00c44985200713191465400410a40302403481c20300409035048074030110340241014580e101d01260901500380c02c115039035900c80303403210080c000036008140540380e0b0801851406529203c88640040c061100703c81204c404141c440078041ca14000d0700e80340100040210500c1c2c41c100c441515019000c0c00f07149021500b09070020681000203040f030540415840d09184680b401e01d1482440b040249407200300a810000810007510100203075000f071380b1507070714a219400d00d50f00140104004c40d03075041c200711490040201044a5560340d0500380e4007820100d04031026980d01c0c03503414a841b591031a00562242c580203a0000c05403107802110320003000700380140005101c0d03005542d1100c400a00503030040c40340d8802304904400180c00085101d00041c41c0c60014008140a500300311000c4c0d50f80c1048800300a09450000003d003c61041490000da58090301c2001078003011004408200c1400c82c07500144c20030a4100c1810202a6440e0817a5442d16001c01c00302c84e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 424759037 1250 424757787 424757789
    0x203040303050601091a0702060c210c0709052404110c0c030114130b0a0204050d080a12110412050f0a1b0e01030c090209040b1e0a0b0c03030601081905090304 70
    0x800500c241301e000881c02d41080c2c6c10200c090481110383d26010340e0f50200001030308401c0c50700780b1502414076600c0c1d403142c2400c0d4240707800744c04c003d9085d29400e115150600b0700c0810b038055415942448100250011080c1e40180c2d0307240c85038800b600c11414080440c00a0480440e240d01c3d03004005010003070010300007001d01501d00304500134008200045046640752809964004210300310036904400a21001807880e070102d91001d0050a040d55140010410304951005542c1c602c030025482c4000d552110040101703c1d0f4554051040900e01c1c0e281c040079118511808807011002d0400e00b04011051010351001100d0000312484c2c0402e90508061280c2e1190042c1c284815507000059550710b642c440d11f040702d03005814604120718292601029504c080c40159126076035984403071050744c81d0030100a4100a8200045080000700c0038403651131655044040842000e0048521392280082101e604c50421310344211a0b4942165001d074498064490b604924100000c2002c400b0000004d40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 424760287 1250 424759037 424759039
    0xb03130f0b10050a140603040605071e2d020a020f04020d020304060b041407230f0307020f1204050603010506070c0b0d0531020d03120c03020705120903030d050a09020402030403030506 81
    0x500034568500c01d961442d0761061725180c02c1201840058040f0f07034941e22281d4020000c0c18080d03e100380c0c454040b145403100c0074039580451603c0752070a0100502400c04400b25000b10280b408409103280c01954032000d01c40024454144504202c1da103464540560f041225804070564480c103007072515002500c0c5034011240905e141100314042070010340708080c0211090344030300c0c1e040b550700d900e00d49400400800e01c207850242000290015007000f8011440388282e81e0180030111000803645041080c0540881001c020612041c4821f03a41e50b403c0300c0c1151802c40b04c0544d00c0034070340b60001c82000c1a0740070000c065400310300b000c1c1b400181e40246100320349809002804003041c8040341e100744044101d1910740c44901200038018106000340e10342c040d01904006101c0e140300c00340e03041030718060002c010003c0d030042070810800c40e0403c40c0241e0403110071042814020a0000b2a50b0383c018980700f40b03103d80d2100042100c81d20190b0295280e590003510642d560720342400d014000d448291401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 424761537 1250 424760287 424760299
    0x120903011503021f0c0f0516050108270c0303040e0114090112030309050f1903140f12130f03030203040b06040608060a020a031506090e010e010b03130f0b1005 70
    0x19001c8030203060325002c2d40d50003041d10040a0584500c0c0d545020f140d18130005110900c1114000b14150380880d2504038402c1c802424941022000e4251219441e8055814800c4800c10b1014202052600c9100300300700c1501090a068030b10708591405000003410b0303416000c0040e0201d5250607900c0418140c428591704003100480207003c1c052001424821030700d40100007002c007000039100ea000214800c0c000c0044071031118001201c1401c0081d2180240c607244110490b1004140e001100e02d90000d0000c1086410070f0b00c8101c5c030726a1881920724245401c81c1c1036000907040d4400740d0400107401c0d040220685039112910307000d0025402602c00340c9990700c8034400600d81c0c0c601400762a041e40c15400c0074000580310209500069046040740006041d00d5804600754048170310401001410355641e00f080b00f610b0001400b02102040e00300502070f51005c001403000120100490350440d042c50403403001c0d02d055041c100400c02507000001c000b0300d018411b004122001080400c01c0e64011960 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 424762787 1250 424761537 424761551
    0x30705091c050a031d012003070c0906140103150311151201180b0a0e071101020f221202010e181f090b010819060302060c010c08070f0c1209050312090301 68
    0x5e05560380944811043c001029503c09815044445070360522603010a4112410401581e0310701c54070024641217200b071103a50b032034200003100820782240001e031002c1c08d040110f16941c0340381c0d00c5402080d000103400401c6626605501d52101e100c504140030403800c14a44580942e182005130007420f200e007603400340c50290414220b003200d01c900821644020400c00080b80760155290001e800140780d2400d100d41c20719440c41c448020300080000c06070070341000f542c0c0c00c45842d10f003004000000c00300c0c0a4001602c4180450111f8185000c0e140b60242000800050316000242c0c101c0b0140e00b14010500030038051112144110a51040907902a2050700045848400d2030045942d849034440c00125640089a03444020403604072080501c80404124641c490300070483c281c0c8203aa4450490b9550b0980040c003951002680350481400d29010380366140d075001c001d060601d43c2d580585000d61000d0303241d07030280c041c03a1410000d200190944055000300c290b04400c0c3c0d005110100c1c0a0350800c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 424764037 1250 424762787 424762817
    0x4031a0903220b040311090a0213060e15071a091f0905010f09030815060406120c0c0b0907180204240903020303340503030705091c050a03 61
    0x5580308400d61401541404240c0c4500401180480d40029805600100205160788071000600241d4003504442c1e1039848010203021a560000384609203051041c00038052118486150100700c0386945001e00b0f222401000042101c071120130046a2070200050207000c0018840140352a000080c5903440c855440010441c0c45412090791001d83e4040100c0c2400b40d21015440a40102d0080c800024203091709a03610007103582c40c3c00e0035004160b4070010000d015815110110704c445c025078203e03040c03e1401101404220f4141490a00d0a2315982421840c600c07940c481c040d143c1d00712005400030f06281c1c000c0e54482003180540b00801c2c60b42d084500e4010310500894044520704481115141041c807483c84420320b48101003402c01509080000c00359404001400c80701040180400c02100360301240c04240d4500c51411101000c07070400100800c1011047d80c0d800486801c000e640e03820b0000008565400e51040000691409842001880000039140c002e844c4a5110500c124003084 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 424765287 1250 424764037 424764083
    0x1502101a04051501122c030301170a1121011506030c090302090402150c01020d020310150e040e071a07030215130f06020c010c0c060b010c0206031503030f07080403 72
    0x40000f6010030000240b0551400003036002004040c801410b2034030000b524030000006540140c07100b42c0b41d9101000510030200102c4910b011089804020074a902295884003140c00f0030300c01c050303c900da0b405151115541b400c069040c416030074130700801881d403401c03d111a05000303901406001a180210100c16603000710860815690002d2a8030059900d80e400c10a03080070300000f190203a041401a0700350440240098a419010190094ac903454095007803606014035502048110301158100b4042c4e82c0c20214086051005840c0851400d400d12034241c64a21617a0294072025543e0605480d100c4580024014031032003a0300703840c2000c002c020701e0354400c0d4060b915003840a00711000200001e2461581181c40b070b02c15200036060140e00d00255003102c02d03141408000c034541160100800c26140300e86500c94400b42041803001c0c1a503004142680001040442d50038218884110a640c01f001950207440159040503a200114a0701c840281c10502c011074010b00315040a0304d000a030740d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 424766537 1250 424765287 424765321
    0x11130b030f0c13080d030f0f140c0a0527190b0a03050c040b0f180301020f1920060403111b010e0a0e010f033503040f0b010f0609120203071502101a0405 67
    0x6d090820a44e45401c5800c12440d40b0011291301444000c0198021034016031900c00b1040e440307100080300c0f446104042c0100740d039469000c3e4070b01d4007a601c014407074fc0c1d0701c00069405030101c80c6070005860780c850100c4003070783c4601e4010104064001c1002ca42c0a102c0304014500404101c40754500034260384140f509178001c003803a480d000c0070103120340100b00c3d14600540c001e0490b00d103002c00301042034080403110186030043c0c1c00003a80000e000c0109041d003041407010002101c10041c51041d41032060702c0601c10350b00c1200c90400107016801c0710599640300215001d800310f0f4840c40311035613440f40440b11206052004403002034500c610080960f24030340d03210900042e0441ca030450101c1601031078a40398401001200c1c128010b0040381c000c07174042d0524a020b0311405191921903800c05001420204203903116a40c2103034428101001070310003107250400c54a608407100000c28000605904182d40d01c04c01c140c100c1d1415590622101034407142103503010040d90200116107550746069884511 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 424767787 1250 424766537 424766561
    0xe2e140301020405100503130206031501030b0108071407030315062006070c030c02030a0506150f12030405040e1f020711090709031203090611130b030f0c13080d030f0f 74
    0x702000400f003038006d5006503070080e070148000b04c50400396800606150010769141303195a4414003038400658151280b1030030140242091b80640c07030044001400d5891407564601c0071440400c030700c0c08150194202e0403106049548565071607464a030010b00d00008015907a1004400001901e0580000708100e0b000319040e592301d0044080c26101036482c010b000340100e82500c035507038003400441c00a108042c0900c0c45d00015024007085d100c10400099960100c9a21419070088603082220b0000211002c40e58151030205042d4032070302c072441c10420000d9144403c002500301d4041c018986a0040003600c0c031504c41482140d281c141400b250540c1200c031880030a0b40480c0c28004207407208441005e50610f49000300d00e40810396240400d03110035040c1095454400700c1c02d1030b20b0b0050360b0a42d034003500070520018250b141010b0310b14007210703028092008c942d1000074000306501485030240c015040e1a8101c07000c03014034400040c0100140d811640d03480e407038402141030b045200c0c0222616804 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 424769037 1250 424767787 424767799
    0x80c040e01051c0503071104290904060212011202100905100c05120a0503090c030109020d03050d0603021206071e02100e01062607050402070b010e2e140301020405 72
    0x8240000e03c000001c103183c9041201c0f52000080000075402c00c000c0000a2181c02000035810150301030205403101c986400c03c0300b00080020202490307050441900700001201c4658240d21542081c000030300c130780d800d04042c5803900d80021882d00b40b20900c00401070b100382c641010008410b401166400c0c00c038010f20307521007040e01080715014801c1c0c49002da5540180c003a6240d8003c00c51180701e05900c00c911101c0070030404000c01041d42018050504600ca040c0c00a020088040c1d000820405124000400340000460b40c2c004100e815400781d00a540d000c4d04201f18075928000b5181e480c02c045030803800082c40c545005902c05250300020185035982e030000d0024810b1800d5100c003030203130099081810f40d40d4078000241d211036000f02d09082e03440450010442440d4020385410007089422441c041c500406c0b0400014103011101030454401c03002a200300d48840c2c151810a140e45242485002c3c402c5d28803000c4141e5110301401115490351404000c441960240350907030040f44100795101d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 424770287 1250 424769037 424769039
    0xa060501170405120a02010c0905030f07052701090b0906010c03020c0411120a020c0708150402210a0803101715100801060e0610180302040b012d080c040e01 69
    0xc00081c6003681c100348580700340d902c050302c21111008241c0201101c100144c0d120320710360f400a41c0044a42010784000d03800341a00c2c420b45208250390752150300c1981e0040031040c0f4146010080a1901b811000301c1816401e4107507502c1940c040600b400c19083e078420200301020400ba50f0040c240015090340c0342e000b030300242c5822001c0100030100c483d6084000740c01004078101e4447c07500d423141d110700d034442001604c420580d48041d1900740990000c032019070140c0240e402c1100d03810140c650083c0c0c11110070b42544101180408400000380802e0854411103281c0300c01c0100d1400a18402c01000e101c05802503a106444011208009410413240c1c00580000c0304e01040d2101007030f40607001c1d503e160307481c65a07000b9582c2110f003198040d001e0a0310082c1480364600d400303c000c2403044013a2400560070f242210706220741c0c0c81d003888000c1c802c41d40c2d80c1209070181d0059801519134a5241130040d03a142c10781d4041482c3c903030521100c0f800200302c07100003500c0d501e82000750f4099032042d400c4907e0701d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 424771537 1250 424770287 424770317
    0xf18020405060a03050a1406010f1a0f070b15100527031207150c050306031009020a0911030a050603010c0215040c15030b030d110c060717030f07080a060501 69
    0x1824081d00ca25080702180e400032010405c2001000007280c0701d071489000302a0003140341070411206801014000d000e0380310821210203560552540403070009a038a50707451107800b00c082c040c03264a000410142d900b800700704080c101c41c2d040280e116010364460701008a20340d000c0340c292140e035104100014104c04070500714a041c032071645140c02c1c003400b2103801e08000310307450f5215040454112145038110070b044440c0039090140d82c9413084a42411401c1d4101180021780300c000380075000220650b00d400280544d51640ca4100052a860004015481c1c04d4115010144e2086401080361800e02c80420880d003030520803641b80d51403580c00350502c201c10440900d9840d03005041900c1420700254041250102ca02414440d0405514001350f01c0c0c4080d0b09250901200d12881d1051000f40401c0000c0d004011685200881080b50f2107982c880961030041c02c1452402441584200c0c0482042000012030162600903011510f580c503080e60fa80f035100d4203540d0f640c012140000c01810b038014038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 424772787 1250 424771537 424771541
    0x110108010b071e0503042606061c06200a03050f0f0103020d0609080a0309021206091c02120c0a0221191a04051b060f0a050c03190906030f180204 64
    0xf01d603101046190780030402d899540c034641164028580714801c0316151040c03016040e2500040d01388550103803005d882c041340003d0598400350640050010303030504640c2000440da0002c0481455010346440292000140c44170603080f044140c800b00c1d00d0709005c039040ea04ea1100c0a445980e01602400d0268250360a0104942a00d081182c240ba110480d24000400e24005003140540550300090440d1450040010301e111041d4003406941048080c00615140403512015003a00105a01c0861450807800c0340b034010703500c40403010b00101041c07d41c007aa0700401c96440460080b00d01500307500410007514007030030307800c40c0c840000d902400b0340c856103652020581e00010b000703000382c80d91220002d14001c140c020480e0111520380105c4a108014028401c0340961000251041c0b8106003c0404809052241da100c05091050100d007500151404008560081c020503174110790400c6003000140c220a041d00840010078140a240010122148a005120040c4017403030442d4505a40a01c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 424774037 1250 424772787 424772813
    0x60207081c030e0f010f020d11090f040b0a050a030f1703090c09060f040e0105010302091305070e0405070f0b0c010c03020a050306010e01050c030403080408100c020717160b07110108010b07 83
    0x880b8080c407044e0100c10a0203115403581c211044501603070301c0780c540c600e0f10308564030880700b56001b050a100f5a43d10380c440a08442068400340c6000036003c42e0400000c41a040e240d01c015030241640301d0100411203103a0f54654100d2042100000405100b0003c1090303000442c1d40380d4043d806018100c8580c580000e01d683c1001c405000c60a80d500c4060105003950600e0580234030680d1540010021801c0805045520521090030841000c0c800c0d038803951034011504c500f000340300c1c104022505100d001d020b40c00c01483c240c8a103900b91542c5032503800160f004060842000c0d442c00c40149000b601030b00031181d2140455440519560b01c200040d610300b80c520400708d0403c00180302841005d00108000c0014601603204d25403942d160040c4c4a00e81014402c0c02e407610760078000c0d40b184040c0c000a035601071346e0070b0ba24814000020404424540300740c0801d8000d0201d600a030000f0840d01c1c600043c8003a43c0224805812717048404015a00100c0030320401c010303000e040000c0c0001c1040740c5a000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 424775287 1250 424774037 424774061
    0x3050a03020f0c0f07060203090f190806040c0306060b120a0203070306080f071406040807210f0317130b011203050702031c120504051c11011104060207081c03 70
    0x10308090b2000350359441500700c0c58030f5880340d030300c0420340d83d034081c00c100100c07402080d492004601e04940c05000c58030415190407210b000c1d40f000010308140c0000740c40100040c005100c101c1d000340c40c080c1003190204400d88020741c0c44600d00b480c0807803140d100d107040342c2c8a5014280c07004a80c0d01d0312782c00e01000707500080c02c210400d50b5545000c00c41c1e20051090600c29100c032030060a490b410260102840381412800d1445110200700801480901044030400c0307890041404200050700c0e000350380c9200300f0301001019680205001b10425401c60400d1580705070007680524555240c0740003507281c402564000c1d00b100036080040007200840c48070748400e81d220b403816505004440d130103e0700e40072030103d4421907454608402d03403c0c1607009510048048142800b44194141522955103e0544410008400b00154403058403140150015003070700101740000c000c2000907440ca00d0b642d4000d07016800050050310000100c00d071002466115998284e01c40a02042c94948141c008100000c021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 424776537 1250 424775287 424775291
    0x140d030e0a0e0108100603020d0308060303070b01090f0501092309070b03090105150315190204180605100c030e060a0c05031306020d0306082509022110080a03050a03 73
    0x29032558903140140350003040c000d209400310354142140c0d1814910b1510081011610302081000565140007058a000d901414240c0780b40c3c03100c1c80480d041d40b09014028103040106000040e44400d03a6210031000156240c082101e6601c0da0043e8094510304003811080030f030030a914492000c001e01c195a004010b0714111001c1d550f1f59004503070b058004035100c40c0265992010400018480c00c122101c500c000c4014108420400900356603007200030f0140d10200c1c96000001007682e015034100c41c0075051604040a0310300301030f043c84026000c980101070181002c01f2507800701d1809201c249041a03819200c0c40c0540d112681070203401e4100030090702c00c0002c0c0d040c04202190082c40100481c005900c0c4241d8410b06204020b464610341c0e0548004141c81c04400b04032600010034641c40620201c001c81d61062020001014603995a40040c002c2c0791001070040c040d0b1001c0c0b031011012917601240c101140d034494891400800e81031051500b2a0860701411001a1040c002005100d00c031f4200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 424777787 1250 424776537 424776557
    0x11109060712351303020619020904060308090102070515040504051302040c02160815010b0c07150306030b0f0609011a0403170a1d010504150c08070c031a01140d03 72
    0x140c980c0c4100c1d01e070700d4007444800d400542c1c5070044403407184d0210304c0035035007106800e6030758000f507070342c50010100c00f002d4401c1c5000900c1c440d8282c0468036140001041070110039141d06040d00c16a200d4000c1e54003502c10a0000201c41c2003c826149030281111f400506083c40c01c004d000c00703820010001503003001c5a4808400681d0341e480381c071070705003003541c001c1130300003a5804100c66601c05500812010707803003900a80c94002001c0812410344940000e0a80c0311000c214070541303000d02a07000002c2c02c0490001d03a540c0030b40d01d03900c03690449000e050111420b840b220310f1038035100b1f82070f036010b13400c1088000140190101404041080c01c145d00985140075039a481e00b18070001e400c1c10004098100040e001c0d9610362003942400e000c140074109911a442070000a001c9200310b20602c010641406116820280603656100e403594011394150380d9a8000e00d400070485015010440d86c1125403544480030750f0002c80c0507070580f040841500c40070107015040100304806100b0440401c041854 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 424779037 1250 424777787 424777817
    0x30b010207061e031e060f09111818092d0a06052203030506130b0d030e0102032203030311030903040902070c080d020114011e0b130f0b070302011109060712 69
    0x7041c41c412102104c00041c24608003501f40c0c107080b00507407040b006641000100c0e03001050318801c60701c840d807821036602d00480c13191000c50000400c020751501040304c08010019031000228030864044242640c405240a1002048505400b4207402d038449078400c25810b40090707070035800759400c4410315420310300343c000c2c0c130740031590541403490200c0000340c44500b80115410880c6044000200443c010701007580600046015a026846c2c0a42003044044641d20943d001b842212401c03c2041040101c0d00210300b80034011350b02601c000c400103864408984910045003003035030b0107542c003440038500e81031a01e001d9101035003064400b07071030b4103822030030004601d60100100a5603020b01c1c0c001155024200d6240d2120b080144d019809096800514004034a1160b00c80c0c2c056511121442d601d44011040381c0c804c6000f503401000c22145404004903080e80c8003006003420a1195009000003040c0c0d007401038030750189684442d0041800c0c8a00000240001c1050407856202c0c0340100c0c031102c0c210 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 424780287 1250 424779037 424779071
    0x203121501050f040b130f031a07030b13050609060d030912060b100e0901152c030f0618120304060c030e01110c070e01061704050f0307030906030b010207061e03 71
    0x151000025100003e031a507400788011044074000e00c02441f0011980b491070b01c031449000020b030118581140b80c400001c144078000da21840c0001009000000c0d0020304070b0768034005142c01e80c2c0540c80b4098600002d092840e0128024004962541e100c14843d40742c0040c00c40e402d0211007048071140c0d25412001c50310f03183d11500c0c14440140e5030340c07914204496400e012442d281a085048905030030903180c503c00750001d20354141219500c00d403500701c3c010303542c242c800300c002008440c0d4540114242c2e0307000a03800141441c0148400181241e10741e0200c0440ca40d83e85101075000c40c0b040f828000580880e803c0e60004410035140e04002c5524081d8500240c01c5601c0c0d22301c020400035010a0214036820100403007001341598016681c03403941000300103801c5005c12009584149200800101081414031905a90300122000c69454035410318000d0f2501c4450b0142e4070000f407600303009601a40c40056044116030712515000d003104640c0c000090240031110600041c1a19040d943e00720540c55 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 424781537 1250 424780287 424780289
    0x1c020312041218142808010203090607020307120f1701080f0c04050105060904020714010609090b1e01091109092706010b22030f051c0203121501050f04 67
    0x820019080c00c00c0c0c81c2e805050207035460669400300c82c201e6028000c5515102c00094812400c5507810803c2182a24400e1101140090300442c8032146800050104054026501600c0c00c0310a0b640a941c41c040100d99901520310060800e422610074004218040d103880a2000c105140c105132a03551000d41030070680702a48288059170065210111140e000d018141350f0b882c045a0901c40c952501c1c0009a407805200c2c4a00e109641c00102c010800140701ca940707030000c010900a000303103590b4150302801030107035060540300060314000040031040c1441c00d80c00c4442ca402e40c0d000940c0d00340340d0242c000302065600f08104440810620002c3d50fa0305211621070348920064500903144194000c010f14500303e01040340f0382c45000180000c44100e41662403c06198807040b8907412a4041410f100d032155101410556041c0039000a006010601952100003401d00c120410708101d0102e81d0b91090181802d062410900880c010009000841d861081c05240c100c0c00d00c490400d01e140d1903806 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 424782787 1250 424781537 424781543
    0x705010f1b0c0509070306141c150506040531030201060f120c0806010e01060e0f040207030e030f061506070203010e030309070602100510060c030c1401060602120c1c02031204 77
    0x180b810060384c03800e0a65194010050701e0240322152506e0050743e01612a0328607184640c0744034519464140d00d82040c007261940150143c0c440105a442c01070003854155400c034061401c240000d00e0280543e4210fa2900c90341e001d0a400052080d1945030308a491084201c04554880c0340000d0038a0010b100c0001501031040c0c00b49510a0070310301410319120302e81c802c4103d81c002c0801080742c0b020307400195045510a003042242e8104250010300980c800b8405103a11a00c0070450005155214031800d5401205030708541a42d13141d128415565402201c0c20b01115030b20450007406400d1000241400e5440a0700205000c072158040b98195002100c41140542c0588010000994100500020b01307002d017404200504001c45100c4004466002c0c0405000c0300c030014000b018410b0030904080381d00a02e4900c900303800214005e01800304c0340f1640b00148203900320014032040100444068668200081441228040342c101e000061107460005601060206101d41822110214441c80c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 424784037 1250 424782787 424782803
    0x10080a090605012601090f030f05040305010c080114040506061b0a050f060f100605040308031806190e030405060909130614100e1b1c0e0a230705010f1b 67
    0x14100d8a414002591400c0e43d00300da0514986c80042040e84c0144504030380c03d442c100c0c908a140e443c0543d024419940014000d40c64418a0054194042c1d07549041e240300d00c2c0440300240110701007100351002038070402c2c0d00c08401c020010140ca40c1200340070504d0306450a860341e4403050784035141408100030301510140c000c41d0400c04d2420091181950145094900750784c001d080c444d000b80640500e010050418070004041079894032042c2c1022120700300e000494107a85040307116441507850f04000001c1c031030b08000040744110000b2040e0340548901400c2c0c00d0070030619204002041d50007400740042c1e000c1b01d4100c80301052050040c0804021000b180712220704080c07007042160713101c0e90f10404500900009119100721a08500021007922401294841510440040455245c0b14400300e90b00c0c0b41c00315003107030210041180d25800e4014003109450342c034249a00c0d0b0454403020800341442e0455a01440250300034003072100c1d840c1311481d02c0244c1c011710780000c00400c1c07000641900c0d83d071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 424785287 1250 424784037 424784069
    0x30a0b120c1804080702090709050409260a051804020909070905090f010509070806031c121427030f0c010f0609020f090d0503130e090d090510080a09060501 69
    0x1041444001039003008210401d030711440c054540000da1701600368020301c030302002e9011452035440348620b41c000c1d01c401402005411100d240c4401014184452006a0740301004880150030300b0000f6138203440b000340c684a01e0320840c06a41d4030180220711196034816400c2c04aa99240c5a0003006446442c0320b440ba8a8024144001c000c4516401080341d4017a8010000502040e110071302041d40101c4a07007001a840c2c1c59410000b8101034014a01c2c040801644000c1e281055100011030741c05440c8030800c20140102826070031160b04d048076030b00c501400354402d40300c0c90b03611010005a0224400300380c9041101a40c966040c55010b01034000e0f00360746035050344101d0b85552052200410704041c003180781455a00641003103029000c54a8840c0100300113074001d00c00d05204031204080d201c91910652074840150411001c82511061b18911500541640b03c80c0180c552105950703005040240300c0c01071040c2200d000350003d22501800d40c50302d21f03680c002889801900c0c06004903231101a400d07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 424786537 1250 424785287 424785289
    0x40b0301091416080a0e1b0108090705100c031202040b090f0307030309050f01031d010501080d14030f070c050d081b040e0112020102160801060f0b1c02030a0b120c 72
    0x565550107502c1210000e49050003010626003148001c03c0520342814491581c0d68900d98008051050070305c45c1c1ca02038003003400020f03c1d01443c0302c0c0c2003081c01d8840c0301a903210050019607848040c0586500a0340718404034000c2d42c000c46003000f617540f0901c1c00002d03145400921a00b81d0308550311094205401085c41d241c1464001103110350700d081070300108607051858900522007c26489424020001c110b500c501603482a000710000c5883c014001c1d81d07103900014000c1c001c2000b445000b12a001c2d003210340c40110300c00c4820402601610501d5030860b12100c002d00c80c0260090b0101c01448807154101c40010010300060b08440410b80781c860443c0b81c181511a1002c150a0305150b8400040005100c0e0003890008141910012400072401b18100d01c010303440c248800f034102c01400d0101c0c000040391541504407600307960144050491041d61030700c05199900039a480c1107000300d030b008000070304d9003a80c0d4059036009203d5038011a00c0c01121001c41e42800701903108028940220281a803d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 424787787 1250 424786537 424786541
    0x804120b0a0c0201020903070605090303070605150906060a0f03270f0302060603070f0b0d0207240605060306010e01080907120515180a03081905090f060c090d2402040b030109 77
    0x142c002d03640002d41c170b0002c540001071740710b00c154054141400710101d0400101c0c1c0b400c2080d00d50260b0b02010800607400c0241c41030803c0d40744000c441d032045000d500050700e41e080609c241c079241322058843c6440c1c86d8070a0003e601510b409080b103042d81000d080d41c1e610045510b40c81d00065401160300c02e0102d5500c0c10000e0a0440040150b4000d900c440e000b0801c0709d90140416084031000020180c844d0a13000409011f40b1039024050310b170070080e801d03403aa80c400d036905020075803094800400c401c6580350180816400225401c41c04a840d0000075105135000340c1015034001c480c0ea00345c07000ba40e2103194804002c03001142c1504c40c1d6100100c0e03c031080920b00c40d41c0d9080654007150701d0807001e000054a9072000318400007810170030f10f040814031085c00300d48500441d84400b00c0c00c0c0301503c1d010841c160303564088001d5136110b21810000c0b41c061a261021508101c80c05042035200b0003143d04c8400c520f42d03816083c001705080301d6280340c1d840d44162010700050110362900c6666135240142c0481 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 424789037 1250 424787787 424787801
    0x40503130b0a080a06083a021b0d0c09090201020c060a0302070209100302150d0b0a06120c0c050d030e0c060d06030203101a010c020303130801150e040c120804120b0a 73
    0x1c0c180c0e103001c5c0e090000250018122158440c0b240000180303140080032a020b000f00030f4202c1440b49645201460000d402052a00662070038801d0b900c0029041010040b55100c0e14201510740384030300106104000c1280c102800f0140103004a80e0444500000b00e401c03a4421441000060750100b4440708503d420070079540c0004800b1003201615041d83c0001b60b001c541d08816500180d00028150790a002540020311070a00c01401e40c001c030b03035440344003502011002c4404541d075482c1c04414401d4501412980051940001c0107000c02060704506400801d8850f8901100d0702c41d8158800c4156145c100030b101a1800c440c0200702c062440c4141407600003031034810088c250500e46a00039044400c801402204000d103051154921240042415031007000081c0c01100001e000105a001054000e00c4d2414440f030b020850701d80d80c44503228200c3c0815640100954421042003021081074a00046090b000e07000440c6040d984000c4450b010341300103c202d03800340300035013041003820303462244030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 424790287 1250 424789037 424789051
    0x3010915050603120702150307180b0301092d020f0d020f07031719110405040203090d080a02040b090607030302120117100903170702030d0c05030405160b040e040503130b0a08 77
    0x1c0e06004041c6c0c0068400b202107015134001980100006036440c0c07080c8001c1c440c501031b0003489400c1c191950301c051060b034424001c01528605002010500106c0c2e030940d85920b044a01d02c008a0802111b140030181d03201c00909480030400b442061074101d17092004090050030901096641c200e00c1c5400740003030400c0814901c5e8004403200300200c0315170308a1500e003050030054001031040400c600080440c001d60b00016000307807010042140180d4006089402c4610b16100da0000d6075611140c07400f41e00c41c6014000c00703440309102c10b10040c00c04401401c05103209013005030130403ca280304140c000209a1250221034941c0c400110091400c0c0840b000500c0345a8081c400300e05540c5000c1c1040e1440040401e4050010001603245803080c02901c3d0303280e20700c1c030707081c8000a81e09000500c15042600c065842d809202005c22070841601c103410100c0d0000c070030103401c0c07500d41120140a001c1c010310685207404200205030070321000d24800000b03080d5070001c1c3c3e80c0715660580f004084c42c000030084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 424791537 1250 424790287 424790323
    0x626030307080a0e0a060e0a030e0604060906050f1b03370e040e010509010b0102070e0108070611030c0a0b011805090c040b030118050c1f09120203010915050603 71
    0x101000a500540c0b45910048680011034a0304c410a40c1510300400311102601c0d981c070307144d80394400b0880890040711484c02595405030403031035074041003402c0c8540c0c45040003144440b0741c2048200d0050000e003a0040000b841070f81810180309444041c4d9070410740c0e41c816a000001c294484507c2107031816003e40c41064000d8549444107104c107902402001c030713041401600e400c92042541c0340d401a82005440c0070090103141405c682d440d002c0d090f0010500c0c054004c000c004500d20102903c603e04950300b00c001820b0036860103c05079994159659865401d0004001410700c2c0034040119a54540c0305103028a0039614254142c0d91070182c4460100b115400d0406118503034070006400f0601c0082140d000441010080000780101030400030444031030301101204092140c0400c8c400c5d40301a00b50303191612001d00c3c00030710300354610250041020400180060192010078046013182610140001580000a80b02d001803459055800c648190712003041000c207003420f00c202d941c101140070075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 424792787 1250 424791537 424791541
    0x12020f01050415091104091506090e0a03033206010906020c100503280c0e010813080306011202180103241208070c0305240408070303150906260303 65
    0x25050121032040c20314002c1c681302c0c00c4d410103012403152000600b030303c000c10420040074035240076030065901c0d00100c001c1c5450048009140b007494060701c0302024000018250f068001e40c2c05400a0085480c000095021191083c1040248407100c0c030140582003a100242c1c0341904c001030521030f1640184c0115009551124010740710001c0031200c41100e41085a100e9903801d2460b03030b0341b0305000500709042c4004114000d0035001580a0850364802d580c8040c80c0c8200740d0010745210314141c0309442d1000352039003c1d00102d40524041c2d50400d405144c811034420410b010030b020382e0071211b0302c000c0790300030050740c44015078140c42002581032550041a042c1900c1e1180303208207c01e14130070750215881d00030ba10340030043d0f01c10844807915446007800404940320300300242d48541c501c4801b08050400c1032040d03018a04880031138400d5a00c0303154103103458030720340e000c40c0949080081880004040c0d800403134001d40b01d00074440a0900c2e640c502d104080d50940d06e40840c030b200401d42144e5041001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 424794037 1250 424792787 424792793
    0xb0901060b070201022e090b0f01060512130305160b2e06110102040305070807030b0a020711040e0708060c0702040609060b091e0405180d0305010503061f080a12020f010504 76
    0x701c2100007000c682600c02d0a603482c480c4211408807103600440c4051905d0000001c0281d88c61400b40180d42c2c5000e0000340707a8031b9080541d501d2090b004848032107034900000038040802040c504187c18401d1816174109103110f00004c0c100d1000c42c1c030444003ea195810030100780d81112050f44100b9038504240c07a03026030100480f401414038060307030b001c0103140031892201200c250101c600071544503040b070710702e5980d4054580c2c840c040e600040340d104e2540d5001c201c08807414001d64540c9600039400c07465461400c4208402040912136024250043c0500051254801c0c0b044501c901900312680b07a4600c194410401211440d8203d030300d0940ca0a8010f114503e03800c019074040220546030300c1e04a00f500141c4030030500011507aa94041d040000300a2031305100c48603021501c0000c800c1fa0320041d841071055060313070024003c2c00e4056110000080c0329900c00141103515440c2c4944140525440303210315801c0001207881500d48403006404946e4440c0c0c1040f105050790101d070001c10040c18141d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 424795287 1250 424794037 424794043
    0x12051219030e0a03121d1024060215070e1801141903030c0f080414040f09030c15060803040e1005010906080705031009050a1e09021c110d0b0901060b07020102 70
    0x176a500340003950300c8010040004111280040d06150386048440070260150401e001e8590344401100c1c43c050000c00074101d054540a020640d42c07160043c1058040c001a07600e8403540c0208000100450b0241080c0152100d0300c0b00311079040c00384005d005542c1004c8412060501008070180182002c0d182094a80782c845220000c1d2603052070230000702d88181c10f18150807109040301501407031001900051404c2c1c01c03484000d41080a440511a40c0d0240a09200f220325024002d0042500040300d4000614000e1080c01d0303444010b400010030302d4448054620f950010b03002581075120307450a0200c801292070302070000741800d00e400c58201e810480003c0062a001e812101400703c040041090200e43d10b0340d00000d40030900e0b0400140c5054444d0310060981c08039070f11050f40d00d5000c0000c0661050240d0300c807894010f0b04a01420000f0040d0000104d43c0a0701070380c90505200240c40c0e02d9884005040106010301100c184a081c0750910a00b103030103551046403130050801254005076008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 424796537 1250 424795287 424795307
    0xc1203091101050414210d090305071a03060d06060b0408010209040b0919020c0127030305070f02071a0409020a050c060c040311040506040e070602010f140103050712051219030e0a03 80
    0x203480c841c0c1d1038114546000202c00740d890359206d1034010041d00541d115400045001142c0c010360445150941e906000501c0c030710440d8801496400c00c1000554900301500700c41d01117031080d0000607805a0314400a440c40d04160086081c9035000500406e0314035041c003030140c881b00c0458112445d401c100c241400300c0883c03440e1448159401180f1207611403820340c8000c1c10300b02806c080024220a061100148107100320742240401d103007001041e05103206141c1c103041c150260f001400700c1420100c00982495102480540a0500300004900e59800d0f00240c40299100d0711703001c0c0c9078504400b890b414108020b00c6400040814407023000486c004d65441e5850020a440c0007440c2d03140c603030228018254402100c036681c03048440014440d40c0c154005104200d11500030011000d541c00380c210491428032015005a1011000b0311901c8080121445454800c00807115401d004040c40e881d00e4001801070030311f180785020114019078040c01681c0f6500c40c08000740c00c11403640d582c041c00390400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 424797787 1250 424796537 424796539
    0x90c390209250503090f2116082206030b0f06090d02031507020709200a1709070e0903070209150301140a0606030608070305030301150c1203091101050414 68
    0x6401c04252215140401d2007401c10030000c0984015800001c090882d40c020340d001c0610344280c1040c10f88641001c1502c4040030302d1034440c0340000d901841c2c0d000c5542c210880c01d98040044480010000c0c00d540b0003800b40c1610590b0f1448000030a81c030303020350048240d11080038103042002d80003c9948400000c11030260071140070761100700000100300900c1d01101d00035054400c22983e80c2e42800c0f00341070242300307180315400c482205844849074400e0b9010246410360340310304890080342516502c0e001e00100300d45490040480c21050031001174259080c0c1d03002801e07070800c02081c46030315000c04020f68440380b4a40110702d0040d031940401c0400300c1c01810301c4845603919030402000e66080d003080e0071a0389110501c4000d400d1907880301f001005107110342c2011030b10342400007617003010200301a0100c0740c01401560a40e868101d8400d018013001120804000c09000241c000a442c03444490414085940008048030315140503343c0112044500b818840d090200b04059007100c5c0c1031070703e01c1c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 424799037 1250 424797787 424797799
    0xe09090d1b0209070206060a0906180209012c0102060c040e390301300303050405010603080403060903020d0e151614030c15070504051207090c3902 65
    0x6842861141c0c040c0c400c0d500940c07203049903081c451101c0e400100345006880480740c50130520394401c42c107001c685907071288030b021000c0c05092610f001c0c000c2e80a889080e5040c1003071070032807841000d514441c101c02076120007840140c0100f24150f503030411805501c03182c110f032031618107400d040b20100c10703180040c642208144525a030110303052a0944a10b125007003403840e10f00b10001c8507030a00f0541c1003401010590b0003a04412188000c0020f1464003942007501481080111a01e0071000340c10018420f98a943d22000c0c00130000d0441c0000f400214000d000c001003c1800c4e01c0c0c003d003015140943d54080004100e100c86179035641e403c2c00244080000c8403903554086100050b015032840c0a00585811031021078222561804070091540e03034024020f98041d0075030302c801848040d20558544001a1052109006a0500820030520045420304a0340c5240e9941200019a05032418000c005070940c0090401c44140d02c2c008800f50145000d40c00c3c8403901040203850003c45050003900c520 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 424800287 1250 424799037 424799057
    0x1005130608012910201f05040302160f1518030302030909070305190f1e1a030604050615060d090305030f01062c0609120604030e09090d 60
    0x490660300010007001110001d111521110301d4100d0940e15481c0b00a0900d01d001040441a14010820b2a450101e686849418032601103044000d43d0071100c540c002407281410b040802071400c051800115218074011507246020701d002418001c0000c0b05540d40709120780c0912208140664050546008900f02c06451050b04400c8450a006994054406c0507280000c405d1503070100040440315403c0d0b407010001d07140c0d41000c600301c8000311241610041050340080405c03501d900101d50300300b1034081c0403504207441f440856195136400c10200d081d0382d030b807404084a115000d40f01021240210003800e000e18150711030f036490340d03c01000d4a003440084611030006a0b03512007a10741507014003504100703800c150b00d4042d01d1b0f03920903134107580b030084080000a107141c4103641402121400c60890303142c2010014691040c03000713a46950354040c3c41884002c40e0b0f40c40e000d41c0080f510303480800418003410716040c050854014400b0281c043c61081c030401c41120400600c8009260903480c18250340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 424801537 1250 424800287 424800319
    0x90303040306050f060306010b310e0a0518030406050909060d0b0106050a0e040506031005040618050703060b03010b060423060f1902010b0f060d02090303030c040612051005 76
    0x152240d60001081e00385841c081c000640f4500d0f80d40740c82040c00750112050390740c9505500100d80560b840500440e0010b0719170142c4d143d06401594081c6048031040d003480d64940410a51001e0202c45900e41c0650720010468541c84003006c4c2220308164a001e10702d42420800028214884e0280d06c0740a1142c0d840800c6098940c00f0503d40c40c99000280f46406584903103000349241e0003100c1087c00988041f00c0c0c08511324052140314040c01d0014010b01e204081076402c44080d040040c000c1e81d05590b5035524100101e03109800b604014400e1011705009421445d010040b0380408440600a80c0750011065840d00c8441c22581695031104031007031100610a60b4820380e0001a09180c0c2201002c20400c40c04481400500300c0c0ca6a91010a10f1a030640c0701c04a00321440040c0090707003e140b5040f18881410160f0092605040e034907009403401400e84d000c245150b20507596a0319503000081d00b00440c80d44080880c80c0d00c6019070381070245052181902c00c20388d1240c00703030030b1080041e00995000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 424802787 1250 424801537 424801543
    0x190504090510051f05030d2c041d010609060302180a02190f02061308030127090f021503061e06160506150d05060a020a050d0e07051e03070603020903 66
    0x15000c0a5001402180390260041100322004d46444940b020000e0b004207491801142a03010701c0c00d155952038004210048000d446103280c0804144c006001c0c003501c009441c0d1380aa00140c03242c10708001c10b9140c0a01c40142144c40342c2d0300030031800740341010900060b1b032072441444d00141d200070400c0d42507e42d10390910003481006610200142281240b0b03c2c80c07a0810201042507a2580941c1c501d03a40f07205004034000c000b46c100a040c035070200300600861010224030300d1804100341076a4a0b0080c401060f104440c2c4e000419102e01ca10101501c1c2185010000c214603010305524450a5041042c04103e407805410103c00503207400003c520703907a4540b40e080e991542c801010f5600c50395203505006848e00701c2540c40303540e40034601d4140c03c02d40c00d04171240c00c0407941c000014201e80da9040304000c025001107214008001e41084a202d4040c001c1c004c2024240c0e01401800481e480e040401c043d990b40b09038803204480b2442c0c03c03034033680c6c1c001c039000d01201c0880c2405031399001d40c1000641 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 424804037 1250 424802787 424802803
    0x8091503010e011505190f0c0c0801091106160209071407060f0507021b1e1201020a030515090a050403141206040e0f0a1217150f1905040905 62
    0x60000400001840701c5400380050480301445100303070643c0d0480408491911a020b0703e017030385040403c03014012501c10032051802140a203446140f0342244d580d2050200a5030303100122aa4586c4180c000303200c44000e110351070310001c0f83c06038034040c0d0462103200150403100c0064801e03140c80c0005901d85010303191106015603488046a03991001c0e02c2c191005003082c50350309400c5440d00d0f0020381e01d07a000180001607400c09980c0085506483c800f04500546004100d40c00c4c180c403a640a62603465130301100d1720039540c100002d43c035078020a82c010200d41004000400d2a82001d003008000d4840c0740d071281d004400300101180c56511410155003503081c000c403c04200343c0001d41d0080d00788855581c02c2c0038038030890b01400700c1c58040d2031861b40c49401d43d0b070060194000400410028080540c0e031000c45440d4202048c84182c2d6020311401c0600807202100d2201e1807000d041c2d0146812142d506041604807960300d81070340b90014400b21440d19004141c0681e5441c2400028031804000001d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 424805287 1250 424804037 424804069
    0xf1c03060f08030c07050306010506120a020c12210103020d0602090312040803040f0b0711131812080a0c09120f051b010909020301031106181203041e0b070809 70
    0x46440e500c4110b5641e03944100d40446250040d680086410f01d800b207000d03412608010451414509070612441e400e00c0050203010b181c031390800001016100c18001b41c0c44085146000c0c50300c1d4400081c401854291280c2281c031000e2215005000580d20a40c80e60b052540000b4018bc44016207000300c1d10340301c3c0c01038000303a0010700410f0018035074200000070025070765807000707190b407940e42c07405954024003664100501c060078003814038105041c5011a2824003546c1040401c964203040c1d05501c03070385001041955140d1081cac025500d0150005822900181c04600400c0f50001d1840001d1a007109401200c80031303020b180d103040511128001e210b000580120968080400804102244444000c0e01c0ca001ca8182e10001a000343e0b140300381e904070f0381c0100481c43e101e8411400c2000640c02003080391440c030f920482d621556114070180c446180078480c020f45d503e45c02c003811640c082142542510490003e401c0a0241c01c105c03000740d581903988403050940302c0c0c40a600103030321200240265 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 424806537 1250 424805287 424805309
    0x206130609150c02070603050415020703230d0506030f07140d06020408030306090606041a0706020d09050f0c060a090b0a110f0601030317010e060f13020f07020a080f1c0306 76
    0x10300300482c080d40c000c0c820b80c0d0f01038085500c026500c19040e400d071081103c000e40010100c0c0072400f181e00c3c041d001030843c0c40c442c2c0780154404c151111030318092640c41c07016000800c004501608010190702c2100d821040440042c20400c4240e21001e42d00d121a009021800303060144402c1d580e1030b501c4041c45240d034002c200f55216a00c1d03002560303503508221840c500c01c0a03505c000c6890b604004c2e017180c05507201400c9240e01701641c000d101c540c1c2d500c4150700720f480030307800c02070803081010500c00c000348a841000505454000d0a603610710307000307c0b0b40f0450b1003003800b006802000c41c4c0140e00c0d44226105112441d4a030480c9001c26034485e60150f040c003070140650b80804023619804900c040c1620312940320400000c1400c5051041e9886c24040d060041501170040b0300a450446000b034909280207000f101030305a6603c06005030382107a402c040c02c810000c0703854011441e1094a0b580500038010080000c0d4940c0c0140d0765417200b000c41c0034900b01c4075021125001520982015001d44495101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 424807787 1250 424806537 424806563
    0x1439010e0a061a0607080a0e0a03120f08090714060c06130b0c040b030703090c05130c0e03060603070501110a05010c11060708060a15020a0f0b010f1202010206130609 73
    0xa01500d580800400315501440d20480c55901c0f0402c6050f00440030000d0502ca040100b01d82e40c8400f258095254001804407500d0003a040740d0351558040059403041c9440c41803842e12900181c03070222407a907a102401141f40c20030a4021000a101c421114804401894031402c800030441c113115181850400380944400c000300080741d20b04c0300c40c405d480f134044c0c50b0340d45d0b07260048481c0c607016600420303100030003c0000c07400c0c2502c250010450107000e81d04598030340350303540001480c00143c4016841c0941d00d60f04510806c44e00010600d043c0d034000d5014090364645180002d40342c0030b89000d0380c1e061051000c85c0e140c010804010b14550513078000001c02c844540c046003d40034683c540818031a82c455070000500c0f02d8481d003000c501400c0050304144c41d060900e031100030b030442c410001000314440c1c030100318082810301503045071360b074002e680f5030304ca0b54100003c03a100340b1250340113110000c01d4850490b0060b42d0003c2c1c8540e00060b51b64a408400f02c0310310b4008060511b04202038410484150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 424809037 1250 424807787 424807811
    0x50702130203040c180902011d03030c2d070b0702150f0c060a0f09021f0512010e0a11120c0d1d0606011206050102031207090b04080d143901 62
    0x14007581905d04c5d445000007080c0501c4d03028010340e06440402800151354400030b441e00c2d02e680300520744100380203003034a04003c1e80354000740c50500040140f0b010100400c424500d09517038544400c440d00700f1140a000064282000d404161040b00c8000b8003415110031042013091521040c0e40005c2c0c1407403040c950312070a190303041e503541f841600e000d004580ba080d100e81000c1031901c2280306159000e0003d80d03e45d04581d911040059800f4401410711200700320f1100e0702c20b012540f89028042c00a0325050a080010844d8100c60040000c0c001f440010055030020501d4901c0c02c990204110b62100c0c0d403030303a1042c080c5000d000c24043c111024940a20110011000410307210700c1184282e980c91440f8441100010560f6070a1160a016800030032a0303511036040c0307100b80c5511440a050181ea02c9958034403243c2e850f0f210340d01c00541360b00410034245003558002544120151000c5406081441c010100e905076011004034290101c0225007004004001d00308640c0c041e203a5200801c50405070030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 424810287 1250 424809037 424809053
    0x7020c0622050603060d06050403020f01090c0806090f071206110c1509060709050405130f03051e12060d020109080118020a1d0f10080613150c050a05070213020304 72
    0x1e05108282038462020880741000c0d8240d0307100340c034020403400c9803000c90b41301c02c802400060800d50841c02000981c55001409004900010b48a02c18580a440c50840a241042d0018024011542110501411564000807681c082d94600303455400701c298180740c4180140070f00a071001000d07102160f96140c008010510400c04403900f9841340d0035036600c60000303441d00811038026010400030881403109040903804603030b018561035100d100d60621a1a032003141000804c5c114001440050b1051400c00c1c036101c020b610310b01c0d0008040c201003c030300540e0744141e00107107102e014000d83e4080340700790780c45210b1601c01050018001c200f800d03510f03d00d10280d50981041030340107003800341c0c1c0042d5008c2c52040398075207104000d403005140d840c0d010a01d0002d0704090712030410b0340e912000c04140b4803024000b5030702940d10030000303080c070b00001e103400049003102e1440240e07a145845545000950410201d80d0340500c240342055a03405a84000f03860450040c812241c10761000c4100003c0020003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 424811537 1250 424810287 424810327
    0x30801080c04060510052101030b010816030b0708070314150111034b0304230706030c02032502010305090a1502030c0c010e0705040c0e010c0b07020c06 67
    0x30009039000a4000c105000c15121070b84035058214510031034001080d48a203019040b20f541d00d070134909a0390703421805811121000c3e002030703803c4a00d510041010440c100000d1b00b1400c01090b4803489249107440311607071114001c2a40d0188003400b0b00141e600782c401c2d403100c0f082d0103600c00900518201030032071510203500c5564403404520f8444022a980000005a500d84090024200c4808998002c1e01030401150741d9240300c4804c000c003200000e0030041d01440200c200201c3d00e070791030340b0300f17820600c01c00c0314410350544041c03e21f100a0690031501080c40740560f03006c0e040202c3c0007815040c0c103c4c603610a9207244da1004408509000415450740c00c004a424003d98060181c1d44981d0078003505c0c1c3c0c1c050340000b09460000c80d40d01d070b8034001d80d40103141c1c02106482600d04114901710410f09444040304100c00c20b8020711001d21641c6824482c040070009603190501d8054112800079150800500c030140084c05800009172a15108010a6002a01c0940704603240d1056201c0d00429440d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 424812787 1250 424811537 424811549
    0x402060c0a0303200c061305120a0c020915060d1116030801050a06031104030f050307120806030d08060d0b06190807090c05070f0b0405010603170c0606030f1515040504030801 77
    0xd5000b40c445614204d030185d41c51101c280c8080c0031140c03251040001c04e0b903800c2d44222a40c0c01074100b50b029039401140507006005040d259510181903a20400000b6a4000c0107414840310006010300d00d920f86606507402c2d00309000e40003030050100c01440b40e0700c0c00b58500803d414a40720102804041c0d102014a040b0f40382a200c1088a589540064040d10059440030740711000510040020407503550044480358018026240750410f1030700d0701101d0441080815022410700030a20003107041c100b0076070914009600e0800b9150400200040364007110080140c60010318202054280d602c0000e02076416030702c03e47d603034111070791000c14903283d44641c0300d1a50007921309520305041a001d0002c030343c1c00661000c0c980c00c40c1c11540c2c0e217206c503110028005503100d40d620000800003c0002c8850f564078a4092086900c4501c003503809460040000c2c5190b02079084070400d03184450000801ca40141091446c0364499500c03c000114440711445460f0390040c20107040c04181070b008a0108c1c1aa02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 424814037 1250 424812787 424812821
    0x70b0c0a11100e0c040e0619020c061003050c01030902010801062604030e03060a0506130c02030c10020d060f05130902120a03080f1510080c0c07030c14011103070602030402060c0a0303 81
    0x1d83c48100002c503084d510301c546d01500302c4400610024103a804001032041d640038010b05143c00d140200b4640300003110382400200c80c031201402449003c0056046250f02442c00340310b0029681c2c0000d0035030b24107204010030720180718210440c840c401040d6028040c5d0892800140d80340030700b0000c10840349110040d01038000c0d94081420080035020380c41c0305042c06094480a40301c488007050003440c1d40300340d00c01107010a00032581425400e1142d884007007009000540c0f540c50104000003103034480d5102075508803e8079004c100689441110501e00f1070b1950b800210904640041400700f15580404040c600402003960304054100c070407a8007503000018140300c1540c6190b001c0c54080200804540d0240c010950070b0b0245216010311580b1040d0007a00c0c41c113115407420301d04d151012a40045803442c41c0c2c05c10901c0385440360410840a00c00c24601000c10b6565505115200d106010016040940000016096450300d00442e40421450021145218074500b001401008417101d14100ca01d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 424815287 1250 424814037 424814053
    0x60905010207170403031704020109030f03080610020708071502120313050705010504180f110c0703110402070c031401111b01050c090a062a0b0a0e0102070b0c0a11100e 74
    0x4000380342542c0039170358180c4a4071040031f0243d00c9800c1e2104000e100301d040116854002c0000786044004500461290301e48150f21f080000030080c03d0032034101c030501190700c150f0082152500010b541400c0340c10307074a03003100e01101042c1e040b410014082d440c64012440001400320516148488a100e203020320107031a08583c0720b20044415110f00d01c10503640507200101c40443d44016440188000c000030b01c000391400b210143e6156035002403240d0442ca2304810307005c006010095803580c00a4100b140c00710b18166155440c6c1c040c2c07010600002d483c00e80702000b404c1086500b540445604c0700b140c0d02054075407031840c918940c02c40e11807204140e25400e00c0040b41100c6142005ea403840c6400078880381d110b9083c058102e0381c910513018850302c1c0410724080401944020209a00703c28041c1d40c0e1603495141c10065681038449158404100340c0c410000306010079641980b594121904440c0c0079904c0000e440c0813540c0749100c0d600003100d40948111071922183d01d61203c103440344000180c0b2640 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 424816537 1250 424815287 424815323
    0x40503220f0503060c0901110f100b040b090105090103080d020f0d0b1f0509060a05040e09060103020108100303200322080d03020304020a0e0c1c0c111b010503060d060905010207 78
    0x340c1c13040d5103181c030f034200c1442940b040398051181d0030440900c0e841220340b0030540e82c1905141a0b40710240201d06c981e103000c620380c5400e05c0e01a0310070510782a100c074142545441c0102d0640b1205100190500d41c01203400034419600340c04071580c141240c0d01540c1c079804540360100c01460315866007442007441e141c880003048190385602e415800309442c0e80b82060020014003d82c0da01c20641d82041240030040480c00f10140070b1350390b02508040e002404150f0440c400584120000780c1407a070108a10801000081ea1201e0611112000c0410194070782141051042c42c40c09a005d40c2c510305070003240100e8140030743c9a280005c90f1240c20032900920540e50042d8100d11041c1c50294008032040c80074002c0c0b03808800441d82041228045c5490310341000d03008070b80900d03201007a040c005c2e103a0902c85412540040c503040418032000c05404111403c0c1c81210580303400c10407a5040c00804030000700641c1e02c0c1c4c02143c03a461380000b03051010f003400c0c1c83d10134000c1d0b12259084441702c003d900031511b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 424817787 1250 424816537 424816543
    0x905072001180618080714010e070803030406020901030b180f010b250c05091e0106030c0507170c07030501151409040f21030b040b091509040503220f0503 68
    0x1041e42c44018440c03400e40d4545401c009812a00707581115013004046440018601800804500b03010704641400407140850302400d44450b02da0131101a48a48414050100d0120489030416400301d001a510b412800040e0003814901e1440f9030702086010b90340c410400e0300d4174500d210b08070b041001cac1036982e2502150400381c002d03003201c4c588001100d650114500d1411701c54500050046c8183c502c8284c0e00c1d000544011400c880810b45440c0405c200707014981e050700040e024140c00e060601c034140c42680000e240d80a14900070b0414400f40710315201d14102041201d40749107003501034507030858480c1400f90203032440d4030359130826159060001428400041e400004940c0007060301d000764895444d400f03501071150106490380c0d000f134480c0c44544d08000120044042d500d88011946068200801c0100c1e100107141c507000760300420030800c981d081c80042c06120f007422620200d80e81c4a505002d40341d802944003521181c41c10001951a5000b4500440e08a0f1504d00c4902040c42d250024951 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 424819037 1250 424817787 424817801
    0x60106020307031808061e01050901030209060f0d05030a0905031b0a170106050a0e150d0215070602070803100f08070e0c07020f1503011d0408220905072001 69
    0x20041c0c00901441c0d0000780310742540010b10f485207507080102500c84103541d003003490990380c2c82110640309004c01d40484c041c8500718010942219260415807440c0c021a042000c01400940f064013900e5058510f070303449558450103250001c04030707501c1d6192800080e08004203405118030a00c03a514401c0b141031000441c2c03000c5010064580c0b1b038090700d0840c41451450f00c2000031031595403207210116040d103e501c0c3c2d40d401040b403030703021a0300c1d8204a01810900484002030701d003e480d9550300c000240c0c64285c01c244079140ba19020076a50075503414110024014144000d00e0040c00000348000d00e40d0b9a49851f0945440c1482d014280f40e03550b656030750398072080c8141a104100031000658410707140d00540b01300c03400a8200c80a000b0745100190801079008156141600044011b0114034102600c4030880341040210921508190b01d490019004045620420807034032204402c00d9006403403010b00900d00f0200a00035401e00d40009400502020203034081d03446e403969105080e11050058007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 424820143 1106 424819037 424819049
    0x807051c2414090d17060303160c03030f0513060c080910200a0503040308030618070e030607082401090f0e09011802030d12140109020a030e0601 64
    0xb4001420240c8203201c107501070500310004c01d410285055240c6695920700455030344034000a881e41c4100070306010141141c0d10200c3c100202d003c1c103003054034800c0d110000c0c400b1015034101e03528010160300d1504800242c008020341c5014000302000036015281042c41c12402202051040424117083d20000305806018081549000c64040100a00308050500d000a0307807030f403c0d0740f03006034000a84100400408280c4aa448100f070003500007040e00494510728194001a281c0c0c0c003100031090080c001c0e400001c3c0034510900c4e04d64807800e14100682c0c06000c01c02e8019014003d105a024144004071101280311109004208020002d00310610700f6807800c02c2120b429100c102c240002d0450030f00e0b20381d2005a5021881802040e0b1900d001104411402400700c0501090075450f212a801c180c00860f00324001d400800100d51680c406000b0142c0040d078280e90385070b0074407542c = true := by decide +kernel

theorem cover : BRFrame.Cov 424640287 424820143 := by
  have h0 := BRFrame.cov_init 424640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 424640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 424640287 ≤ n) (h2 : n < 424820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
