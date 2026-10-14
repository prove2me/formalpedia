-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1398
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:46:48.068108+00:00
-- url     : https://prove2.me/submissions/95c3c6ee-1949-4613-a6a8-6725826c90ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 251258992 ≤ n < 251438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 251260242 1250 251258992 251259037
    0x6070c03052502090f0604061d041704030507080102040e1501020619151403010b030109021c1a01060815190b160c0602031201060801050f040e071a04050f090103020f06 74
    0x4080a180c01060380614040c41403031b198040000f07407047c40d042020030b4100c4110341500f0614284400740c101364800d2072148207400361240c100c9203003e0b03a80042c0107031042c0c00d0006421349042d8014000d82c0c610700d06070610740d56031060034505160f0450640b4016480800000e2000c28171001e008815450148080390008040388004c102c0390254120111361520714110740c42c40d02d424800c1084880054000340018412500080c7d0070145116801181601d9442e000c1e00300a12703a007080c085000d03040441145540c4680005050b04021680b401484c0b000780000003861402d01000c020060000783c1c9406090b09010540ca1b807500301c1c00301008a481c4401501e1b0008090164202c054500b9070300a680304c034020113545012100603803088060000410040c040c80d1250166a100c000027039401190784c140b11459a45010030300e5000c0b081d0001511011550440b500f0000c008850045485690300c448020810840c9003007844001d512400d90084406c01c0d050034800340c2441c0401d004240c80b60100e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 251261492 1250 251260242 251260249
    0x30a1b030314033312030d05061206010b0a03150e06012d031806060e0f010f0b03070c030e0409031112120a150b040308040306060918031b050a0605070206070c03052502 74
    0x3140882000e0740c6c00209100c5520600c80c8901343d480281180e9030707003c08801072a110385403401030183e0590f00300e00284004102d0300079040341c004111021000010a82d0380ca403c00d514001c196403050000b0550010b202031080c450005c00b02c44d80e04990b0380f41404000c01d10640c020314012119040284c1001d0840020a504d4440d00700282400a00b200c0185480220a404000d058000e002c00142c2020240302044244007580d500c00c050b42071400c8a0501d41c142a610031180d560f19035401070505128400f051b5004042d081d90342d01d51411610410903090314007809000d084402081c1074101000103412400a8000540400701e030341c3d20a425640320058603166911680042c2c0321500700250030000c0142603c21000106402c0e0020452500c21441d811640349a49001404112042040705e09284032980c2c21b614107176015044030303180245446d12a010f00000c42d07599000d801407000059540e80a88035000306158145d81341071600b01044416194541449042800e80da403401c00c0030010385 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 251262742 1250 251261492 251261509
    0x90f0f010b1903120e010c060c1106090f0a0f060204080d03062c1302030f0f10060e06033705010b04110f1206030a1b0303140333 57
    0x12150004548401c9000c00e01c07011084903640c0459070140000200080307110840c1036260400f46283c40c07030b13010b08450300480e00f9196040016112038039040420740314540002c82d034041c41580380199907a40d6104102c9a461310b000c41222140c541001d0401000210044441716071144a5040141426182c01185280441d514000f9002c240c0d0381c0801c0c4040510b05107580c4206154003004081e01241160080f03680c1405400340f2680c880d41811102155018000c0f100e6a10102c0c1c1181e2107a00000c80e002e43d03400e6120025000980b8201000c5541c40c40c00c85014403486000e001004007a1989003405031043c940d13243c40400448982c040d0701d80d14190101690050302403000800c521000fa000c0004a032500d0f180b20a11a20410546501c55031190543e117501c0d002111081466640002190501908280003494080710721034803c640c02002c1841400d0b68042e540e10102440c3c400e00801d414030080d161100e80c506551582c01c0b030382030060404880c0d0301a0551040542c01d10a0200c0e1121 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 251263992 1250 251262742 251262763
    0xe041b020a050c030a0c091d0d02030403060b04020405030601030210030e1506040c0f0206060d0c0302090a0518060108120a0c12082208090402071e11011b0b0708090f 73
    0x5800107540c22003444010010010380303500c00c03006050703080ca00350b45048603c90b80d4414454600c1c1c54440403000d13092541c1d02855208410403e640081c02a42e00007900c0c1c1e8400c1c00202e071000c1c0381154018141c20244240d6096610140080803685d00719000c212078441180401e00c109a2102d1001c40041010b00541c1401c00c280ca008412908064040206a4003548001c20800110402c104d111035400a0043e03000a01a1843c0781c081da16400d06403103400303454002a41201d0227a0030301c580900203500c035501c070700da4040c0459003250706d02d85400c1e150360080c482d240c080c2e0f21502041e603a520368040204100200760400c0d0b58201c80b2903454035201c08a40a9040114004c141000341c0c2031a031086d200d1821420302c080d82444400c40c4c1d51a04903019100c140c5008035070209a070300070000046025030b0201c040d80604402e210040c03500c4103007800c40c2c01c1c0031400600c0403900c0c9084800d00b288030760301069000039107a00a503a04034044910010051140400c0e200741d40b0880c0c00b55000b4000b07035400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 251265242 1250 251263992 251263997
    0x1330306020a090303030f0b01020a08130e01080a210f0e0f030f0f0601050d0201080f150a03060b0319110f030c13020405030d0207050603010608090106170a0c060e0604060e041b 78
    0x41813541c1000340480d40031501040703525050550800b4147e901180f201104c0b43c0c01b00110781c0b14801c04854104004c490707003003c1610303003503140042035010001543c0c501e401e200302d0b0100b5842c0c440f48590302c1d190450110540100e03071040c00141105001e110318103403042c805000c6040c03103941500060700c0c104860500b0342e40340d000200001c204040c24480c036405001c054407454110220750340000c050090003860360030302d03040e6100414840c4a0782501002030b42001403001582c9501d9061000061001e01c0c10a4400e00c140c0c210301058941140080a40fa50803000c0041078130724034014084110610601e250380b500030024409100d80d01e0b6210742c90302c4090410016100c601388014103260140d40c1c00c120301594408a1700f0415595a28200c03410f6030402e01c0c003000c2603150b5a540780e000d0700f00e07034002d8400d15000d008080400d1400080c144001802040c0d65103406580c0c04003903442e801500708803034001c01c042009205442c024284000c0505010308006150254624540c03540420042003000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 251266492 1250 251265242 251265257
    0x40c09060803190311070f02090f060f04021308010501080634050d060b030c040906090204141311120403230a030e121303030f050a050d0e0a02030f06060109060201330306020a 77
    0x6600f03004d2508ad9211034590038030002c40c1020710002d042515000202032245400180c2812840601c950020040c0440e100074015540c44e200400c1e2a882c04950100340e01c600980d500320381000c100c0e8404100707124950380400c9030003800411106a44503a10300d04015450344400500e042222004500c520540101c2e542c44078205441901a9400350b8091041c4500501042c441081c500c0c4512101480c11a06140440d682007241d0001e02403803000c0c2030f01c1d96004200344044d0782602941340d00c614829903c9100c01c8004e10f82d00d1a42d01d6002040c1801004144101c0180c1e50190f0300144071569038204944807100345140c0d8410960110154000d03031020301c40100205508034940402483c09418114201201508014114001c1d10703243c45240e900c841c901d11984000b404847c01d00f0341c02a0568400d25800980d083ea40c030803d4610038000b0300386110008400c0c0c410b1007801542c44107103d01215406841d8800c2241e85421001030003440802500040007907141e200602021203d6245c0c2403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 251267742 1250 251266492 251266523
    0x3040501020705060c0d08090a0b0f1603090b0109020a030605062205061606050403110f160f0803030414190b190e06040f150603030305040c0906080319031107 70
    0x904201c0b2590020b8025042404042d0b4024004a690011b1040358940202180e80e00d21201d4505401d010b07010f440095010240031035075051040c0030f4800c0a035442032400000340e1407000c42c103d5001e04009003a912550005000b0071003650001c0013540498030b4089402d85d164000240941e000310800c800703000c00c00710912800b01d04c52000da070042108403131890501e0560f0b00040c40e070760721600b80102403d6651001408260150070000f03003000203201201c00003010b8994240e940c0c0100c0a43c4c002e040740c40b0600044000e07042d41000241e5040f840918155101ea0340ca40c422410740e1000340d0348034081c14421041c503000d8400d0708a81d40d0300580c03180605040c00103040b107000c0800018180420b04000c0d00050380c2800159860300140d02c040b0950038407965042808201d510030100b034103040e04044000041c5039141e00a180540c1c000d405080c092591400180c0c111111403092143c40d410500c00d605000f40821340185031030216090100314602582a8140c45038410f8004840c01081d0401c0c0d036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 251268992 1250 251267742 251267747
    0xc020405011410050d020d11030a050108030f12060a0e13060515100809161701110a0e1504050d1202010b2407030504090c020c18040309050f0d1403040501 68
    0x650050420300711107805a00080007040f840301441d20fa460501c880045c034001d071a4003507030446205041b41802001800b101c1c50142c0f80542c07094420144036401c18001141c02d503004004c0b25200c100741080710341b030901c60425215000000070030090780460706640004200d91a074003001c0c8119200d00f480c08500707040749082811550090500182000c07462044503640c0c03241c14600704229060709200740700350b13a05c44840307180c00740501d8080504001c2c00e00001312420204107801050441d10024001078080040c804030500a03800f8020002d600700340100e20138140400040b100305041c00b41a880e1075202c0c0c0214190340f400160407108400c06030038996500394284101210400219108a10035000f482d464a00c605c11126842c02814002010b1b420180548116001040810018400500c1140020352070780c0e4a007451a01034401c0c186e09410312a0403100301e40c8644e901d521001c80302800d00f070a1101240c480749003181c20980120040020407483c490020f4a0301c41c46004503525030511000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 251270242 1250 251268992 251269001
    0x90911090a0510120c1205010b0d0507060207050306240d050312071b0203100b01030e07120b13051005041e050c03070b120f25030f060f05030307030c11100c0204 71
    0x99640321300c1480000d030000d143e4125150482d030681c14050f001000e01c0c04c007070b030041121500050748800c1b05000c1000b001000300d00345049895503002d954000d90f40700306068a416044410824040c0701c105034140c00150000c1d002d031003180c00f800300d5040c10400c0d50f0300d51440d4014900b401001410320100410158081e1280100034110b1340660840440b545c0403907074440c0c0d500e4124800030b4039904410300c1340c0d00c40e51005040716603002c1144c98440d83c44c1c8140c170320461401d409032101003524000880d400c54801d4210641a40b1100420790080c03104414401041e000c4c2c0300b107c0c601d08801c1103290414a07820b070389004600400140c03110b10540380c105071400c3c401e580603814891061107100e8110326086500d03035100100b0900700b49a40d9454103480b211030040c0301000680103c0310803028416038554403002d00d41d0b1540e00100038094651402c0b2010303507403900c05d49504da0b20400c070500009100f82c050580c6244100c0c107154000c5401400210035108085c0802c0004414180340015490203008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 251271492 1250 251270242 251270249
    0x25030509030d1d0103090209040201390501050124030e0115171c0e3f0601060c0f02100e03060a0b03060f100312110601090c020d090e01090911090a0510 67
    0x2406c1040d018aa80441c845075001040a410300007802070b99a81d0703903c1c0c14116640300102000307000c95440000b0b00103607a050f102206998540c6050000319150f210304003842e440ca41d03000c0240d00500c4c4107820440c0034001900308900d09540302c06081d100700e00402c001c04043e018854050003203503e502e81e41d6140c030014208200c181d0640f1239940300020b4011543d17001c801415140402c110000d5026206480c000b0aa907041041661001300c0c2c03c0d0f805108043d9100c03506c0000d440160341d96443c11511408425800b808040c0030300e2803140107103072161054002c1096401d200283d0003081c0002070034000f04407a041e5a03552208040c480301e25092101c3e962008070b00c0c45c071801c01e0608071409400784031140401010f0308848000c050b040c600807030381d880880500b24100d841c250b07124040c0002800c515502400503100301c00d00b9041e0704d40180440e1003541e25070022504240e10f000001009407180d0303902519803404100361021070382c4841860728411455014081010704124150070380090a031351 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 251272742 1250 251271492 251271497
    0x603010507050316050f0706051e0606040e060d05070e0106020c1f111504060c3506060f040914010b070c05040515040e16080325030509030d1d01 64
    0x42081101c1e82c000b030507280c0141c81039083c203c500300d0300c460a4035540700d1488207071143c00001c241c3d00c3c1042455004540b01c0c0703600780080c0c040e0018030420030114200649540e035102c072043c0000e10050451007001070f480321000300008103540150b11018140440c94000d2103429a02e02c0c01400782940401007a11010819610b048055446044a4100031501c10342e010800c48520280c1103120400c01c24001040d68204e90000e04e420140781c6400145081179440010407080f402c00742040490311514403501703204521408881301150010380c1c3d113110040080da442402404101c007a00d070650050001f501c0700c160000f0701c0210340030050704201c5050b4000003400c40300700941c1e03000400120080313003250029a00800c0036161141d10b00007550000030745a4100e49400c14070f111484002a007000c81030510072442e06406c0c2c581c401c00c1c0d02c910607409040032507410811b044a0140e110784658180c40e00915103c0d0500c100d10300002d0070310070201c042100142040b00341910300a40c0c0d4224540e065000d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 251273992 1250 251272742 251272751
    0x1d0f0105041203030603080f0406030b010e0303030f07020f0a08090f0409030210020310090e100c110a02060c07030501050f1608061e0d02130213080a02060f0a030204080a030507030206060301 84
    0x9003148200c1c05005001d03000480094105802a0020000386078004a46516a14140000585500544030b41d100190410b00090030f00e50060300c034004a040050003441c0385503a00035001c01081e0004c1d03c2c076070031440740f941103035500c0703000f40100340f07810b071003410340c1d640d550220020005500122500a0312891a0004007400070303070002000c0d050000728103000344c0c82e0fa03500c040781744800c20740717a100036403190400d4117a440341c802c04110308a000d5095001000305040400c4112841603d81034103043d140e101c143c6020142c50031401501124010340c0440703030384030344994815003508c2040e02c4090104043d1800c1c8500c40c20004040c0e21141030524000511340340920015880314032103040542d0310414408009915200d07064600e40203134020340169004405420400002e500c072096550030803011000100b50300324082040008550002d011504101607506080c2403030b03001241610526908000004012606014620b030060280c0c550f81e4482c07815007800703400c001c002854548283d241 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 251275242 1250 251273992 251274019
    0x30c01020903070b161e0606060f0201140603030a0c050307120809070b0f0a12241404050c070b07050706060303080105042307050904020f031807080607020d050a09050d031d 76
    0x3100500c4007a6800c00d44007a030381b603441c01c40390315800c0803000b000c2d01c0fa0f42410401708480741c0103040260078107541d600030440408000c10030700d101c0700250365003580364001300070340040d040c407441d03501548034019015a032801d070560750303460070701011316a000d000b18100b0402c00041d000d041c00310b44010700c900043e81d8606a820702140c440780c0300300582d400610049268403052846182d02040c5428845e035010440403040344031303030b80502c2a544543c03040102c0c01000350b101e0f42818060035004100700c1d5003031410100d19503103040c0e151400030720320010400240140c50114070a8041d0b100150f029881d112440d5041c5000c0c4001c0e41c0204c0414040740076100c201c91044178181201e10b41c000e880f40352254880c901030000402030302c1003002610110070080184010408045481c0e4180401441200c4826681d43d0000d51940e4007103c511001d60803030b0b0450145a801200185841202c900d0242801c503121000113002c04108042980040c06042008042e0381d500108864241c0003120b003000014403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 251276492 1250 251275242 251275267
    0x4050105040215180d0305120406140901021c02090111061305060c090906010f020715081503071a0d06120f02090609010f030f060b03010204080a15020a08040f0f0203030c01020903070b 81
    0x32100c080a01911144e01740a00b41442082078880f56904207114040609050412002a2403803841c0c0e0b1040052000200b40c10540c140b0880e0020090b182480c103001b80c0c080f8003075001350001102507040c0041000d0105144100344005440f5072103d8008036a120307441d0034014504240107010740b20940303080103e0700065441c208a903074425401d00c0d1820303400207001012410b26a16501120102181c000c100550030341180301ca91244030440e413008541c10350607040682d240014842c1c980b040d05480d4003020224451b0005040e0340407003000100da030a42e40c2c109055444000c0e10282d071859500e20b03649045140207003081d500600304407030261455041c02c0e0100140010707444003d190600e000500c008125540d0440600901d00900845d00d4540d0359401ca0b40301c0500010403034100019460281008199109540c40d03071445070380781a81681c0d195121101301140450941e0100c1c024043d20340103903002c00c000c00183c2008400507848410746800c4c0352804000343c021140568003841255404070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 251277742 1250 251276492 251276527
    0x1308031302010c0c15020c030a0b010b03070e06070c0612090c05040c0c0515010612060b07031b0c0902041d040506072706020d080106020a12030f1404050105040215 72
    0x4205000400c400c00d80c601c010b030355015102d8401400c5110700c000005e180f41181000110011154081e65540c511160801d80c81d08684140103202000d00801030201d401420040c40d404500340c1131810f050300c4103100240b65038010210071032b1504214003080c008142e000705501901c2c0b1002c2c0092060200f107540f45400e94015000d058003c3e59111000b10b142445610410b07050368001059407010ba801042c4401c180009025000124046a05000301d030005441078004583c20115001e061544584c0c044503004c6920500d800b030900802d1500001c10880c2a8010007010580001a95945007560302c591f01c41c2a08084045040e940c1c04000100e5004074106034000528034000784003215440241c0c0c2c500030949415441320400080224180b5000100d04c8903902060321795240982c0da45204aa8907031007544000c18401405004040c2d10b40690031000c0c0a10005001090309101d002c00b2aa6954007228142c4443c0e440e00244015400c01c03c00c01a88055619145440c20b001e101c1d0307001030309 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 251278992 1250 251277742 251277751
    0xf03241302091c150e03030f04030c0305040e0a1a0301061d090a1a0901050a0e0a0b0c0c030c01091a0103030903141005150a0b0a0f03050636130803 65
    0x903400081c1c203041035442d410301491080340d8621583c60301140c0d040c90140c08401c0c42c02c484829150848805040c6000410b407442502e0343c1c81c004c12143c0c1c03541c1c2d084442c440080402c60500000703000129480d02e1556500d803045881020003e91503001e40146100030001c0711256000740d24040341840300500740a09142d6120020700301d1110740c0c4030101780c640f4221803d80042c0510302d400ca03d107900714103185801809102d107030000780196200d0407130702e03000c6a68070120b541e019808a20380600003900c4040070740c0e000760256021401c0c091122515410340d8090841d9044a0350358505000410422a08100800324141144440c0d036040d1340d400381407420745000207030402c0d80010b416115001c003082080841022010103120600300b469480c1c0c1003501a01402c2e104100c1c22070042a0760100a055900010555a880d03000110161055004080181010b0780000102440d2110201c2c140040364480a400328206c86e600f4410101c0d00078500d01410940c0d400c2504c0300040086440e0000f569080b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 251280242 1250 251278992 251279029
    0x2120a121e0e0f090f07030b1512090a200a142d130f0c08070f0f022107030807030902030a030f0203130b0307030b06120721020f0324 59
    0x10800c4900280b180c1005200d00303507001610b81c04004c11968458031713841c0582e030745403000d001d426841420008000c2807200159079524041c0a0360960508990f02a9003240380041034070070362042902d448126511600d907148002e40607098001c014141200c0d040c00404600030308843c0260004001402144140c130168419030100b80c0d401c03041065450b494284080042180981d00043d000742c00c040e0500940c5103a81503c3d0035459200c80d03009001c014400c4120307a6600300c00007448442030360418011503844046202c3c00481d0b441d03c58004241c0c40d8640718084426456140514000700b000ba8010b111404050034a40d0010058500191141c5080d81c542810189100c02480485c0345001d00398651020360b2054000061026401000710300640071780c0d070300740070407401c410501c41940b04142c07010000749110400501e6540c0b02c0c141da0074800d805043c0c560741e66011080074000340e81044440c0b0010501c008244540700c080e5110815010765892007000201400320001003049181078100c800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 251281492 1250 251280242 251280257
    0xf020907050d15090c020604030e09090f0105190c090b271306060306141302130b0a020303010501020c09060105120a0608010e01020301050a09060302030304061b02120a121e 76
    0x40c055810b0b14207200842400b00241020444081002003061180102c00d525114000d200c40e031000c0b940b2880342c7d40585030b8290110340ca41c2403100303c2000034070240c414000d030384000c1c10601c82030040c83e00480101200c1d1600140c82c0c1140c2c01150701806408003070115440c400c202c3d028051050b80c48132101408401040d8900801083c03450300c81e100e09603030003180c03850030007150f41c000c0d40720324241d6059540402c0b807030303445074207a41c2404413a1005640c405151402080340b0101c40d002064051607481000e00b00784d54030701810146402c00d5568101581002c00144070550b4100200a864002210700c0d80007401c0400010780503105002d0851a0310a4820002d01e40707484540200c40180340110007004400303140c4006034000c4d0428050076100300c800a03c0000c00c0e072040e02940040d82d8004014501e0140b80003c03e441c17440c0c2021302200203859940c28203026079280400840c4145c40403010b404101901d25051b1098544400684103100c07080800d51520060540320200e00c0d40b507414244e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 251282742 1250 251281492 251281501
    0x1208040602070b07050705060108070501051b25030611121f24030e0303010b04120507091503020127140a03140f061506091017100513090f0209 63
    0x401a00c920540034100740400c6090104c00f0790f10900514070700b40a042038484590701c4064558030b480152285500061041c0500c2030503520000c030b00712103001e140b002c43c1d2020f80d100d00f60b1901030383d422b41e90201151000008000340007840c0112541c0c862601c0080d45401c4446c88824640c4001030111500d404801480643c280e400c440303a18007512002148a1820000c4086826203d81c0401180000707420301c04422405100042624181c0e4090000306003454107019001d00a50842641510b203071081e6a8002461000c0c0d110b01403032000e64104d04001349003140005440c02d41c0c0303d00c01122648032080ca170350390300180c24800000e03202c20301120580060300b00c0014059401a40024000c04611b0011158001c4002000040c0d03542c4171007a95555540c0310011a01c440444240541000040100740c15030715000c4a06120360480f418180c002200308800071200030300803120400c4205c1007903c10b105500e0040d651500800d0960400d0004134201c0d92542901035004100a00949000c000324 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 251283992 1250 251282742 251282753
    0x60507080c06160e010809102309030901080108060609041101030209120c1008010e22080d090309120c05040507020a15050402190b190905060f0315030307120804 71
    0x1e40000201000310307215414500912640c80c1c1c60a02d4920210300b510301d54491a50103146c01d2441a11100c018003d200400a00d0902815108100142601c4201a054a0140b070140154014003245006540f25103403040054070303040060300300010325400b800c20800140e43d484d04d0954002c1c2d000308500130188210006a01034003a120500c4c0d801400d80b200052240300004100400c00c5007111441180e50344000d090324810001e00415501103492400605075003405c040300f80000b48020400c2401c080a07460760065600024101200300d074851500005060384004d803400603080c1d515460581c0003031907441c0d0000c55403902c6242d014544420015111a0090082060140d005a229a0404401d105110080800321001c034030a0000ca00e06004000750407081c403007916540b03a0458035041c3d000c441300081198000c041d404000c03141c1c3c8040ae0946841000d000842d903071102151310b9050244200f0111140404846d000f54024030220f000f040030354401082101d4170b41040c0301192100e0411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 251285242 1250 251283992 251283997
    0x50306062b030507020a050f130b01170f0901050906090a020f0310050103050604060c0c02010c0204090c090204090c090909030f120e07030b07120e060613021e03041203020301030b0106050708 84
    0x441001c03100a10a4020705400000a0451600c210b5450441640b140d0810118600034003403240c21400c0d941910280341c025a100c4084030740c050404583c194049007100d4100750003201c00e0800d0601c174005008007035509009a98000030808043c140358074000c290107079a2003024602078455046030810042a84040c0844800000e41c01020300081d03031030342041a0303500303000d41e001c980c1d4034501000c94850a104103000300d98158160b4800f1601c5c0c81c0c540803c0060680b0313180648182c20b0581c00026030030720a03c004d0009240c26440880c81001c2404040d01c94103071644040365060400e2281400254080708441040e041c0d4104801c559400071700d00001421426200c1c0b44520901501005110445001500c9601946d0b0f0740c1c001d0400501c46074081d00e40701c0d450110303540d00074070200c1c40914000d004d88098203602c0790014101005220a1603294203002c1c05411400d40010030300c814003040c2c0c0c0040000c440b4a0506510f5549150340e200f8941c1030522818040120104a02081082c45000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 251286492 1250 251285242 251285299
    0x901120f0504060606020d0e01170403020309180108120909010308250510110c07061d03011401050913030206060f1507051006050a050a05131503080c0d080105030606 73
    0x3000c0180d40b80c5858020000c00e554040c510162184445203415a8411040c4849030801030b900c00c10f42114071682c829000c90003800403400e6020500c406000d98a070300c4a0700e01c141e00030004461455151052050510014101c1082005070809c80c01c48561601708119044951210b07089a0701c0e48900701003448920715244100c45021504880d40c02d00100142100014500310001c1003804000ba40e03008145c40384e4071800c149600060000c001d50b60080c0296030b2808070460b201e002d02c50a1400003070840307003440945046024642c1c0107220508001c2d0039190b0000b262400c46220000e035490103035803139000609584c81500a4a003140454543c2140729250507050907403280c5075641841c0058039001070303c900511083c5000070004072490884086001c0714009090402010304120030303c04402400301c0e0400e081070700c5009000a06281d84c8400000354040c006007621007900c03003481400c010102c0d513150304000d11400148001c0d03074081080e0b1741100c000c07940255100d80001d00341041c00200d02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 251287742 1250 251286492 251286521
    0x106050607080d15060f0c020310020c01050a0f020702030a0b0c09100e01020c1507081b06010b041502010506010f0e010903120e0a0b120403180503030307031d060408090112 76
    0x4240e02048030603405003d80d16a2594244041c194140e007002d0080d0b400c2c860080020f02d10044641c3c80c0d4090b40131000d185001070b0603294440304049120040e41e04c281c0b10318540760340da1000c11001d404140b140c481400030b040701c1940340810341d03000295500c2c100c0c0700c058030309d80c00c4030042041158081e00711040b042c809081e00b040c40c1d001c004081c02560306160094054060190f81500a00d00740b43c080c4040013034a07005905212a82d11914269080308a440206000032460002c1481040191314001c01092010985c0c5d21700f0035581d8000340084501070002d6a0429040c44466030700800340c8000c650f40303031070214100a840702c0100d40da0f8039a0380c400751100800c2414041041d074000b84260038030805807000e62483c1d54401d00000a4400c2111080401c0441c00100300001e202d0001038403984d0400f060888041e45903c0000c0c1960310a9844e540070070390754446546100d03803070005105449540406050305107800c0e29096203600c1010031403070412400c05d800c42c0d07400a150340070429156810 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 251288992 1250 251287742 251287747
    0x1081b07061803110c01020303190e01060321030516050304020613090b10020703120e010215150103060504141f0f08030307030e06010b0f1b0105040b040c0501050c0a080c01060506 79
    0x50340142c082c42c0000506038005500803090300c0a0250010b07403828001c406030b0080d4915520100b05032106400341070240807c0d0f0311058080800102402854013450080702046655a85c103401014100c2144507007a050609080c02c00860710f01002c103819040f0701c9420300d26601e0391f030380c80025a18404ca050021840c0c40c6085d01080c0342c51150f000c030f0707034031101903c1e04110fa42c04094180d03a9000d607803000504d40060005200b400768807524422002d03807410700480310f22040300c4159581c42403048801c000020003407441d103c100d42c0d0502464005290a407403c10101d0052006d84600c81c000820310340c5e000d4149407c1c1e05103030b13032032102d41d90081c803007400d2400e06280c4403d013450303c0b94070030344102c0d001a043c24910880082e0200728641200c070905e080030711300040015001c80c29080303018500b207402c1400c00c0702601094203000f6248540d200714649051403400b03107000c0301300014940046040140900c4480b2012800040560000f43c00030009034503102c07101c0d0740b1350140030b05401c26900507202 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 251290242 1250 251288992 251289011
    0x50904060c030e1209120705120d03061d0a0b120f0f0c0a0f03030e0a03060615021006060203090409020a0317030a05060108040b01030219050907050a08010503030901081b0706 77
    0x380d0300401e0100c045a60a1203070b508800c0607503949020034121800c2e8250108072001c958a45560f4030200301c40c0d8001a01c1c103076503403540042c0031501c5640750500a0307004a142024101d070303d441107002070700c002000280d00c46460f0a00d0014a0801054600c0541d82c60003058030a5a40f6200001026003002c122a000422400035a869040c2d844285405104024420407a450044117510030340b8505004203140d18a9510221490249180b0441c0c00502140c00440894020300076a00036180f00a100c801c0c0ea00c203542c000707191034024030402000e1450280240f2107035501104455034980202c80101d5110910b000007101a50b06070f000070040c007004011310b0100084131016611500d81d034401000715541f03140054501c687e04980050021480100510062500c8a89552071510308424001165110030120b940408161602c3c00030030408513461804c6644151060302621040c1d02030742c00d001c44040044e2200c41c001e0a01030384050581e00400c448141e8806682080b6001041030090811 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 251291492 1250 251290242 251290253
    0x40b0409051519033005030c0f070f030f030504050303010b0702040608071d180307020909010914100c02370503070812070f0c0b060409020603160e030d0e01050d06050904 75
    0x851208481d05c84260f898038444c690702c14241000c1c40d08048000e03040310801c2104640540c0700925161114606125036001140301c1409020000c0c403404044008500508001d03111400c81020282018105010480042c0340801500c0c111601140455115205440010050002c41e00112043d200b03e00740064030300d8001540d0300e14050081c5694806032a04040d0929001340c01c0a81d2281c1da100700415401400c050444950015a00e0000946025580d444030b4030400141000100c0d075000030b1401c24244000c0c801c00c840d605490000b03100d0f03452006603441103400b102515200c3d800d104070341081d1480050103181c40241e48042980d503030350203925044905400c52040444540401000502aa1b0256580502a2640d1745418208007100c0d07603000f8040400414068225032984110b20041c0c0381e40018601401000300c18407224116484000d210300400140f00b40300354030500e01d014403da00718900444001081c685940d0768480c0105040180c25590b000f40d40000c00d040c01c2000b4040c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 251292742 1250 251291492 251291539
    0x90405010b011b0c0b03060d0506090c011d01140304030c1509060605040905061302060d060e060301050901060b07080a0e060f0702010f08010f140a050d0305070302010b06040b04090515 81
    0x260300f41c8a2000360032040300e19003458508244014100031103c0303814000d10940d90b000d5544a000205107101c00350003650764904007041a145403606d648102c62240c443d6070006845074038100b0321080004071883c1c0d1000240386402c141c0c0f00d55074035a00003002c101413600c01c441142006400040d1070100102c2503412400a050304c0354107403000e614001010410b40b07800e003e000c0106820600400c8141c44560000541380024401241e002004102400d11441ca0780100340c024140607034100b080749842c0045c142540e10090181c4050b034584441070045004000556002c180c0085e40641c84600c41c04d42541d480c0e080d0700c1d4440d4008004039040c1940044100113180685c400c0c1c1e2145041c192560382541c00c42c030280074203120104065000c0c0819040e842d90100510001010b820306295180d0104100c0d11805c10700350700050700050142c040c9502401041c184803415a0500d02d072a1420310034115502903805202400c980719004590000c00701d2803d01172088004140ca403c413181d0822092014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 251293992 1250 251292742 251292761
    0x91a0325050303030c0406030509100f0603110a06050f030901153c12050102090d141203011202010c05010b0a06080106090602061b0906040905040602180904031d030c09040501 77
    0x802200d000807915040201c2070320b0160300003102003800c081c100718056016010003000149141300d070165010080c0b80c10301848610050180c0b000071028107500380300c80043c1c40da00d44e03913000d41d014004c20081070f5032000c202d40c1f80860301d5108a4590b1030342c640460141514240d625440c3c2107600c0b001c01d1000c00568a042c01c1e00c00e104c120700c1c0800040360515035001c80341c5c1e0f04000000002e42c0420a0300e842070701e003000b8140719500051401d6582c5000078074121000706c09a68685078410031020520702000f01f1f84000210bd002603007150324040c0100091190342d0402410002c090100f1000c01000b5004582080781c0106448011a1950380003000c001c801d11a0070700060f000e41000074640d00100300c1340e0050040f10304034004001034414590181d4001010950080710070800000c40c0704281c803c86006902c604009a5540e0041c40600781c800418004d2130312801a800c24840026000080303003800b04504000440092a41c000003814244408015904100c00c00c00704002c000c070651101801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 251295242 1250 251293992 251294053
    0x1c090e09060a0f0e0c120109080f130806011206091104090f020109091413030513090906050a0c1706040e0d020609010c21020c12040b070b01050105090604091a03 71
    0x410207081c1040c10344032201350a106030340200302c1c1c24809040010801040000400c000304402e0709503a5500e4980c1d000c242e8126031b14030089001d02ca42404110507000030101c86005044a504144420a107840c20081c02800903540303100410810107000826001808014003c100c0340026042050304c00719604e00c01ca0000c1c024010104900303009204015920000100c10401a07030b4a0403000b00e15200000c0640074018140420142202d8082422010300345021011600c460f20f440e000c000d81e18003508a01c4403a0401d03040c0744e031866100903409034202000e2000d41e0240c40320b00105000b822108644881070062013614003800750000382c1113005078803800c001c01c420070765a14101c6604c4030441e008401601c2444007201086615005054141d0340e03c0160303000c190700c0c40501c0e0110f50280e4064021483c0c042208414005c51004d880d004003420b0030702c0c2c0d252083e030600150300d0744123900900b1401d035a18820703103541010503030031682c6101000d4201e90302003504100f00c031604d001c0d40c0e4450b4003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 251296492 1250 251295242 251295251
    0x70e1201020d0e01050108070308030a150f0e09070509060f011211070b06031b0d03020f0303070309151b03020c0309040501030c05030d140a0f02100c0302030a0612051c090e09060a 79
    0x600f030405100701412a4204806890800d0450341c910f0442c1d8805400413245070740707460118040400304140c1c48020407048000d0302d8040d243c6880c100f900000108a24120b030080d0310100040d84400d90b1081d44004101c412050f140c0520005840f203c6800703000e18010741c40c01c00d07101c44090000c8018400700e4010215108142c3da402c080541e24019114200d0440900c4044813031142058809844118480c0c010390345640c0b2108502881c541045803d200025201d040b010140000070041150020540c00c0a120052038011000c0c440c100e800c00071805c00d5170000300c40541c5034060041d2490a4001002031181e56524200b000c03980e00f071806018840c0c020b0301d05609a25005810003443c1d140c2880300141840030440059503a298543c01c02d40550080702192040c400140c03082d4600481d460714010307180d04042c0c4400e03040302e0740c07a000035051002d0440b1030004a00c000680d42c40c0c040105205485503c0030b00d6044411081d80e9200e414808420340500440c0324020074058400c44c5001070400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 251297742 1250 251296492 251296511
    0x622060c0e0112111605070b03070c1208040c0302060f0d1d01060f1202040f0204091404060b120a111504030503030105041103130f0501020c1b10080906010905070e1201020d 76
    0x181110b0440f0800035441104000034405817030748149483c8024012416501100d584803c4510541c5c0211503420001e69075441ca1803c11038003518202001c060340c9043e500350324060340c0d41c02c000c940a01003e80b02c0e00e008038180803110300ba00c0c00c5615000021105202484140c003031180c45800d4521040d01a5090000110300404d00d1042c00c0e0031a0060300c0c2041c00d11407280c09100c018002540001f1880c1e17000c11000c00d01641a009914194150051024181c5014101481101c8680340c003e03104160422060240c890000f40e9014900c1e00410810601484a400602180c401d00c2d0a04c01c2044040303000024043c01002550483d80240d40c01c1c803c62038448020b1042d440704965002d00d034444001440085140d40202c80e103154410360006180c01411030886d464170300c0d84030006c202c00000d03030f03100c050300c2c1010b541900340300c6598280303c411030401c0d5401036103610301405201207031035482000071070807841980309072030110010740070484944100031028040c0d88058480480941004042d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 251298992 1250 251297742 251297777
    0x30f0c130b030a20090c0903010c020321090a0516090c090302100305150402030907090b03030901050a0c1104021323030c01120207060c03020a0f03020405030622060c0e01 75
    0x1c0841100082c00303441d2500542c1e590044c005640e50f44c494408408a48107405600d40d001000c0c040c8850140e401d4440d020101007500759914140c600c0300b107400500c180d48000403c400c00c0880300c203080c8207201c50344c0e0740e24010a262074103003c0003910350b215a000c504410048003030040140c5038500000d1050044101098841e03280501c03000750003030030070345288000c0c0c0e02c80c1c0d10083c2c112a9150804007120940c000143c01d03030300143c41441e07003900008410004c485403841503416890f0180e000e5401c01c201d03440041c180380500003d10080c000a0841e400400c01103030158015400c00038011500c0354035400f000d000c4195140150b0340480e00000c000c0c0031800000c204c0f264450f000a0081900400c00401100c000014020241101d6001c0c40034500082d5140550070f02558550742c0161960782c5d1000c000c062581601009049c03520411090040e030302c0204800b98880d100068038004450070030122030580351000405001d9074a40900c03100c566610082c02c1010b01000d070b84040340c0e200000b07c1c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 251300242 1250 251298992 251299001
    0x60906180b1308090108092e150b030a020f040314010212130b1503030f0c01090b010608040507030201031a09040c1509210c030f0b0106260402010815030f0c13 70
    0xb410407642405800303141d40c8544103d80c1e1000340307681078469690426080001211840c1c441c1c003081c64009108c4054210f0522811044505103489a100c1506d00085504140b2025003d420544d80010780e060058400300300320780007190f215041400158002d01e010703000790080740080c444802c03a600403651102210860321016600030000a0f5284c07901e0504194040d0f500c45082d0f010300041c0990b0311540d0a080c06806107280e40d20012404015900d0300240780c082c142c20000501c50f6480074040413400000359242965420300340020542d680501c0c1e40038809440c40c045070b0044001007040b08100e0324102c0c5008403094102c1c01c0b0300401c600b542c2512001054040e1010102102c0c00f030181e440c6003800c40b480410700400d1030103182c0b41c8948a840c503180801c2e409942103299100104882a80000b07008980c0c615850701018034260b0f0072501c105404007030300180c100070380034012030284200f018104200c51030007421a00346100c01d226240d11540d40d010941d1080c940c4110348901d4035000c0c041e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 251301492 1250 251300242 251300281
    0xc0c0906091501030b13020408070801020a0c0b09070b030a0c030b01020c060a03110403210e030a0809040b180108150f07020d081e01060507052b0c060906180b 70
    0x1c02451a6a940b00701808001c50800083c1056280c00b400c41440d01e40f03c80d0b02003083c61030000580d441c2c1c00c216245103810895400580180c1c4100012101c0701c9c4e22120300026654441200151500c0d0382c180140b40880030f800c02141c0d0740c1c0000030302007401e446034011628440ca649090229001c09001a0707102c0da10a20105d401c444208500c2a4981c841d038082e030b1511040220090500c0d44030b480350804000464603011105030b0005003d52401e030402809511040c3c1200140b00d190000d540e80b0a49016000310180104c1d00d450120407103035525a41a08034003410300c0e002c04d807913a54480c11580e980740405240e0406503084007249a07110740301c5c8414070410168000302141d081c4454110350314000200a0300200c4c2070b800481484070080242e0a00a03c05656442c6c1c8400181c2001410904c0c041c044030000091401d825050303a08081d40b10701d040f800c1d81131141003800a0700701540074201d02080200117900e081800e900700d144110002910f58002d0901c0c80703841d594030080009480d03c519 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 251302742 1250 251301492 251301499
    0x270f081c020d0f091e02010207030803070c0209010f08070e0a0f2d0501080706110313030b15240904090506190b19091e0c0804050d1701120212120c0c0906 68
    0x86001c01841d000c910f685e45400c0c4180304036408180d40351079041094005030360180006542440700020f515022445034054260481861325131031402c000c855490726076218a04490003030400090f00700304183d02040c001c80034102c082c0101c2e0704a074035a00c20030011a8021440501c40320391641404668402d42d810703104220002e06000b401c0035825120a00c0c2101c0b504501e110412145680280300c140120040d441002c04030741a0411244850f10343e1825010103005080d058029444801114500c01c0b07038190100049607601c0b494404038024180885001e815482032000340600045181c13205007003121410000c0254010440401c0f1880f90045100c40021413600010320071400b59500c050003408502c6c034006160890044540e060300c2d00240c4260109141c42c041005001090044440711040c030724100a100d000703c40e0030000071106005001e4010302c000c03d9441107450f0381d9007110044550404a03100301d0701a5000c040c10364403510f00400386002c0d2460824580c14a83c031414025003004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 251303992 1250 251302742 251302763
    0x106050109300b0609010b070302061506040f080c040b0a05061e0909010905070806030c0d0b1e0c04060f02070e070309020a150c0501270f081c020d0f09 67
    0x1c0c800d6001d16194a081600401e031680e5810040003100324800038680f1035800100180381510400c040740c0341c142c0c050b04400c03508010040000c0d501181d441d40c030000010045000080c1940801c0031401542c000b10003220a29101003a8031400203084042a00106c405000740a92401031024410203031140030b821010603c43c1903852030348003003201d0300140d0004010342015054030000700480020390002700003d54920502030030039444211207501000940091801d045070b070b008551307500940000a0704901c6114007260354031080480c1c1500946c0c101c1c500b00b006052413900000d05611612540f008101603584030301500d40080381c0842101d0020780454030a1b600c040040d0080c0c40155000c82c6c0c490594040072841c1c070b40e800041d4625031010ba03210b0b0300910443c90a01d00b1681102000720f443d54003120b41d50000c0c4500034080070110380c0400601021403461502c10350780d000314200410303d40072150f00300783c400c00e45501901e0031a410042c2840807503002c4038288201c3d2400c02000e0310702204d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 251305242 1250 251303992 251303999
    0x2030601030b0c0c010c030902032103010b1602040c1121041206140411040e010e0318130c0f090611070302060a0e090a0605041d1005040f02030a051005090106050109 73
    0x12107012941c000f500c038041d94038120a994005084440782d48900003c203690305094401d5003410441c4400740030b84a07501d440c0d5111040400000f60005218440200c030001565074404001a081c82401560182c001d0041402525000d09002c0348103401c202c65102c1c0211070100c400181c141d1245208507810780c03070b103400d0410800d20f40003c2c0c815010740c0e9168864042c0068000c000100910450094840c4141034501d81b041006a6100407488070321a070610020000d920004403c56641d40b140c00c880301082000c600201c0e1800000c0031a0805280c50440b04100307450704408480c541101540e1103c0b48070341c42e2001511140000c04d04050a40d110a0041c401410702c1c900400c241000343c200340d00100c41d100c0000703007080d80c1151409403440d00c60008100ca824203000d1004000c40d4243c45818803c2d150881959070041c2030302c0b800d00c50391104045000d01002041d240250717600501603070081c140c141441c694070015030103039400076440d00c4001075680b401031040905940059543c410350625 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 251306492 1250 251305242 251305253
    0x10801140403050d1517010506010201050702010902010207121a16021c0806130f020a09080c0a08030f0d140c0309060609060d02010c231005010801020a08010306020a200102040e0903070203060103 86
    0x700c80100d2900c100350300c1780219003800c4422003e034401d1650742c00801c091a00740002400e581000c0d01250035613041c00c1c3d4800c0145e80115007030b81034030b40f80301000004800c982402d008494040420720071580000c0d00b449842d0428851005515001303408680144034105140c0c0b690184038030382e000000747d118010030030324a4103c0300059060802e00300800c001c81118011030880c1e000711110800310309061405c00c64507405100038141008102e507000c1e40c3c185004405a01ca2007107030302c503907480c40d40010081c0d01c0c01095840101c54000c0403a5404c0c06203080c01c1a056180d20681e05c48040d40300e100c00040140c9071514000c0e2080501810404c1413010b55801901d554500c3e507002c0f120702a0807903001195001c01d21b080759480009800900e03103d2040f81480c0c04482060f00490140c3c3d004110709220203800000840c1120740c402001a607612440e18115004a400303110140054a0b074107041c44807034015000741c426210140c0b503808030b503150304010790b07030302e114a0340001e4164100300010000b041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 251307742 1250 251306492 251306501
    0x7061e050c0c0a090c020c1905010f03020f04120219060f0c0c1208071208060d140a0b010609211208281508010c02070312020106050a03050105010801140403050d 71
    0x200407004440051841400107140240c0c0740d080250b002d540c039081038048960400112181c0e81c02641d80e000914401c107230b2103241d2980b6008a9050218960700c0c0f8030b56501c0381c2c0c11240107024406040352995142c140303081080402160680c4030350b1007019407103118148010404c2c2220780b207031503501d500054100250340001c580c25054414403200d030383c0050543e10782c1170103000a82c8a204855a684414030f000d01d1000e200790084420000c03007504111032a120803696290003500112041c5c0c621003006103151401e40340460080072051020700010b000ea401c0001003007601e09804400c0385034448042042808510f1000107040c4401c0f0340a02d203443d60252100da0f0304400024841d0a4400c40c08500d011070000381180303d41c201e0342c1d501980030100003000c0100c000c7c18562000b400b4a10002c440259101c406002c060b010714401c044651026000b54483ea00600c1d0117030044107156134a0030528001c000034420102c0c29402c140304500030101c107046451159900d03031601390a000c181c03c030300c20060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 251308992 1250 251307742 251307757
    0x3170405040b01020f2d01020f0d0e0a0c0614040b160c0b070803010302040207020f0907050d0f110a0305071125050402091c02030c150702150a0909051b040609030507061e05 76
    0x321b0111101000e00c1c4070a00042000314241025541e580f12074010741c0e0211122200145a1500b2000e100c20004080000001c110380b0140307414181e00400d0408900e0f64805da40c0f0120406900081c0e000302040d2440f150074515000700c5450340b2081d50f9412105403482140002404003004000500061406602803d030190010700818040c0c041c2c9030100e080b4102c1605c07000041800031500b002c1008260180650a00f14000700344483c02d0b001c480c3c50b86070f0103031013003001c1450303180c0780090141d078400c41e16411920720301000c840100c4281d1b62000720701d40700c4030802140c0056030b503004a600d0070103008807a0048006071031441c141c1726084c1000046602848126414012084a40303480ea13958000724540180d0076103001d5591516104000301c0380d02e10418403080303c50901090400c180c0000c1c0700c81c101ca01000d03022070a603440c011440702e5801c59010b145000500841c004c03648550103030071001680c0c860710032948860303120801a200f809403a1210286c178030041340305c0302c0c401c0c0c0700350080c1403c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 251310242 1250 251308992 251309053
    0x9010305150a181107030c03030b03340911040b070521030604050a0506010503060607020d0c030804030317091c020a0c180c050c0c010e010903170405040b01020f 71
    0x1100d40407000101d02c1052a44082501507401c000f128142c2241e00c500c03451184840929840c2c542d2503a00900050036000c805000e16959180c041c419072010b01c05e81c50341c0c0911801401490113040800c98103046221000c1e80d24100c401c5002c15480700314881c46160102c40c00b0020304083c5081c6000e010b5a00c40d01c3c084995026455200c10140001040160f07825a699031b1076031a482c2c210140b1045840c014038100b9098104002d1107440c4e600141140d800c039005441c3c0035503500f11800440d014034911007001704140691940041030205400203003060720b00c20b6440d6034050010200e003e03031404c8186e520325203c2d00861220790035540e85184507031240e105801a0f410300715140d03d0b041d42c0100e25030700c100f4200e41c000c0c0910108088510900c54103003070b107003001030a203016441c20603628503581a03400c0c1480191104860f0581c0035481c100000c5a101303008001d400120110440f0f21780062045034082d50500c0402996503002050036415070004000030070824141c1500495081200c00c002884c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 251311492 1250 251310242 251310271
    0x20d03110105010b07022803031d030601030f020a08120f1b03180f010306030317060d0209070302190f08152b020a060504050d150f06060f020d020106080309010305 72
    0x54500c003806524003e0269450041e00e582250051001385446611110005204d80c00c030480070940c0104100182c03601450304041200035070003904032040d9401680341e8584035240c00001084440703510000355601c2614003015496840c140140d8602101d03404034103c20091010486012050b0040c0c10a40c074034101042c14061140016411503101d6908220414601001002c041c18404103240015100707280c00c01481d803543d01c00511005c3d01e0350240c1030392101c10010031006c0e82e4030b95030101c200b034004040740101e00f80540083d00039800b40c1310303107a203180c103981c0184d00a501980030f003250041651107070103040d0b48406115600e00745042d4860b034845a0119014141c10074040140c40100d0713112952402002540100f04150300325030700440070030004200900c107544034001c51010103544200040032104940441d14094048052038015940c0b403c8000240d103a402498050050903130740a58848150a03d41203090362800d0250b0441540100031290055100c1d90040d0740c03100c00030380c2140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 251312742 1250 251311492 251311517
    0x30702191a010b07140609030403080706020408010606170c0f0304260309030a14070519030302070b190509060708012603040801060807090902030a03030506182701020412020d03 78
    0x20200c002a000f082d2808000300e036000c1003040008824a011700044020085450210b011650324800d03400010502d6902251000c108241350701503030007800e0000003e001c4180c9a0400900482030b00200c041e013503041e103001c9020b400d4400201ca40c035050011229185669544034541d020032104000d01c0e4040f54200711414525240c0051750090701610081e55503440740d013200824440b403046030302d48105000c01144001490005115400c601c0ca0b10540d0340c0d5103014101034000b409110740c041c2180c0182d008100908549000c00301c035090480404012503100c0c0911640ea501d001c0761080c5c0407c40c018010b10100440c1c081100d462000340d2030305c84941034240b035480e0450b0040d9004401d9a911100103220104003030000c20050452814108031104150300000d558080460000e0f047c10b031780354003140280e181c2c006401c03206072110342a42001c0c2086000e096680300f85888859180c201d180003c1240c800600031641101d5900c0c0540d40b01030705a4080104c00031104000f2018010b47d48600c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 251313992 1250 251312742 251312783
    0xd09060909230705090a060305090c1908030a170a020a1403060424061403130b1005100807080a06050901300c05030d09030b0a0c11011a04060b03070219 67
    0x611038040c6513541c0d0317110404281441041c0d121600503400345401c007820003416500000c1c0c03580f05107000721035a03903680e030f0350303682c1400900000d4010054030b010014807940035a410000c4658541002c0052551036a11a020b620890082e091030034002442e0340807a20a81141e00701030b5401c990300400008001c8030030451414200494201200e02c440c07209001c001c810707000801800800840b03c0c0c242c4c40c62800303500420000402d00001021500101c0c0070840c03042011540c48054203000c0c00300c00129040b0030000e400d258045840400103088940041d0300c4209034000c6000320b6001928010540e42006a050110418201c0c20f503c8201800c000c20f1004452100e04031080d40505107204001c0d0501d4185420019000302042c140240504c0400002c0c030302a01d034540c05a200c00b00002c0c3e200c036864040303c01d10b4801403018036a60814401ca103c2c152a00561808518116010442c543d0b403144666042c0c0412218140075810941c1e000c000000c03400143c0d00114403d50840a0303440076103509 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 251315242 1250 251313992 251314061
    0x1206011d0d0609021c021305091606050c0f0705031005040f0c031a090105040f030e030f0f010b0306101a0a09050307090c0806030604020918030415110d09060909 71
    0x41d2070950f00e8481d141d00f0360600c08030070008182001c035003418122060b0045002c043e6942d0005401a680d034001925400c810301c0341c4079071480265281c2012554a55009066421007805003d00d4061032111005800340006c2d1030f0100d0764054007510070040320501c050000c020042054540400c0d0140300350000c0d942100500107140700d00c2c400e9034241200c492242034940700901002580e850f0005100208282035203181031564140780c03004208403094042820002c942d05c60400c1d5104807110b0455000c8107420003a103110041d41250f407256a000d0311820b4880440c4a5603da00030a50328911074000114020800c00c407440c1800081d030b50383d910201746402980e502c401c40060780c0c2c1542106465100040d83d8010100f02c00901c9242016000140303082d4020701600301010004e00c0b08980c404091080c3c030300902848451150100560700080c0482c0e403e4a13142d10b490113a88500040c83d4020121401170718115039990011364145110040200085c40001130040e079810031490722803d00062 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 251316492 1250 251315242 251315269
    0x120606170718050402090c0304050a060908040501140910030c09150302030703060603020909070f030b0d0c03020307051f05030612010c0e090c0c03030a090f1b15051206011d 76
    0x349000e500d840b4003400240304211814800c0e90038882440003503560090499000340b600305000f0703981d4a9a140c039925016403164020400ca0400d40b4070420b121403440540200d40c0c1c280c807440154501e01600030b02c2403242c2014698840317103118150341c40e54401d61104036070381041c0c00c10980c1192100104000c800b850030307400340000c2d00001005100c80d0316000b18001400141415810445030070000350424400510050810103034420b00c03134800b442034114000041c1c1c050419035000c1d0150400c2c404100321400264000d10809100140c1800d010240c04052101440d1000d0080c4007220101c442e50f00191015030300254490440304400e01c00e21401c1852015916034401c205c1041c8140504c03114001d0050120000c14001c8004802c0e000c4210796010b0a00340c80010041158505940c24090600c0c001d0040031001800d6410441068505001e03188810351075000c030241240125001c0c46505068008520502e0206000c3c0d40101c00c5032003140b410403841d580b018000404036888111554 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 251317742 1250 251316492 251316539
    0xa0b090106030606090903020a030f050d14010302030606010206040b01031707020a06020c0a091509021e040b0417160e0601020a120f090801090c03080d0e010603030e010314040c120606 81
    0x201042009001c4c80341c81e00400410b0024010f01c1040d85019403600070480019080c07001400303118a0482c4a18219445041c080004009078060140c42c240201401d0000728001d00c904408108a907000040395403280d0b0348411040b00ca81c3c21545e5226421800e50396101d0920b000303012000c01661445040000342004d5802821500c8040302044034050696104503c41460040c1d030440c2010900050340681e02a5200035075501c018548100d010100038000307d03500d00c40804d01061b0304100c000100704558603608110555185000600e0701c5150503030f884000003400d01e5041100e105501c11180d03120f581401591401803507915200542c2805241560014040c0000c1c4849950005086009019207000800c001c03802c0395600c09985070300d800050001c03600032540303402c2c00781c8903046001c0c0302c001c0c54004c1c801c1c6a660f00c0d0144c007001403040500d010070b007403c1314a40c070142484401445180c005e5030406500b4541080002e6421101e441528030300e8840101050000d603202841501c1388008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 251318992 1250 251317742 251317751
    0x1f050f0417092101140403021b151615111c020d06080f072705090a06060807090e031305010e0d06060f0312090b0702010534060f0209090a0b030a0b0901 67
    0x14403145084030b0300e4800d240444117100080c800401d43c00a01c2807031140302c2401004414500790001099141c001c10a00911600025103810070403210100e4550b02e03201e010110320000c46400c8000940d81c45900d031001d0310b8014800c03411850b01c403421415016400000062420700d10709079650036503540750098009907001e5045210780c01c03410004003005100c41140b54000b003d0b20502404120300d03403030440112589400c041070309114140080e8045540c006020840b1399510040c241d05d0305040e120b030421441c608812000070340b90200c202d80088801d00380405402d41010010345440191071102a0400125000365000815903c0703040b0141c8130012007164503900c0d40ca09002d120300389600384000c000500c0c408020080d01d074070030355031100c0d4242482c03611707040c0031107000300884180c911a10103009110400d401c28824414918011805040148100340c1d8016001060b40b0880c3c0c000c982001c0c2c80e4002440d52426503000400003036006017503071801011038640740c07002442910044180d9544 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 251320242 1250 251318992 251319049
    0x913020c1e0d0e04050405150403080a0605040207030503040b100b04030803040b13020907050c0a06020a050a0905040c020307110301091406070f0201063803091f050f041709 76
    0x1604107070140240c1c0c040200704015514900610120040035601e009603150004982080400c1c442e0317807010321540908864500d0141801000020161428440f0a01d095008140f6080c24000c03100c030207800d500d460b4034644036941c0c0c00408281c000d11102038007000c0c0401180f0603c10300010002940280107240d20b909203030420040e84000988021114030780c00750150010b0b11481d00e515030003c2c00c1c0c185592141860040f0358280700d08110000c00003480003d08684654014000d02000a40c40d5a0148043c1c3c4a409002c00c642003005140050fa0081c005c0200089600070780c000100400743c00032954403c81d039a9411381c0c03a1016203030046074118208001d2501da21900300c9800085510090142c10316040e8007123048065128441801650f20740103550403001403d00c80c280085aa60766580c1386814940942c13100c559000600d18051880089090001d45000c3c07180262140380351801281c0f641e81d9401c0301000d80c2500300c7c410035030502c0241c1d0f4541e18941183c0e0210116074001080002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 251321492 1250 251320242 251320273
    0x305011505010810051809010209061209190309090f0e0706050306120712030305070203120106020309150f03060118081b1f0e1e060d020d0612030210020913020c 71
    0x1402020188102d903009020004c0d036640c80304003904441b00780742107030301c3e61100300216029229942c41039401c8040001c65060104d843d9180601c00c4960302d066642405005d050b0240d110104040a00040c0d07603c2c4060140090942c003c042e0b26000410004005d814142e8860801c003140d4001000f04d00080204821418400c00e50074a0350700b004080e1188609244001000d80c0107418003908240e034070400070780752074020012211480b0115555255660356544029034a42c80544502c2c02026400d18404501d0b00e46401d950392040d04140a03811546c1d210011259000341501f4030014141c0c080c00062650414404d2b1b6006d80c00d2405814251006c035001d00059807031007a0310440d4500201c02c801100d60f4000551714000b0011280d00c1c0e108921000c41c4007905581c9204147c1c00940004d480c501c03004160300402c80a42501c80a004a0390350b8009010121040100a0056007080b690b1810022096004002000c0001c000051081e100700e0340c201240c210b904400503a90185101400000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 251322742 1250 251321492 251321507
    0x50a120210240b040b0f07020406050d0b180f0c06030901090b0a0903030b15070212030f1b07060207030506130314070503070c0e0114120a0203030a0f081303080c090109030501150501 80
    0x440d03e10324910300362420311105c00b2403059a155680e2504003140e100c04564a40e0060401040000d1a06c00381c840c041c100071144480c240c0f40500c00100d407820021103041d0106095251440e244041d02150840a0901c9550fa0004003190104e540c0c4413080c1000443d501c00b4240034158424001a02901070314001d400c0301c40c032480c001d100310031100c03012000400c1c503400c41d0314180c1d0541d80c0300d2284201490851560050700603440280b10f000c2000220141d483c290013a40c08182c03001c40d12241d60f140f0059032170300c55501010f4030036003013040010722201031540c100e41c0171842031030014012804040d510055401075101150309420000740e8a0611070282400b0002e00000303445403045500d403610000ea45030b140101c0e28001e04240607030008981c0f00740940140d554000c0c040c1e84d56004110802025000542021030108800d803000c00c0220a03084102460f07150306840702100b5403a030142c0030b5015000811181e04020141b0408000114280565101c00346109480f81e09641030100150410703 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 251323992 1250 251322742 251322749
    0x101d070902031504020a0e090112150b21030409050106122a0309030e2709010e0607032c06010819050316020a031725050a12021024 58
    0x900520500030f020321040c040003110380040341c0040c0d480c05980b009036080200f48007056030142d080d00002606180507403200032a540f10301030201a513040c41c0381c8030044509600c0700d1500110440c90070b91500d1074000e04000d102c250700c1d003107074240303561640c40c4c900b0b5030001d03048400000c1c1d2092040001c40c4940c0035070070715803010942c6030020004001103400c1c0510036883c440c040540b0b034101f00086c94021810211050005050030141c2d888242c600344142c003540143d03000070008080040c0c00c10106101d952880ac0c07840d00580815108c4400031405040d10034888660f1500c03104003000302c4c01c8001d20300c0d464410000c2c0039007100d43c54000c0441c2042c0c0070403095030348041c15521000c0003840c040119600c0800c049203543d1740031072600129142d16403940000b0032070820000b480d074404000070041e0414103544204810070f4030a40b03820b026480c00d1000000c02560180c10a5000034030001300c3d050401e049441244e40007001c203440c04040d994004009101c012640350401000c4082258001c0603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 251325242 1250 251323992 251324009
    0x120d020c0112020a081519151b05030a05030c09120a02241b03040f0621090201121d03130504051003021e0f040905010e0105100807050909101d07 64
    0xb050070604d40074004140060001c1c2402c044841c03607a03040c0d520144c1140c0801c042000310304c22075480301000c0401d4003c2c05007010100311980380003500b440c406c01c40200c4059011000d142000175170316050300c40d908090424440558180000555500c0b281c40e41082e82c2c4402e001001c0000c902d00502c90542c2000c4010620300201c10520050311040c0d8048540d1806052a259403002010130f100d41940219000003800b204405400100103500030158620042418840c568031402068200100c500c5804000e000c9054005440d0240d00c155014103c0714881142c0c02c00602040504103003998846800e44441c02402203040c041418684503295120406034040700145082d0380003d85030b00031110281c0640b08180c03158110310b86414203040b15440c40500b081c41500007610b0300c0c5e4045c0107050b220304a290b00e44800240070168140d0100c0c121000f840251040c030b8101410302101d1f0300c00500990311846070880000c0412194495900040250aa00c100405012400504001059100007074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 251326492 1250 251325242 251325247
    0x7060f020313031805090103140d020601150c0c03080301060c0b16020a080a020c030a08031501021b01030b180f04030801060804030f1b05070303050d0f1401030b06120d020c011202 79
    0x7007200484a8080b20710f416007010300c5010000220402000c529411503a008101c1500000401514140c0c0a2030306124100340d0f0010740c01d0b21400c80e41c039102440b8031a0a00c9a0050b1040d94070300440400c521140100c800e06503607512602d4041c2564401c1e80240d001511411800c030503c00044d20441d084840c0e00d0003030b45484030745900290b940603036540c040d281c1180086c684240074020000d1005810002c0c00780c40c14881e2900b01101e55400844161100302516903052071a0f61010546410360605c40200b1804904020011030080c0045052a50420300710002c0c005074010740c40e4034910498007107030308030802c0c03405142c02050013006030b0045c01417040b81030034000080e13000303001d4101c0c0c07a996140616a855031012441440c035a01003028005004600001c4203040d0300c54010306414024440600c140c260301074000040300e61914850269000032401480001c0b44080c1140d0027040c000c0003480d554507840c100906019045580c030025030710950060342c2658000350a080c00c58100d603411070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 251327742 1250 251326492 251326501
    0xd030501140f0310060602010207030f112e0e0106060e0307030c15051204030804050d02070332030d0203150103050408030402041e0e070e0a02030c0a080402040609050c07060f0203 79
    0x1802980200c01052240001402d5441d40d0b8a0410042c0203000e11000240040d5130780d414064000e5000c0501a030004004e51810b8032160f00500c0000502017042c0004c00040090301c1c10a00d40e06229040d119061042c600400d10003243c500550200080381000002c0103464120050507261000032018003136084902e081005c90058842282150304010b03009040841c02142150309128004000c0340f040b034500e0500c41856030016810703200e98460002c440d11850324840036a034171461880018501810401804402200b0310390414125a404054880c4122491011402d5400200e500460350398040208082110708400980d4504000e090401007410252580d100c0e61000800181c041c03078a030009100e401e0310b2003005c500c1c0904681010094000b410040c039480e550140304141d004401040410030424003442203900842210f00c10a180400309202a0740f4848000c0c801d07640190388920005903180f881c0915489801500001640da507824a058021582e0702440300c0e01c0c0310710500801 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 251328992 1250 251327742 251327759
    0x102010b151c140a0b01021c0c0c2907020a120819140a0302070c0302130c0201060b09030a02090c07080d02030609091204090b1903050102031905071b0203030c1c020d030501 76
    0x11390080d4024101064240d4941c005074580305c90020a910781504031511166440d51240c014002e00348928400030101d5910400c080d5181d560640300c000e066064056640182100d00003098190302c0076044030116640c561038050703808801342c01611007040015009415958820340c40501031070310704041c4502e9000075210301541c064cc1d03083e03d0526500007808000d2001e50f50881c0c00845e0300900608603000d8120f00340b0003034843e0507a40009582001e80204280f40b6202c241d0780f4a19001d0010300200710b10381c0030807001c1071001e001c02991510800207140414200700013000244010103015940381098420b02a00541c0200800a180c010340880302d41c10030040b0403a4102e80e04440041018034682000812024806000030720f400b450381c07400810410190043c612071305014540081c104410711200042d550111aa500092407015040c03860500800d03103455070500241c2100e04040071520540d14000d4034800603150712014107040022039074100304284542d0840e2609100952405110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 251330242 1250 251328992 251329031
    0x108030304020d030e090c0d0605240a171302150316050d0b0d0501062907020402160b0403180506070302030d050a021303060c09050d150b0102010b151c 67
    0xd100d0a8103141c1c03d07040c1845a000c15228031401826480d00b8180041c2060569110003d6200705030300380300d0300050303070b28002c4154900604840c024050303c2c1c1085407203484a92000d6191414840140002d07203c3d10b4101a815104a8800c4244400c0150324010448004080307040000910b400b0410452058026243d03480c0c100038034109252500b5803240108003511001f40282e0f000100c0d0044003051200540018080710321100c0c5500c419a0103955049120903041240003400d64100101d00060a04c6c1c2d00a0079a40ca12820210110440e035880d03070b40400040c6d9041d00003c000290105006081403296002004200d56580c03a020050750042d48900440e070b0a2101283d8850004294418940413206410a075040700d0401c15207910b0703c8401090b103004004c0000e01c0001c8041014244034070a4020280c001c2c02c8014020302003881c6002802c0807000d10340c119526003000081a465602c8400400c10304a20140c0c0c54500852480d004030220803050380100c4d0070b21058000b600501030b031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 251331492 1250 251330242 251330251
    0x303090501110c19030212070501060f060305070504031209180b090a0b0f0409020f06040608070320030f040c171f05040f0b0405011e0902042904020c0c0603070201051e01080303 78
    0x5005144d1002d404d0a07410907101c0342511043c410002010000c104040d40300170241d8050420007000152611012411560100c0f52000850300810050000c1401c4403c1c040c001c607214a40f426800f030f1605015581c0201c0d0101242c043d07911042c4c41402858011309a40d88445407840c200109907608000601c410400c10040d030080b07076604e44070b2041d5200c1d00c0d108521040d02502244c0d0fa2550340700700800f00c0030704940807400a8038111280200102c002c54021444d14014003090840d29600704420641130f0180044400500211001802c1c94025040e00042c1d0aa840904580e000d138513003d52090070710501b0030501c2c80c600f80400000500c1d200386200c0e581d0304100321105960342d900d0900c1c010b02e1100541055410f81084010610f00c450f0011100240f0a580a000040e6001c0708204a002c007464860b081e607202050070180c03800c0560240080c007400c1c400319a5440700e100007040d030b56802078603100c005075140d008200b20207103980d04400c010344035100352059075803401c0141e40e2203020140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 251332742 1250 251331492 251331523
    0x40509090a020f040b0111121e03070903081804242c040503221401031e110d060b030403080c040308040e0703061e03030f0f0806060f04030506040303090501110c 71
    0x5c8000300d240d11034004201030b48403800848442030341150401030035070080900e400b900c4800e0160034055072022030a030b070300030002500c550f030b0042e096a0714000c80d07800c80c06210701c40410401d036071115079407203001d250660603526141c10320034604172400c281003c1c40381d000030840e00440c1c0d101c9003504216444210711250b84015510350b507204c501e0102c4c00c40c89003010000711400c00c0100c40654803141001d40d01180c80108025609a008000540585400051110403258250544411a880c1d42c00040c841c1c828050703802c0c0303070001c04145e40b002c82d4502d4114441540010080100705500402d4003508080c8107200b650506184d030385c0e42c0080b44124010039002000b18400703d030b1070b50b0090700408041c080101c0034251128850080c81100c5142e880300b41d0003d140c030000703111407500030610103405681c031707903681561039840b00f00b0f11a01d68007845640030496400c00001011440510426004a210b9540402c0081c07003420304600390340007032507140d142010400c1010f40072400092007010301030542 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 251333992 1250 251332742 251332751
    0xc060e0607141203010f0f0905071b031b050303100609050a0909060207080403051c09081203090319090f0e060f1212032d040201390305040509090a020f04 68
    0xc010183c02e0003503003203030070b650700001000101d0020004100743d4191000c0d403a0500d00c00e41d54150b210300703462041d110032011401401c4d01c1e406024405207085900c50003400c120741c0000006401c0c1c20075102c500740540d05d6401c003000b0700c03851096603000c1e040103000c58642070814505100019507034041520400505581e640d2a040400035240c0558004a400c026800e40300c0b9070f0703410001d172142d02031405a03540c074170f50100d48052a40070312204010784040c44014854042d80503038803000c40d480a00034110510041c04806402c0c080b61150b19000c541c582e549006483c030b40307080762010086c10f4000c2450724254032b0800c030b020380780d2072041a00c1c54411642d2050328111150309500f0304020252001c1a0880042003180050030b01d0303000020f913404800c2104088660300c420300500242a00c00900240c0050b0304212405405203110140ca4203000928040b02c4440b1021703142e00c1505101140410000f0800300b0203172403e900c4003a031141195029100f0414581d0000d0b51000b03110b51103034803a0750348 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 251335242 1250 251333992 251334023
    0x7090f0f03170a0e1c061508030910030f06060f0207080601030503091012060e060111070308090607081201032103051915090515040b010219060902010e0315040c060e0607 75
    0x1aa44c007044904000e441d810429994880040340b011001d501505d0050031f10f5414400540050550012556640d020310b0500701900c2c01c0150030b0540c464410101a115034544840b03403210312a64000744074644812241a042ea100682010010b50040089400000c010004540c01008072841c20400700c480000130940e10100b035446080b040035090141e450003801040350101000480e0080754242c8540710042c10700d290b02075440016000091841c0d1050000e080d260034601c0142c0b44040c803c0c604182413034115000f88400741800d0f88240c0b000001c004481c03420701d440d1551030120841d030b0329051185180c000401c0c140c1008840d52b2803241527880c48001a507a140d00b400402900404000340498207211800700d60285003071402500c91490b2042c1c000c10707580000f805201619207003032451000f070f009881d00c0005003908402079061103810003241450342d82c103020b20002da8a8000080d00e2509080c20800c1c80e68a442c0c02090034001c40d1207501c01c0b0380c0d4a84040e140c00d154003c9408010300c03034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 251336492 1250 251335242 251335247
    0x30b130902040b06070503041e0e0403121518050a0e0312011a04061707050c07080f0f0a0309090207080403020a0308030403080a06050102031c02090a03050717070315050a1407090f0f03170a 83
    0xba50790181e000cae00f1540c41844100340d0f20180da1002c010b03c242e0140b080008600c2d10341c840303102c036204042101210100311400d014680c4c000340e501110f00760f0000ba0100c2d56603050b42c2181d2114138194a580f2403000140034202c40b43c500c00451440b04903d60341490b0402c078000c1c2c140011010391501070300940000400551282c0100c4404045810546010940c0c07015000d5507110310001c455014000c41a020b4074511001502c400c1c3c0a80654031000c107140f40002000080d0f00401d41601d10403c108404000b50326490a130700000e500c41ca0780c1c1f959901c1e1070300703004280d41c1d40a03065152650400703600b04410780e8000156014480c1c08540031010142e80c1d00329030020701c82d2412558000c4a0400000140000440c01d0f07000c4811041b00007a82861600036151a2035903070200410301ea404803e80c1891a80d10f03480701d40d1020b481e2400082c240202c9007120402001210504000b072444441172045c0090300c10110010040c54070100d03010740c210b03603a180c1d40c04d07060055896940004910907a0350391 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 251337742 1250 251336492 251336549
    0xd0807050a0618020f18130309030c0605030114040902060315030c040e0303011d012301021009061b020303090d030e1f09060515030c10030b130902040b0607050304 72
    0x268009010010107156a41c0c807120f2002c100342c00e030301c02d500c004d141307150760308068200c42c00480e980201391001c2c2c1e40d10006800e00c150034180940030440032500101c001030000c3c0b0341d24081d04240e1903090310396142041c54208140300101c0d150186042030610340c01a1a00400d40742c0200104c44010440503d440c0420b00c0c0c5806035000590007414280e404010300e0012008605031007071174041c187c103092040d032f80e6040f00d0420720903100b0300300e945071014007909100d007041090a10140305407051641c0c4142c0250a030f880c0001c059491958500d818200c0351070075218603118030f050740050750030340c50400005500c1f0b40d140b008044c14151100891700080e60180940b070466250742c0541030b411400d850200c4001c000e02d1108440c0761740b400000c40c0444003180e81003528400c00030000c10452800c0b509002075403800341644410b160b214883c00c6919078844440c08409004000300090705200c3e0300401c0182d071078030340805000300340800494001c03070004000c42d0151144a5a2102c8103068a818401c088 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 251338992 1250 251337742 251337763
    0xf020705030d05010e1312080a020417070f0501111209060c03040905090105011202030a30020c040b090402010c111c0312060803091809070506120717060d080705 71
    0x50000050585890416034840b40c1031714100b00c0000910740e504414224000c1440202a0a01c071603808400d0030984984041d41c1d200010041c05070406a841c2c0c10869491403d0b420000d0507008040e0501c0b6901c01c100100300148001d10300010350031b442a55258071006a841e0008440b9000995501c2640300c80044032421030268080366552aa1514044001d040c141c170a0990381d4242000080d461016590709440e0742e0b00213003d0503d20600d40c0c1d0340341004c1e0904045d4a080980d0250800b40f0180721200356682070555000707042c1d203808401c1000122924010f00303910601c40d03081404050303603111144491036603021070b200303106082800004100140e40782100650300c18000c0b0402c100360b4000f0150407001e0a40300207025040c1c0700c0352074984038001c4008494111803000481010a1020b900150700108107105561207251124081500359008003105005502c0c2141444003142d88409a041101c05d00e400404c03060408500040707032004145030141407408013064040c20f109003400040ca01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 251340242 1250 251338992 251339003
    0xc090315070801081f02090f030106142b1401020d060b070b060a05130b0a0302061911011a0d03050d090605150102010b060301120f140601050a09021306030f0207 71
    0x540d0600341403442032403401c440650000e0602c2c00000340710b400001d4030480301c9400c0b5a14001c08608221004001d4110484040e445102d0048661030b41d00c0030720640b0040c0c26580311110311081c01e101400204090020b812210180c0c8220401d1000490301c2c1c1c4005441e8004650041c03040740c01900c0c1e019000300c60381b4032801171500301d0000303401101400800700076102e0300148149a0b1217804014481c0c0152048503003040c500c00c854941c101080e48030710000f101c01469022925140d03004110140c0200030810b41c9032910403510600d254100034000c03007250090000788403441500ca40d6440c1c030f00c100e054090081750282031400805000310252000e82421242c208094141410000f000e41801d6600d000884c50740941008a544103002d90000220003902081c03844e4641450a002d05e0b50042c403c2d2410355007804d401000480782041c0c01c16010818000f001254105030070003000c08501c0c0e003d030744500e00c104030861005e1100492032003101c40c1400c000507041c041c00160b40280c03292030001081c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 251341492 1250 251340242 251340253
    0x70602030906190b1e04020c1f06050a080703030309031116030606050613030b0c040b07030305040c1d0412050c010e0708060a02030f0a0b0402070c090b01080c0a0e04050c0903 77
    0x161210000340b09846030002451071000c41d40300740e0380182202d0351400c00c142c125004143c1c3d50b44d000a913071180d0400c03200141c40145001c500c0400b540c10320601d03c40c0140301048100748142d01d100240604c1d80a0081211031281c0341c0d252511f01031351001075110090503d91210010401d1500400e20f4411401c089815140c08600314101109824904d0004843c110b20349000800c4608180c0d00b81c42131100b0306115031941ca419034640f240005001031000c10061420000491101c07106c8015050091080e2004145400c082c0380200389003100e5000559510070103040128946140190b0300c3d0007580110744401c08807a200e004035054810b1180c010007560800d200d6046400c1c000800c00704a0395410243d50b49515503100031401e0348400e5841d21601c4030603c0208441588613070040c517950b00c0c0103000600d00b913444d80e160385032220141e00c0300341600d585070300300c20301560800155680043c54a426520b485643d0402130300c0d10305000000390013541c7e00d03000222101c000f1b004031242034a00404991 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 251342742 1250 251341492 251341501
    0xa0b19060203030a05090d0207050f0307080a1415190f090206040f09050c04050604170c0a09020a030e0d0f0c02010903050a12021b06030103021e10050307020115240507060203 77
    0x25034940c419515840c440d45010b0000d50704640c04a08140301f06160345c0944a460300c2c1c0010400740a40148405505000303504000444c5201040a010005e00c2030010362059038034488022f0411492150441c0201c4a40d403c0281c0010000d00c0c0070749108154400145124007055020300600b13610720025000880001d0110b0400751018040c41102c0d130f8501d06100030b80c3e60002c80d01060046101d4950031a2081c8002d1000c850150a111001841c0d01c080310010301036080098000d42c110303840048210740c006021090307607906000f52620840c0c00d41c0201801b44107418020160801c2d91480f10030000011041b00441e0b228840c210300554001c012114a118142041040c2c08201c0780e590003d8415110a80f081d11410700382c0e100d04041c01019542141c2c070310740a00c0020b410507082400ca036210070060b0402070355040400f1103001540c0d41c56a840b031402001c0a801c603030300b0749400e10b10301e1130072803040001d0741002da44e4607043da0705c012a1200e2501284c0c401e4541d03000d84140100018008000c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 251343992 1250 251342742 251342747
    0x207020d0312060501031a01080c0d05010303030207020114090d0b0c0d0929010312030f0f021206011b0b19110a020a02090a05040506130c1502010f14010602060a0b1906 74
    0x7600c2050080800f08400c654410040d42201c0c40c3e48900440e00c0550344450315591302900d603c5038441c11954050b4a05038840d80300004072030003600b003200420382c00b185003025960300c80b030420b840605001d441d9250412120000d00d55001c0004018000018071300000c40032513813102601c40b01c40941100b40604480c5261480222107080104400e03403104c844806000e100305003105d41240e801a080380540c209406049000d01a22242e00b4002038484500e92007100d12031000b400840c0300d00080d030007142408000107028111040d604800c20880e04e04c03070004034038103003400ea82056110314044078100c00020b40c03e0151400d5113100322802e1011411001281d00400d1041403a4800c94040f01c0e00e5440b80c04200803200d00342c0340a40298461300000c0e1800f0030301000d090f5814050942c03c0c0c5440d03a210750b0b8001c0203208100ca20300627519001a5032648407c1d014000c400b01100b0b003072401542c10f000f0025070f183e000400c1c0481458960040300d8407078075000b9070407a414a40c9100c0c15140d94460001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 251345242 1250 251343992 251344007
    0x302040f2306120703091106280305010b0a1110020c03030711010203040f020d020307050a270207020d12030207060c0e03100920120303090a140102040b0a03020d0207020d03 76
    0x9148180d4020076008201d8680788046480120381c00103101d1460302c038800d0803070040014001c2110a1000203010100a40e90b42002c0c228242c1c0c400b00f02003c824840c010b80050220740d004003030a150401c40140040e01808c800e07540710345040c1c5005440c020040124901d019900c0f40c258401e140f000079182401000403000b10303c200705039100c0c100304c41c030036610050803403100300e43c080d2452113003a0031800186010f0030506405070004045855842e152800680c20782c1c0700740d22034002c01805050b0b10310068460740c1c150000605500c0218101100c540200d2503010307006a00610b0011140c010101035800399050701c4110780c0000c0100000311402d9400340c002c0b002c07c207500788a0321500341541c580000c640140e014456201810440d291030300d040c00044125180850384e03004000000452041d94200084c500c01c0115600400d014105e505011003800d200103856000d69004110030f000746040b0004440d1001d503240b40069464501d401c0400090082200c000d6000fa1100980c40915900992 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 251346492 1250 251345242 251345279
    0x4050a0303050712050418110904050f07030e1501060818030a05040e150a0e070c08070605060a15050906030601030605030d02070603050c0721020a0f050a03020d0305010806160302040f 81
    0x854003450202a00a51780303409144a6890180000b1200199a442980028201605c0f541c807107030030f00c2d030114006016144121040c4c090047c440b0b00f0015426814060341174581008400b81103200040c101d00c0010250500904e0107011a41000c11070003201803076130100d111b15080c181c9444103440d1900a0042c4d000f4480d24840003031401c0410448401c200c0c0d4410700302c0004109401c220b10b4180032070b8800400400613420310048075007034008180c065000300745092188030300080c949882401c2103001c06030b45d0010220602d08091036011240c004044441d605801c1740e55a40701e56880d80103c010708140e411003a05409089841d0017824ac00040000c1a030b00300b034a050216076100c07400e113901c5d401000e4020f0107400381403204079000354500881c41142006481520003001043d00e54941c50602036000301c4d500c1e0b214044a030281507060184d0360300d00b416841c0174440e5501d80240240e44000140000c40c031407039401d60f59034205010350f0480d4010100d04084e4500c2503920000c011904500301e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 251347742 1250 251346492 251346503
    0xf0708090f060d2405030a0b040206090d050f06070f0503040b060d060c030c030b06190503040c050303190201230103080901020a06050a020918010b030c0705120d020702010e1207170304050a03030507 87
    0x1307840425000151680320a48030f010340104091010303512a84078030340c0c003d0000d9800080402ca041421740300c04041e4a0224000c00041c0001c0400c040e016150100080c051001c0110132026021096840011640c1054108440e5040e0f5141c0b0000076042010387d62004055524001c4034515481d01500320180500071a1010042010342c5d00501c40f580c40b5085004040c0c0182549410074507005401568200317005210018a190300c44001c00d00c0c55102030440400d003181d000c504c0b99010b509000b03018080780c030320030310502d841c0599209004401060000521414004c10340002a0340308025211116030406d1040c0036600744090800c009500c00c105440c0501d081004542c8451032668940d03048036142d5090511316580c00000707a1251308414011142401020381c00104080c1c080c2c041c0002c3c3d108400c005940d15a584005450090f6980c251400340c0d0788486c41004d01c40000c81d411003220b00c92280040c0900d00b46034581d0a503c030311f400680c3d000010b0040030080c56442005406001d100c1d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 251348992 1250 251347742 251347781
    0xd0e101a010807080109021303021206100b0903120705030c06040308100504091205070201050c1510090e0718020c0118030201060807210c031a1006050f0708090f060d 73
    0x200c0c01198444030403100b80700407a80d00c10040096924a60050401c8811071a22078000341c1c0303e078000f910182681c1d2910800760302c000b00340034a0010110703080005200a014184c686400034011a841d00245d60900103040d1002c10070406010041c000c69400344050810344400d4034162401801540f019510300c0104d01a242000c90241814842c0c10080c64002c190b08070717560f11340101118541d02c116030032410004d0911425400c10010042403128819030100d8183e180b810001c41c42c8818101e6022204850416040c038103a060041200400d0303a040b1b1410030110300c0f220300980081c0c0701d00c1180540942ca00361042d007002120700304004045110317500a000240ea98400582d488610380203070004905030a81c07540c800d407800190b5a003600d100303456100f040340c0d0341e0311005a160201100a00c0e4540d4000c01c0110011480105501901c014240a410101ca031403980020b8014448010210740001541c884603995103608400f00680c010082541c0c1c400d5101964003600981480b510681c081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 251350242 1250 251348992 251349041
    0x504030f030c0c11011809020a0e0a030807030e04110703031d0102040e011e090e01022817040f051f050a0c050708031506040f08060901060303080c0d0e10 68
    0x20780a0039905007030703e03074480b5101002034440d80345800c200c1541c10f0611001c05041810404c401d10014002e1109640050b101c1518030710141c04260740440c0f562050f0140c8005000090b030300c006584000703030940741c42d6204845000215008102e55450340303035a0900401c08804060b0305800401e50540d00107a0341003800c01640b400c900343e0107640988040d40800d40018000c14100440ca000c5c40542c10076211141b0b5600c14900b0110707102108141c3e4140d400140c84010266102c0b000030030041c03400102040b5144030f082c010141401e2202a22000e0600ca002c030f001e004034000e00078030031504007054815090306808088098403c1c100c105951900385000240740b039070740f8852450003a100e070300e0301d5280000599500e641c980c801041d594142182d180352480f50b448100240c0041c24012102180843c10014018548400101800100c2e070404206100007540310940341c0e00038940075031701c50311076200140000150038510101c54091084a011010090040d04083c941080c0b45039010184081c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 251351492 1250 251350242 251350247
    0xa02040b0f090105010f05161124030c07050f0f0a020109080a0819050d1a0a0806060f0d0206040b030c0304020907022b0c020a080f0105010b1c0c120f0504030f 70
    0x14841c0c000c1c2d4000d081400420440d4021720422521154030704e000f5140149003210310360880349203181030320120301408641c503560910142c4114580350b5042e80042c0c40410102225251000600f0041d01d20004586a420044100070f11a100700815060b2000c800c030304000d83e82c1c0c90b9003a5006a0000d401141d0005030b0b4600461000031291300301ea0b0301d51510404440880e40301400f0740030340003040020030070320700603a1841c880d120b2400002d4007411600c4144100b040210551034002c02030760740010f03080c05103650f41c1e0032503082c0103502030f101c0807044240b500000710580195071169085640000070054010302800046229900c2125100010b0310b1b18241207030742d01d020f00c481c0d002c000003c92070f942d40a180fa609003140804d0620f00000603455681c0895401300c8a507005c040c866004071001d281c600e01c00e0050501425141d119681070541050b0140000d00161440c1562641c2d2a54000141c0c2e00c1403a062030700034404071062012101b41d8860b04014041164150001600075070400303001807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 251352742 1250 251351492 251351509
    0x1030b0f010f1a09011707080402130209010c12051b010626030306091807030f020f0d0b1b1b0c01230d0b040b09070f020c0303030c2b020c0a02040b 65
    0x20000e0f0b441460104040000c00800d601404102e4180101c01b00c1070b007020090130440901c030340603c1d9200f40b0241014418042e841c1c1464460041c21401405010b0040c0d0303011020b00d440b1504005910840b44d047d250a0710b07075102c4c0a0540d101c40f144442c507120140782c150020021122050644081c0c6040b01c000e050700320801a900300c03035581080001c0b0741d4501c0c0000520b0b42141038140b6450143d00500040e078904400360303000710b490719004c0a521080d440e0401400480e04404e59800310404240e0303487d0128040001d0540413032000120503445040005800d03103080340d4501e039017101c044260581d0150303100004034500c0d00180e00d00200c030f00c0c1d020440c0d1a00b100186c0400700a03003040c2415803c0405012544001038010360346a0b8042003a5840184160203548540c44a01c03003c900940000d007440c41c200d4420b80258010000c2c0251682c60000b105c5520f82200c1c0c00c10091060710482004c405551107844d2841c600204140d2015403010a0a001c01e80c070888003042803c0e50b8005204112 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 251353992 1250 251352742 251352749
    0x19080106090f0e060607020a05041b12111909050315090d0e0102030406230703080105030d030207020915031e0f100603020a0501080709030803010e100e040f120c020901030b0f010f 79
    0xc103d480403030300504103400030f04440d505c01010f051401c1d44030f4000c5401c880d40e180c01c0031035078514403031100501a0854440501041140c5050011103a07022252a40c1d2080c00c0c085070000d20942a034245003441000c41c00060440101a245401410740c0c41028600741681c0c1c00f1500e000301040c1280c200e02444038071440b414182c000d142418034000d002c1e1401500c41300150324194100a02142224412000303101e4684252510152035041c101410f1034141c03400010b40501d4410030a65000d40e0f21940155400345007105080f0100b100d002c080381c14098801c0d6551301c0d0100c8540e4100ca40d04001c26a594007503c840c048440081702d00c00300c0c00a03680b80c0c0c8806500706007500d000703203c81e5118803025540010a81030044d0055030b2030f074911200d42e0090380034010500300f50040c08402010301001034006c250012080e0842c0c01e0580f03800c4100b0310a60001007122a500322a80288c900521468080640042620740c896a690410401c82d400440d02802c03d8010b0500225042c0320201ca06402d9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 251355242 1250 251353992 251354009
    0xb210402090414010917070606050105040f0b03041703090a050c01020d0804120203041e030512120f0603010e01020f040812190302030603030d090303090b07110c041119080106090f 79
    0x25450740c0d00d0f0301480c000324964218482d500c814828021407180c4104407825200042d20710b6860703040d07003040421956650041070401200708410444020313100400c00540382484000380d1b03251120f00c0d200078105203420103580410804010440e00000210740032107414051419030b04040068001242c581440c10001d4000c070352400301040102d42040c900b01c2c2c3c1c9030b405004607490941c81c0c0e021701d500c05a405c05d40c0f81060210060a00402c41c040c03014a003020191040039080ca4004089003400c00c9c0c0c0200f100714201000d6001030000d03a0f01750800d655201c1c2c044001c550381d0034a01c890a40d541d000d802600c0580c4548901c0210380038040d4200d500312402c00340d02d03540310290300404801a50000e0b0269905100500407000d0142441c46030780f034a1417107910005102c171414901440a190000c0c002d009014404d01041000007002c20a403885500032540054140082e8034101c0c0a400f400c0c00c646520501040044606604805030358180c071255154032400a5949440c405c6400d481d0084401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 251356492 1250 251355242 251355259
    0x1205060f03070902030604140408130801020a0c021c02150706060510081f030b3102011e0302130b03010302150a0c030305060303071401020415020f060601200105010b210402 76
    0x542c695031380c091500b10300c00030b00c04100c130881800b1801169100b5241600c40890005030403501c11640080c880c01860750324000e600709500b607000680f1884178400003a0088102d1410340c100104515080714031298000c01251075070b01c240c00c001583d50043c8500303e5000d031800300007054500c4d10010034014601185d48510070340e030714080e410207045c1040314540610100840d01000049120302c82c00d1040c01a4540750911132354540766080400810040d440c203880112500304050307640600e1103640c1c500c051040c0000200088000ca00901c0b50310058101800c075914081f42e1070b5142e10086040302c0c001c807510a00c600c05060915902d11031040e9a8011410441e02000000d02980025611000050949090031035a4030f46c07041140134a03290441c1654001000e200c1007442d206500c0c10100035100801540500840007a5608809019503041c0180d10f003409015414111450105294580c000d124030350b91171406e44996045900303602060740c4d007580540c00c15034080746110b01c19600200b6000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 251357742 1250 251356492 251356499
    0x10c0203030a1512060905120307021005010e100b0307111903090b0a0801030b0612011a0319030206150a0f0e01060807030b33042c040507140102030d0c1205060f0307 73
    0xd00034400c030784040324140540070341c1c140c0c400d82c944061842b0310744135009418040e9484649504842e030581094030400480c0040c44030701d00b4501c2010055034003918110750399449401c0d065074040500c140072201841b03021030802c0000d4498601d550302c90b00c07a449502546407118040780785070084190503400507803140e004102054001264517081900601040190018071802e1425a1440200c000104d00b00074020405414104561095240b0501d40c4143e959010b50b4000e40720031000c0d2010141a040e0b5407240480d1b40d9102c1c8880040400840d28048241c0e20092242e040209100d400046420f0784000b0300040e00030b0007603c143c0c00005150302e00004030718042d11049000301e020070310381e0141114840050050b000040000d4000f0f10302d40701c0070003161240d140100b00c014190001661080c0240b00001d000003404000765800d440b4100c0b048800000100d2641c029803507000c0c2000d04101038040d06036040070344084500701000c000e00896440da010302c003168100340038494041d4032030b03542003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 251358992 1250 251357742 251357753
    0xc030303130c030b070c0507050901060e0427031707030911010c030225080c040b030d0f050c0304090605030c03011a150c070605030106080f100e0c0c010c0203030a1512 74
    0x8403203080c41052010b001e2034503130b100d80300a0101102c4410105511054080c00d105042100340d00034201103c0451282d81410002000d505c9403600f02409203440c0c100d03141ca0452042c04080410f00d107454200d81201031402c000706525205000d84005160b041c02092805100c1e0184101c0c1540214285900651040c0110381503005c0f070078290118040e103020301c101903900c450840d03404502003900320403180c1130507103a50900d81e11039261485280380c41240130042e01c4c003180d1040644114142104031903000d4405541901c47c0c4014484c0c140000100450190261351000069590aa00b116040e0b141c460906003207460000c0000710003d40c0003c002c46629105030203020400b00340d034a040c00c04405416503850980c05030403200102d400840144107042d2700420039540a29081308803501030070700c180e0340380e030401881c000c00b1007801e80c0e01d00050007015030408070313403e030017101c0002c00c20100c0e2000000e4070303500192171030701005003080c1002c4240b400580101081e5684600e40030005040f0b6580c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 251360242 1250 251358992 251359021
    0x30503030601120b0901080705191a03060111010e031b0c010c110d050715020c012a17220503030a0e0409050a0b040b010509060405010b0a0c05030405150d0e0c030303 73
    0x52212500c0da1310401664550b0f034070041c000c001080050007183d05013810031500f614160a6850301e901c038100104107101c400541240c0d048400020326640f03461b06401210191004200c0103103e602b481011896411300000400403400706600d180c90301845902d1498540d030340c4c40d1420703002074901d4800c00c021601c140e01318159000c000302040b020248a5540e14284103481d44206181e405a04030100101d406028400042e40c0919000003500400e0074070203903186ea1100d4845d0740c440911102c0041240070800e1a00d0480c488010644509003010300c408000c100c80c03a201300110740c0c2c150000e02d0341000800e4030280c0240781c4810946003041401d03c4010221030a01307482c030f13108140340c9c40003203103410030b407203000f940101b50310a4150f04190034407448100107001140507510742030040041100300c42c20785640140314030304030901c240301d420300310316600681d0031013030740000e05001001c0c420503400d0003007201c0340c041c14007031041101c4004540d4450386503001040c5c047e00b0802c0082e85030801c0317520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 251361492 1250 251360242 251360267
    0xf0603060703020412030f031b171f0b070602090409060b03010605100e0111070504110309010507090e010e15130b03060c03010e040f0c091506020f0a022b062310030503030601 77
    0x100000d080340c151003c0004242e409e2103035400302d21102034002e089050301410a91003051240f050480090940c0082c0c1580c10350b114444441c980400c0100400880340c04494147d48e0082c02405020300905180c4000c0c200d0881daa0700c650320740403000925003025500c56083d182da5484004001c03460500654440c00301c1c1c116a0420700980c40d0225031980d07a4030a02d0882150400c841c1d444e460301c0d13842c20b402c4900142004040c0700000e401000320b0503003600c03620f0541d03e010076140b94070303102c0700c0100038603800c6114499400030a4056100d0341040782d034440c8104610031812a003058541e84040c40c00f40c4800e000e5200265401c00004001c1502d05850301d0625124003210340b1107942e900c580108603000c1c01d0140b49019041c640401078983e04200c0e40c1e240004c044060184101035030300041010f0000802c4032a01c0c0005154020421307451103801d42c0d4135410500034061f0030206944841558160f0520152207103900000c98403045902e1070103815241d12400451441d120800190346400c841135 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 251362742 1250 251361492 251361497
    0x302040308071208071b030f030912030509010f0605060405310605090c120615090d080a090b04080709090f0f050d120213030f1103060f0603060703020412030f 70
    0x80000010141002040b506000300441a05030702103003401040d02e1400392000301003007400081c01122100d9401d0713030003a181e45400c28070103401c089a000e6018040501c40a000007105a0100112036050341200c2c5c4524800c0e4002c02c44c0c0d4146041042c22075180d03010703407600b01c40700780003c2c455400c2423502c00c07210300c603035014610003c858881200d1007201d690301d10525950f2185010080d50400b000225041a00e440000703007030a40c0143c0c4c02c4a00d81c00100414860300b01c0892487c01b80380c45108a81091102800308101d604050400341e02c5603111034104000942c00e002c0008403a1020021394040d06d8080c405406e04c140b504c1c4245001c2c1c4601c990550303600d1303c04094000042e9086110020705886000075113614815018050800c07110001da100607140100942410315801301810419294408220150003207907040008035100c1e402c2c0b1094140c4a1a41070222414030440d00f244684821402c4401a03918002c0c214241d0140d44190380ea1900f41c0c250200c000790160198904c4240c43d031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 251363992 1250 251362742 251362747
    0x51e0304090b04090c080109021c02100c0206160b01051906020304030602070218012c15011101140106051305040207020f041d032b050f0613020909010b090102060702150c07030302 79
    0xc1c5c45943c410109980000c0280c1e644451010441c2400c003011014a9030040c10344030025440e07008603810040301c11507003081100d014a20000c643d201419115405e0404101050075022450481c0707003100d0a014003803003059110090461116020800c1c2c092700d0f0305502650401d4515a01c1070043d4010407000c07030380841203c03400950582c0d07000e042d6008261400c41054041c0c2031010b164960010780400e88803c2003c281004000d24003055021200142031805c0d8513100d044412050042807110040b10049284600010f0305a501c00044e01603508040e2601105c50750700c104220403449901170007034002c1000845c030442c62505a004983c109000030b6203546024038044013a003582d000743d0394103800c61506d0030a0310580e2044100c0c1c2804402c9a5004c00207030800680000800078003d1516119440e8a1400f503034804540d019074040101c06408444656140c81004117180c10000e030047c010b104090018400520010341d400d004210943c1810039601c4e07285d1500785a81c000d55041d41459001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 251365242 1250 251363992 251364011
    0x30c240307120f0b040507030504020a051021140907030b0f06120f030a0e0a0b0403020409140f06191b0f05130f051206070819060e0a0603051e0304090b04 68
    0x15004a40380f01c001c1078400a548003610003000200e4401034565010185400308010051b01c039800b200c01038640c21917958023a00d03400c03d000c407001c0c88041c50a00c440180400b0810000419810020140501503840c1c84d4030760300c03445102d648040c0c1344406413011010700003054210301200c0c403103504810050600d0500e035040d0100c4c680341581d081c1e401e4490782c1c000207041c4510b03640310302182500a02121590b029038500b1400312103d00442c0006031003159605144d0007001043c40c1a0008003041030b0507114034014801a15498513011205003480c0201902e000c20381c003809108100f0b5088588088600004000340100c40452010120009108003000940300e10709800712214001c0405145000c0080e0401c2c040c007200380000d40b09000d1542c0312406000101d5004201c0a42c085882d48000740e00589030200300000c0c20081d4080c0410940000900c00065100d0704810290b074084c00c21140e281048002e500124503045221080301d420900043c03003440d00a410031401c41c04020004503010f102c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 251366492 1250 251365242 251365277
    0x5030607052a01021b010501090603111018030b01060f0903260f0c012003040f1b0e070f171306020d0f020f040303020115050a030f0606031b05030c240307 68
    0x3045004502c040601242c004417075509004440c00b50407011400c0c0452451b6941c5c495000402031019441010082e0500801c18460120003c031000c40f140b03403001080c0d0740e080c03003501c4460a009420000b910440c10401d141c1c010307100744013202d601031014440c0440810412891050380c0340907508030781041120a0042902c603000d13002c4030440000006038250503000c54581d5140e01c2c54070748042ca105004000c081030580100d071805a400201d00e1031440502c4450b566a083c090b0817080b203d441080a2003c0c0d03070350280400c3c0f002d43c5191280c00161000d68101c90b1410707401c0707401c03551204810f842a00016055000703000038000c50000800d0400034281c0c403000f660071a82201081200100c1c080041c503a090140380a01c00751600d00018050401c030101d403201d003040c04003030044801a58503100300400741d400b10300110f42107140072507518a103080d02c0024003410b10446110748243e03080052503281c43d0015103c540c164002c50704ca040c0641440e44810340000b010f0005004984006900a50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 251367742 1250 251366492 251366497
    0x60405010305040204151d100f0614120c0a2304090911030a1a0f0606030403030c180608011e0b03040201180329070f0c02040b0f0a12050705030607052a0102 69
    0x400148803c0101f4444110b115074400186401040c0d24000010010300982d540700c0e070300b550031915000554a140ca51000c2881c07060344440782c484100d00381042081c0114102401800819948011210809200301d00700030440181c030381c040c64000c010810442c0c06990201441900c140c00000d150482c0c1c900081c100b0340b94880580d444c034800b05465403201120480a94400540110701500b800c0540200c0c1441c0402800182499039030f040303200d0310a02917a030308405142881074000c10b451f21900c00401d15a0284901c5100e150071250000d40c1c80c4158805405685004071990b09545d26500115078600110707401140000204002001180000d6003203e000304104a00191200350b001131005900d40003000740c1c0070814644078003901d40c2e5100070382c0f00e40341d0380440700445d480d0071715400034214080c01c0b40ca056005180000000e80d5111f0354182200e194080c5003654001542d5400b0300d07131103960031506c5c1400601c0801c01c100d03c076030084645540e803124010412845070010500c01c0e0880c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 251368992 1250 251367742 251367749
    0x3060f010305010b090708010311010c05160305010b0a030302210c060106080f060108070f030c0e03010e070806090601061709070506160b07110d0e06070204060b180402040506040501030504020415 86
    0x8a10140140284a024042c1600720300090344d149885140c43c0701c0040c00041c06020040c460714400c20ba02502c0e82c03081e01542a0381d600841135440c181c0203031310280014105840304880c65401d140d50102d441c41d04540c1241200c2d015000f400428252602401100e01448074004030386805008414844104207c803c1c080e02071130302c1d600303032038100499400c030320704c00040045041002030802c000743e00d030f0b010401200b04402c1d41000314ad0240000015158078030020170541d090342c60b140703c06c0240100090710344211442001a180252504215540c0782d00c03003405003034003081000700002e070719842c3d030900c0c594400c01107016284241c0e01c1c0d90000c7c0465015440141400c80c028a0f0002400b1010305a59000805801c1020b440c070503070314443d43c030b4000840e0030310240510320b0381d83d1031180c981c20120381090b50300400800c12140c4036800f145654000c550464080c1a002c21412098102031003201d040c3ca42c000d00450406241000440103054002c05c200e0300240c81d8011702005030418983c81014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 251370242 1250 251368992 251369011
    0x40303022406010f1206051f03051b0720040911040e06070e0f01020a0203100501030b0114010e04051e270303060609092806060801060509012109020306 67
    0x410990404180a0300190741140035054285401d00245a070071030f0303003440310b030348107082021103883d204107407800030405a0720080e0007043c114110107034a000b410f8144210075041d2000c01c09515212844600c4900e1006400030400342008040041814a0800b50b1000541a0765480341740881012900751002ca400403600200e901c06401c003d4500360140364032503607000740108201c0c60a250010400e0440700c48090240243c0c000000752a4400d201e007582c0c90350094103c421240c0764900201c018002440150b454404800010540800b6008a2003c0c804141d480c0640c200c201e000300801844050460820024401461032001c1c0405000920625087c401410b60040c0314413041070076020035000107400d8008008000a87d510903042c1d44455005442c009516074901540c1007288641c0f5001d60100700c6911003000d080202c640090060710041d5030760b201c550340e03106000d403200c0c003982181c0c5012440380f00040c0d08208481c030f422680401140c0b004180200740740c010a041120948070b0402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 251371492 1250 251370242 251370253
    0xd05010c020d0f0e0d14150c030402010906020a05030306011202042408060f0a03081605030c061512100c0e12101107081914040905091c0e1c0804030302 67
    0xc0701c0d0002c0b12403c5118143c107044003207510410001d003418007040001807010820751160003c4290030011a0b117070044075030310311183e814803018880c0940c05c1100e04900003180307440c002c07942c0c0f44081000d80010780e2002c0114115114403005444003400d400c0c198031000d50038040005e140d490b040c410520404504428009022480402419001c0090445001c0d610388008030f205501e03007a2850080300d1b00090100c2e21000868044600c41e0001e0314050020710010880c00700c0c2c0351001c2038280c029440c454907100c03102d00c000c081c030111b480080400f14458004c0c0f10000b0300c0000700c1d0807024441c0f9076031400035140c6008500103108016010200c1d861640918400d51002042d446034511103140480d070541841490707555280603101c2c16410704c101c1202c07080c0c01400580241e44034803440c00c41c10f101c503444545800e1004010003003154414071520803078114200d40e0400b81542c0419003070556445c1c01d0b0344050002d111400802a034811880b18410142002168034000070f400618443d81c080d10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 251372742 1250 251371492 251371513
    0x203070c0b07140613060209030f061f090902010e06030601030e06010b070308090708071203140f0903011a0a1703130e09070f0506030103020418050a030201051f03110f0d05010c02 79
    0x543c83c2102004000040e0b2001c003d00102d0018113050442076503000d40056aa00c0701070000c6030400420390855542c3d8403601e0140003084281c21400c9004d448144075006403d6551070390f580540c2c3c0b070504041d0115084e042e9000660500e14029644450103041c0400c0c03084403402c00918000d400d9100c1c5e000780e00c2c00b10318030080603803140d642d0350030407000e0b00200482ca09154070301d52114003034814160030311080101c007001c140c000c00c41c804483d01c0c0c4840907038699000c0b512410b4141e0101e41c0b014402d5103002101c032409161142e281010300c8002d002004142d043c25034081c440f11800b020525203210601c0981d8443d0344101c03080f000782040c0c820b030305247d091984441c0c0c170f811865008244011140345c0c0500403070f218101901d044135011103010500e4801407820b800d101200403000f038000d008100381041803680540100c0d01801c041c0500302500e105030700c8180d0001800d400010280c1c11023113410b6640b890301003107507850031600504038100f090710307540c46c5030031150420400000350304040210b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 251373992 1250 251372742 251372753
    0x51804021809011d0703020604260303010f0603060b0a080c03190504050307030912030c150f02194a0a150f0f020d0f03020c0a030c0c050301150909030203070c0b07 72
    0x80c28a44c0c1200300a10206044d94005485405030740910401d0b00c4015484000350072814016400c11049241600e17942e5860700c844200d401c0700341c003400307011030306001d0700250984101049a11511443d0782c0c0840507114940b0b940c0301540040c203100c6031403440148080c00c0801910949010b0351042000f1a581d040c1c525000e00b0081d41548141e4840340010184000300360000c401c1d00b071166000102c1085008400c0e0744800402000305a01841c030b20124003002c4100b024101800000c005848102c000440b01824071401c100306849401588a42c00c074589241a402c00c1c1041c04810b420a000030702200e0b8004144020300c558400f0034034881c10036130301a01a40003074540b4a00172051900c101d10112003035020f555a0561807240381088103031956851440d12a038103a0304600800c5042e12030b1165a8103000b0b00100d007403001a20b40b24203012000899180507c580311320f01840c3d04042c0412450160003000808480710305505600041059100280400000401905410b003480703880700c00c5824503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 251375242 1250 251373992 251374031
    0x90406060c02120102070506220c06110c030105060a0b030406020d0e03040905070309030c030e03150106020d180311090a021e04140406060e190b0307020c1002060105180402180901 79
    0x14951307910400c0300c0000f0440226500f6807000a140d10300c060089415400c01e480d040c00b0380040d00b5641e0303600000c5080c66100714074042d2982e0300030466450f64108801c1608807003040d81c090340e1220260b0b4003040b4541206000c2c55106000e1540181040682840102514040102e05216400002c0c00740014001d40c820107401034401c0c40d003085000000c2c1c2e400341507164520380103814400100c00d508080d03130701040041405280581c580b10556902c1002035640d00341c500c07007400401c040501244080c40307a06011400c80c2c4d00448042d0442420760180100900003170148002c4940800201d981d900102601c10040d13214a20305aa6643c40c103103c8e0f202c40b82010100038480d5062030420802c40750301060706855040212800d0900e4100c00d98070500c008595800400e01030404420000f81c1360300481d401da4502000e48021082c0305600d04205e85032242402030680c0301003c180c1ca9080b068080541c180d03c21b101402641400c0f01c16545a0400c1c039040718204080d80d11b50b03c141714820b8440c1072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 251376492 1250 251375242 251375269
    0x405091e09150406270305040503070608060310050619030506060114130501050307020c0301090b0403170c1815030a05010611030901020a17160c1d0613090503090406060c02 76
    0x1070407010300b80d806010301a4601402c054030301c6840f503001d40044100100041c400d02c40080022411964501c0d01030899042441440d1181c0150340d00091a64050304006100b01d400a014001c1020151907a900510f00900301c03e4124410746500480711614900020107140101d00030030003454107030001040c2c0c81005120780c02c00a0b00b48545a40d80e190241c0450a845003400c11030381301d40d10984101d280000310260998151b00b008000414804040d50840c0940d01964815007108609504241844002d030740c0c4002e200c0c0c0400120002c4404d8000e1901200d000820700c0e800c16000c40c1d40540320750400d403140101326640d4401007002513005812a881c40303201c00b02441c00c3c407501d000041d468089151000c1c0c07030b0842e6030464030b00c00740c500004c5660724555103176000b0b80c240d07590503d25080d0700c1078090740c810ba60b94580d88024011008030b403144980002070028141501c000f44101c081c0c04c3c4407004680344d1100b4404c0034110b68032401100c002d03080a0380d80c130300340d549503004201c0750b00007181c6c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 251377742 1250 251376492 251376511
    0x2030907051005032502190203100218180c0712090e0405030c010b01020c150f0c010606110d0302120c070c030c120201180f1205070b0a0c05101406010309080405091e 73
    0x12244c0070800e80111f85c0003004031101c08081800c80260000c01d0402014401054007980f0000c0c0300613050854100f00e00400905840900c3d05050040b50588423120646501c00d500c0014400500050f505008000511019280c00130110341c1d500001c1c25807100c1610201c4407900041880020140240f00d4040171640901c014451024500085000700400c48403400e04100001500b440d40c840c2c010449040d855640e000304609555000b008100f18403284209510307008401d00c544a85100340242d42c00131008940c0e800079511807000e000c020b940018400c544d0319414100c00400718902a10140050014112031019060940700050200c00748901c1030040241d40b1400b44580c0e108020000280c40c100d402c440388000c03040c207100e85010b50b281d120443c200c07000074100b403150354008440d0041e00d10507412107a02203100c0440509030b0780d947c4640307c0c0860386400040c206600c0b230341050f41d940d40505005443e2507103603030205000710400c41d07603a1120741c0620300003112407140800165000d02c2a031b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 251378992 1250 251377742 251377801
    0x12120603010e0a20010203090a06090302190e0a0207020d0209090d02160806010501180f0816080c010f05090a0906080c01180e04030f030e0607090e06010e030307060203090705100503 80
    0x40d912a03800749180c0c0891351010041498204041c5d000300100d81c0e8803000108521303001075654400816045032408128042c3e41c042c09401075a00e1407059400079105c60102d555410f40d0b0314480e58000350420fa0b42641d01039074405100003d070b00c860320300500400b15180030b0000c0346607610010b403620b003414000c1d02d007110b5120b600300902d61020446e1415038400346410301c0b20360701140090380758402a80256590a0404600048001d00003913851039005600040510155032072070b1041d01c0745510b010603030219030540b400c0f8202c80c1c400c0f0014503c0d10720081101c68400c0d11a1184000c4400e9608004a07903401803035418107942e080041c002c80c224040c4000c540b2142854190402140050300081c2400020740380c1c0d24555003c1e400890201d00f100084910520705140010030013452803040a064002c2600484c02c154481c80c80380b0210000640110b00d413a41641d603240095100400c0c50025000703001020555030740e0f407a40103028001c1a42d07141e480f41440403000c6820402c01e502c01c60481d414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 251380242 1250 251378992 251379013
    0x606020f030d05060109080f010c0206060f0f0d08130909060e0304060c080a05040b030f1e070207030807020f031c021902010c20030102130f050f150c12120603010e 72
    0x41100c1c00582a480e003c140d80e101c03200143c1e11200d0345d070044581400745650030303901d441c415440060000080d5003110401c2d00c03070724240700d55820341000058100440500c1c00a0504180794110402441400410716054111060f51120902d541146000d82e4503001c80d8030601c012170150300354460304000690320741031130201c0c05005d04105000c000e00746100070814035503a41c069025507005001c1d05100b40d0781ca10b0712020307500b0750301d8044407140221020141080381700000b05101c50f21a000c070b500100f07240c900b10346521000b50050351040342c0c000f451420021054a0901c04550030020070030f92030802d040c1d2194041d040c6050401018100c07a09c0076006400360784e0110080405a40003c040000c21010103101c240700140510603640542c00069005102c1c2004c11042049a4159400c03192407901c403c100151144104d281d80e5110111200b9108513101046c018125007a6541c12113080c1c1d0080794040301c0540000f1000440b1100d210b003081010305080c082d80b41c1d05100e00b400b0780300c075221 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 251381492 1250 251380242 251380273
    0x140402090a0e04030c1b1809031b0f210908031303020616061409071a0406050c10180b06040902031e010b09010f060e0607050d05070c09050f040501060602 68
    0x480c1c401c02c103480104601203424540146500d841045c2c00810040005810b80c4400b40100c1e414402c2200a8502c215014024490361150900165240c1d0701c8511210350044084803415070500b050350800c444003102000079030307603000e501130b200728030038600e01211660207003d014103640e5844003415406c20421181c0c845c2441000d0b0041c1c0b0350465a040d15008845981c000007200d040c8001c01d010316020901d0444d20030756141c00d1041c00140121901d141c1c0340c03240e4040c810710703001e10001c00f01c0c000c0c002800b10b01d001e00041c0c400400784408031b80c00c0d08070204900c1c041e41e00b420480ca15132a450708400c0140b0a854041d49d500001c252028408040c07207a000c81ea58846000d400b80700d01c00741c8807402150600a406c090a0710340003e00c41d070f401d96192407a294100000e4414400852441c01a075100c40c20413a081d54066600100504109a241c03603041d0341a5000b844200d540b000c845401090b490181c0c0308850280301d803048400c41c42c1c9000e29080d42110b0072608510150750020801048000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 251382742 1250 251381492 251381509
    0x6090f0706021c0f0e130603050111040e0c0901050c030d090c060801060c0605091606020c0f0f0112051009180605010609050a0b090307080d0503070e100504091805120414040209 78
    0x383d0b140c81802004540d104a54446000802c42d5024004203410a00d245294028209490184000b04111048028134198038422480b035556403020307890002e00c0350940c44000c2d000c6a50706042c154901040c10749076609680c03103074540410b00b40d900d03603512003804450b124180203890f003800d02076003650401402030812811080020907803511003001071010001402800000c946d00c0c0c1c02964010b40f42ea002944400e035240216000c4d000d09019503046180030203040a880006840b00c3c520703108000e5600c00035000042c8504240704034005d001499081d14070410340704008040d00e00009103010701c0c01006551041c0c2c0f114040081300c80e0140415950b0600b5081266650010b03c1d40d0b4010700f402190a04c1a16842200c143c0145010903201c541c0200c0194030440d10342d542c2510040080040140042d240d1900a001404c1844140800480e542c442c00c103030300c484040d508404d01c05980d0703545404107001001c0a85032010400300710620f1040000840440215001e505001e044d201180324034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 251383992 1250 251382742 251382793
    0x60806060d1b03022106090f040804050d0c060807080f06060d18030903050d03051e042310110306030d080714120402010e010e10030b01050c06090f070602 68
    0x548000030045074901040d402064408806050803004465140707002e002034000c0e510708042d44503011318501c800070700340010394810324000380302d40601d4481c12481540f008000700226110b0100f0800030a5540d200c043c02c005152250309007050310fa0412030014204100138000106106070041848494500c2c074000c6075102c04140d611588465079102c0709030203800d004000300540f11000812105040c1e03c00040d00c1502c1c020400c692141030140e5044084400c12241d10104680f061182c24001c0060402103802031b00807006200402202e1701c40d600c081c0d4921414819030362102c0040c041891903030050f15035482e2100b80c21810351401c90b001c20b460308010100f0000300001000050541d80c02081e000c900c0c3c0710003080315510b40b0700d41002501c076041c082d5000c1e4040f40c1c580300b62842c0c40d84120324030000e045010308000c1c103d030b010000c26805000003031640d6040c07000a02c0300d02c213401d00801c0214400c9800340000c1002c050100025403c10300c09405c100c0071034003c132081c98a03010b04550304000c20f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 251385242 1250 251383992 251383999
    0xf03060f01051c0c0803130b0a090603020906211f050108010e0916060e04050a0612060c030209030f0a02040e030c07230a08060a0f052205030f04030b0f0709060806 72
    0x1103540e4603250000395800d00f20000d00c18044135802007490400000070b0400d102460511088031904d030b140441190180d034203010005441130006004041c400e4014052580002d410079042101c202090209102458402c00e21a911402040340502c6038540015880b801c2e2040249820f00703040000b010b210b01405000c0a94052401050b208201000105400004030400010075612401c005046004102d4200d208909203800301c0c0280d005407090004483c1d00212540b280e001a9645001070b0141104a4040c1039007803140068a880900a000c5054860030103030004012a01c10041103071014031408d12980d1080c004244106d60014040301500d01d174000c5d01518100030070390700620903009003c4540014103018000741101d03000034064060a880721050014241021243c0301300c503821100c4d03001d10b00c0c40321030341240307245095200c08005000310181c83c030300b558500780800182e00540c0112400d0704482c080190008c03d001c42950840346ea450240c81003454900d00403c02400541114030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 251386492 1250 251385242 251385259
    0x3140c0a0c020303040f0e0a06150e101103130518040b071209020a0b0c010c080403091e0e100501020d0f0c110d0210030b040b040204080607031508010603050601050f03060f0105 78
    0x15582d080054400821b24440b1108140d502c950200c62401c1083e03922102e66810b06001040d02c90803d0620044402e40e0b6480388105070000c01049040c1800161305070034004100f41c20703180a54144005e010303000c40603001074161850241485a40f8050000300c5c0410034102040c440000c03003848a154118003945840b00071aa42041e10b0001420b1041009600849003070300003403a105088040c4c411180e40308000c22480c4002d032020b81780820708503001070010706460824007090003010716222040c03507a80491038903a501d58900280154046d1084036031000e250004104640c1c0c1002510385812440c54110403d000b14031004e040025189401000d0ac00600e03a116015203a0300001800d06400420005e00c84007490805001004004d0049000b40e050550484d80da062074000c5400f110b100500615003540c62180031402019609179250740c1440405002600840900034103002d076000302d0103490b02c1d5240c01308000314194404c04150082d004041001480c5091b1041c0c0d81c11a001590100c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 251387742 1250 251386492 251386517
    0xd0b070c0c0b03091b010206040203071e0b0d1508030a1b03051207090e0106020309150a03110406052a0303161116030507240e01120501090b0103140c0a 67
    0x807102540e40c00201002d034001c01000000700001804801c111002c268200d00281141d00481c4c981c0021078000c3d4241d03001c188100010221900040054040c003641d81d0125500c07500810120f074041207604456507110252244000c50281e561002400e24600451618524000c003070310790a0220414480100c2030700c024003d16000e00300310340031441c500404038038903d8807145c090407000c03072409000c0d400803418002040450000003201e50b030150040007a010a01c00c142300841e65032005140b90308260301c1e0007050010480c004040e10240401c0c0e01c500762100100da00e01c0b03083d11855140e0304502002c0d01da0307031000340c0030100c1100e80043c030303860380e05072032010001050f41ca002d0852924419403086060050303041030100a81b405580c8038400b5200059601e801910b41000606d00380240c09103210b41c1130b64114007401d1440c0c10264103042c801d021110a85c0040c08880c0240c2c072118442d80c8520a0590941e80740c4207800b01e40c00031034803104030340c10f101c10741526038007032201c5403c280a002e00c12913 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 251388992 1250 251387742 251387753
    0xc0504060f0509060f03010b07141f02071407030c0e060a05013e07060809010203070905091003081b061003030212070309050405010311030f010c0e010507081201230d0b070c 76
    0x10740004c2c9945105d01c0d41c959403510200300315130200c507042c3c0711344d0810044104001804102d0505034214008001001042c120201e002548640821201042d42481c814a03400d0709016403802075009401569619117010303080d401e0640c0c002d04042c85400b4090090080c1d80e04460905095840500c034000000c03400041e0050b5006106035030851108040305850800c4000200707002540c4040c0d5902c411600c46034902800d0b0302040c1c4480340460655003040c0100c1c1414001203a0001001a44000a540e22385500d80c86030301c541d5032000180301c1442c900c1c02013801004604d03048283c59040108a80c60350f100203440b10601e4084005090f40061110107141c412000c0001800c4000e00030015543d40f1b10b003504016280f5190b06000f80980d1510b884402418414005110b90640711040a103809800441d42a804424112820071040c401c0c11804400d03004418081c148501d0700c004048001030010160307403441d8a5a51044145c0d00f24240000d04403100d981c0c00610302e003401408510580f521 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 251390242 1250 251388992 251388997
    0x90b1305150904120e0f0612040203071205030d1d060406021c3215101e0e0f0d080d2307020601031a0408070b060310060602100c0504060f050906 64
    0xc0341d4001c000d041444280003444212960540054860490480c5c036102480350a807588113209601103800d00600381460b80b220035569120340b0040c140c030700d803684814030404482d10394a01a81d05074404103001152000901c1090100b02001c1c404010560001604a6640500030001080c42d038000c0741840001840c0e000d1701140384a00d03070b000d1013061b000c1d800756031151600da1001680d01c80580b0a003840307c115101d03903d0080c2e205080702640a44030701d040c81120100c0140c04401c001c00129099007400c9d000c08918800156980d03000e403059505400c00c403000e05a200c405114601440303030000018410022034217160326545000c29907210041c1d0131a80c50880d002c50a002c00a408200300b4000d40c0892864162481000b042d003d03030085103000d10a80a088800a2228004020282c0400c80c4200d013070b903100300c00400304c40c040140c80c043d080c2905c4089d8440700241e40109044070088046000e1640755920929180303003400d150010082c4038400d8003003480c00f0b100c400601c540c4a500e4a604 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 251391492 1250 251390242 251390281
    0x504050402030c0409110d0302031905162006070602070b0f09070314120a111209100806041d010f05060315040b0405070e070903051509121809010311030601090b1305 73
    0x43c04060545048c040d441340d02c060081c848080b0a03041c201c01890040d4180d13854281020072070303000e0100507070352900e05c21084100722a10740060b0078184095a104002040001d2280741c01586603c190f04e82519800005440d80c00f203028082c0c1045416480007070314808584d08810a4401c4c840300a918a082c00b00c095400c1c4032958000820b0500719400001810700841034034101e07180300341d4221804441e80078040700755034010201a00c050b000c6216120003504004020300c00101807002008910296454441c0040709944603001d10000b40190300c03400345d0104080d00505112803060b41c0001042c040204020007500f42c03440454180481040018003801c08402c1a44031030a0004001d07068070f0340f51100700d456224500003500c0c03006d0a0b01045001d0050381c40246011f1050040c0441e50fa00148110001410707082c0903440c4680e50007110301c3c000c500802815a80003401c50038181000016004800c42a050003451411030722480e0180b44054a0301100168a4854400c00f0901025004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 251392742 1250 251391492 251391499
    0x320152a0d05010302010927020c01020c1606020c181308220e130b06060a021005040c1a0a080c0304210e030633010c050d0801050a0504050402030c040911 68
    0x507840151107050b50026059a000f42c1303840c0c0c19150b84244600b0300846c1035400300da0414070010701182d841410340161004005000002d0704044240507903626101c0009101800c03010340c0041001070300e0f018850300780c07610800d1310072604007440800c510b240c070a009400625050100c000304000d02c070b06407080d60340c1154090b008110981950341c5043d03070f6010320300540741c0c01281d40011500c60b80703184982040701341d80820700492680e204810880942c02026659056008152500340c5d101071512603d071042c0d2207140302c0305582c2c1c10074800007039589480d003112619003010403984580e035802c4000d041c3d000a01e14001c5030f4a1b03403145051224003803540c2001c0c04203001100c0094800e0781107049010110810350440e00f0b40e5580c0d101e4117912a40110380b1201c1d40c0c0c28882000d8503500d40500b4030f0840c00d810704100510600c02d07541da074a403031220441030000800f940c0042c0428a1309102240c0105012075040c0002d06041c0c0000740c80700034454403603110300d9492003080100241d01d5000c005549004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 251393992 1250 251392742 251392747
    0x1704050c130507141206150904020a18080c01091206110d02030912031311030111030c0301030c0b0702130504050106150f02011d070e040804080105040320152a 70
    0x85020001a2205660441c00705152074041d85104000b44c0039214036100002c52032066849032024080007081085115501c41000c0201c8240f07a00ca60004011000566030341a10440c0c0c01006003e0b0003a5907084940c0941080d49254043e0381c0c4080500d003070f1020305150070302e901601c0c507002008200030081000180c8021680c200c0d00358690340510f00c18070361001911200e520481c008881ca04c01112413400842c0d0282c0b0f40000f01d1100691201c40f000040e00001e903186007a030090120380c004031451460800004018420004e003940306c00000c294009910f81000c070694001a644185042c44901c1d1550700c000050501c00d09401040040090fa00403214810fa0300d040288100090071880000d0b60a05a1000c100420500c503546170720000005003218a042907035466080e10003800030f94003540144000701e000403081c492705000e14402d840300d19560380110b51021503c04440314482d003c3d0030080c1c0268071042035440c026440601d0031800554841400302000c01141e04525140d1040c902 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 251395242 1250 251393992 251394019
    0xf03230d030903030f09020303030a0c0c0b0405060103050706050c03030a050402010e04060f06030b0a08060c091906050310060305100302011101090b1005090c030c0d0510030206070302011e06061704050c 89
    0x5600c0110068069a404c2c0701c903d000b85c1010f01510980074009416601c1080000c0103908160700c45640380c190351608200d92069515000070300c05e410340701546e4513040000104108030003080446c0c010300c400d0070507508108000b10040d4880c00018560305d505521a4001402c40e07100300110030f020540200100440c903100c2c11412801001405a00f02091402d01c03191040d241ca030b0000002c40310844001c048030759494561185603041002e50039008205a10401c58514041c0c1140d400b030040c03540c580d80c0303d00d8448140710300043c3c0760740400309052808050051140444201c82c040e6902801c00010340002c0c0c000a030300425010802409003420042030204040d8900aa41e04445081710300c4081074039103031414005071205885214035503404004000d81090903400c1581d2140c944902281055504d8020400c20ba011500450040c1d43d01e00c20400304407003402140e0111440c00f0401c200041c20031202420300c074515901c04403aa050321001130304100b0100301c0110440006001102003414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 251396492 1250 251395242 251395247
    0xd050412020f010e0709020904110f190905091b0c010e0303040c080c06030f060f041a0306150607200402041e060215190f05090f010e03040f03230d 65
    0x2000920030040c002c0c0e6840841d40c142c1406915180d00340e1401900a140c070300551350000754400f944060300180c81d1007000762194018809054500c1c0c07800700c0c0c645c0c2c4440b680030461310024541c030440c007880b003201024005030300c4c0c401074035511094082030070210004c0618854043d02a01d08150b1a6600302840a510f14030080701550240d40b0401202341810388a040e0b2a481d00345500485400030410300018003004d1504007507d42100300a0900c1c02c402c0a510b02113815034800c00011100c044851007004071900f07040150036484620400701c04401c4107030300700140181c450380300301034285040d411004500c41402540c0a5071040010411551940c0d80d081803201ca0030541918200c01240030f000003207090010804914040180f80c0c015686c0e9516030b03602442d005013901d44040c030b035a201190f81310094140302e9035028460100040c00c22042c2000d81c10300790380c0850403040c07860308103001c20044c84911540c900140c070f0744082442e4001c1c051600c40307003c0c00e01050300c0c0340a41c4203149040c0c06041c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 251397742 1250 251396492 251396513
    0x40207151a0a081203130c03050303040c0e0f0c030106031113062d0507080c160605040504151208030916030807061103100303030b03031b010b010806030a0f020d080d0504 75
    0x1030280c4402c04441c0d590382e41540c070707420714005040400c0700c10400540621001010319211a00c146941c607901600c7c1e84a01d8910b070401c99003190381c10003444007400441800014640d04c9900201440d503145020f101d010002e000c1032050300f05050300d03228000c202080340000d03501480713400c6041c11f0038181c0e2020014114448198004405054035080100d0045d201231a4076456619464140c03400c1260f6481c401694005520794880d40101201940c12030540546640109036a503149602c850500040004513014111181d518500b45d4408026440900d01c4003070083c1d07007041c0030a0300c07552501025030804444080c0905d01391011603000c02002800000307042824020041084295802b0183c02c10a00c01a6a443d4000007a2841040000e201340c00420b2104006000c1e2800c040b54400c52000204240703185003d581d446801103000355a01180c01c1368422411401407600d0003007034941c0900719000d600083d0040105201c80c40030700c40c60004803076021f8240c14040101c1e03c0c05081005408 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 251398992 1250 251397742 251397791
    0x1140114160b09010507030b03061e0c0714011a03070302090a02030a180308070905012604050304080304090915020f0711010903080d1d07060f032c0d08060109031104020715 76
    0x1f900e03007070903171101c0e040015055101d488200d00844a86403682111114840c00420320709408008200c800c2c00554004801162000100008205854106004200c600103801c44038082d6025000800145c1c0c0c0d0200410303000405e20000690301d464003400c66015190401c881281d00084804ea00201071f4400c003000c4c802d0311290303295403c040e115801111f2180c449040700540308800d004030002e52048140c4690050700c84c100f03ca281507030b90700034503046402c280c0c845101143d03030f4030804041c0b1045102110b20041e40c8a0114a4401000105138640c000d030080a03044000011000402c0d90048907401c1c09103422001c6a41c07540d840d00c080d88c01400d04040c0b103074180a62007400030401c50000841c50151942d0b0b464580b400e60440303c08400401c040c440809403031032055090440c085040f00034203a0080c0d0100a070091502c080d4010b008200c0c0038015504100381c90070100b0115854518201400c070f0200d4026a955200e41814510009444082a1310505d010490030540140d1401003424 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 251400242 1250 251398992 251398997
    0x40303020a03180b040b0918161815050c010f050c0c01230c0a090f0b0403051917090f090a02190507120c0302100c05040e01140114160b09010507 64
    0xc043c04640701d900b040f07050b881140c031a11000e01050050079203d00240ca51160041c124a07400031500804500c800f07001d80d000700b2a4421001c0c2491203a0b031003015035055446440074980e21a00e048500b11445030740c1442a001c001d40410000100082900040000340e011101401181484030071748040e039100300110324080d840d025036000c00a041c0b901c002e44030502c08080b00740031303500c141c1c1e2148240d003c2401401000340d010804203000007540442030140c042c901d00030352030340e0a519190b468510800c3c04a407481840310100000122241c0c01d141e0095582c1c1042d98480c2603803004100d061703050313103165030303110031854104488640940d010f881580d00905003614103d1a8a1b0203450900c42e0381030241c03004003140d180407040c50081c203100b45082c1c840d01c11192100b503007541240403509844510400148001400c020200d02280014054a10818882d0b005440c6000203848013072400c000c44070500000c03c0f01103250805034040404d15070003500c0b9000310300d0850505c50003050110b442002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 251401492 1250 251400242 251400257
    0x8010212070905041802090a0f020c0c010206180703060f0b0d0614070e0904060203040503090d08030906070f021b120a030e04110c1b15181201020a090902030a060308040303020a03 79
    0x510385440c0c0205a407a5400c9103005c01420101d80174800c044000401e844400e80e1031b04880107050000380b00500c00a118100078105c03540c00800020304124000e01081e0a0a01c400400b00924001013030b008216680850009009054581e0300e0003d0103c000c0340660000c21791414805124850300010300300c0300c03444c407a015265242c06042da81c6446c00c0c203030240c22040c10000500011980d078000c640107401442168104459100000c0c0c041501031000c47da814004802e004040e2020045550041c0e45800c00c2080d00b681000c000395200145d01508544516a00096542c1c3c0c444920b00707042d1403a1981620714840c2c0e40d040150803107280c3c00d800e50203907150041c00c821004203d0242c500300e00006020303041c001c10b4176001000346e80c0340c6640c03207500200d0344030901c001c00c10050041542c00b0060a00070b8a800c0c0441c00c224402c0721a8948414690040101e149081ea0200c540e200303403030f14081c00584903203840346481c1c01045a5003000348007020000780031041c5600029a40e212500c280c1d542c44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 251402742 1250 251401492 251401499
    0x90b07080610020f1902040f0c051e031e040614010605130503010b0a0b0a021203180d03050606190c06062402030702060405060706241a030609060d0507080102120709 73
    0x784d0301c8540a213802c0b0590001240105002d58610b030074420359000030f1000c40d03d01000c0303450b1030494003500c0c84e0303001040f8005011300c3c8120f80c20321403041300080c4170009421840d01c80a10108180440316011682030301070002002c03c0300b00d81c45540010304002440ca110742e11110050015400811000203e2042800c009914075050089510303600020305089013103490522060345903000b0310003d205600a0b010241d444d003030303084082c511984040c013414048030b82d40c15030301d0f0070041e03400c85480415007040c08101b60b035292001143ca10401040c95203070340e01500401105c501c038510300001d21180c02d11134000f03401c80c6c0d4115a00d400180c0765200701c014004101050303a480c4a4510b0003500241d050104000d40c1c1342039800740c002e42d40102d6000c1000c18028403501c50048503ca4501c01e80b40f4020300a01c0034500307109191940c4854441c60700c1c6903041c070800282c1e070390100a108070303c1113035002c40780002c2100900c00340300103202c884000e41d01c4402014100129107411160000051060704000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 251403992 1250 251402742 251402747
    0x618011806020307092310021e010c030507180e090703020d0f03020c01050406170a0609021c0f020c0303061201021308070321050901030c02120f0711180109050901090b07080610 78
    0x3412003c0240e0008056060ba0740144070314104248044030039070203a040c0c0d540c0720001040314001c1049d1142c000003044019043e015084400c0a00303844200b0010502090481e003a1002031310580d910108030b0b00c400d540ea4010585804c501d0340000b0b4008004070b2a20040001c0d20003c014803611a80958040001410044409000d00d100e4000010302e210180030421401c06a056000260185d01003001600c50000b502607a0100681c0b881c0c42002184004540829110700c0c80c0c100c002d0f283c00e40c50100f414242035500e0001034031440c842c3d000c4001c88180140254101c23010b00c605280480704056603003080640304c104a20043c0c5540d40780071105401c0716221140540c441c861074440307904100144004600a113807004050043d403107040828005101240c0c00380840e60454450a55a07d245103840000b07a0081003007030303004007111864804051400c81400b03042d6070b00110002042d0355400282405054000009001c08641c001030102207a8000c0069224503020b584a440700801790008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 251405242 1250 251403992 251404019
    0x804030203030a09020102070b0a18080601120809060403170d05060f0904120c0803100503070801180f060b150711030a0c060f03060e01090912050408061801180602030709 75
    0x180141c00400c0080c0c0f00940341d80c04600319030b00601c104c0d0034507500c50500010f02c0d07104200c0240801d103402c003d0702c08081c481000d0005417184001424055140c00319064030300303983d940d001b441c1d40f4000c0b540030390f580c0760f0400340e03401913810881c090035491580a0791000781c2c1c40040c1c0f4000c0d240c1018000364140c03d24804e10f11005070040e0032802590303100e071907a207980360800140d0010860001c00758004112081e001e54000c036950300c050f0348103514100401d8907040700b5600c0024140d040100e03407a00c540d100003000c05425048180c041d04040a031400800800c0b5981d22140c0c80102a070200c2c0300594180c1c0900743c828032031140b520700000e400040550b90400c44c1c100030045011640140245c070b1041401202004240c240480d0784e030344070148604d05c03803026080305004654824100003801044400d0b451902071a00340b50380f506003400082610f641000b85503600346019040c0e2010001002d60002c10403038608e40e80120b681c0b2051a042000c0e520545904001440e50070000c91101e0400c01c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 251406492 1250 251405242 251405251
    0x102060c0d1b21021305060903030c1b030d020703050703120915080a0b120c040b06120901240b0a0f0507020603090604030905031207060b04090b0f0a06140f0d0203030c012a08 77
    0x50741c0c40d17224070b424104041070f803045150a4060000340f21511085008200c80702d815a0a4001c0c1d80b011404134091500d44040c0c403800d101158005d010030000b2400c046201e00550784c00c4040c0c040213801408003910003507440d60042000104904925101b142d00c1030409001d000c00b20303410710614a2580c100941000c3d0002c800380d107604507080c03086251415500c150130011010707020b1800c0010020a011400700201c0c1c02c2c03a401d94441001c0f000c485140760038440084444985031540d0790406141c1c0c0203e00821824000f07200503440032400c080d000b4010b44840a50007400b641d0750346003440140e61645004e8400314007080c0384110116285c61b0105000300b140c1c6056099500340000307502c03900054040841025000780d540c14064001c07030003042051748076181c9441422010306120302d002c0c003211219031150f41c510001d000076005941d02c07000c2c0c42216070003c03621000155040d0000905601ca541500aa598a403814001c101c022107485102c0403654803c2c281d0b6282c19211094811203001c68 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 251407742 1250 251406492 251406517
    0x1203021b2b150603050105010806090604080706050c130b0c0609010c0203181206160e090720070b0d0b120f071e03150504050f0c0102060c0d1b2102 65
    0x1076210301c2586055607184118003a4a00d0340102200d035018800301c030303600c1d002510a070b511080103214542c410411540c008460368000e2425103442d4a034660640a5130a00030841c170703141d8010a0f5003403203520585548003984802803100c00d50301c1040c001039030b10800f140001c1d40140ca002401d012418401d0380395840c03080c1c0181d0718010040512100d0291000d0f041c59120340714038030740c501c5040100155481030714000c04412190386160030141c020a11244c80601c101c202204220499901c81880c2488002040c45031010410140980b803c080c2c05800000c82d1583c0440d1401d820b4100750084044c0b2001601c6008034100c1800780c00341c88040300c1c203861000e6840980100070403441209562a51503081030700d130700d00541700c1d030341c1b101c1d07010a070701d4050121500d9a00b031105004091001c0300a0130f014038005c0c049140e0100c0080c2d240c080040140d4000b24020500058002aa030400c200410382e4500280ca000c1c042040500b00c3c41e0f8030182040940e80c1031041c43d120440500c01c640b244810f59 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 251408992 1250 251407742 251407789
    0x13031103180f0a080619230f130816020609040906051e16050f0c010504050106051215010308090609090f010303091d0c0a0318150b060702010e0907091203021b 70
    0x80703181c0c1c6c0085c14109000c00c905903204028000c031400d1314860040c0c00311001c0c00a000d03081c0344c40f041c8016003001c1c008025840c0c1c0c00c00c04074001916041240c21070340d05524603900e10850360001611900507500d03255040b5081410020400410754002031244001c0e13405841203207a101c00021301c1007800c4038100742c0c401101145400c0b03280601c0c0540856000d030750580f07142c200d00802e11030a440c420744048959070745a000a20907403130860b064201041641d0b00a0408407800300000f00c4004040c0300c00741c050840003580340c105813201003c480c203200000e0326039911400c110b0380c04a1039040910081d800182042404103410000c0c10120301414100321030b0002c5034a810341d030b00c80a9488800c441c02415954104038219481a207a41d0420a01407042c4504a2105a07008030559100c140c0c81c03441220700308112401030717810401b00c0c03001040580f003200d600d503070384607003a40ca00e442c0c1e810015404240f03100e281c003015400202000045540454070042060010a0020051101400b082c280411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 251410242 1250 251408992 251409001
    0x1c0f090504051005030d09081c0f140405060c0312070503010509010e0a06030c0b0a02010606050a0207140a08010e030c010b04060f0b030405010609020f1314010813031103180f0a0806 80
    0x1c0c0d00482c0d00045000701c0480a25640d10000b40b0300342400d04a00045070700000e0401c012541400f184e201d1541c0c403085440803011454000b00350794000c000c0c03c024080344034034410419216209542c050315010b040700b540d07180e000942d41c3e500d40124440055070764580e030004000724824820360341203943c050444c0f00147d0a1810f036100180307004200309a107507507078100040890040042a00204a91a2071695421880000900b55101a0880c0c0103101c01004590b0440b0345c0000c0c1202201c0804620356601451800042c4200b000baa116a51960804c803114401541c003000821191440500070808800480700384410f0750300f1407003444003c6110940420a1088820095134001d126100000304903403204041c10880c3c00c500f44040c03094001060490420311000920000707081d5003500c588245500000007012000014166440d1a210b0b42c1a40d08140c0907101441403103040720280c0e0380312000c091805000806004841d4461010111015030398141840c9580039920520080c0ca5259074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 251411492 1250 251410242 251410249
    0x3020a050f03190512040312270504091506150822060e0a0f050304080f030c060429010b0304060c0c02010c02010e0f0d0b070207150e01120f09051c0f0905 68
    0x20400401d03901d9009543c1083c0745e000000380104081c3d48100081048807010000003004140320313000c0d266078018400700c1548070b0031520350400222030f02200c000c980d03030019203081d01011401d043c80f5440c903400e0010100301c28440000c41d56030202c155441002580c0c0d01e800c0b14294526580461040c0d40080d4216008200690003180e511036440f0122900d15880d903640d2011010340180c20344440d00042002d000c0c109041c80341e600140400c0c0c00450178250340303014443e00c504010740700034420702452200f407546000c0e07120300d12a44044031074810001d40e51051510515881140d040300e80314076150000c14040e004403210452160180d44166481c642640192040b0104c0c48505622401020b1049180d41c0c2d6520205003442c80303048240c581d410581c00203450100150800b50301c0c03281c901025141c1680c8045012082402440d10b5010b0744511b440e450010300510341160019414507261000b4410001014034081c0031a4040f440450b00c14001103030048000080b8100180701c44804005928 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 251412742 1250 251411492 251411533
    0xa060f0e0111060a0506011103070203300406021b010f0813060e0f0a0b0a05010302100c061107080a0e030106230609030d0206250906030c121503020a050f03 69
    0x106040440115001010140c50203804507414000300c2d1700e03041013120950740104180b04101070b620056050000b1680040d0300c0300d450504441900d111b812034510311442c030851600a1000000c1d000d0b54980e01c403d0025203510010307200c0009840c11100c2e20030310354404e9503203118203052503484041546030140d885100d007032032020079038600d61101d004900404040c040420204204801082072064520f00804061801000c0400242ca00b1300100096100d88514201801c568901100607031010301e49200107101012612007202d0000c0303a440200042034004080b41c0300561100d0038072803101ca0415090b02e190703000b404e048810800450403140c8a85103403c50480b8010724560401c2181c002180c40c1000c0b5a090b203006a003c1e01c00e205c4400411907810442d0542c00c943c5005001c04040082d00e444400d228800c105a5a04080704510b84204401d4010803150001480000015003d0018031521808141e114614280d000030762483d040354882420b00c8090b014180040d40000350343c0c1d100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 251413992 1250 251412742 251412767
    0xa080702070b0d0606081005060301030b090f060f0402031b030d03020702010306030b0f100603060b03040b3409060521070c0f08030711030c10150b18010305060a060f 73
    0x144548840451611040406030000c00f0107807100041551501500800c0f00e07101503d01e03071147c524614144001c0e1030304001c07681500d4108407040308644884030085c0c54104041d1a8a0301e80c05140180400b00080e00311aa0259008030103c0781c2e18001c1c43c3c902d039085885203c1e2164907921034003422840c80e0098018180040c014100000c0982d0340c0d480300b004c0f00f001154903404481c01c80e01040340e581f102d10f600794040c0c881480c08009041c01c2c884500c040f4440900302502c80c00a510019400d000e40401551079040800c0e507040d0003c00102c0d281000382400301e6080081280b02101040044c0300e40162111051440d000b444882140001e901c0c071480090065010040d0070035880000c221140702e103110f150f11a101c84ca949203800d2a008041040c000d1103108160810040c010303910070005201c800c1540030030300c0002e6103071030070704000c8180d2000c0e40901040c1401145490481e02c5100103c041d800c030030389050016994881c01c00185104a00402011070710654203240c1051152084070b810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 251415242 1250 251413992 251413997
    0x30d0807030e1204090c050c03040b0d0e0f1507021b0d0614010803041806030b0a051518090c03030a05040320040914010b0604122405010602071e0b0a0807 68
    0x440008215a0341843c02e02e0700f52018a41c000079081103015164890103c43c0e200500d0503600f1310140740b10749a280d2040344108180d0132004500041032a506c0e60100000b06071100c1100c4d410705094820130385a03403e0554803c0f0403140000040c01740c3c1c0c001301d0f10341b9001101c104200d025640d03803810008001c00d094400c0d07841c2c0380e40c2c101c640154a02d1082c2c25020b000440011034440e46440102d58181c22080c0040354620f0801c0d8040000800c0d80b410150440140760012032156a1000707035006007103140c00300c59480f0441c03003072031101078035164210303800341d100d00c0c05a503044600c0c0018107989100c3c25800d140000e0040200704089400b0b01d034803100808d00c41080103030010101000401b034941820060340d200498a4107100c40f050300348264440d03813400356203903402c040c5006c504d8a00000b05220187c903103e02580f10005110b26002e003240f040781200020041543c640c1d400954400441c000c440c10740388215001e1441d170b203080c88184101d84009130300300e140031a8018110784446014008009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 251416492 1250 251415242 251415251
    0x9290c070812120703110706021803100f18020d0f1b150e030d02030a0f0c140f0d020a0b0103060b0612070e0a050612070e120615010e0f030d080703 65
    0x18801c00a0001c2100748036001d24003601d4110950000005100c09450304080c1458a000c04a2180070705080d2172105411800050310b4010204851400e200481441541400380451600c00c1880650156515400c281c00c1000b07240142203040f01300c4c412444000c3d51000440c400200044c40100d42141054400c0340c0b000004411915121002041034100d03010700c400c0a078041e1a280d901c00d4828080a8013100105004040040040d4891080307600100400130310712144601a8042c44c455501c82e0303448078490705180081403080d9207596900c440c260850051011403032107a4030000340541002d422909070300e1540d107142d0300e13040101030551031a50848018801031300051091000944192400d071a0050743c090b450b8104000e450054001134412041800600b55070407201800c0d80d8008080d0800d170140c280580001040a9000403640b1440c3c401d007020040c00e0300140203d0502c0000a8880960300300300401000850b422000f001742d010303403010800119aa00c80c2d540c03640c000049040004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 251417742 1250 251416492 251416499
    0xc030d1806050106021e1f020d06171b240702010311070b010e0106050418020904180804051003020702030606010804020f0d0b040510090c0e040c050a030b040309290c07 74
    0x1003a42c000340e01c8080943c00c002c0101c01c81c49209200110014800c10103081721208507845010010300000404021560206d400d40c50403500ba0711001c0034001070900c84114500320458a60707180d69100402c100f1130750048804809045c98a6240001c0d94403900c001034003040705c4604030194001d01c40603410981ca0300c0d1103c00d0b02851100401c00e80d405446505810340c1800318802e504501a0f0018041150800c001c015050294101c04903500c5800b60144e51a40780000103000341031401c2c01e0300441011f40003040d0401440000074403c641080e19011040d0282c001c09074100e01030000003a4241c0c0041c2c1c0000c10943c450400c69910910003840c1700100f61000c070200300c107450901d0b000c641b165001d40c123000501c20b0411003003600b4083c0c1e08090014007956900c0c10f44002a0740328540801400f40c0110b800c01c018908010054400034020104107562410400640441500d00f900801c00c1c0301004221a070a10054048004030040c400210114a070b180c900c07241e00c6008600c125015400020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 251418992 1250 251417742 251417753
    0x409020d060e01090f2d0e0106050a060c050d0f1b020a091503060501050306150907020a15050a0b0301090309050f0a030f0f12050a0206062e080106020d050c030d18 72
    0x2400b0b13020540700002ea0000e101c440b14221106042809000c007107078109102c1c3c80ca14141c139086400100000843c0b010582c0ca80107016000d41c1c1c0210303a0140c030001c40450842ea00458001c440c034043e008036040d40416400540c2c251300300302d081c40c0c0000c41a1009460410580e0062000c0500c050400005990340b1080c6808464107200e0300400090054004c00c10720959000e2140580310482c054100b078200020031040f00800c0319030f404e0052042c040011401d500074451010300d140c100000c001c1000360070050500608045800241e4140b4114900015043c148034410290b5495181c44030b281d402d0030200440c2040302c41c101a80b0500780320001c00003031a154044448a031090411003a00c0003d407401e00711000c2032400d2802044130500520302180c1d0300188041c0c200c101504c107144041c1d60102001c0300981c003c0c8804041c10f14001041d01c0e2694008000c5048468583c280c80607800800780c210b0760351141c2c180d01c000da6401480807040240c1160b0002d045007508120328101d98155075501c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 251420242 1250 251418992 251419019
    0x307110a060c030e03030609061012150e091c03020f0705011e200d021809070c0b090102040e01090e010b130f0513080a031a0301090f1205030601050409020d06 70
    0x101d0784940c071041c2e150160340d014098081c0012120307001d14114540040410360aa600412a0f4452080300300d150762601e014a0940f600016a03000602c03031150a0300001c58150118418007500d042d8260000c2d031040f00206280b25110400300c0b595010310b2603004210069001466140800c100821010b00020001d210341c2d6110b000403045100c5141604140204994003060ba907402c01c188400d0941000b8032100894107088010724005880c2c0805960401c403c050540009801c80e5004092103100d03070b0031900d00c09030740f44501c1c020045959007481d4603090740200e00c00e11748203503010303001805015116040811903903056000020b0701e00c02d8600081d90180300c4180e1410855642c5903240781d031107a50182c6540410070422989000142d81d07190389031842020b01078420583d445081030022101c90020340550003000300240000f9100741481844d1041c0c1410451748800f0b0000300100032801001940d100d108161030305030a082c41d20f410980a580b02c4d0100c01084c0e07070b0b111800314012003030500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 251421492 1250 251420242 251420263
    0x20910081f050c0a0507140a0c0b07060605010f17090f01062303070e0406050402040609110904050a0e0601030f080f0406121503050c1909090b061011030301050402030711 75
    0x7075071600031980303080c0c0070210340014001c800031031010048601c0da82d4108040701c0525034401d03109414642d05081c0241000070501004000b80a203140020700d00401502900c1030f6805808108a01c640c0c1304010b54200008002c1800402e8903a0507070f80618010700c0a2641c01114202035882c1e28408109860031104039403c640580b213040c0301042080100d4441d800b0118006a0040102c1420011801c0b040c1c00010402030460381c032000040c08540707903600801e00a003031f07440060218003804140e03001d4607045060650f0081f4508030000c0e99441030340c0907002045820380060310301a402c5440d082c44004803500150b40c26081001085d401e400b107000140010301181c6d0b16040d41e0032103201184107444099110740e4440341058410320200b10085140300c1203010881c0c10566119039006000e0304c58505900505a1500c0c1c011b042e020302c5001c0001034840c007000c80740c580c00c92003044400d451240c1c08201440b031075401440140300d81e0805900440c0c01520174200f00044004200c2e50900c2c0c846c0100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 251422742 1250 251421492 251421523
    0x7090f0c020d0e0d11010309020d0b06010f03050f1305160603051b03041a100504090c051503010e15010c050a03090f0807060c150908070f1205030106080402091008 72
    0x24900400d40c18485030740154030302d00c0c10a0f244001c003c0003074203448145002620841191009400a0780242c4c0016000340c0d000c0d082082c2c1900c0c07401d200400c5c0c14101c54042c02f1910750190390326024802c0c401c40d4482c40c2102a0429036490300c55062810b02401d4200701c2d41071250601104c00c8580245116004140d1660003140300d15045201c0300306210350b555201321000c001c1c0107000015001e42e1498091600c800b0604550390b95009110154a546e42d000e10b800c07524080750030f801c3c0180820301c0c3c0d00360340c02076440011103030030441e41c0d0300d83d88424810310b040b5001d200081084100c441031700c459900c405244c9440c0030465925400d0904e0400c1004501141c800281000b400003d01d070707580c0c000c010600252407014600b50000d0100170721a00010914086400700340c07400c0150354420b40341143c003c4582d030348840b945e1920095071305040500742e42f008501c2c07204500592164003224161161a80c440b525a2619400d02104010241c1003034170001d8000c101003100c02080141c000c00800b00c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 251423992 1250 251422742 251422751
    0x1d240603010b180712020705191b03030e04110405010912260324010f0e030f0f0a14060411120a150903170702061b0f0f070b060901030b01090c0207090f 67
    0x2180c0a40103c45c20340f1000c0c101c03401442084081400812182c000803000c1140010101c2c1e40e02d840130407405110500140b2030014076011041c1940020750a2115a09a8080025110f462940d009600486c407a07240003800300f240c24441e50100d07803984051035210300700301902c0111103181c4c0f01501e840c542c50204440404410004a402c44001200d00d501150005422004958000800c0300c0450700340710302405010401d03640d464608001c0100b40c0101d41083d00d40003440101d485481e0ba0000d507080d5004c3c6500102c100c0c0c1d100000c28654001c9a1008950110b480c03580c0601c904080400a0540075004035020131000c658101d841240f005080d540000382600d87d4940030703010902e214090b2118030f80820800c164240c0004801d07410900405114484038011030030280075202e0541210b500a4000c92464ada4400c24070161515a100e444041500c0d40d0310350902c03940060034071000d07201f940400f004003d800e4403a84141200e680520585e6003040c1c03141000742c10b480c1c0701817038100000d698 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 251425242 1250 251423992 251424001
    0x50705011b0e0405100b2506050603060f070807080606090a090b120703020618060705070605030402011d0310110c0a1a010512060402010503060d0f03031d240603010b18 74
    0x11020502c566001141d0401c014140300e034035030b4030521640c044c0303c80760b1100040d1808413030485001940e03a0416001d014079020355524002002c0d01c001d0321864041e1040074003044e04100c4600055101d000701e036480e0b503580d5075162000c031041c03400074080503000001081104030b9600c400001201419420401040c102020414081d02030b10340300d80740d695904480018401a070f903c5046400c0000701c07000c1c09030131103120130008038240b18864008000d403207a900c001483c1f6170800041c5208074007d07217400058080000300849039030842d00101d5415003100e074040ea4160360a9008405540131003002d80d0504d00f0503103000d4038100800209075580e104203519503080070381030000c05000d0b2a003a285840c80151444c80d560342c460000e80700906000c4040001444c0c1d40b1124407a60801790416684000c05140f42400b40040003002c8448519403006006013540c1d00c5d00185400300c01d8903001074414580800b6a008540350310103007800e540b654035601415159601c1c64081100700039805118005801d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 251426492 1250 251425242 251425247
    0x106051005040b0403020f0105040b0304060b090a0209030d080c1b060910021603031e05040305070308100b0702010c050106122019050d050c040c020a0201090b03040c0b0a050705011b 80
    0x4902501408110701008207120000030740040da0100ca605455400e68070500c880161180e02032504a82030a0300044100418031000d6000f0404241090f10780600c46d0316088a120143d10407036074100e40584c090030030b0407043c0d1711403c2410340c03107540606602e00b051104101040c102c00d0b403012842040c1d0055040c018180fa040c40410001c1c055801c08502e400002580c40e501e1441c0b000001d818181c0e9590340740c40c242e52000c4003000007c01e481c010040c40c545460007422503001454140d00240c0200000345900380c841e081031040c0c800c01c402650900340705600444008500c0c0718115400c0d500d401c4005800441754140c0c0e1503c2d8031038020f04c500721500b49040e000340500000200c6c42400c100c002c003040c0030091400841078501c00d9480341000b10312030800034075040e103d01c42660003e02d040284030002d81e0204070451494401d0b602c41c03080300c0c0c3e10660000743d400140d030b016103030789504075041020030f002c1070050000010901b0024180103081d03c40e00e0850342c032002c01501035080d0820000740d107039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 251427742 1250 251426492 251426509
    0xf01060603240f0501080411061204030e040506130902040b10050403050d02010c1e0c1713080105010b031f0305060f0106080c07050a0809060f030a0e010501170c150403060e010605 79
    0x1200c03590b445010307031805030360511400c442d20500c0e0601040f100403d05010651200800c00c503c0503241c01d54440e46441252031840b01101c0541c001007803940081c409240034040c0900401004020075242090000440c0050101c0e21081780d00c287e490480a8094440856031204d8450341c1d00e4803603e503440c42c1041c80c1001c022150110071039143ca0000d80503503412070800f03800001407a804d01018101d0003c10b9030700641a40016000d80c4002500c00b1020b142c50b001469000c3d0543e1842c83c1c107507510701c0b450b4261102070003003446510080c070005080704440c0c0004075950031780c11706610043d580c2e515007500b800d03000d84603100b0329499400140071031f0b07400410041e001103102c01013034135102c12521110b403500c0801c44000c0c01c0840000f4003103125981e44054400d104008070030740d580c0741482e126250084c00040b031414010350030100000360810480e90018281e42d005405800c1c900101802c01140100301010601c418905100100c0400d02520480307110200113400024002d040204200505 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 251428992 1250 251427742 251427791
    0x605011403040f03300e0709020f07060b0d0f050d02011803020607140417030d050603010c090b2803090201170112030305090a05030f030a060f0e0f07020f01060603 72
    0x19034200240700000d0540121031420640518004d02c405100d024184901d41034100c120004101d503a2030400004604c0c0e00c842c0b10301900074210781e0241d90368603004080c0d014040ea4500a80018041c6202045080d00215440f820080580c25400c0655465250a000840080d100380d4406081c11115035024420324515908107090190812815034000f56140070081040d010800d507944240d0003131620a058801a107488000c0c0c1101c880070040c650f80c1c07074002c2040321036020300b00b8000c1a842c1c24184280806a902d503540c00203500c0c00c044800f003959000c91461550a07141284140e040807000703802c610300382d20704d42d0b006c00c00300450b00004101c40010110300c17a0001e0030b0340c01004560a1200000c194582c58280856030707907554440c10b420700c3e25100000d8110701000841440303040002000f1481025180b2041004a403100305614049144c4e001c0e60f00c0300381408001c5920f80d00185135641e800001d1744102c0310622b40e03035103200d402d41b0b845500000100e91120024800e68039030001801e400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 251430242 1250 251428992 251429027
    0x40609180c080a021e01030b04050910110903030304020618130603110a0e2a04030f0515070c0209220c08010b041803080603030d02030108031306111b010c1401060501 73
    0x548401e80004c0c02e6003c190007401e45c1071001d9213100c2203c1e4043c0d0804210708100620030000e91520310718481c2c0394810701c0c1c01d43c00741504d40120000c08040e58802d0350240b160140c02107040d0b40e640d074244480742c4d102c41c0c0c4450f000b251a1004001c950740d4845076810400c50040003080d0f00d07265240c100c00c030b1030511100ca40318500740c1006125003e00e0458050303100e04d860010400f1780201c00c1c2006505085404081c442140000303020051001c0000c82c44403640c42102241c6104101908504902205070b4064002861814104e000361500d0098a9044080200325078040a42d0f0804212102c010040403500403034104010012030a00307100da07060f03481e402d030303424084002d01d079000c180d80d007212900c028140034058000c5585070f10300304191070b2a0840d024085507030756100d51300c59a40b03070131114075041c1c400682c160105c1d99620070031113401c40311707620402004144420700c47c0e07103070402400d450f0a0400c96a4440b017404074140b407a03d0042030015178000a0301604000c001041e40c0c4120390b00145 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 251431492 1250 251430242 251430253
    0x503040f1118011d100f0e0711010924060b1603050903120c1209031c030222090b0906130e0c090a140f0106050f09040609180c08 57
    0x46040503580040003680300380710385048201c41001465035002002c4200041407a40000b1500c14180d0103041c0d010405024072800c40ea07203140f1144a80703c1240105441e40324101c1080040b50b00490250b42c0140441c2040c240380c10b03d000300f9900711880e001e02a11210010095a902e0b40b10002007503200b40821041441600d0401100003000c1c45001d0031482440e4081d100c0c0e0051600c41c0055411000c0c00400740d60000c0ba114803201c074150040c0070103143da8010304501500d2403c0c1101164200800a80074200070500607141604c1c50309071940b207105254080107401d901d420000c14403810100c0a13808607001c981044044821124542c0d691809601064148105561042c1040c0060f100c0c3c840041a01d05004803542c2c1080740d00ca070b1044e0018404020b1129480c90354210300100700e048188140d043e0388491086001c0e000038400c160104208220740b001441102d0300400031614058000b14a003075803041e000301116507905150800c0e51420101004101e82404108000e0106a00511 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 251432742 1250 251431492 251431501
    0x603050f161b0317151e151c181109010e240a090603170a020a02100c02040f020406080a09151a06071b0609030308161715010e0a12081308030301080703120503 70
    0xa207d101010000031408601084150380301c10303c480d007aa96000c942609111901c1010b9003d40c8108480c0b10880b1040c0320206c1d5440d20303080080101c1d0403601c0407036060a0686030301c00307c0440048001c000c00389500c0703075850121140c0c8070f00741104003c0609802c00680d0030b1443c1080d00105649001c6004440c0d020000d0348001d80d40055a581d0440d011250b809900b50b0300401039070100703045000203400505160800c1c581c404903a010700304460498507060042d50740c000200e8221220804020007041c90300440c020312401590200202e000116100d880b02040e401c0007908907007004100302c03248200340c0c03441d1900d003e280b403400000b420541400c0680700e0941c2d401803c0c001e40244480d41029824941e855101c0c410440b14500040c1c4032840946801d00c2a4800c0001c0f10143d500d502081e540d104c004e9160a04d620100f0444048902c54001078995031384482c00c84c0d00c001d40821804000e5140030807030762428002503000300303030001c0100115031451500a582103414014001030080903c10007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 251433992 1250 251432742 251432749
    0x305030708220b070605092a03030912030d0b120307061a0613050108180a080703020a050d0207050a050402070b150a09060603050f161b0317151e 64
    0xc6109a078001000d944030703881c08901080410501c0340000c20b182c100c0c070340041c0400c10300c4003c01440340184401d006560341c0f14081c0f44d540c00908080c48004c2c00c0c10001040300200302e100440300c00e5005055910300b0440704000741c0c41e01071081428400f0342000507000c800303404601c524044441d0a41d6203c1411562409443d140d020b2940e010700b4194541e00158102d081d07202c0d1a0111640040100b074039613000384600007410045000c0c4901107110000401c0d401d41800b48403801048025005100d070003803d507100e000582001d80201d00394402c8a4400d0000740c0103014003d0096850f50082942a2805d802c200d00d5081c0c0340e000901840c0b04119550100307903100d2102d40c0c007081242508070340080c0c02002c1403020307401d40e12450448e450030380e0124078240c0c550043e90042868030f0004099032220004001c0010349000f90001150810001d890084404840c03150428020b04011383c1c1c4840000d000300340704c0c408481c1108604000411a011850f01041240c05005c03544404d201000411010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 251435242 1250 251433992 251433997
    0xe0402010210182406060503090304061206050604152d0c03020a02060408160801060806061e0406121a01080c060c010207060e03030118020313022206030506061207030503 75
    0x40b6494151980310038055210152080406541e000c540d85915001c18040c90651500b00030303e21142c282840c400080d441c0c03060054900034841400907610381440c281c1e050b07071b1422800121040064991800180b65030b05d8a000d4801054810001030f0450901c1b08010400383d003007400e14a07260401400c2540601e00a590000300321b034581024106200350341800e900d00001c03d10001d5211000103808648400c020500c00c0b05110000300214007180c44408003420b035403203070040d21040c1e404140065610701e420224081c0042da504100030310405020023290660310399070048600500b81e1000001082030340c01030100401a6229510003a5040c0030603103440b207400c6649903110300780c04580b0020121003903040740d8205034000e00030080448222001901c0c0d410134843e01ca0b54080340700d0744811442c2580200c0c0d2050703182c0300c920717880c100665080001c0700c0d078020010482000724a506020070300035840b400010310f001c4d030300414191511600308025802d12618101582c0c0000300d01b040000c00000c103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 251436492 1250 251435242 251435263
    0xa090e07090302040209120d02030409111c020913060909150504111e0301230603030c060112030519020a0b0604020f030a09050307020d210302090d03030b150a11070e04020102 77
    0x80240e0360706c00d080c0c000340080e4480d0072010840e010301001e80003a40e40000040c030440e2420a424010900100e140c1091405104004403100d150500130b940c4c8252140e009121490b002040078030b600b403080304503500f200e2280c0c001000c996516440082800700210816000940e1400144418505662000e848241804001d4003a001c5040151040c809401c0c43c1c20100f04080c00800603a250303801418426003088e1001d4222000810103e00c250601108a40c01d0390b103c20000c00d0143d181c0b582c910001050300300168104107040c041c2544c04a00c0242681c10300070b0b1030340100104483d5082200302c11002a01c001e1040784100418003012150000366503012100f10740020b200e0115061060562181c918002d5010894000a900b00940b8014490259141000b04441040032217415404c13840b980c01c10b1030f48180000342d9100024440d0b00716a140300d4014103004260a820540c002c00c9801c0044003c020a4034240440503006003000004000d11f940f6458024504150300081c1d15200b0004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 251437742 1250 251436492 251436499
    0x303290405190207260a05030411031c0f080705090d0f02040f090c03050631050a0c080304051201061203050c0705030d0c0210030504211b080a090e07090302 69
    0x100041e0a14035941090201c52100c2c4500795503d0b24545403190038400320b0705181d00c8100307496424800145031a4103a8003044038a44891740f0356112900c484088000c0c00f43c00036414840c160024160601440d449c00050b0f002d83c0703c044690000700c4020f0a520030041c01c02c41044818400380a613170361001280390180c0d82010100c00c030050b03c2d00205010713103d02c1c0514500b890500b0803001c108040786a075582101d004a0986030744c0d0710745038a00c100640c1035050300d0200c070342c92081d1340346001d09040244006c54450421038014600c1e9a903240f8506c50740c0c1d440810302e40c00200b405c0003581040c1c40841c4420b0071100003008114181240d0780754255110801400f0480045901c10745580200040c1e00644001401ca40700c0c42c1203100c0050110200e51000c034050b408a1064041d40f501a009150081f9401500ca400c181d2040c400700d5480503885908004110840a5140c0300c294440e004180b581d024030324050381e41c440780c84080d100713085540c4500c11904415042042c1a039101c04035405036503044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 251438848 1106 251437742 251437751
    0x60106090311040b0409060f060807050108160804050304121b0b0304030c0b060a030b090309090702031606020a120513051c0e0d05070b0406050703032904 68
    0x244002004107007260510416840d180c0c10205a4113405800003400c2452030303e41c10700391243e8858a10003543c1c2c0e11410712900a05000c5c01028100030f0030b0680f85030602140d41401418a81102410004100089000c020f02031007104d00402d10414a182642141c1c200101c180b80c016140780940080940005a074807440c0701564403450301900c442e482c2e21182d848101c0036010040c01c05038041a410400700000d0f0501100b2401010703000c0096458074442014440345040c0540721100f50341c000c0c0304249129a100341041c03240c60380304d0800740c6c88403401c00043e44d0306181255110101403c0404100000c0c0269101d8451180903100f2a1020314104810145440911f503004002480b543e0208047c0d003800041141068441d004036128185e40360001c43c04c0c0c0c0c0158020000140300003e17070070700380742e0705000720064860880c4c0d0500003840000414100b200d180028a8021511f4 = true := by decide +kernel

theorem cover : BRFrame.Cov 251258992 251438848 := by
  have h0 := BRFrame.cov_init 251258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 251258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 251258992 ≤ n) (h2 : n < 251438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
