-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2807
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:48:25.442738+00:00
-- url     : https://prove2.me/submissions/e6d44dba-bcf3-48ed-8cea-d4a3be2535b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 504676258 ≤ n < 504856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 504677508 1250 504676258 504676273
    0x30c0607030c1704030b06040f06140d05150a0209120106030506010b07051e0607090603060506030c0c0712050c010e0d02090a0e0a0f150b100519050904020a0f0f0513180e 75
    0x184a80d03550f4003555030b144071354604800027102da01948107502c21121142d40c11054011540200f0503210900781064a2600500210701c141001032021a807280001d2600141c48200303440920440e003d100300c04407d40d0385030034418008a00001081411110341082166480070716107409801c1032942010008840d40b0900c812003460700204040744101500d80c1e640c0d20081d5034102c01c80580703100f84503140d00b100040021801500b04000108000381111088a110079590001c90b00e2180d8015000c2d10a600300107402070b800d40e441002044025005c0328150010b4134642c0005080c041f024168402c81607858840580b400c40501100460b960080002100c00b18035080a66556021180152180d403801910400ca403903c1040c030022825965180c0d41442940340e4038003a102000340c3c80c10305010040c0221110b0740c0da18001091000c645541e0311101c0202c0b690081d001c9041104c1041c1440300900403060b14181c1180c01d4001c0703450b010440c1c042001c605410750000d0252050141f60f41c000d440c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 504678758 1250 504677508 504677513
    0x503120334091a16021203040e1015090501051603181d010503030a0813020103060302130f050907080a08180604030f0b13030806101e0906020c030c0607030c170403 72
    0x35014822100c040c0601c0740740340c003c40c420b80301ca48114050001c001551122901c00760920403a101d00489a240840340f0b0031782c55071581d104a50044401014080034201c05002d154103410101d04000040e080988a850800d00040e00c82d02464622040080c403d1800b442414403980c100000309603101c0111205940716004082042c10141c1f00c0004180340c0000050340c2d083c00000c491030501c3c5a1744100440e244d940c07440115500d0110181d042640320040032000d03035a02c2e40002d0382281c04060014600c0c402c40980d1098810040c1115110b421052080141314404103000c2041a4001c08542d0b590b010b200150403405030765424940c00c40340116002c4108010b01e001080c43c01d00030b043c0c401e0107641e441d0344462484900d07e40100068000404580c0d03600305109034580085031420311401c400d446103549020b0501d809011800140404010407031a0740502070300558030026400380001c2c21300c1c00e02150705841070413401020410f12100150510561801c60b86601c140103104544d030319600d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 504680008 1250 504678758 504678767
    0xa030b0702011e23130206030a0906060b030609060a2706120302011d010501030c170c0d11040c080421020f030705011a0d0c0303050c03120901150503120334 69
    0x3e81c08180702d110100c4e0160718100b810380b40325114100c42007a400e1500d4140d42489084d81020f0400d60069850f00c8802c1c00254181c06810003800c2c0001d011612032526904120f02040c01408c0140541c2005506000440100b562aa441e84940011030347c800c114000c10b10003002164000700701085840b65040801d42d064000c1c003005c032003115030319100b86542c4207440c1c00ca890a10009128501c9504200408030b03074000c50a2001943d40c080e110308002071004129900f0405c4012541100c1e04110340c0e5051410344198141c049640c42c240e8072a01d031543c0e650302011001c49400b9600d2560340d1140140910800169901c0d080c00750680c0e40310780c0b803403401f58045c00b20980e084203903c490254000031410b146006611854200000d02d8400b851510150b41c680e001007003201c078901007008004ca004400861b42030080804400009801404e004400304030b08203500201e20a40011200c22448070280341529008607558801d50300d405c2011000e00400d110b4506850001d1006040c200741d0309402c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 504681258 1250 504680008 504680021
    0x603031b070303080c0a050d0b0402190e03010c050a1209020a03170720030d0e04060f170d021207060b010507060501090b10111009141504120804020a030b0702011e 72
    0xf0381c85042007525098403500c5e41d80260f00712000098000e000f002d14021050b04070920310b6101900c014505002d504145c040030303201050b003d000c030341001c00c4d00c00c00d070800344502c5140b240540b503c0c13410591121310007401d490002c8203980340e0a8039032009905541d1000440c070021540100f445150700d043e01d2051015802080040e505c2c014034114401f44140c0907803205201401c0140504503000c00354400780c0314090628001c6070070540d9041e02107519044900220040d08501c54451501c0f0100206140340110503d2a00c0c115001036203440b4510042d841039411040c1d10910100d60340c1d4851004941d18080c0c000701604081c01c0c08000a80564103038000202c41c00d042d600340e8a403034074102c819102d0801031403000206034025281400203d100350f02c51034501d0b2080a5080d458801101082d18100e003400480c1e200100321018042000700780240d240c40c250b054100281c0601c2d00e0f07000119424114400503008000303070340004030075a10070351145054601300410807031030810304070341d92000781704 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 504682508 1250 504681258 504681263
    0x18210909090831150e2112040905060d0b04170f07030c0615080601170309030f073002010302071407060305061003020c0705100908010f090209150d03080603031b0703 73
    0x1c0c00f84041001e0301c18100e07000210250762030317600d0b10100c0601408031a101d482c00f40103642c440d840d41c1500d00e4400340030442e59152010300d401d4403982003008240480700042c045078030a9282c1034804001031340202200b0b03482a042580e031071911204400c0d40d42e00344105d04000c03d499000040c8441003542101422418501a03501045801c07101000b04480c14a40e00603440035078400300042050a240ca1942d0101e41d00321402d507410306c4800d4002c607103820380c445840007a40c5c100c15411300a400c0b00015203180d28610200302c802440354603143d10008605010080c6c10541c0001da0039041c0b08240380286000611a021a40500d548036001001041c099810a10070192840b4a4141d00c0c0304e802a65032940d5180d01600b4050b10309010480c03076a0080c4907640c140f000c2c035000042c04900030300c180c031205160f1080200c0c0b08c15041c810441d076028003c1540000280032441102c00b070329400c2260211690600b840d5031a51500740020385503000d8442e0415000d070039111000c3c11050046405011a403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 504683758 1250 504682508 504682597
    0x8041e0311100212030603070506030901060e07050a0c02060310030b0a0c0f02120301230907090f06050a020c040906060503030c030c010e0c090c0715182109090908 72
    0xc1100c010001050484a0b400d001648061070110000034540c0c000c580008005003191007490f0f8600c085959038008541090181c2d43d03550041010802800c0f5050b0300284514109103000b4074000080d081d94081c0c039029019440c04400582002da44013045006103401070400e551034a441c91084001e800340308401d2000440d044044444030b800043c80030720000300c0308440c5013583c1c20540300c402124103150885d1f005188403c03101045444001d000e40c021444e90b42c0300c0300c0b00d50030500c0e01d00300c82c04194008001c00400f004a51a00c0d40d002c10a000e210004403404135100d009410f0000203490031340c100550502002442c121040d000100401d0041da09070024040707108100782050f210001104100c0d000b5205e10000b075548540c09008040717140c85408d045000481c141d403200201d80001d242d0200da501c41c03075006c8007802a9007a00c408c11012017000c1310008000600010700031082840780344803403034581c043c100800c50a40156644142818120320000c02ca84154080c0c20030141461101203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 504685008 1250 504683758 504683783
    0x30a03091716030f050c101704060207080304030206040506063106030501021303030201150305060402090414010c0c21021e01091506030312090b1b0d05010e06030d02010509060a0908041e03 83
    0x1400c2080d01fa288003501ca41301d9004100d545130302e22410002c0108203c0741c007542085074000150170309000e14043d60081c2d00400503403803e450964035010004d401c0c1c80c400c500300c0c0c0e40c3d00003440181c800d00203024821201c204c495010034103420f000e0541500005c0440d40040751000301d50603203906010071607002e0b900a00c0504111219105002042c1c000940141c04c08000100581032010030305802c0385c883c443c1218091800d129041c2101c68580140000a500d42d002205020b02402d02c03103140321264a062010300303420100a5a00c410044441c000c2443e001d90b20032000f1420b6101c007503081c0c0c0107450f0000e03095903125a41d00800039800110f0106140540924410f074407031090010307440d40a54000119100c1d01e024800d8a489d0b044540003600702004400c1c014509806418002c1c01c2200b219405400c10b8401c160925040303604c40021a0725110420602090000c3c00070380200c0c0c45040003c04189a080842c02072049800103607800d1080908103052000b100801c4c030840e809100ca82102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 504686258 1250 504685008 504685033
    0xe070b0a09060e0d0206071b0f0e07030506010f1d0409081b1603062703210209091f0b03161b02060304140f0a080315030a03091716030f05 61
    0x9200340b52003e02d40211050034a0070050500d0401820280d0007000c229045110110b512405034502d50065403401d124003d00b0064400080420f0741c000030746d41070900ca2490804002880151808910002c00071143c00300c4403c1e9140300803c12200c20058000e01090a441c1010800c07907000d221400b200003030010100a001102003807100d0310580c0002c8940d20743c0d280d0384642014204c07181502010142e03039050050350f4040c2c0940040624401d0f241d5480702081409401540003001581b503c4039801000b94400c03030b9540030072260740050740310802e19130400715030b228141300070302034100344842a8000140400002000c03c0381c070490406d643d542c11942e5101004044a0800741c000239004070090021600103490714210510241e004001c640e45210f0f1314064500e09450040f040d074028000106014070f280680c1d50004940b40154001c0c50102807542d03000301040c08070321414030703015180400095100d02c2405101c45411032200f1081c0c0d026142d04081e088580310700012981880350382101c510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 504687508 1250 504686258 504686267
    0x1009110d03090911040f09051609150302071109070810060c03090e090f1b0103060f050d0b0711120901031d0705012105040f02030d0302030c0306060d0e070b0a0906 72
    0x440e54107507100d0040ea450b2003040300103080d0070491600040010300002c1040701005103100020806032070082035a007015072400c0140c10b05281d4090800104103001d001304903010703c950f00e00340d625103030050359000c40b81032665070075440c5210181c1c00800c00c01405000c640c860303200d50080c5a00c1c041c01080c0e50b0b84203000d0782c056480520003008201c00c1001000000d0711b4268566001070305c481a1030400c42c0844405050000c1110083c880300c000d8003d06207156818420362010b045600c007000c1d4020b06140000c2c0c4882d10702d210040040006000080c1c00382d03c01c3d1914900b42440d0001c8030070111b000d13414102c403070300310411a500281c503140c0f22130b084000232080001c02e03848545c0a810901d00303010044602447c5805803580c043c94607401012f55456900c100303171180b130240150314403805540c4100f41c2003518264082c420180140180261808040d0403030303411440440741559035281040d61080641890f00500e1050700454000003000500301c0700a10340c48000b5a24034220545a69080e43c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 504688758 1250 504687508 504687529
    0x10b0307030311030c0a03050c010e0f101e0204060206250f051308250e01030c0b03060d02040c02060601020f01093c0302010b0a1505030402090a0e100911 68
    0x1581540082400c001207405048100c0e40c40101d0800c1c1d901c0d020b15004140e290182c000400c80004000044d04d010291080c81204c9202c46868064516144000101c51340ca2a0003800c1c00d4404c2e03074400c4006450840d4804844ad061a0447c09549842e901d400294071070000300e41d0400d07804020b41800c80c100080030945084292503031540c402d0f5007490b180496294002e507140d0309800e07039550000b283d00034003040170740714a12010240800c2c0c800c1040141c514500217502c009901103d010051002440000454040d250700c80c140340c0d12681d031180010803200b85981c1c046e400c1845c106401c85125801f1408031700c102c4c030030b0f021900e64023019044d003402c0310000c80026000d0428071100c001148214003079079040a0303403180c00c100e1070310b00b4041d1101e080d80708030300480240c2e6440c001d665503800c1080d1450001c0140050b00712409040b603501510500c00208020b1048a8074070000f030410440f03600112002c2800f8084969481c00d490f502c500a0800794000e44500c0d1520009450515140328104d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 504690008 1250 504688758 504688781
    0x60106031404061d010e06100801141501020102130920031501032c0d020f01060510051303330c14180913030e0d020f0121060308030906010801 63
    0x2002166a10f480b914000c14000c450883d0380c40c09540c64162502090049283c0015004c0150419040c00c5054144141c00c0c3e50020002d0390404000141422000c1035a50b07200b101c9088500e2007a41a4004034020300c07604501ca000116080000301e107040d1a80d04c4010201c0c82d000100f20b030000e40540c0001c031404126200032001c0041c40c4628055403080c5c200c181020780210703030350344501007910046140540070426803015511201e0284111a0304021204070071655000030400702d4140400b1401c00d81c04e400000c024054002840d056504c1800b1480c0001c607003048031181c500000c4102c440c9003070300031220201d40005402007175030060340c1803150034140211600c2c0d01c41815004150400300345c0054442448041c0d1402c03042e02c542c0c9030310605070321503080706004101c80d030080d260280440e9103440c00c2c64014180314039841c1c010703203030700e1410b1104a02c01d00300300d0000c02e41d103054680c0c000ca0021070180218108000007040083d00c6002d14040c0a000059400e160f072030711112422560762042c5c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 504691258 1250 504690008 504690041
    0x60e010c05060c090612070201241d060d0b0109050108010b1f0305090f0a05060708071b240e0c010206090d0504031704150807020c060405013c080906010603 69
    0x410b5000380d40d01c0040c07404681c0070300001c0c00c140a5807002c1034002c0d8201c91840260351250075410320070602b8105504600442e1a440d031419080c040d0041a611490340400301c58001040403d485035100403000c0000d69110a0042e004e684076032081d40605828825030080d5030070b0980603c682c0c035080b03c1c40e40c200070207510f002514400141d07040303001c0c007801391030202d05015030048107000213000e11103002818018002003669090252000b000b86a0041070030003046154412600c0c130016a0440c3c18015400405c1c84e040c0401c600f0f192210320f001c000d01d078003995240501c000a11000840c90304500f6009800b9200c0540d100c032813541c4c4441c00b200629000510400c800c0c000120301c50680c06100c401c01c07040c1410f15464a4110086042110044001c03c40b103004021541e681000b005613584415140241070514000019200000c1c1c407400001400302501c00c9520120182e042c0c54030841011420082c02420722000b07425650207980c8051640540070020400030700038068a84900d18400e030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 504692508 1250 504691258 504691261
    0x100812120a090f050d051206060408031204080c250605091014090a17010e0123150d4d03071802270d170904050403030501060e010c0506 60
    0x72440014124070702e00310303012041d082c0c84201242c0308012401c2d0b45241ca4441d04e507203a00c0d00044098130800103207804d00c02c0004200a00c803114022003520030741440041c10104035101c51401111034002c600c8440058824540d041d90201c1c9081950318403003011540740100c003500c13000100c2d0340e84078100045030001800b040f500481440b820541071440d540b10750003810304840d0b200181c04032545610403643c03141c0070035080c446518284a90210780104000070003a00100810759201712861034401e5040040da400061400b414044182d20600c000400d050040d10b06071130b160640d0310364440000110504036404908616110882d02c401400ca003040805034503090798000007034070601000d01d806002e20040001c110341003030a42d140c02411804003603155080350203c0200c05113080e200100380da48495081c100c0c0d840c0c2401d0040000d40060740d4040000810388d03500c41c0c40c8a000304158100d4901420072040c107074140d104a047e541d050361035480400103540110380c84180c150340503145800000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 504693758 1250 504692508 504692521
    0x10e0a0218071e0311040f2102010f0c0602070c2d080c0d080904330b0d0e2e0e0a0b0115210605010906050408060103080714030310081212 61
    0x401560f0340c9012490003013a0503041c659902c01039003081d4006a20101c401074280f000c10048480340400e484200d00303514000c9a9a00000c00102c3d190a03c4024000d03890802024043c41e501140d00180c0c100c2c0b00489125540c00c101d0001d98074899015010344503903200000c542d1075004c080d030304a45038980107001c00a139241c00c1010040f03a00740225113401c030811a40805468074003442c1000000301c11015550400521603030012400859111607001d0704820920000c05004191855909540c0300020380d5808100124540b4084100b01c460341c0110700300c1d400860104a010200e20a40c5000c00e22a0841c900c0c185999000901c03c01807545044100502140c1600c0b20000600343c0c2920b4104011400e044060ba04546614003070241117448000a010707958110b141c0c00010101c0345000c03480c1c6440c0082c0030303442c1d800c180401443c400c0c0018102c0180f22101c00014a01034910381960b60301d0400381d00c074185031944c500c501c0d02d0300c3c01a0300840801000110507118646002d0010f14070030340d01e07203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 504695008 1250 504693758 504693797
    0x40e010905101502060a060b0a09032d060204080c0d0209040f02150703080f010e040213020304030905060d0f0e0606010c1103160e07031a180414010e0a021807 70
    0x20446245940d10b40d07400941080b0304030200044540701d401074211414414074803001e4654a810080d0f03034a0301046501d880d10f80c080d0b42e8104807600030320482c150b0300d50f0003040c00341c5440103001070b1550710b402c410100070300400364010000c48459800b1039604503501001c1c0401c1ca200d101d0080d500011480016010032091107802441a100500bc0c003074030702d007a0044080781e403c9280258000349084d0204003d5800068686000d001584107024082c50b15a0000d0b10f41014805003410707241c0c010002c40e0406001d00e5540e0081e100061a254545021894140080c0410328401100600701000902880c001003042402880180d41d9085c2070b034040d0300c40f6080004000f69050b014420409451081e56480e4659406003840d0b80850085042200c001026122030a8196414500b40344a0740c2c0281c0c3d83c01c0640416a08034058444e1076510f42c1003c02409001c10050101c82d42041c141d80349034076000c5003040c18a1701c2124900c3c1c5c40c2c40c91009100d803074001120401c0c0820801020003400000f107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 504696258 1250 504695008 504695011
    0x2040803211b03100b220905040807080a0315060c0201121e20071208091603140c0d060b0a140d0206031b040603050105010806030d080a110c0f060a050c040e010905 72
    0x760307264a01e11680d91201e0017072992100c142c0c4980f010501c40300c0d102041d482220703400108800c00c018841c0d42002e4643c4640d510520b000180048030028a0790b400d280650042d81d4514107500c00108440d81d100710140901e44487c508030b00003000d485c036041405005108440003e04000d840d142088541480c041c020103000481c08a0703c00322455042d00350389107a0050212174800e106a480440d4850304c00b508840010f8900400d58110700e8091a0941020f1020402c60f608030703548843d0142008401410506074500f45500039155501100c1480a1038010b65000c020664508007060759a404403069905074140c90755208138071521031000340c504400134517080752610444040c0c8000301d4115014541c0150700030004a80c80308010442907801040301d60f406002503014151460207580300419500c001011129940d5540d54009030380c048003c240d4a081180384100c2c0c004010310740700c003a90380e8030894607c41198207110002d0b100348481c40c16107040303034424501203c1503406d0910b0030014020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 504697508 1250 504696258 504696271
    0x29120402100302093007080303130606030b0f0411030f120d18060b04050a020906030a09030504082401060e09040605040602070f03030c0e010318030e060d02040803211b03 75
    0x1000e1040c2c2e040b9580d07030407450700c100c0089054811030fa80c0c00b0045d8189242804010b25154201c0002001441008011a640500e14000c8032806c6ca01c0c92801e2001000b403500040c0154030f03500d0805c40b41301e4070b01c02098022405003202180c0d0303c0114040544c0d801440401c0c800981040001c030950040240203002099000c0602042d0042000100e01c60605050700541c2e8103500c031015a0b5042c10070f44200c0383c103d10480f60a500d08104180462098031024000c0a03d0f6076441d0210340c01c1c540305900341c3d8090a4080151500125148030000148084810001d0100744c40b070b00000b401401410702c0c40c440480a0030b140c445644584540380140001031094440702d80030052440060400c40000485500c640ca0010f03400e0000100144800c1c103592801c0c0c1414a00024004812401604034460310390516151441c0d9001c0d0f0041900d5020350021003101ca400802c001c201c4020100c09848040c1c21025100c084100d105002410104299400050039010381c1031803080e620b96000641c3d1190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 504698758 1250 504697508 504697511
    0xd0e06070504030623040c1a0301060c0816080f0a020f070303020a0803070302070c0308040e060117130303090b01060804051c081605161101030608010204080d0c03090e01291204021003 81
    0x41d100070451117142c2180e080303c0d0811003a90a0002c0d11390034000340724440503080d920382590705189020705240305500002d45255004104c0320320110442003035135002c5030b00409458541040c1800301c003090700041d40702e00c098000d040b060b5600800c0000c040f8122501507000340001c0f00d041d10769030b41c03c0c0c0c030141c240820903070200281000f1840c0c120b19000154441c026081d0b03128508031814080c00c5000d006c0f20b0400002d03800b03889940841100031074001060b140d030b900644195141c00d50041c000300100400100c0d102c000011110781003007400c1d102d107000b0410f450b20740485449440ca10071200e5401008248000e005c0f0300880000502084d8414450510500d4108444101c4542440040003180c00e0b1184143d04040355a2501a00e801410020b0081d400c003420080d0b030790b4840e800da18090b41002500031100c0d0500d4030480140004040c207650b0845c02c1e5844203800004ca00c11351034041c850f010a02c5820140110603021200340c464203040300303501c0703032116400c009140e0b201030181c00406 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 504700008 1250 504698758 504698801
    0x5090609210d0f0806101205091501030b0402033307050403060207111e063403030c1815080a150f09060e06060403060e0a0c0b0d0e060705040306 64
    0xa01000030445100541d00c40030f000814424005207120001400940102c044c083ca610030700d40c000300c000c00c889908034008a82c0c2e80e00c0c940102c2ca014505c4c059a8480450030000000740324800840c1c0340114029020394242e44040f45082e81c050b2200041e12103498200211205924444a01aa000a5985001483d0a0750b9482e180f00380d03005006e0644c0e07009a0818021420b02d013504d03552001e1000c0e61b69807017601c444e0b6000551680111084100041c200450f852038040720480100d54100309024101c44540790303414002c00a04452600202189000340c1c0c42c600c0c0181c11422904482c641c2e0103034511a62000c504444601010b00048440c580f41c907100084905809611000b03000d040daa01c0b0101c1d850210f0940a55100790301c04850f060340c032030501100391102004c540c203480d00448040340000ca80310000c0c0c9001c1c0010f1000c0c10010580c84003080f6005035074000e18800301c01100030701c03c0d084002caa15480711030a998170008103404201c10000501d084d0040605007078a4062030424 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 504701258 1250 504700008 504700069
    0x4060902060705010b010f090605220f082415100e0604120b0109020a0e0915030102071109060405070912020d05010e060f010b0307050d1119050d0b0105090609 70
    0x35500300305421500f9945809400c109541d01080100b40210070b450440c0e406841c0090150007482031100008030080c0c00000c5296816400f5861001070000d20501918283d41ba020a40c40d000300c0d9a0780782181240004000001d07a80c2d1600d0350040882a1a54040c5407200c0b04002212030400300000c01c7c4503216015410598999024200034000c20710311403000c48652801448200d4141c0041044030710620140c840d00d980240c0100c65240b060711001d40300e40710f5803000c143c44815500300c69419800061a802001511420300c0d1503070605407100459502d80d80c080200340c0d03c040b030320f480004400300c1c0104201e0040300e0094903980e0003d04401585a0705884003400d440b055200c61086900680510a545034018101d0340100741c0c800d140c9081d41800c1e41c2c010401d01c03801800c2e003005034842c0d00301d68054840000700c0d40583d500740780e0609142d0b44128064010342042141030013041ca03240200c3c15a5010310101c40c1d84040040000c0e10300000070003004135038850010036907103000c0c00c4c0040014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 504702508 1250 504701258 504701269
    0x9010e0909190804050a05061305101e170a1e0b060d11030106020d181514161401061a0c0712050f07060e0108040b1f0303120c08070507080304060902 66
    0x4005029050f640d9a03035060000703010488038243d010b140102c00070411403807507590002c103080607602c0c00c40d5180e030036004020044600f20740c6484100d030380640013007068040c40e4002046200002c54681815801d60341c0c01c400004440c003940800100d12004000106044603951203500f05034070041c151800c0840d40c07948030084601d607030114002c03e80000014001c0d160100a00a0181c8031850009403102c4c0092810350f11210510400c03000b0b009803a17508503868061030950407480207103404a51202c465105148100010000c1a540010020503001d030804060080101340c5900303030102d21200b42200c2c2510a19070207600c00401e54015104046070104034006c10300e41071400341000b400501c0100c0c11b00740c10888554043c0c42440541c00201c0360341e9811501d401d9100303030000b020300103d90328901e4a0308110007c982203501c0c64868580401010341011030000c80c0c19188108000804d2104c2083d60907070b4080d100c100104505210f0440006c40083c000e41c1d1042c400d690214544805502066 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 504703758 1250 504702508 504702553
    0x1e0302030603160305030a05070206120405011a010926010209060c150c071a0a0f060f0303030608190f290114010f1e02150a0903090b09010e0909 64
    0x66000400e11996107400c024500e03d9000518020032124919918145e5070710440f40f030782040c0030010486109565038103090f03890404030410403c1e500d00d09403070060f0007007101c1c0c418520001005424011154810600e68045d54410100012074403070a4403000c07400c0904094010b480d64082100303c01c50385070980500050b02000000f401d00303000d40c00b40f00d940c42d200101341d001c90300f80610040010440700e0070a4141c1104000816019407038010040d0094601a91040c070101d0400400080c090100c582d01d0b002c0700c0c041e42d42040616110750902c0e0f15082d0440350440030303800601b00800400ca001c617118021601c9a40d1824851001001c410742c0c1c40c100d86950740c459402c580040001802803107550181c0301091074240300d04001040007501820442600d96103084007000402c0d18a03000300420055404e540c20038210ba0f28040c0440000350940402c110700060075514001000202041901d90b42c03541612480705030704c003840c04e005c01094020109070702d51140c020000500c691aa0411 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 504705008 1250 504703758 504703817
    0x305010603050607080c0702100804060b0307061d0a0311150706060b04050f01020d210f050412030e0a1101081e130b01140607020402210c04060206100503030a030c 72
    0x200f000e4907203048043d00d40c0c40300070661440303075204103c545c00581c0c0c3c140c0c4040540c0c3c01410300302040e0311103040007c0100000c015158142c031440c240482e01581000401e2240c401a0300c1c0350f41195042401e0000501c06488010400691030a4511591131700002c00100c0003409604641041250345410043c4c4040c2e0703003e912400c030300040600103402c3c0586507072900b020a000409900c00d074640c0041c0001ea003a020300d46060560403160303513400786075042403400390642c40c030030f10450400d41003441c55100c940700703a030b80400e141158840320000040341c4081d010703802c6507420503007000ba42d0041d07600440052807644280c400c2218422000c103410580c2d8040c24404101c000c02c4107980c03030316206003a01a00204a041e603813445980352030343c828040380c80455040e900581c883c1060992101080d804150550b88031214004004051080034080c0c01160702c1d07030b4210b40b041d443c1d02c0c00300303034410096001c0c3d40d4051704104490300c51540260001c0c0c4041006250008503000e000d002d5141407032010f20407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 504706258 1250 504705008 504705013
    0x1915180609180203240310150e090609060103111908030703080a0b0607030c17120a1b14030711030a0201020a080f0c1c091a061e0604050d0507030501060305 69
    0x10b200050840522015074860181c04501d941046420a80713000114000007000401d1001e000145413414082c111200d10f030341c11b05100d610046208081c03003080c00d004080282c02e0320b10004642c0c1e00002040e60141d03503040b025020690a50702d030751200302580c2000c03d40149081025050000c2d40d132120200509a000c051a100c04445c0b40c000d200b60340140140c480c1c0d5007403400342140c65560804841c42c06501d424003099224288c94951610b01078028212405d0002040b41e40c40c195542410b54803441c0820010020b00f1900d03d410f4220482203010303040001c030f01542902c403a244403001076800a030141450981d070000004018034650103101c0120040c1d4011030103407550f90b08032031300707a400010b029910f440c24545041d025086004644c20104c98800902800015010300e50003c0da880c0c3d000420300c05510514650846440b03001d5500b24015120f10400d80c0c0007440010655a003032074010b00c120300d0180f500041001290072590152498001c5141c00070000e0700900c1000c00540c800d201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 504707508 1250 504706258 504706277
    0x3040905041a071d0a08030c01060312081611030702030106060f0f020f0d03110f04080c0a05010e15031008032d03070c06050703020c150103050c19151806 68
    0x41c107040700300b4121000e0041c02c4020082c0700080381c1040100c154103807020440e2030040794180004407101da490380000014000004e2803252903030190040d101796802450341030703171a04107a842203c1004048030f04106904821480c0d0380700c2845041c07199034042410048078207007a001c2d00000c0c02c542003640044045407004024682c0c00b504101c00a2550815001504500031504402030311014040e0b80901015611880d0000110342e0343c00f0751b80908024002c1c5900c40d0f4450759225524160328401c0c9100740c5404000180d15031066220740100040a014000f062070310380410714036500082d10925079012403030004114244100040c1c01407001d81e070b9040f11107180c9040e030740701c804210342400030a0035030030400c2014842d00305000306840c56020301d001a02d6034812004038004e01504a491080c0e005071445004108080140316050364000c1c410340d00510005001c11030024040a1000f00d0920b038003000f0007280e209190b0881c0040d02e24181440c1140c0085103440e0904031940212001c07400441 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 504708758 1250 504707508 504707513
    0x190309110604031a04020a030c0308131401050a0f0212161a0c2d0307021b0102010615050c070504060807060f03090f141f020405090a060b0901050a09080304090504 72
    0x800380c10500040d40d10a181c1815500c422086010205043c141c0c0344519012070110f45038007031690f0040d60001e03001c804090300ca03e0101125401803028030f50011000c1c00c00704403120080790004c0c0c80b4405840c0c0e58582213820100703445c90a01e0b21000010740c0102c03040c4160001030707400141803d500305503401c0c540d1401071610303c0c00fa40c120340001d807514940d8000c2100701d0b00b060b02107032a0040302400c1c603108880007620003100140086d0520003805404014421401c2c2c0018240c90040ca82d8a141800854401c00483c200c41440c41081c03005400c005031401c0080c041c00042c424200041c0544840701d0702d41012a082d202c0d5a8800c0020307a01040d810040c450f0b00c4100520010a039150600c92100c29480e048400d229075240a02a4090020744075600e0008101c05000c080c16a129404107525090382140250031a21030700d1701a211403c0081c240395018230910055078102c909407810901e00b0b20044519811090f40501809690140800d080c0002c10150004050040d40400c8524291 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 504710008 1250 504708758 504708773
    0x180803030112210c14030705010c051215060f0f0d0905300301030b131505010504140c040608090a0c030503040f05040207020906012105040605070e1009060311190309 73
    0x31018142c0e01070503c00c050400d964032004400f4800d80090404418580c1402c0460840c894514001d01c1986040141103400c2e030004007a013100c14580492655a9a40c00070340994480d9011070700394801c00410850402044090190074a402c908031030a050030781402240c000c03240c18400650f00780e481208030800000c4505400c0451660040c040e10303054035400101000ca001c103010040c41140b007480081e0015014000c900f00c4641c0100b01da00e07107030300d00c0b008141c024142809524013850411240303012105051480e1130044d0010480e0500e810b1500c40111a28440907124200b1806090803807030208450802c12006980900e01660f03a031850208900d0300441e945d07104502a60040c000c1c50090380e1403444165001d2001e0170009a41c5800008050051603080045d6000500e0720052006105072a4402032103990035840d01c0c1111a41c5c002080f16810921200e400040e100810034003030749101c2d070403581403c45100d074918107044130000181d185100413401100041d0b52603003c5e50034081b95 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 504711258 1250 504710008 504710033
    0x6010302270402060d090222050601050a080609090c03030c2508030a0c02041d0a0b0601050c03040614070b0103030e090601110c04050c190f0e0102010516180803030112 74
    0x4044049107040c1841141c1550060002e2000e8800e220105190b0081101500001c030060341c010440380c918013003400301e0140026643e600ca0b00d1076140c100011040d5000344229031503826140c84640c0d450747d52030108161000000c0001d1040e015802c40c200c4180c404202910880b03219030f01600082038000302081050210b80a8507202d054000c008102c007290102c12038400c0000740ca8086490f81d0940082809861000005080d1182030070541100311000302d000b00d2301a1042e20144c100c0d80310140110345501410750032010a4000300000c00046004003000310b600700700300c0d403040c1c2009450b44901e00f1180b400d03802500410706209220701180381c01c504a40d030200003400d105080d030f4004d80d0b14681e1100304a90550082d40d4031000324003080d15000580d0a0380d410f134107001416002440004000400c400c54486c00301d551481094002c1d801070194901c2a200810302c40348013007411404485601c280441c4c2c0d08a0409107a0205402100b0710003140601202516042c02c1d60b8140b4208604905 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 504712508 1250 504711258 504711289
    0x5180609150a0902010801091d0708010f051506030c07030c15050a05090a2109090c021c0306030209060907120501091b0507050c0607030203040e040c030606091a040e0106120506010302 81
    0xa441d0701880146e0b0060034040c1034900210001411111240c0000d8000c180060b050740302e80b04204000841c10b034150411220401808003e01c0b0b26120b2500c01e0ac651400c003500191701180a1002880100200000c7c0107614043e10348040d9140564903902c0d0358000c0c41d12110141034440c0c0801c180b0302c8503405282d8103c601d0500400707c0301c541d5120f00c0c00310100702c040c2e503d440b41e603a00c003140120f100d03082031009406001d00804c001861400041d40d40d40440c001801c03c1d1501e0280300784007074040d00c614012642c02600c0c514480c1e694070f0801c018100024000414024807a40c01e08908842e445064041c00d4021000214210450441030a5040c05031800b0700f00082080710385c00003800070500c0380111505071145c41d01d4003151701e0140d05500894000d0f6119603805002c100511a143c4003200172039006003c10803101e51a80f2420040c0e50704034150750b00080c400c0310052107a041c161f125209450300100000340d40d6444506500c014440ba020903151a03105100510940c038054081890044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 504713758 1250 504712508 504712511
    0x6050109020d05090f0a02010f03060f0e01060809030a0e060f07060509150901020715051003170306040501060512060d030504050a0b0904050c0a0f08090a080c0604150c090905180609150a 82
    0x48a0170710550b079001c0c01c034000b030400018200078485c681c0250000c80240200e100c84184080e2070342e200f1000c1da54240b0034140041c08510114400200100c03c84440d100d140c1e4882c80800001d1050203410303030207000402d202000800003480410000d05c102402025007401800408082c0003561401d160064120382c02e99104105040006404042c140c40d009420003021500f640c480e109a55034039400e078009000000001071600103800302c0402144500c0c0d04a804000c60313601c420302141d8034010802044802c0c407035000410b045e440c0951a851070715101b0b142007031400d92590081403801d81c0c0d543c40a00a400081601d81c0d29180034080c9a0380100c900900c00d0401410f020001d2080d44006000340a002140c8007103003010b48240f0003004095000841759a031407445424095072110119002d4840505401002140b00440d024404a8049968640d410035080c030119074003c00e0090110782e0003094180841c50b1010050100c58407444c001c1010308a5480701c2c4103250407080c4003c1078200c943d0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 504715008 1250 504713758 504713773
    0x806010b070212010908070f1412030703021c020a0c050106050d0809010c03140a090315110414030a060606030c080a020a0f05090d1b0503010c020c0d08070c0306050109020d0509 78
    0x8180d500686280e1501143d00304180f90010031414018000074001034050100054a02c1c1404408481c030f42e1100d1103924144071540000c03c801e5203c03800780801d001000010808107074424429000f8141e055040c415813000000070b1002d40c4208e85c4040d0f003500102d0180c056103805d04c5402e209a40c005c0100303a803004201185603881e07035214494100c00764103106c00003844e10103052042a02c0071703040303c0212000d40e45c0d201d14a000340100a25100440b0f811007503116801011209004c0e09600c12200110346041a080c80782d80c1d04413041903407046400d44100c480c0c002c003054080c007440004000382d4900080c0242900c200600c1d4481c01402c0da088180104017180c00c1541c4a51004592000c0f0b2030016151307007240e400030b051540400c001900403c00a42446800010b400c002d404841c1c00710000c002c90a0404d00a80e1105031155001da0702110003000c540c0070514010042110502c00c0c0b0304181c00d5030312036980200303c070000e82000d4206540403400d9401702e1502d20809800c001c4540050402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 504716258 1250 504715008 504715019
    0x321b04080709110412050c270a0b0d0510050108010b0a060f0507030c14010e010c2607024e2704020d0905010f0b09010b070317011e080601 61
    0x120005403040b40c0381d040c0e45101c0d5a6568845900b074602402d4144c8280e803c0150714180595940300400d0101e100c2d0344298011814199070010520070107121100e514a00d54800c52600004e0540d0b40c00b1301e4018640e0042040041c00521041c070801118400011303035035040044e05400c4400e2282c0950003048000f105008164001e600890100c1ca80e1618a55640440c54200c403080b00305071000b1f02c01031080924400d0b011045d04144a2901020001c2144880071030080343e00251600301007000a01008192241003514010164480e540380111055984180c6c030380b070708240031020013082107000a851882400601482805601e800e0b0a100302c814010340b14241d12486407860000340454039030ba5900d8000741c0d000c200024460018411500c980e0148015000762401e00b0082302c040d441c110f16001008a14407401c141703110050145070044c0e081c819011041d038010030054061110780040c0f0046038940c81c040038080d11490b003403054458240c3c00e1000c00f100d0701e42c004140641198006008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 504717508 1250 504716258 504716263
    0x61d0a0309140105040f0b03060405070302090f0603310b100f05010309060b0a0b1e1810030e12040e10152618060c07030503060103321b0408 62
    0x10365518030606044403402c1c10040e10340d84035a62001510031400d2400042407510700010318412202540c05006075611140704800300e110300183c059104220340804443c60610802455004498410f019048141541e0b8a18500342031032a180b1407009950f80002001086821aa0024512150200703158240080c8903680c1c21a402014105a0755544800501c00d141d000302c524850090300280038151541c0030481d541d40940d400981000c040102800504001c03421901710300a550b040d0b1036640c003200100500d01085008540800d0f03212070308030700044400d1005850010b9a0320009070b441345420700da42c0e9070841c024002404c020310303010100710708500309001c0700781d2650518100400628821080e4402d00d0000890007212000310104000c82100c44035010300c1251010071200a0341d6000a2035009201e09000100052014404500d0070350098012441510003000f91156076088040708403800b0b15200548658000302d002032181c21005400114180a0000c3c08545403030f09141850340e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 504718758 1250 504717508 504717527
    0x209030303160c02040903020d091205030a0513230907050703080415020d021c1103040302070501030f140a1d0106120f05030915070203100b280b07061d0a03 69
    0x103200b40c0d01500c20849144510b41c0140c070f06900400800000e0b403a400d000f90340f00044903520000c00c55541000c1041c2404203c00807089900000640c038140c044035003100d0340e41201c41b04103230b010100039010a596202d5006d16599015004c0c042111080314001c1107603211001d002a000d00504001840c0840d40c40300009a02c0b49d0004031340b050840d03000103520020711903080101407561010a903a103204082070f405820026000d83d0602410140004001703c03440140d5009000d44e1040504200950194102d80300e28103800100107944160504c00c82c03243c0408440c3c44840381c3c0d4400d040d08101005048000c00ba41c0c104008002282c2000f0221500c2074030342c4006000c2e44907042d45e81c2c00b0000100708490b0802e002600e001c00440e43c41280c40c101c0e8000c0c0408900c28003600e40103a408401510880031604001040744c0c040c9400c0200800b40c42c0780c1c84a10f0500b54407422004034105a205000300b440c81e02c1898005188a85040b007803020384110380043e070321a0418014040402d51051490 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 504720008 1250 504718758 504718771
    0x10509160513110d020d0b0f0111060f062b03110610030f0606050d03180605090604090c02010b06181804170d06080a0303020a1706011d0f04060305030a120209030303 73
    0x42c8440f151144802540915070b2480c3c440c0340002054000005960003820641600350364401c3c1d90300b40280150b80785c0c441c0406120440d489000068a148483d51034140c208901802c1c58000149220015902c00c1c010703180403658a007010001410558085520100158490054116070030101c0360302440d0304c160310018000c04103e000000034420701d5800800103181c002c2c0210702c10501894060004004d00107030305040d003d1400300180c094014001c56031901c2c4010001c41c60141001c607001c2c010300c8801c0305502199070314203003103c0310b03110300c1c3c01458082e503440b41c0400401c20794000c010a0b101100707225889100140f040c4400910300c25503851404900d000f40d50303260010b5894810091500d64011140c5100380c10031041815003541c0204142242e13542d542800c00d521030b89200b594441940e140740040c400030f9800c1038850007140c40c40510703007005048070107e10341400000c098410301d400c1035696800c0064040394064200c0d08412100c0001c036802c0d410011014002505d078080249039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 504721258 1250 504720008 504720011
    0x6070905030d200f06040308070c110d060213140307050312090d05031204110907110607081b04030804090501050d08121909030905040605011407080f130305010509160513 75
    0x1070251002004140866030003140c0b045034004c5681e14880341d900c110688068010400820220700c442c0d108210304024250025686843c1c0d98401052017138110398404151040d036800e200100011410300c0d0158028403242e50301440300c60310320301018205406d96110910941c04000091480c4c42c681040d5469150102c8e101805c0410500b801e42c218071511860307043d06c26030142040100040c21742e080070802020341c0c104134070b503aa140003a10800c2c4040c01030411540907100062040744906589640b05064401503204095805109281078110703400403210700401141c02d01008649201c0e450061104940b500c81d030710001e485400040c800c20030f180980c60b441074002408045a03000c6003417a15810b500401c06400c82e070078001c001c681d19000b82c40c402c27814442c000500750f100342203111180d03014200f110306c2e00076256140c540b254003050f640780c400d140c10f1000f44409130342840350400550280c0c0c00458680351481d041800d10302151510094820540380500c00ca403a46103a04510b810050700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 504722508 1250 504721258 504721277
    0x9010902190303090510050408060103150609060302030c090c090a0b0306042304150b09010b130503010e0d051303050d050319110a0e0102010b090a1a04090f1e0206040b0405010206070905030d 84
    0x400c5510b48210b4011540920ac0c540000082204503101c0d10001d11645200308a601c3e1102c96610540b0a01d110182d819442071850400b03a02d804c0c00c4e1a41c20a10140c01380d031624101c8400b281500c0b00d1a4041043c100c07006c0308100c99030a290081182016a011002c031409500744c4029088880140001d000d19200c05282c42c1d410f2055413081408000c010400c400560307451208408070750100031540c02c1070b0705d406000545400d05000d0003154000c400040e01e008507036520203e4041c1c0013400f040d4201511081c001010900501070441d03150300725a18140e40345400c4800101400502140b94140c0303140080500001c2e0325681a600d551203945007a0300d5105c1101b00403400342952a90303940d44162100f05005262003141d00039000f200c0d503450a00c640c2e08040080004646800034094042080f071781c490000107030041e500400800700181401c10003022600491341903000398004180041c00098148401d60301002842e41c843c400d80361404005090401190b103d494003039100d800c2c828841c0707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 504723758 1250 504722508 504722539
    0x1a070312050115121109280306090519020607080d0e010f1b090e062202030705070606150212030a090510050610111507030905010203090109021903030905 68
    0x85006140164400305009950b15103201040162040c100380000c51180e520346000b000342c0340601c1d4a003940744e5650608000901e414005521402c10300c40d10340491524052071446a03040707000c00a14001c00b40020715910502e8218a0b100d280c03103010082601c500d60400059403010b0444141c60391203000320b40c0b11800005200040c04114101403070550034100c85c0d602d604115802190082d80d0107500d50241908900c0c1507403175500c2401480c0643c54032100180390350406144c0280c1c980c01117120b201850f41818404000c0f0380084c0d40d03280000d20f00145900c14800d09015950103030203140c1000644130049080650784040c08541c0ca4500480400061020070165124407850341e042429070340f42013400501e140081000300e548912a91042c110000c020b446601140310200000000f82105090b0b07001280d22150002c00e020201a00c88882c6c0001800a00181d4025030110002240d440614810421410142020821040782541040020030f0380207074600210303001a5898841d54030601d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 504725008 1250 504723758 504723767
    0x61206061302160f0318060503010b09010c021018150206040605090c1314010807181a0d0f120e0d0201080c0708040305071404140411012d0314011a0703 67
    0x40ba0540c0109205103c07000c0c0003a090b00701c1300d0140310b40d13a01c83c0c50903112107109500395228001c401c0068000d00060049041e01e10003060788020506040030303814043d50001e0b00b010f00d8094050001103440d2003160805911802c117034040e000c00a0750b1660020380000c001d41c2e030a07000b0000f41140380c54402042074030300207001481101001400d00f0416251a83d1172002806c0c10540c003958920070500001202070b004503040741030f03840045941014000b60f12100c1e01401d072041800090442245440c0d2103a981c041c0302d9081c0b181702d0b4440c08155802030509080c40750b0000031450074071000c00c1c8540c2c0180e0321a11010941c541c2428203007800d490320322040590b1301500c80c000303101400008000c414407000054410407510000c151030519600c200500050360140305022180300c220f1008580040c015030200512940c06261080801c0080505201c540b402010040540300e02e180d1202ca00a9060107558024018264109000d5141c07940c1c0c106c509244c101000079008000c07418100300b600c0b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 504726258 1250 504725008 504725017
    0x3420040606020d110f2d100f0c02010603020a0b0c0f030c0a020901290924040518061c030c060c0206010e1e070e0d0f05010504020108061206061302 65
    0x2410421200e62a044003a40d14102c0c48105030200324154090800108001224030007100010081d0600c3e00d20001d4440050440400300050712421005e9801d081204012030400340e5200388010a100364044285c004480541041070308590410000b4005600c0381291402103e0114580310303604c032125481182003000d0f01c001d2558600001031050f03002400050107520440c003c4803044040d90b40c0e82c2810914038501c40c000c0c48481011840c85866501da0b001038248058043c0c413001e41c800c89085050035440800620282c42c582c0858140040d04000003a0100a0480000d000c442d04221002400c0203e0b00e00c03049070416035000c020401c00d807161418031070346907003c403062040c5061f610029403540307400d000d4a6005c00c2c0c004009410b950462020b00445804070318960001d84404c036085850301120218140c005a00401c0600020300491a04c00d480c0d0160000040314240752000412216001d40f03041e02c103610250000302100004905160040401c03200d40d03143c040c0c80010308010b4003e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 504727508 1250 504726258 504726323
    0xe1c1a0a200a05131806050604180213080a06090314070224070c0305030309061302010f0f14040303090f06141602010905151c020a0905060309030c06070534 69
    0x40600045d8011261400c0307070072900025024001161128148601c50260f44160011002000c0503500c440030b2036401440d580d0560032103501034075200c103a06881c0190340c1c0001c8400d01d0b500c91540d014546d1002c0c50b044000d16000043e03140854903000144400300c0c1079522105541d08401551072004480b00316140f00b58044502507142e640ca04026459400440740c00c0c015010b51030000c0e0004074060403254041d54141c49412100807801802c030344448410209105201b00c03c5c40c010420a001d001034401076210b0350325070510a040400804880001da40500b0900c6050150511020b10303032019200702e0980b01c4030005100046000407510090103602841d00254414030307030252a41780b00b00034010480e4689240f8180c101c0c802045049104104a5000054182c070044c8114a0600003c50b00040400c5c100da0400389400340107410300f201079442602181c2c0015442e07050000c1400103045d40c1c1001e001030362050441c03142000703d41c0c801c108000c1c18035120341d040c500480e100344a04642c064 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 504728758 1250 504727508 504727537
    0x60403020103051801050403020d0e060304024b0406050907020304030b220b0a1404080a0309030315060806130203010b1c140702010510050a03050c010e1c1a0a200a05 73
    0x7030a04029484d180b1002c20ac0c0c0c00110000000b400500303006013200d005980c080c014508801403825444a0f091000112901c0c0403100f04074941d0144181a480020030032a468402c4249616020002258502d91045010300350301010018100c0e004000d613001c4a811080c2203147d9a185c000003070121501c0e40b65003d103c040380c05120148003181c04280c1c801e80382c151741080b0035800c0da1002c920744c1e003048900904200c4201300100e42544030b600502640391182c01c000c90b040000044c80301c0410381582000000622900411115190201d0155166010907004501e03650400710407c2c078a10070000303034145240011400705084e25003a84801c400020f6860000c4103810600c400034064801901c01585429040c000450180b50184a0208481c0e0080007820048412001500c61202100905600c481a21104d2202e02e22004001210511071152030014150021111003030600141c501c016841c0303040d803990381e00c100305420346800b88001340c40183c40780d115450456103071141714222840f08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 504730008 1250 504728758 504728761
    0xf01180b03071403060a0303111609050405061f030221030a1206062a1b060503040b070504050d0b0901021b0c0a080102070b07030e15070809010f050606040302010305180105 76
    0x100e0031901440c0540c01c1661a141416a80d20f000c291600040c2d8000d035010030703040300800c00240a217020b282000c0130b0f00162000c9071294030300b244414440b940b140340d60355250810001006000e200280e8080e051010005d0381c610300c0070300c416503043c1078003000780a000b07004c0b9644001144580d103140720181400c2204d5403001c110b60000c1011924103c100103e40c01c2c2500410302c64040e0681c001b0580b0b070b80840907210140c507118240d0600f030f040d400b628240c0900e480c2807074031401e0b40e01c0500909025100e0342c1c2d41341454a0100701e0550b00412190800105000c10700151b0380f010800c0c641d681d0481051001074640c0c2d1101402440780c20040d0405840c024007880c400301d4081085410740c407044400c02e454540c0d60100600707038421407000400c90300504000640460007036000e0700d03c408000040702c0000d00f00b810082c001c04000c0d03803428040f50014082018201c1c09005004103c40403d400348140d04041d070200d031450140303020003414036480c1c000203062040c10b100142121310229009024a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 504731258 1250 504730008 504730019
    0x14100918023934050303040e01060f0503040807030e011116141806090a0b0402070b0a15050102100b010c1e02031b060d0e010e010f05100518060f0118 66
    0x4101c0340881d5042c00c12580404a0041200400c040d0202280524040154900e0150400b203c020595084080c11500c034000700746038500300f016202515a8542036520b035414000007612065404070b420301000010810013000405081c15143c00c2d9505017441d0f800c42c1c0d030441c01610518040052100c981c0b05180c03940c5010051552031504882da41c683c041d20002184080c0003170203401d070103d02c0040c4284000720310f050408810b015804404402c0004a4580020018050b40e004401c00d48000602078103001c003440740d510400f011078083c082d52003030310751130103001175150010031144400041d501d002c2940d85900510300328001070307403003190900d6410312034414098210307d11005071301030300c100c0a9296a0b44101001c08402810003017a0f903060503c00348030030010b400005a442819500c502c10511814030901441580c0054814081505e18150f042d000c840d6026510092190164251581000e86030000060b0004402e46070100a1a5210010b0312001041003004007080d0550f94005070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 504732508 1250 504731258 504731317
    0xc240207211515240c030c06050703060627090c090e011d090712110409050d0f030b030114040b040501060308070b040501050f01060f08150301090501061410091802 72
    0xd0030b02c0031001d031210f001c3d107680c01d12070f0343c5544e29529111502d40940b00c11203140140c02c0c0c084014807a00d411030351007034141d880c18140d503815194403000ca80c44200074803005403c05604900064007203c455116080c01c400314184005501c1803915075641c07103840711582d074030949805000c1e140003550f03a134a95a480890803080400c0007550101080c42c20081035040c030022500c1030454070101ca07021009952074440703400444d0004d1000303510507610140c0a0020710140035800114405072515900c022100c0e01c054161380024440c01d100b0b0b490604010f14400c03840030b00036040f40d0002c0d40b081035035940d0f107003032070040a840d08042c00b00c2201080e01004c00c070a85e82c02c0c900c642d00c01d50003400380d030710354006c0075840300428061030021403020102408810b01c1050f0340c6902c411403d891001d2000c5002c0400d08499070391205039040d945555043c403803030f19500c1d140103030040d0588606450040310b06000340260006c0c019045007410304251a220703001103405840b0b900303503464800d102d002c4c1186991074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 504733758 1250 504732508 504732521
    0xb040314040b0c0a060f021612030f0f050603060906161206050303070807060f02070201080a020a09051e0103110910050c03040e010b12091c1b08070c2402072115 71
    0x101c0c580e003006d0146409a200740280c5051700360410109140e0382083c0d66481d00e000d04031841100b05070303031032800f4000240103002c3c064003110040340c00103031170814500741414440c000b8003104155001c070060001c80100e07100d0000320f00c0c09518000200040f844401c80290041d980100d1b0705110100e01803050120b0f050003009500d1040008000d903000c00c01d0725109a02031840301034041000d000002e810f2032041d0300101000c2500d4034203a0000c984941c000b0700902052085030203900c0700f01a46285950305841010115800808540d0501c800f141c00101c4400504070030b5010001c1c00700d0350403040b0740204203440181071000d088400030741e15000d03605280d0f04070603840141c0d5010840494005100411142c50300c9640200070415580070702403c1c1c4502c800452109241040c48108402050721100036000c518810384031544003074039180b0100d40c01c10701c400c1e0f241226913840c1d8000e540c4540004000c41100c88519001c44040840b0b1282400441400809804550140700c080d020004507803209 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 504735008 1250 504733758 504733763
    0x21c0503090d021911180406020c0f030316050a0c12020a030e120a0b100806010b09190e01032d03090608071d120f0a110a050d0b040314040b0c0a 64
    0x5034462025410b0032665441031030200c94590101c3e440b07240100e18002c0700c54000000140c100c0b0840001c01c284110030042c2207505031a40d95000c5104202c0500c10b0060880e01d411000055041d82060150801d51118601a10301408400038296401900034400130b590300390080607079401840a07401c06034441c556520f0031000107080c1000462289080d680100b18415410010090f541050f52070141401016194249889903241c0c001170402d010081c0794040d0400300c0030326451700c400d801405080007458080c1c644c08400141d040c000c1c01d0142c0c2175541126044060400801c01a941d00d42842816030306004805007040741c13610a16030071592030000c4400700c0c2e440242540c0c80070f00440d9629074500407003180c0b074154501c220a0340791012080109070030000a0700c0c210401c280000d450040400c500300d8400f521940004074600d400802c2100034030f03040d28030149101143c1c0d180000044004d05c0201030100c1130f49022210001c40003514050040c80310140c0e50703076107601c1ea0541c2d10382246004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 504736258 1250 504735008 504735013
    0x30f01091e03231b2512060b0406170c21190203010b04150f08060106050a0818070f141c141002041719150c021c050309 53
    0x3080c41100c40c0400740303922601070f9180000c02080044559a44000c0c01c040c51100105002e00305114580468800180c001d200040804030851a07000800d407615590040010300550380400c0b01a003d60403174124a90310050000384070384420f000030001d26281d00020f8440312610340000b02d2440014070307110b00b0f040c12102d03003030074a01c3c003d10400010400038003001a070304011031b0150917007041000ca4180520040c00481d0406140c00843d046482120f00e85410841e50385080091a020305540303400f8000c1e060107006c9541c140b40010f0030910410081e2810040c102d400141201d100d03180c600242c4202c0c00a60700318a0795001c180780781200c940034508000005070105451403418114148201018924080c1e1060b065150074a200c00300718020802402000e01c9180c207456548018000340c0a00d0301c0542030018440c0740d040c504901f2540c0102fa401d205482d0300003054502c5022400c004c400900410b49240354507040b800c0101d004202d2001550721a100c290003a08070740950300c607140030401c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 504737508 1250 504736258 504736283
    0x90903020f06070e01050a050c0f0601030c0f080601060e040f060e100603060e010521061e0903072105090402030903071a04080307080c04050d1119030818040902030f0109 75
    0x80305030b150031041d188800400e210016600895000d41c1c0505011512401e186051800d4046003504021078512851150703000707100107004004882d440c130001352074103000300d1074080d080c140219030b1800180100000e0040c407040142c8940e031240c000724170310185039400b03001c25a41c0c0e45040242c10005c0c2e890b2840001c00c0040403810310b11a2080c541150700e10958092540d10307240900540482405003103c800b00e1000955000e400200703e468001d5150b405040d1000708503544101700c0a101520018041d00200300080100e003011071420100311088544003902100000c05035000d11a5100c80c0c1d400c10f00100c20001d8a01e00030000c0c100307603070007850180d40c081083c51000d08400c10440c0d00610020301840440c1c145807281e4192a40a0047e0041c9031030305482d080010502c403284401100c854450442505140c18000c42c46401c100401c070855104030b0843d42c5041c01d03030140080c04440c01c4211060b080c83d41d40e030794102c0d001d07058018054404031450345140e503018000400c002d4402c1088241c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 504738758 1250 504737508 504737533
    0x8041e0c031401110f03091504030e01180501021b0303210a0f020703050d05041b03050610060305010f030204020f160c1401020307020a120c0f0f050906040903051c0f02030109090302 80
    0x4d020341c00700070540043e180c10b81015101480d174001500d00c0380f0f64402e481c242e988010f50725a506000714000d440b4000b101007028001480003c28000c801d6030401c1c1020200302c1e0303907000182200800e00d80b5030341c4900e50398040007092842c024400c0300f40561818450b08000304601c8005d01d8020b18251106104528000040c5026446820001030001710100a0003880042e540d1006030410701ca051044201a202c111006c5000310303d0f08141e0700c641000c02444020005c291820005118a007000d101d04d62604007200c07404012440041c1c0903540008030282c4080703d50044a00c00b1540c5490814100c1007410700005102103070040d00c001030080e1030408030660002040da06999802011940400c0c20300140001002127810308581c0c11100d00d03c040744d0000c031501c0300b0001c2c00b080403107804580d190034200303e9090809044940554942021503000c01d6102c002c9031000780ca1204030042510b01107941c2c40042600b00c501c7c48000f44040000304a440d03043d0446020a0300a81c03c460140030061b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 504740008 1250 504738758 504738761
    0xa05120a0e060c0d0503040510022a12090d080409020406020102040f0801060b071e0501050a1a060903070608070c061e0c17161b14060c0c03090108041e0c031401 71
    0x25031203800c2d503004088044406215400541e84188218192782e01c4010300ca6401c0103981054807450070f1500b10b42400e09040d03160426015140b07000c1c070010200154040c024154610440e03150328011555600c840003400f00200446008101100301155501e5490030024002d401c18040c1641d03404039490001180c2c001409841c055a44403d401407801039036598031441d0304034041d00c104d010107007000d900700442c00c05e20a145c4500c21444c400308180310300200d4000c2c8500902103851103518148403100b41038900044c0032049e6005420040a02c0e01c494a06547c0b11424000080070079060542166030b50b01e244040035100c148001c030a1200c0d5071000c0003940c0340e030901024800e98030500400501e1501701c0041c030340d440a4a50814090910102e1008143c0000380e80081c1d40203181a0882844004d040281c240c1c468801002c240c18820740300070042c1c0b030b0311669282174104040742d004523040c0800c5021060007460315444034480000315207883e025150140c84155103003130f025010094a12810f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 504741258 1250 504740008 504740017
    0x9061e0d11040807050415031e050705040e0c060a110613050c010309080901030c03230108100e03040e040c0b190908030a0c0b0a090b070519030b210a05120a0e06 71
    0x1c203000307040c0d1139003060203000041864551307600d007038040ca07800040840c3c42503050001e682c8203060390072250880d50a203030b49480d01c01d80c0018010b510f015204070307490b640131076480040c010454030980e451301c00c0001103851411850300200c442c0640f10500ca00038890500b54500c980c031440c1603410341d400d034034015003c031007400a001d400710b04200151030b55980b11781c1c0000d0300c0e10384a040006e03c400401c5480e01c1c02d920303002c0404900b0403080340141301c50401041000400c0c60410024800100e03800d407066104d01641c880d115060480002080c10000c8100440015024000c290f0351500e65801801e1102c8003207039002c0000c02ea182c040030030300800200480710202100d848030140c02d1120390b1100c248610041120901aa42d001d83c00c0026a841050038051807255071425260012994007446d04400c0c403c14005051820701321000586510444e2071091050b1010031514070300207920745040a10b0000000c0c109d0003003c0102c4107054100e0080d280303c030402e964450307420f41c0c4202401442c3c441c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 504742508 1250 504741258 504741269
    0x1060804020121060906060908060a0528021c020a031407080106050c03090402160b1e0408070f02030709060f120b060d1a04030c03031406010c030509061e0d1104 71
    0x40d880c885903c00c0c00d500c0107403448800074140000d100e035880981c1c5040390529001540018103002040150700001c100c0300e6002500868100706034280303001c07a095035054100340e030f031160b070707509400d00003208007a506451380048c00c01c080008010441004100a512910303050001c01d02d440304107101c1e41c1c1000c0603a4480c0c07030b181d141c00320140d017000020b9605811008141d1014442080b0120711500c8900162800b80141da18441210206140c001880c0344000c1654000c02040e00c00b0350211140c4245081d080364020310318607540c4809040c40091401c1540c4082c3d007612030303682c2c006030a40307165101404442c480750720003040c15200d002030301c503e442000010f040c10426a001c00c4091500700442c2c11742c20311410040611129203440010003403011034044e00800c1c6021000400d16415004606da82170b01000e9401840c0b5001001804c91030701194060b0400001040b8144103489540444202d980003906400191344070421050490b4000040350260b40e040145803c41140814151026244c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 504743758 1250 504742508 504742517
    0x8010302180402030c120106051807030b010c0807120e0405040c053c0609030715021209220b2116030c03110109170115060503011508041403120f010608040201 70
    0x5024010020700d50b031510b0000131b41d5582c402c400101c076030b01c1c80140c800891f80c0f60030404a914003484080c00719800400b1050511008031041c1c40010a09402c540aa660110f030000c0009485101100c1502503002c0b05034205141c0801d00c01070080c0389040d907044034400c5558010341203403110039048880545040510320760082c28036652864540200e1064018054625410080b000001a14007003182d480b1803115102c501003074800543c14014042c03122480002140f07015401800315110b40300b0440301c0510702031349071000c4180340030f2a00305801180c0000c008441c6011031002e1004030b10202d2400e2402449a15401c41504031000316020840b0f0700880c002c1030302451900d42e81450000311100b9410824480804030720018000080040c4082036800090076100720038003a11b02d94140d0f08148103000042c8010440628000785100030f00c1028944a190354555151042c2c3d01d0032040c001e41e409020105a20790501c80b596101442441a0303400040701b80d98503a41902c640703d09840182c0000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 504745008 1250 504743758 504743773
    0x1020f120618040b07030612031205070329010e0a08030913020c0102160b071e0c02010c020d03080619050906091e011e0e090601140a030803070801030218040203 71
    0x241008240d10350240c00076200b10103442200c1c00018910030700310340450b5288929814003c0b800d80c54410302020305044c411484d0800d00d5920040c109050300e900b0b45102c9030b125000a812644690402030455440c500d0301085113414118508803200480007090008220340c40d64141860000490003c4480c29000703540740090700c0041c41b00c03940b84d8403005040b807a003c000801c80030fd0309200a0680301003802129585042c1072422181501d0084e110314100162501616050700641400e4900503040e07081a10b1403803464801601c44202041c000f941c04502828940107040c2c10503040c522551040f2809240423070104204864034001c0c4c0a80307500191400002866030800c0c44031150419003080031800b05003002241c0c1440003a0076004464200a62041070414036014558100645a40300161860345441170159607240070521400511040e2175402005d551500d03040b150245411401c12a030340d02c0c1809024001007000e01c0100e0080d00780c004208405c0050520103401954000c0103007a02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 504746258 1250 504745008 504745027
    0x1204090c03150902070c1211040c050304030e012601090b0901120503041a0f07050d020f4209070302031207021305150303070f0506090106030c0e1f17060901020f 71
    0x35004a04c04075280324800c900807c10146440c80b00b425148640c0c0307080010b0503510705200030f030340f0300d4519001400713030500900c4006900141d0b4074080a1088c41c2504459415108101c44880660703000c041980c40703400003003000c8441e5041001041001d132a0000c40c0d0741c0e294145a030442c90140c001e082504140001e1001d090503400a5400301000484103051040b2030411b5840390f40107100032903142d0300c080cac3c0c2c28080d59018080c200000d0b032504054007083d0a80040b81e034601c40950090482080ea01102d8001d00307082c1915003c43c4819114140380514200d80303041da40702c07414041688a84288071005020030541022943c01c594003500300107103000300704400006040c001d4003140c260110000c1d0901c0644040028000090044d4031078101c2000e54103003e070500a0150504500d40d042540910100f00700c02403103012a0180d0402c4849070b81c80f035100840054890b41c030210710ba58884400140b42c1d42d0341040300c3c00000c00d08c094915545580072141e00b00c0c418001a40860714041c01003040313 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 504747508 1250 504746258 504746261
    0x2030307020319140a0804020a0e010b0406030e0a1e0b0f070509010c020111010e10053105010608010c05030910140105010c030c020301050408070b0f06031018051204090c031509 78
    0x60a205042042c02604c000d02c4121850b04040f203540c00040502082205600d401c1e10a00c00034000b2407815040c2d94100a00911248903d00550b01850707195014041c3d050810003018902e540c0002004644003414040c1e403000d060b880f04283c0741014101c1c04107c4c40d01546103441d01039800c80e180d0343d1a00c0c04038030041d110020724140036070511442884540c4c1c000c07001c4c0680101d00454a000d40040c0394070403d420121500909984422244a036180400c0c0f02812803850a5403841d0b0383e004102503a42c83c00d81e01400180d001940c9079400c105920042c1d070b800002031030055803d003042d21451040c0c0017603e402c540c642c45e4002c00f20410b00740108415400750340c103404141e02924102c5a50b030800d801103401d48009481c22201503030006450f0060141c142c0c81c13550010150b00203984c841c1005000a85e4a141c9182d0b403198140d82c8503402000314802496480d102a44902914000707080000c80c01441d130010720904a00a0928103070340c0720680710b4841c00c2020465060081c0c07820707040046800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 504748758 1250 504747508 504747547
    0xa120902030f060403030c18031e0213022803180b0a0e060f010f0e090d031d0d020f10060b0714030c0f0c0a090c0503060907121109030c01020303070203 67
    0xa825001e1002e00c82c1c110501801400d00c41d034040d480108100e01d103440010101d203908040c06040704020700051000820b010042500b01440b030501c0d220110003400018101c0c0f94440d90040c4480c030024881052134194945030070184980c0c280100340794484201641505c2c00c41072204680da031001f0841c0300283c1307502e50b220f810510500d40083c481c0303114941a450408162044040c0152a900400c049890240340f04058404642c120200b0b0a1031780300c240d50754400315481028152503190aa03899549480c00c58821011201110034401011601a44a103a44c510241d07241c003c1c0b01300b80842e044903005603c2150050750085117460780d10b8544121140103918800941d00041090100803a13040107480c01042d024000b41048000e02003c206103c0002d43c05009000d00300030044981c20b8100040d0f03584401c041e01c80c44a10340d40c0100850b252907011205000640c5000c01d2100030b6640d8102400440ca0283e040350301c6e14000800680e0359010807104003005900800c040700d2240c2d048800308 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 504750008 1250 504748758 504748763
    0x6050f010c140123011d01090203090a0c03060f06080f0703080f0d1b1e090306090201030b0a120501140609070f0e0a0b0a03150b04050105090d020a080609060c0a1209 73
    0x2d820498090200c5003529201e640701e101d80c1c4200442591500c000d0701c15640140403290007031000d2800c00d8150719680380148116500d4070781c04400540c0c40e0380c0a00000242c264425a604801501da240040081643c12460341c010340c80d1403408101114002010344c16000840010200180b8666802d50564000342040035215400d10405102c04040d004803404a81c41020038029030394141c3d001032000301d000007000300060b06103141100281e04807600c0310540381c0050000c83d01c190a400180c020b41240c848598204208031030004450900000003650b03540700d94000e0000b01903400103042c4140c0195900d07a0301203140000700b0007540c007441040c10841401e0070044081c50702030002034000c1000ba0f0103040f1a00000841003c2640d2521818408902003d000b60550381030125181242c012800b0300750500c0320004032500f55944240621a007183c2c001d2052440d01c4c2c0b40c461039501e1788070a95511003035121b003001060002c4031820a44440c15110754903070b514540400302e00009002918402d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 504751258 1250 504750008 504750023
    0x1008070519051c0314040f03080702011107060504080c010804020306131b23030f0604030f1205090a1a071d06041508160f090e150613090b0406050f010c 67
    0x4031501c80010306400f00603186049030310300d5494280645480000290307542c00d55403c000611204079074a5410342680e13000036042d600d40b405440160382030741001100c0001881240000075947d43d11000500540300710f003081c0ca03034000c210320042d5045e00058400030341c1a040a40050080c07001c0507a0b40940601031900009004051001094041c4141d040ba6160f61187c4040b04c020380c4130f14400c0c8608510950003400345e44100c64045480c1d5401400c010100402c20034098907441c8116003c80d0310240002e010401070070b290514079a91040010f0031181c0314030041d0002003c0741c0c00d94096200702d4550321007501400002c00805c40ca02516442d255002e0f00034000410304000c200020044094691a034051504150301001611404114510304120f904154041d140c0d03440018101114000b02c00c00c0601d8513640c84159007034100052140e04084041140005015985100400c0f1507841d101006806ca4060910082d1034550264039042040008444000c0d44950344480380030b07008040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 504752508 1250 504751258 504751309
    0x30c0402071e0219091410080606040504021f020a150e030706092103050603060a0b060f090d17040f0602010501031205130e090c0414220f17030a0510080705 69
    0x41d040c0c002d10342d802024030155120710100403030011418035034104004160315a5000d1508d034581da07031341c900180003a003c0c0d0b885c0d40100301152540010700e03141041064551690f0034004000942d01d900f030007010340b283c4408031410202c80f64141710f0f402581d0b100c0d4014619104642d243d0720041e080201c0212001814180c41100d16489080b07544044607150340e001c01d8504021007014940345001e01100c5003203240c0501d00c074595464000700c0b082416081496511205041c0020702500304140e006420b01209a10444501411200030700c1664a80e40b20600d445807605022801c9617801d01004005404c0b60040e207061900450140843c940000345841d0665200e00500020350720907643d68101d54854002c0c0d0070203180500032103203040010109982c032407403d4041d40c107044a0034225000309000807410070040c86041403d0424440d045a50120b00100c25154440340c3d9204a4604010300c0ca448042040324501e01d5001d42120b0003400200307545070070281040307000541040080c47d01040a81e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 504753758 1250 504752508 504752539
    0x312052e090510081e030319020408030c01020c211204330612020a0b030606121015020307030207180b0d05150121110f1c02030c0402071e02 62
    0x9402d01c141d4501c501208001c3c500b20409280c440d507080340e1043c04550700c811040d05d4000005680e40301c00109200421018a41100c00080c03142d600002070a000024094070700c1101500204132200b03200c81162076003c424640c0340d4808818080c0740722881d00401000138490b00200b04190464016180e4180002c400b01c0b04103070740f10101c5800d504000400452100c1d000c400c0c40b81000070100210f0060301003445d640043c000c2c0449000350300d0032800c040081001d945407802510b0002035800c0b40559681000605040c12850a1050007035507c4100c05c1203020301d1002c02580c03c40d81e4990010034546040c0132000c104640c2410410910344d60392074070346110341e54600754400901c0c002c0c0b001d03200f04408040000f2a54a058000d020407103001c1e00c2d0311010038440022011070541004410241c441190300052444c00c5c800fa01660001c01c800c403140c4060884807144044c240300320112401c51041d40144420382c0a5a20050441d00c2c200c103541142c1c2101400038012503100500d4019040b6062 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 504755008 1250 504753758 504753761
    0xf0a1e0c080f10060503160c080d050603070f06080f060f030a03030504051506130203040c0902071506090c17090c060c06070f0302162013090312052e09 67
    0xc40102002980c40300c10b11501c0305480711101d0304010182d1100210303504291005e8480e00c00600325110386064404501c10311071150348614240c5500aa078aa603440ca001d401c08060701054520324401d0081680002e030040416200300121050740d210309078140d5a8450407215032a00501c2107410540d14009400c66030317414000541e1171842610009420b0078182099031a02e0b00403003182840c3c0c030b405018040507941b60f02941c2c03442c0c02005805680c90f0744601d84561801d0f0a0341c080c000399400400c80c0400c000d080252032880e81e450902c1040340c165101c1c4000140c40401075440d000c41c0540d41e0030301e0110b000310035640d40458481d041342e03030000110300070031181d030b110358800004c5810501c2484a907962100c001c00c10004503240650030074154403000250702d10403c100508040c01c002000f0300000d18500c4001541c500242008005480c1c084400050011940700301d0000e20039030a440c2200459115013800b5550060326911542103240d0840c2980c0c2181d8150301003d0b0004d44000340a540d113 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 504756258 1250 504755008 504755021
    0x1090501321606150b07080c01020903030d1b140d09020d02100801060f020a02130e0c041d12210c0f0408070311010f170a0605030a0501050f06090f0a1e 67
    0xa10b000d00e031903003a24245802214942000c600950031008400c20608003d04280c17004650030900140d51030744082a054028414111a1a010b00010601c0350103480f00c1d034003000c40c511519649400c210400305080340d5144400d034240d203003640240625000070f9856405a00042c1c405040b00200c0d401640002d04084802468400001c52410041c88203a0340007013202d400d101c09000401c1220040c1d400295211400d038000e8425554803045000e40d940b0410500c0c1c0b200781e001d041081045009604074000c0d98680c03a804446100d020382103450a41c50b001113802e010660306514481004000781c42d14078150103410004525170611641010040010042004080070f500a2851610750702d0015526004045e07034034148018214507003002a00000c048040215402c06407d26a650821010082c20745c3e0300060340503c01d07500c60b03034100001503100070b0258080050b02e05843d55650200100c0200460b0b018900004e04000b0031300000360754016860804008001345004c41003219034000300c4c1c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 504757508 1250 504756258 504756277
    0xb0903070503152d06040b0414100e090a0809100c0206130f090c120b1207061211090d08030406112106060a0c0b270a050106050109050132 61
    0x4030a03050050b0700c46100424460042040a070250405200e04c00c20915030000784000d01983d212036901c095542e840d8080e031405058071201000314180403045008644841c01010042c1007414003148a5000002c0e05080c81035101d001645040e80304030900520842000004091007030b00840b840060f17580101502640f00741001a00c2803e00c0e0000050040c103003076001c0c2d1001c600d40620005034981c040100140e20b80d1110703010034401104004115117440e8424031203500d0290807004500c155010480016034529050300b48006004003610745407070701c034420344294003e2540c200000064241405150302c140034000005158444144840305680241d050720f00c00c040b50304854204a0990090682040c2c082d9526400c00560540181032030703d104c60040c1c44907428130009940c407081030600d00c03125140601030341c3c040080c1c0541165907440303290080340e095007490340c0403e06504c40c034020401c4400587d81c49014a2000c240c40520801d00b940761054218900f00342d00058500100800c040003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 504758758 1250 504757508 504757543
    0x70c090c0c1a0708040b040f02060a020708010614030a12031b500d06080105010611010c02120a0c12050d0e060408250c030b0a060b0c06010b0903070503 67
    0x201d15103801001c03040e420038100070014002050210076540314882d240e11035445084c282280e200c908080d0651340260341300075031000d0000341b100d1480764082043c07812126254024030000d9282c9401281c2c5003001c0382c2403500740c0d100e0360030000801d2001d1300b800b10301c0700e40b03050009403094001003182c117042c0c400c4994004100c02031700044e50880307284250405216202c000031902c0f046c0c40e140d4024a480b400000460b42c43c3c1c05030a1240c4441072040312901901d140307040010580e185e1035140644070920542e004a03800041010702503c06003d07031b52610f04141d002d00001c60b551140054a43c000c140807101f04040e0011303c10008180340503454036040070f030b00c2e0203071540350728402c034020f07654150704502c0c00d90803980c00e21001031044025947d100030f81c2c95501b80d140c00c0901090303e11003030f55003020b13050410146000003070084103040c4600074440c8101c1480b41035151499400a4415954078490692140004000b40352170100940702c001c0b001004e40300e03032550f54030000b03141c0194908030ba1401d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 504760008 1250 504758758 504758777
    0x60c11150f01170d0e150417060f070c0f08040306090b010503010506010507080301120311060106090305010b1f14131403010e12030a020c010212040b0906150a0308070c090c 76
    0x481d5001d500400b652444451a01140c0748482d4075501c4280d80b400c140319611410450b6a501d8441c104240401c04000382e4a99690b03d0f080d040494034808a040350780901c01c0499141413600c92402e01c101091f88070300e05020056a0340f41400107101d0800d0b40c0c4a0341c1800040b00068613170080b031440380e00031401c00606504100030103084410140203d07051000805c0100009030402c801e4a0444440c0e5114039400c90a40c102070310f03421000f42d1158114007070f20001250894010560200340ca000b00f0007005030b0309100c0c0601c0060041e40c1c105900034007018a01c01202071080d450410140e40c086049400c00d4010103002810b05080e03004038400415890305d4030000d0409203d4282d450b04810024084900c003200035144d03521001e000d03034900c10b800144101e14070701d09404840000e0305000c611045440d142c242448080410b450012041c00343d07a0101e58140041d00b00406003860082580100740e286558080780d40d070160030102c5901001078400520000c080c400c6460080c000c1d00d4000e5030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 504761258 1250 504760008 504760021
    0x90b040309060503090d030b06042105060705040e27011802030c04020304110d0c05090a0b010e0414070302091c0507051503070804060e10050c1809010b07060c1115 72
    0x11008030b034100310704101044c020003582450001c1d0020304146281000200400310001090043c4035581298000142c0e1003001e84c000110100d85410043c002d1003910001d03115048d044a1610480c860400c4002c6044003060080c0c040c8020b0598003d50002d400d0b003101103400095094400200858202080d0048a00c0070b40c1801c0c42405030310340341151704515520f800c2d901e548060000304050780c003407400c0d42610401c0120040049008d480000d201114503d03010146034040c2c4203020072280014040211010070f07091901130000c004203806c500303100aa80b03a80c0700b1002900648000c0f941321200039401403280f0403242c12021414040c0e0003603d411410181440501103c034102045903203030800c20003604591081d0990340190344200041840f00004034038520340a0041c9016201526210902002524100c000e000074540703161101883e904540401019034024810809170316404c00c01800052155800420341c00d1280c1072841600c40900201072800f0742c4000580602d0b80d801091115 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 504762508 1250 504761258 504761267
    0x31209150b0f01110706031116110f1c02190f0801021e040e0712060320030c010203070302030403060b060f04030602270f0120010e031305010c0209040b070c0204090b0403 75
    0x405207000c4c02d024010000b8005000e42d21101885003008160383c0e03036084490100c114040b9212003800c003264490110b841d050840e040d0380e800440d14802c2c003601002d41c2c0e81c2c2c03c1c200481c640b616800ca9040c1c079040031607000d021030380e10b10003281c5242044000010900d03e006070950070113424150001038940d00c0c00028000d401051030142e00003440c05000c100040118802d005512002e03624207040054101041c9101800c1385400c0145042c02484020b0342291b051844464034110850480341c11b10420401681c4a1050040140c0103810801c01032012803590b411020010303030041c090610340300c7c4200c950846034005402c03c45100b0380000701c5245c4001c6450903103101030081490741c20020411000120460506000f140c10321510191450980e02c0c22900c1030140e00f2098024482075055800e01078803a8095105440041000c003400b0070700b5417040001c1c03403900f076014110b003100c0c0d1155150000406001003011041000300c2c0402c40c0161582e00545024a00c41c05540f802820700b86030161 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 504763758 1250 504762508 504762529
    0x1e042705010e011a0c19060b090601090f060c0f1403120604060501091401090302100e1906020703081318020301090b0906010e060705010603020a2405040b07031209150b 74
    0x781e0030060700010b122412a5044c2212000001025a81c0d0341904481050511a0501e4000150606417480304d0600595400000c80300a00710f42000383da6891038010354101d43da5000c1e0f05140e003503d020030b018007401406008441030140d1101c00b91320000741e42d0484140350020b0366040035003011440301c041d9590b2040c0141c00503001c89003800049d05003c00208968a2445141c017103103c21804200264003e01d460400741d034000e00b54840030811148007070640d034030402d10180507080d1008016020400501440d060721000d40c06400302c0391460704c90b0410382d0410120704928000e0344400042c0080300e03180c0f001c000607103401d01507180d62509034420708880300006482c1c01100034004201990707a20050181c2840d108448041d10340346d8074140580144140d0b04025084a240c000208480000910701300403142d55440407008989281300031541409a44a1044100300030300104001a000320f110214030b40c645240040c2c0207205231204460405031b095545102d0b6a203640c0100c0c00c0c18103c4119 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 504765008 1250 504763758 504763769
    0x30604050313170c010807031503050c011106010e0103030e0a0807090501060906020f0a0b0a09080f1b1c080403141603030b0f0a231206060405060909031e04270501 72
    0xe4880803030003d09403206180c403072032810016124005060395005e6800004c40304103540403940f40e982ca920b0050359072401d002c5482e01052110140854680001442d40d040e80e5844025640903441c6940580e20350104061036503000500c0c120200b0307542e00c100714100c0102004d550200315545000d1029000c0e01840e0440030464203c18070b600325030000002d0720b148040e40184001906c2c2d03500000700005000c1a180104070400002e0220510002c00c400ba000e00306100c10950900700c101c0c80c05903503070000c90352815441c800c035000c0c002e07501380590f0b49242d0182c000c2c00c0001070420081240c05180d8040e510340304c041c0700c4201040c0700b4954540b207123003c440e0040e11885800342c41000001c20740710243c480c1030a01c1c50241107018440c0441d007001f150f40d02c00900503600f4002170003d1152102c0040380d10f04e0145140000085003460034040c120f019000b80300c061483c00c028803400188124030302d0400c00f0381d1401040000f5100e5443c0155442400c00044401c04280c07440541906440041e03112 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 504766258 1250 504765008 504765029
    0x4170703022107080318031603091404060e040b130c0303120501140a09090507090c050d0f05040314090102071502150a02340609080703030f0e0c040e0309030604050313 74
    0x34140060044400c0700e422512541d4006c04007080c4041440c51449440900080c10300070000403001c258001c1403031425100d11610b040800454001448102e07141445080390310f9643c20007040115002c031030f070740d5042011001c280e0300340c00301500c40c5c04080c05158001c070005201d01d4070300321a95006204a60140c0003000e0703a000040045030010709601c0e114010240016999840a405c02100304440d400505400360305108801c0c031240007030a59000028003441c428240b02a105044402d8802c2920640c3d050701c81c64a8689407a010492603081160864198840c501010860461501c9001d610495641c0140000403001c00c0310800c000e4054003041d45c160041c42005d0222101ca40c1c0c00b25801d000f00840010300700c40014622b55403a510202900c0e06107003108413414490408000c1c800c0c80c3c001c1d00c1c2400300003d143c0301c060494142c50140c00047d000b15803910040d00e403941041c1400c0080d10103d07800c161680c40041c1c20705400340c5003198070780d200144142d40030300312220080c020113501e02c0b07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 504767508 1250 504766258 504766267
    0x3010b01030c0906050a020312010e01031704080a031110050f0928020121060b12010506030f1602120d09021002030a050d1d0a0b0105031009080909041707030221 71
    0xa4600d61844c05500f0a2150109003001c90510030002c0d5000d540901200c07207020750355151303544500b0742d0030701090702c2131105000038035100c8810fa021507040790201e0005100206507902c5c11034101303c48420801441c0101c1009c01e001c440035025a6001d142c01802301d09450500c0c415441c5000442004020310100300942207100120b166080c580854080c281104040200f1103901459038410380409407081c40d0000100d4000b0b4010b020f0b2000704c1c2644842403050b40c9600801c4000c0c0022601115900d00703140005880d40407094100746440d000340119120080a032030080055085424402440b82e6914103800541c80c0092003952941a580091894040d0304040100b4500c0350302c1a00345043d03101c4100030040740d04074802d00c800481c800c099408411507841c0020754418207100e000d11030700c1104001000c0d1045d43c424122035a500c0000c4501e03002d1a030701802800d4100070015920341c0c020039190700424000000070300904e0700c03945c007a1441c11410089086550045d41c00e211080d9824030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 504768758 1250 504767508 504767531
    0x61501120b210c0d050a0c060827010e1009120806090a18080c010507030b0301060f090e070b1903050106170109090c03060c0e1e03060c0a03021201031103010b0103 72
    0xc21054405001050782011141c0328242d40b07103041c100728038030354010302c2d03104c102401d00501040320700300c10b4426038120410980d140000c03030f540101622810602b051b000034519121080b40b400440d8913104200104042161900c2c690408151114241149440c1c809803810445001a09812000d880c24124800e05040c804a81940c1c0020709421400c9d940f03907060258804d4100c00004c44507849801d42c3e41c0e40d10038488240c0070306000e440e10004079081c40190401c40c40c040c011b01d81611040c030700c01c0810034034203c8a1006400c01140c580c035180901c800108000340e0b00c20040020403000b84030003e100820390300c020200c604c168403800401c41c0c0d1203501c1c1800c94801c100304d411240910004240172015040c04142441c0300d0348004e0110f4903004182c04010b4001078107086c1c00d0800c03210245e58144454102c81282c0a902c41d203503050700800c0024407190440f2020f4448280030f46401030618460602d419600030083e0030a40d505004401440d900c2c1c94240141c1c0e05091003031030240120041e80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 504770008 1250 504768758 504768769
    0x212040206070f02100c030e030703031202130e0103081b0c0f060c1903030501081b06040e13060c09090614090609061c0609110102030406050d1805061501120b 70
    0x600028801c190014480c4184503d8a140881e0f56800900341c03200c83e030705004090502c40c0400e4044010860301740d0a18090f24010501c1000c8a4240d2108407598045607180360003035100301100001d0211140340030030f203400f8002c0c1300d5010314820030515a450147d6094104008541e601035035640e03200540c0d090590721841000c509040094907221380751240040b40504141852014800031074841d0311740c1d0103040d415004030341222609029640c410b041044050350764002c804540d0380041080000b0131031108100a01940100c0b2a15082100c1e052070f9a11070566a4443c8042d000510240c808c0c0711001e10f6201c5d000042c000b028801100c0c645441c0429007100c0014552803003110058005441e41e00c840c01030241c02c440000b0100c084840b01d1800f1002414a200c1c00e42c0c0c101d00d9200c41002a5000008850959100d91242070518031a0081c2001508040d100400002c0040a100001a1301040b02c45e0065107445030151114448000040214281e183c00c0c0a84900f03050103a41d90780c454 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 504771258 1250 504770008 504770011
    0xf020108370608060712020a0918050105120c06220506030a06241e031503050f0c0603070c0b04030c060c020c031b13150312020d020c04020a08010b0c10060f090e010212 74
    0x6946e00540c440561000c11f480c40000d6901c1502c1803004d2a12a2141d40790540c84036041e074800312031803074444021480f11955081c3c030020103600200100000620650b605c0c481c1140f07400480551100e0649680110788140c0003036500414954032120244144a0110300c2400c10341090344130000c49620041c0300a0011000301d04541c1d85c0c0c0c0c400b011184090381b12f81c020710a0703c0031440449250696a1a16560700c41e4082c48d80402030296540e0500103143c81021a800341d0a42e40d10100040c0c1c842d26001024807018004074140141c403560a00054030a020704403c0e0850307a00030344100d8100720141814011401603042020652000d43c4e030a81c0c0d1418181480303695030000000b4244d500b142014040ca000c1c0e04054001340301080b80d10046540000d21040d1441c40b6402c0d603d41c41030310010b1009a0242c2c020301c001141c8980c0c01030000641c503001030001501500c0480d1515072240300c020301110343d00c0d0002040b0710180403045c0310344030f414022446048840c00085291030481d10200710320000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 504772508 1250 504771258 504771287
    0x1207051507120207151b090b070305120901180f060e0f032d0705061012210302090a0f0f050a0806060405040510050c0d11070f0201083706080607 64
    0x1e01043c039600740001c82142c44034844200f141040078451b401c900908036101076008000092040d0341c0824030518280a075580035906407546400c041010b4070b20010008010014000c85d943d0307513118601d0581c01d44003520003900a0910406240f410b040900a8070f0b010f0741601c400783d01650100c4052400001220203c19607601c8001340d141d0f0412024040c0d060313900758450448000700e8907100303114011400301c0c080c1c0000c00700516190764614402c40f03000d001c0038019103040002ca01501c400e44440010b01e5154a03e8900140b504a205001800e8a401030b00304490030f410840b070502c4480c000a142030041d0404940e2902040c0c03030718516583d1200001c08250099441c1c1d008602045810048408000d07a0040144018038281c250109031b074105d820000110360503c0204000d16040c40121041241c011040385042c1c030a540054a41e0003010b003c00c2402248008000090411030010f08111020480341081e0800c60f090000d0513280f454020003ca03403c20303001c1c03011036034002c0807400f2001e6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 504773758 1250 504772508 504772511
    0xb03071403070c0f1a100f051909050405010c0e0303070b04021c0b04030e010807090501050304020f120709020426211207052d040e0901090203120705150712 69
    0x1902e100d401c44030401d100d2001000c1c3c0508041c40b80400c4503c1007100101d1000c4001c8819650f141d5420f146050480d01c682c007030039255404240943e0a1000c8800c2944801014040c05250b8648a24040b98030445080e036160b5515880640c0c410740c8503e80c150440d500320f0085007004540d8071818500400500000d20605000d824523810058038052403440c035812000411062a00e0308002c3d0140211800340380c001041c540000360303154000c00190041e208103030340d400e0451f600d030f500f440b8001400b110640ea210f400c400881c0c004020400850000d08403403180507807502d103070102c56840000b181c0c00f02c1c0c0340c003651000e0031540c84e00d0002d103551034002c05289580d00c441c480401098580f2606141d1101403180c04200070201e500800201401088856000c0d4401200012042001d150268046850200300420041c031240c03032000e03507040300224000140906440d07000a02d4014180c0311a08d078203001049040c1441401d00c0000c4001c0440400f6500304d1501c030380014807084001d070404041c1c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 504775008 1250 504773758 504773761
    0x6040506090a031b03062a0f020f0d02010c1205060d030c030c05030307030605091303020c1224011d09120a110a0c05041a0d060b0310020f03100b03071403 68
    0x2e689003007025005580100c084a0120000182510080118042601c407941020075040d0310b02d50600d80328510b10075403002c54001105d41c010031210901c005649004510612800a402c0d600a01803644040140e40000a10b0442400041c2542d00802c8007000d0052810040101944902d070040032096072601d0301640030005c3d03207015609070740d642402a00301e202c080200001d082e0036601400c00e48404454889140e65507822031904002c0c111300c010010381108641c010581041084c0c0402c5442c0c90082c6d1b000c000c0caa642c1000d0007d00d15038074408601c004401085040b04100e0300d000380007003804217442e40346080b6400d541d81d03c1c030212454196075000219910040c1c480d01c00d100030520307070b0001d03203800881a040146208080e4001c1612851800e070380c400c42c54600c004c0405c81c40c3e0b00984002d800c40110303140c100c028171108001c03c1d0140100445203204a0403032000b000c0751151003c01036100d0514021600942c03a054202102c050001c1061181468114900b00e01d41c600d4404c82c281d03203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 504776258 1250 504775008 504775027
    0xf0203132709060209040506040902180c070503070b100f03050303010509040f0212060a15140d0623070f050c06060d080903151504060303091715070e100e06040506 72
    0xd10701c05101030075881d49085520700401c02e85400410301c030380301201d044c01a034135030390204001c452070000000e50028140705428100d0300e1580c050b503032004008000504000841d20b900e03003142e112a004458015112003005020b240c0d03500c250020703121903216103000c1d030300310ba0700e4a035648810f0203918815038800002500b00840c407444498036580c003500000ca441c0d0300140665842c4401d54885100d1070403d015640b4000c2007a1100e021620303040141650b200382081885115001e0300c2c07050321820b40711000c401c07201c2c0200d103101100c0c4a0181070703142c1c00d107007041e0020412020380807100c04200080140d21140100000c0d09500403408503854034004c3d4091820306128400c4181a98150040300d890b00b14040d041031f1424450f60117154105d46c2c2000c14400c20040701c2c050701004001c56540e020601032450400d0010640c00000c07000c56801ca407003110b0b00e0520b0541152040002520508890418101907954030082c00160416501c40c00c00030300094907501490045a00030031000c104e0b07400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 504777508 1250 504776258 504776309
    0x4060507060e0c0a08030702010905041505040504022107080f03030c0d0b0f041803030515100f020f1507020f0106050901051e09040c1d1306020306040e1c0f020313 72
    0x2c01c3e4001003001c2c4100741c0e1164030380d460b60040042a8045440f100b000038090a050048840d2801f5a6043c604041d040c01d00b0000144030291099070800044418400c1c20754084595400e18645117004103800e62030040c00300d180c20185c450f40403040c0c005105000001101703c05480000c402c0c0c032404241c100c0c44c0f07800324140ca11515500c65000c0d040244c03111030400e8400d00c01144c1070017a40c041c022036982e00e0070b01c0840c0d401c5114440e084900c0e54110715149105821600d203a030000d02c16920400900c601051500c41c81d20300d801e0320040780d43d090100c040d404110110310101c85070f009002c498a040009034501205102da18043d51018811404c07100c4481c01e486485000140028000e0405082042c0d00c0719840c01a00c00c1590083d05801100034032030409881460096891104800e8540e1403101940014110a401607100c44030210044000c0c03090010000e408014070004080f004402802c44050702a0700065410801c0a032480e621000b0541d029110314084944c1e000240030313400030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 504778758 1250 504777508 504777523
    0x9010b0c1c0e011d1e01030c170601030c140705071d130803072c03010b030a050304140406050310051623030711030a03020408010507080f15060c011404140304060507060e 75
    0xd9105e200c85510b08160150141c0c2000480400c1e601004000f04500017507917044c0e4081c600d01c1d0900d40000001308558407903000124450708901e070040346880444403181e201d4001c408115000d0300165410300c140c0c0c915640304910704021829504540c20328050b00101e0520398100074000c2040000080e0b0b1260107009541003004000d6502c01905c040d00ca110422414804003152095003000007482c039030310300001e418a000345c20101440c541494114260b8850002e42102504540c0707410001809903000d1080c410f02441c2e01101007541e00d0054450302c40441d003c0d080c0418403072400300040c44030341104141c0c4bc44c8a81c8820440d580d880e108401d403018441030744000c000d44400940c007510144c0c146c000e0070894000c60300070721842d01d6144040d00c058a089034000d0340c2d00c4150002406030541504031480a10011f4030007071501d0f5001c0319850075542010301c0c000c00030901c0ea0521040020807030240700d41255580c05507041ca410004020b00920809101901c0d403501c03503200e6480300100b4030260 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 504780008 1250 504778758 504778817
    0x211e1a130e1501050a0e0108070b07030c12020a0219060c080f1b0a05150f06061c05100509180a1b05191701060b091002030909010b0c1c0e01 62
    0x840c0e00b4000210b480d802e25400b40102d030700507004640f0002e01d0f1740041c04c506050710017403c0a040700310b00b0001014000e80142c101a0100000b03042000301051003c100b91520020550240c044441c050050000340150420214640c0080c10030410200e0380c000b000421490740003072030566403040081d82c0c44103030007110b1500500c20260300300503110b010005000301c000c42c4074200766564403405011880e92240c003203440311100c0b084600000c41d140b816000400340c80c03031801c00700c0350301030a10b10301c86044a1040354090b1000200f43d4080c4024a00b051459520500005600d03494245224115890700080e000060824060300c1410361600c0742500b5030070180c00050002110b940103a0000303042158035104401150303946d103e1690309402c040c09154191001c01d1020303840d0054500a0000d0095036090341c20031400148240c514981d10007280900a0a015144c01c2c8c03251309074500507040144015a0b42042c0303171034001e103610301600b0600c000700100d82428403199214016400c0c008000c0380c0c8041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 504781258 1250 504780008 504780013
    0x3010b0a0e030c15210a02040e0a0b0a0b030702030723010b0a0803040e0903120406050403030f090314130e011d0c041d0a0e0d0f02071403060a0c211e1a130e 69
    0x6c110705034030154058400c449800104550903160a034001080b10340000000c1e410800c2c8030000d1141070548001103400c0400c3d0b01c1101c1c54070100342c84042c404400c1044070b034201350120300c1410200320240680006540c0c00c4640640991030716251513960700c074074401d480700490540300103a1464014029070340320603007482c520381070ba217810f2400800504c41210101c0c04a032410341c03e07011a8441303104407a10300b03a0607241e24601090102142013507030407481c0358440c80c0d191140040f55009188184900034504200404460703d40059800310002d0010200c0c0d8404009100400800c1c060b842e00d2021740701e00f101e808140e91900196800030707007500702c054111403050a0b0310000007540140403001410881c7d0a6034182e03615150040100c85800320580e5042c2c0c428004161081e040e0b5002d4000c02c100f40c01c00354122000f0140031402050000c100c0c103000c80d503d40d032070301d006840039884102024100307101704981062034100c0c00380b00c2c1c0b4404400d80200c000305802d0020b2a80e5034444501520180c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 504782508 1250 504781258 504781261
    0x40903030921140901050a18090e03030a0e030f0403060938060108060d0813151e0309020607060507210e070806060a05010f021203010b0a0e030c1521 66
    0x1005095042c100e404000015400c0c600408940311010130f071250814142d40b090301d400c05101e000c4508071200180c3c5086032085800000791328009100380f03002c4903407060145840e49441a0038004840820b1852003036900200016031040f00d00c0c400700c800b40c0780d01c9000001d16000b2030404000d6258403419111103008010441c003040c1d07440340d410060030303403500c0a0852117a0b80d038001152922400d990f9250003c040100040025000e01c0140602d50b103001074041a455850386180c641c15004141500814208101300310f07510241c414615a40c182414140b0240160381d001c11218400c81c2409040c417039030f81d400300742e6451140003c11282c02c0c980c290240d41c2481e0140d120020301c210240a1203611a460300003130b0500000c12001e03c101002480007180920b804015210000c50000c41c008500070040783d4146001c520700594043c02c0506407103904ca2160320406010b10b40550b031114425801030420b501140c4e01c640440d905003038202000c42c0c07070f83d00c06007100b44560703492101007140300a100c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 504783758 1250 504782508 504782543
    0x204150c050c040605060306120a061d10110405010c1407240201050103150c110a060b1512010915050303070515101d07050c0102030a0b0a0519050409030309 69
    0x110389405a8000d20a540720520401c00b00b0048429601c51203800400510014000f40303050103200c0c407004c2c1e0b01819074507414841e030b4996013101d00300190207111200362442201c20380000c00c040c800f40d1034801c1c82040500403440011025005600c00c460400400a242e90200041d04419080c03a403d07001c00c80c1c51141c1c4840d40c1200c8800c0424452242824031014181c071944140281412250072461684201c041d4448000184c41d403490f02070107200041065401d005410030040c400b1502814001a1a000c0c400070420400801d8007401c21800c424485850002e412448503030440c2c01c0400c00044e0014074103010b0500850b544d02c00303507140c0000b00b0300c0030910101081441d81c001d0000d100b200d0a98600d80c4c0030290f150b090003495000114042441d8a1282d210025500b10f24281405806e003600c42000c9400daa20440e481e11b012615220302000c9800d06400721409400100c42012400c0011448210164014495544140c0e1101d04410615020303510500c1650307000b41e403c000070180c0a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 504785008 1250 504783758 504783767
    0x5040830150906060703050c070e1f0e0f100b0703031b080403020a200a0306140604020a0c020913080a180f0f0302042409140603190305070501020415 66
    0x34290159911081000258219556000015460001401261a03803035203000d100942d00903080031414424200600744030840d04100000c010031030089001214a04880b802c415451030540c07040080601403814000c0c000c20466842e48811a020a60f03440e5842c1d02d0701c1c081d23500c103e5100290358030b030000b030a00034542c0c1904211007084202c249000401000301c8210f030240d004407405401604800b0040c4000f40402d00c0c2841c03a84101c5c2203000b040200c59001035817542159004032500340e030b10404c8900d010304484400b075101c44222011414804041405010303503200e50f40091041a80400240e0300c0c80c0025190426690000c0100b038540240d200041c0030040399201c0c0a13050f10a08400145000940c011a0280c1d0120a00d03102c01d03a10715030a01010740210301c007009405d03a03044002d01030715091604540040517440f00200d00d03642080702c0f00b1180740700500841d00070741206108034a40c1c44201582d00030a82c1c036140081c2d44031158107155009000703682040e01001c8001b03502d1480613501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 504786258 1250 504785008 504785077
    0x120c0c1c0302070522020d061e0e1b0408150f0f0c07080307050705010c1d041803140c0a06201c2706022101080709050408 54
    0x555019280205004200d04088212600140140c0c0200c9003408281001031a107160100001c404561542c80100c0300c1082c2d03008910300c0d044140c0d45010800201803500d03100e100540c40c08464040c4a4107040d84105041070040080c0310055205e0b51b01c0501c000400229001860300c407095406090065807012502c2c88103850001c40c20761004085200c002000252a02a24552542c103203000d4403a66100112740004280c00c0902505100050100d1400c0c0904016031949680ba034405401580840b40300c1d500c0407107010700036440c1884500c141d9038030b06081e81309a078060800070310860401d80c031159140300c0d00041103180c0c0a00030b0702d00208080e680103c0c00c980c5400d02d4a403c3d450302045220014002e50485064020510500b61001c1c40554448410f0301c84071030500c0c2e2011101c00450744098a4284200c03002039000412600401c0c08a114801c16000303420040030b103515081c5c515945554500072443c03507566903008502041410030031900030121140c01081c0d40d004041400f0340e00ca03071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 504787508 1250 504786258 504786283
    0x1020a17120f0106020a0f021c05070906090b0312250c0e0c0c0c10110106030311072c270d0e0f033f07150207080f070203120c 56
    0x7141004a640150074000403810303038185030b004208004440e200d560050300820390698008c2c03035101d801b010b00303e680000c42204034090002042602c0c60012520708449843e4412503505207000c48141d202c0d1b0300490380110315030004a03103680340c5003000c00040c041c0902441c1812031325100313108041004034101030f2200320b8613084030385241039070f6110b201c4c6041d1103089881c4c1e030140c205184002c801c0c50b0404404104021398588510b141001a14050869189030815030104944048541c0504000c02000c40648480f551500b0b54070540015547e401281d407400801441210000807020503204042c22a403220b950b14510070302c0380c5054119110203540840758001a54001a10380c10b041051081800d1900940142140c02020b406000041e5404000080281c0d10701040b0204580344100c0b020303400d44540d01181e1302c2d03040c0d1814034140911411030f4a1814014003407600030640040a44450321030031464140d880c882d0380700090421740d14001d002440040401c60385004800000e42620b10f03039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 504788758 1250 504787508 504787537
    0xf030906081506030a060e2a1e030c070609030309050613080a1b0606080c01120603030f08070e0907020102030a15231906020307020405250e01020a17 66
    0x2900e95008840c16003044805221042c400c4140301500c0c10800000d5611060303d000c00242c50b606c454009280c498252920001000d4602041515444102100021918486409142580717440100f50002402104d5230908440403000904400e008021107451320743c03007c01004002c049180107001040c0b50035058882e486150002140c0c0306411901c2c5041d2a000740e010342c1898040b60040318003a5011880000041c48424000b00151003800b0749c00152141c1e0000e042032035640b400040680101105401e11241001002c00109800840c207640e400018a860803690361181010f95400b01c080c031255821440c0c00041001d020740c194046e50151349156414003d00700c084035040520300050040c00c1b1011940071802003d00d5900c118949801400b41610031110194840c0040488440d404200582c1000450508503d03151044503400944441076000a1400d00d101d0540700b03c1c0d68444405020703441c1d103d862681e00030007195601940c0080e03405106101d0509444098204550415514 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 504790008 1250 504788758 504788777
    0x5031c0e0307030e0603090a0c091b0c080304031d03030d0e0105060f1c03031d010519020c19020a091113140330030411010206093c0a0f03 61
    0xd080200469010039015a18030b03142110762070402c49254000f4200050500c01e0290002c0000c3c04001c162004203030107003000a000c022034000c02a01051040503404004080460790700050b1000d054a4000f60180340c0040190501c0021603000d21087c030b043c50303040c4000b181d03404110035541c01c2345602c03503084002805541c0b00d40e000d10a1032304080000d16444601000c0c0788101000304202c1401083c041d14003c07849050340580c98206c91b2200c54007181b603944138420842c18200c55490804110a032180c11031030a6a04101a070725506030780790040c01100040c02501c15560341740035101c01382480c4002003141205c0b0001c0500306500940340b143c40041c0102c1300044c41c0c2403206440c4000c1c40090060110008100c80210f400101d81c1b64003c0c078101c914904148002c56000907611661044140d8281d03a40346000191600600074902e40481c2c0c0705400e030301c400c508040c060001280902180f0030010102251002103020100d200001c0d51103034950810901c0b07055041d1403075941c06511111b0a2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 504791258 1250 504790008 504790031
    0xa06050319031209060207050a03020610030c0506070f05030c0f150c0906030702100507030203011d1005060c0120030f0703020a080112151d010b062a0a05031c 70
    0x881c128001800c0103a0a81425a00424060070b024203121070f2907040041c40341099510002240c005072016101a0310941b4500b0400d5010826541c20488070102ca40d86189560b89007076101c40a07015040c0140d40116040040001152181500d90b03400710950780c494440c0b07071205a076003c00c200c9000281c444c1c10000040d54144801d91405a90840c3c149403070700442c2c1e02444140d40c0054225011485001525120324003640719141c000c100c1c643e005a944c0d45003001a048915540151940b402e0703502c0c06009c103601d00c20b60144100c6409590054640c0300f28070203180148103041c98140f28150307262950301000e4182006601ca402e0360543e2540c01e0f15415401c4040380940c01e1804040782e07910b0010f11419154007075022105108034408107070744121464403400e8803c42c414102a40c910000340e892040c0b8280610041c0071002d48800d401c00c002e040b408034400c500f021560007a115078001120981c4414010034a01e160000c00b07c03039880d254150400c48107800144c0d40340c015407416440c2c5c80c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 504792508 1250 504791258 504791263
    0x61503210c081b07090f020406030501060e03210913051806040b0601121d0a05120f04090506041104060203030f07140a0315090e030702040e06010605031906050402120a060503 77
    0xc4150072a66040c149610440b4080c0e100070302034080f0f0114403a07501c0028480002d40207140383c1c000c00341400340e2114502400642590010b80094081c0006030ba00808591400116148031038401440115160910103000c0f0452289800e019000900041c50140445180d041180142e400c2d40208803c000c19507009070f101d2005440082003203088002003901503203d226241c0d021190314a002410171560b1001a1900501d0b9544030f580390044a00300003070000a012481891340d140040c217281c010080c11500e102e10442c0a0a158a5078803004240f1603200c5900410210f40302d10800f95981d5140e9002a6894004407551400524254001050107218080d0306815680c06a051414a1100403090f0064020355071840c51541a144d0002042c07511402021840c0914030050b555412080c01800141d41c1c0201c4004160740c400070040040c142c0c840c2c2181d078085607583c0c02906c80c0712003c048a000e841e182d44080e9100d800400c800740752480d12101e5a0003886140c0b001c1103003641e035006268 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 504793758 1250 504792508 504792527
    0x50d14011521020711270f39070503070b15010c020d1109011203110714010c05070b030a05060415030b181c02013603050706150321 58
    0x40e2002d501c0c01005034802c99940141036428800c1912420f401c01c218007080c0c080d0303646c072030b091403801202d80750a290300d5005058681043c2c010b980c964040c41c007044c034040c0f10703802c02c078601c076007850002c01c0480d10b00f0024130307145600e0b422550700907036035403040c00c00036907940101e00142e070b161a500001c81e440d80412101400c030218103860301d504025154003000243d60b0000e00a440c2c0103101c2c0404442640d82e00c00103030117850006003c8214103610304005007098216031801d0031a0303100000034403a40010a030042820704c000d1814600703403010340c40d0813070425a0541c84080200008000e1046001c40c0ba004944500000d90b020451100c0500d08001030601510005c2d005140820200c1c6288100d0340030326040308108411111003602d13066440141d9408804100010307551030319268001c620b5041d91005200e0001108250140c95008455211009181c0281444000122001004120303000601f600c03540c83c0340441026940d0810751203006442c4944c5030b502c1e44e03034a2070140ca18001c41404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 504795008 1250 504793758 504793787
    0x15050408060105040203150d0c060e030307020a050603130503040626060a05060d11030a050402030d08160c150912021603030801030206090a08390904060c050d140115 73
    0x20710345030340f038001800001c1d880940030807211042c0500210042e20385840d5032607282e10131018084402d1800d4001021180c00e4501c1501c41c1c1c00401c0a0400b503070359414204140c8800721000c82e03581d11040c20342000103003d003074010294000890001002c5410009040c022141c4000031322a00925040501c240c600880300b8640c0500900b40a102c1030400101514154000c03660003d200181810030041a400464034031092035201d40c02c20046090900c54001c014201e0b0504551a0409200310301400703400148003010828210007203002d00c000700912840b40088100200840d03889820a030030b07100c0d110860b2102501c10ac140402d603101711404010f0443c1e0301942d40080a03400e5500700246a40302044042d4080d06241d00442c0d05602441910148411042400c1d00c0700040c0020141410280d40b01000300c0c4034041110300700341c451030130840d40550701c5580003402240000d81910740e4090200d003420501d00d81480295101249601d09058407255030701c41d0030300c03161600d0403180406145100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 504796258 1250 504795008 504795013
    0x40c050108180d080a0e031602150705101109090114040641030105070513120b040f021f050a02011104030812070504090f050a05060409080a0e0f03011515050408 71
    0x5540400348130700016908103001c288040f61a0b21030b070100303501e180c104c5440d100c0101c9100c0075003401c5240c400d10b0a4203841d00c01d0304444c10300c40d05494090719906400e080020640e00c0e105950a00d0b822070086404280c0700601801c0e103540c66401d000c80400720b189940d8052403130038401041103900280e0210f40803101c802040c03500c03004550002c0408000070702204a100f6804d901c00c00d1503500b80035042c0b1500443c0e4900361251180c81443e0812402070f4420303c44164003050010204d86504021603002c2e0700b055015a08980300c4c40400d10034088000551300c2800c10750142c3c481181d2001c0140300c1c0e07803da64000e1080c490780442c0c002c5507110340c1c0301c018002082000a55800c0480c044507660242423820207505242c3c1e141128000d80c0c480302c0c42990300325070703541c20032104030980d11803da04404240c1c0c04000c00e400e5a51045128401c410328941407111760000041c1d16520b216800f401c00a000e002440368203060f140ca003818014501520a50780c4182000701034251007002a1030448441000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 504797508 1250 504796258 504796273
    0x105451014090129061c02091005030c030714160813091812050c030301081f020a12020c070801243606120308041b0506070204020c15040c05010818 65
    0xb0149000113050740c10b54020b2414080b50035031544180b42000c0310007901c03c0250307813404c40104001e101a111003010b42440b009105010080d010541907903072112a40c03c00c181c842d107140385000400d0242c10380b0b030044036004101d940b00f0410110041c0c03003a0349020b25070082098581c1d2241e0156078144071501000100b0360800d030041588211660940ea0450516624080c55120810b0656009030058505070380400d001040c0100580607a211032030380c081c4210b0400130404801070168042c1da019013010358020818644000c014400d500050600d10b00030414018550010b8944e14049000049121060080012502c1c5480925000c81412700c180c0220411480340c511100803582c894201c4442c0e40b03440203d644d861179074619050034003d4031012240d04d001e16254200e801d01c88584102040c0f190000c0000307403910801d95002a504940c0580c81d051070029070f40c034100f500059200320101c13030b405000034441800c1342681510420390710030b80e65584190003d034110500910b0b80703640b0713444640d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 504798758 1250 504797508 504797561
    0x140a050a030e0a08150c070209070f021b13090203010b06180901060c080a0f02160308190e0a09020c03070f080c010b010503041104150e0705040801054510140901 71
    0x1c0c5400e6201b120355084c0341c140007240e00801d01410b41200c042010500d983c12950203a5010051040d145151900010a10000c5c102041c41e9200a88403004002d48422000701155020f4109100c034140140070140c0b9003001504000c844140713000803a0140584500201c0c13130510502c1c04190040d002201d592414080d0340041700c0a131030181c05503045000c3c004440d081c102610482c400190701410f4040e40f02c08200310b401c6070300054001c1c04406c0c0144408198003540310040c5000c01c68144500058644a103c1861421481045401881c005285072030b8002c2101e001c018024102d80e0000801400301c40c08010348d9544001d807005018801c08050140c41407510303801c0301c0004c45950001c1c5035202e943e8110092581d1054881c400801c602140070303c031491003403262651002c05e82011110120720645242c40e80c091044008a00c82000700007802c52410406000c0d64a8420208580c0181c85022101e4001c15041428440361261000030904d2a5414010a0b070450400d100c008682002e54 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 504800008 1250 504798758 504798793
    0x406091503020108250f0e090610111609090308131703070c0614010602010b09100b1b030c100c05190305060103151202030c032107140a050a030e0a08 66
    0x4082510659030b11055540100901485c009a0603142d11280d420300302c542d0024044509502d04c1a0065a100f4108407a0360340e100071141d461005420401c1010214040503414105484d600b40c0480342c0100000800c803c260b8000781089003c0d40c2e42d090651a80306981c0300b9041220300182244d011445001c08010108004541141c094141400c0c144402c0d540d11080d04c3d100481c411408080ca00100062030302030146c102021000c0707030411460316141184004003c12805103007a0300c0c0010038000f0b188a4503540e40314903000ca001c120703a2140d0400b18202d80d1007400d0020000003a041208880c1c00f503008400f602c0c88030412a80000c031259000208500030440100090304054417040f0b07048200720001820405000c1101c41d0105596060051524201c01501b2440c001e81c0211034a28203c11000c4d4000142c0e40d1103400580c0e01e0100742499201d803603001c02c400815000785540101040400249181f44501c07d84555203d02d0031601049264880d51141c05440c1c1c020402d142580c0c80e82 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 504801258 1250 504800008 504800011
    0x32a040e0c090c0a2705180901050907060c0f020f0612040c09020702180405070f030b0a061d0414070e091e1204050d1b08030a1106011409060114030705090406091503020108 76
    0x206017081c01055070b2100044e250101d02c030f0a40316603001e0340c41402400c00c001e008140d4444501001000001d10b0880024881e030320581024081c40c40c02e2a88404556400d8044640032000500c0d442c0c03544d20400c2c0d4200307413813000d441c11106000d03510303400521180305000b81c40e080d9400511401c0780d40340ea400b410501c10001002240c6a000b41a03012510030200c41003074000e50700409113403c442c03a2003520300c0100c8140b070b0042200c4105060810640c4c0303c01e0801c0a03070081d070110160401a0b0711100140c40d00305280c202c5021030700c21000304003100750000303114001031511003440c50019508401854440308404800c4c00c0f0058100300a01150801e0707100003200d10f2041c03109e491140900c04d4030320070210258100c02e000c3d81000400208080c1d000002d2407900c1030010203030425525200e040d5840040c07603072038680150300e100700080860780560a944007004140503a15564608604010043d40c401107030240f00c0d41c50040046183c54a910074090070043c00002103002e01e0664006489401d170 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 504802508 1250 504801258 504801317
    0x50f01030204051503030a030209090606040f050d08070f080702031905030d020c03040b0409020405010212040f1401020f011b020f061b070f060c031514032a040e0c090c0a 75
    0x3502c000e0b40c5135585040004002c000b80c0755034010b072141000300030040c81030b0020700100d1140304203000921101501c13210010440f002120340c0c030091100c925284100e4003404d50302425030920b5942100505c40d40e0307801461400e100318191403a9403059401358415851407680504030b5401841324040031f02e1154002c12125000740c0484e81855a40c2100c0c0281c0e500c16081041142e0300803408000310f507010800f100130709078410140c5042078180803201e02c0c092001e05c2105032080101a0660969000380010341440a520009201e0000c48007064118400c9180348800140306482001c1c0319a6000700d0680e02a4003100102e181403104940380f100345404c125400c1c1c1e449150001003000180292050352040801518041403158042851044e03001440e402040383d042103059050b490f55010442514211602e1700c1c0c00c6403454003062008d08010902c440c6c030340241c41d003072200c8407502000490020721481114801110b80d203401c2c00c0c080303e000700b04002002c22410000a00c8103641707220f140001e1103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 504803758 1250 504802508 504802531
    0x6040b010c080d0e071205150601030204180b1f02031215060703030605030d0f050a080a240503010f0207050d21052706010f050411090d0506070e04050f0103020405 72
    0x3503042c0c440c0501548000030b603d01d1255038202c2d1a40910040c061103005040325000913a11810ba619255220880d4003006c101c1407000e40001402c41c0c0c000d505884c040d001d80c0c50035026100084180000501254201da40300340c10140c1343e41e50303900c003420031812015499030195052a0584500500d04d4401030312000c0483d000c10000940c13900c4880103844040d000382c0d00030a100d071034042418100204528404100300c1d50801962200c0d800804550b01600189420030f2261b98040202004242c030001d005402850a8803030781d2600704c4c1ca0744007000c2c2c441c01c500800c2502035040b2054200e2141803001403164003c0e030840740056018400b00000090920380301c082c440c0207541c902c000c03603500721402c1100010104801c00d00c04002c103024010600340c1c400800b640e505042e6140c00c20b000c9846442e104940b074400600c0307480344101c251030740c02001403c0103880c280c0c24603065441d80411030b45003000903000100044185403d0261500507980c480da40d007203503405c0d5001d20001d018010060740c40c61 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 504805008 1250 504803758 504803777
    0x140114060708090d5f01060b0a0311070209010b030a020f28030c0927050c04030209130b07030f02091504091a03100207050f03040e01030605090102070b06040b01 71
    0x1500c9031801d41c244540302d615680c540b11960140345503504030a108042e62180407000c0e05540d0402d015155403400603401008174158a100300b00f42821002075800e01c8254201540020700000d107038040c04005e0703a0764070b040c04101c1450078030b01064011480d0203903005130040010441001008000c41e0458119140580b0305901203000d20550342c80900c04030111008488054151000c642c2c89103040700551030305000e0b400c610392004002c080706000b075a018018060311190410065440c80c0210325130b07454107200b10324140940914a030003a22080e80508440c000042c01ca012181003158805c0e0b001c0010407254644d40801c400400c0e5182080c0c400c6542003040902655440480d81d400408120010307070307158180002403041d03404407200d608505101d2510f030001941e000c1885030412000f00c800686400c800e052891030300000100902c1a030100240c00700c2c2c3c0b40c24080041d8140d80c010340c1c0910043e242c0080440c201c3c07058801c0078003103000e61b8008c44d0b29403400c0d420044c5103480514000051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 504806258 1250 504805008 504805027
    0x50c010e0114160b0c0702010e190f03080c0c01050403030906031d01050f0402011d0d0f05030f0a08072006280609050f0f060d03080c160312140114060708 68
    0x2964030031220704010f4900c900c200010082824441680084000c00141c180512640040e080211f03030441244614481d40c0006100411964075100070118242d00742c603460341d2410a002d0b1740c1e11a100c0c680f0b59000d540340c0398106500a00859040b69810f030307201e001c003514040302140148440c0080300000070100e0304400b00030409005880c01151090b4039140709080600c009020000c040402c1d900c1460380342c10070308082d41c90074a074500300c41d0810000d000f145180c0c90a603003144a0003c4a01003030b1404240c0d44001a0b106000d540b003110181c540700b40040340d000b50b04078001480d00c80c01c1c203984c2c018800554104003d400544110503681c4c0c080e071139180c8400860090f5403450300a807903040e9940041294400340040100e8001302800c1e000100b5080c040c000c102203080c41d40f40a8140b010a201080c007403040e400880b10441c040303540400b482682403400a042e000d600781c041d015203003401c5034012450103000d41281203802200e505000100300b881800501c0e0800d1400f910302d00814030106c1617 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 504807508 1250 504806258 504806297
    0x180d0606080d02100e1509010f0c1725050a0c080309010902040b09010602030403140f0724140913090204060e06030f03090607151d010e010b0904050c010e01 69
    0x90465000581030008840c100203181010305100101130505055502c0d03400100440c1c3e01d0f600140925444d191940c4040c2414058070740b80300d061072000d183c030b2410305c1c0440c3d1040340e9040611040c45651070707645642502c4603940d004004031354060003003500c203c82c44600a4000b803503946c05508000e8060401519800050341080743c498800380d440d0003003003085107490f10400540c001d00729890b0b0003030350600da002580c1c0e001f24080100681c0140c0c3c2c04050700e030320800c00b0640075030f051822191203e4a480380c8103d11906085480000142c3d44212110f0364011900a000c0c910b024211a003003040303a80402ca05440e01e1455030700b68543c3c135aa4540507031943e00400c0c0c0036200d000d0303510005050030760515140071115018026241c00501295146e6030b141130840751056000303c080c0030303001c4500d04100b0080c4005a103c003940b0b41e04170501151880706401003800d10881500170450a1229418894003210840d0014810f0300400d40003640b9600851500792030002c10303d4a000b82400c20001e01c507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 504808758 1250 504807508 504807521
    0xa0b031911030109150b01091a0304020d0605250203031b09150c01020c070f0b090409060f0f0c03180203030306090901150f05030706170a0e0c0411120906040305180d06 74
    0x8501007280380340e40017292038901410002003801e21382444458a0942200c01d0405000c003050f0107540b0000105095613510020880c02e40d42144003041542007200611448002c402c40a01c0201c00c0c00200c000c04a0012042d02c1c030a40032682c0c82032058030381d2004c021040d40301058041c0d01c003640d044071600d245103440c003078078418581500050f03880f0801c81482e032600b5615403200103480d044c20801c5c0701d100b4032201035841300780081e500400c0882151402d40050540b282c1040c8089161a00115200c80182c01c11134610415803001c000d02844c800034425824010794000e90181c0c000c0001c11440c0c1090000030350f0192800000182c04614203540c1d070f000380400d502c03001c0c41071401381003804985000c1c8100c80080c20349050149401d00100701d10030264900600d0380100c16a11180b0200c080400c3c46072a84640c0000c2c0704214801d1600c000c82c1058000865005031805080005140300900099031805550161511424003254002d46030032130000031903460300004042d00b41030003e0068000c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 504810008 1250 504808758 504808763
    0x31104090510060603140c130e0919242903030415080717010e040f1a07170a0b0121090206031006020129040b0303120a02030f0a0b031911030109 64
    0x1040a0044400c40c80403914040c7c1900481d10080102447c50b0315200201401c80d14040c03000c0155a9840d8916410000d800c1d00000d040c882c0646900d042100007015500b0101c0582c45021443c05043c201000300d44182e51003032020550b00f005005c008942c2c00080d050a034000f8205c91070280c6824210010030980a04480415104003d1003405a00240205c0500140e080d21034299071422841031941c1401410150140700382c106031005103e80440c015040c2e921042e40c040c0ca5003040342009004e401d00c1d0882d0385000c0e8410001c624402e417075000c1c28840710016501c2c10200800001030041c8000e10b03c0c41f200005649138480340058582c0c1e8003451040c80000c25844040385001c201a0070740341e124103080341e004048014980d07000d603102070300394110001340d40018501e118031001c82d1070361045001d484400c0b140c840402512264075001544185030b112800641d9407154881c8005850344402e005134560084a0844000c09800100c00d0040d4007940a030321170070440e000404e0071144888401d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 504811258 1250 504810008 504810011
    0x20904020f071505040c050f030307052a03031914070b0403020a060606022b0504050d210f05071e08070507030606050f0102070306020a03060803130905070801031104090510060603 79
    0x403d00081d6452009036901440040c001c910302a80d40042c941214000c0500c15441c84080c552075840420584406a500c80d08540b41001c1e00f400c10103458203035248503c0c00b1050146c000d00c06040c00305c140c50182100c0301c904140140710007001d03103802640e1b0b41541d8070b14600b03114080208094070315207030066003c0e402400781290301e400c0172000d071802a0002c4042d9401121110b040742c0303103070014a050040042c480c8204156a04013201c0d03a20035680f000313500111141d10308081c803401407403009172006440f2904800038a440000c1d16a808220308131030200c1c0050102d940800c1500000000c008403840c0b40540c6180d00f96204243c0b41c110850940c0c656202c25014410450315200d598040c0c9000ca640420010f801c0000079a946524000100075640100748004050700980103240500300f0300007640c0c1c8608010490070f0a02130a17119640a040c01e050214034401c1c02034104070706036604454184203082c0320006210240070ba01a0440d020300c5105079480d0400c100e8820a400703020245c4c0c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 504812508 1250 504811258 504811267
    0xf080301030b011d190e0d02031207090e191e0f0501090e0a0305160816030e0a1a03040c031502071a1501111c0915020d0e13020904020f 60
    0x2e00c1120303030405070890356050040d550310660040b42e100c80315901800250581e5141c1d0010001032016004100e0b0899840c412080055000c03500030000e0089040e000d040b403903c981d40c1d581c0855040c840c91140303102003801100400c100720101c501c21201c140100ca40491000c0021998031142540c0324180154240c0c3c400100d088000c25015090052580e4102031140084071681e0b940c0741c0302c00c1c0600809100c00010314103c9540503042e104105904040c00e5604c030f03040381030003520f03506901c036044001034809102c1400070b02d0001980000d592891010310a400800812180941d10181007131320000c00030100000042d6203480058008503030000702680701d041c2440d001c42005003501c002c9140c8268003041152000003407003022003040e0246030403030f2845240003c0382e04260301d000c0100d0101314461102409250804603000c101c4590046c00c4a11034070030302c000c984403690264040001001600503c0440c503041c1403c0c0790018045200601d403084030350008049a01072000d89440303d80129 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 504813758 1250 504812508 504812513
    0x6010c08072609103f0c020606010801270c03020d0504030e0307140f1005040305101b051306050a0509040e0709111306080c07060504030815030718050703090f08030103 74
    0x700540c0b5091150400c1c0d0802d2a00c01070a101d6800c0380075074450903203ca0050b070b100c0003003010f03420420304000c0b2004001102049800235100c0c94110707405404198134900018210021101644903500d690b601c1841040041244202a24071103098000305502848120300c40c41c1c0c544036050141e442626800365202ea580d0916080c82081d80c04084d0700760b04661a03140607210742210040b80cd1085070300070044000050306070380c0e40c001ca42003e451440b401d01c0c0403590401c3c03a03000c176041004000000302c0c95a00c2c820101d5480c406d641c0c0480c1190300140080050a000300c014101000407803c0540c204203d44010604803034052078000007950000c0d004000700c1020b845022412600c010055103400c040c184000c40441e81e5100348000c0114110000e001c111250068501d22940b03c0c5082c4061308080c1001000f8034000e6031031040c1d011400e060760020b40380004468040f2141080c1c900c4c048c1c0b0000345518000c240c0100b480b0141500c1d41400000680d18100c810f4903544548c04036901ca5040d070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 504815008 1250 504813758 504813769
    0x9070602011d100b030f2a0607050c010c0302010b03120301090c050f0a11071a030411120a020103090f080301230f0904150b060a021b0906010c08072609 67
    0x4003055148240035022480400e5000c5041018012603200c0451140b01c0c1c84c010034034015580ca00383d407070380c050b803010203042c4158401c5003500f41d5102c2c030007010360714941700400815100d042d1700245140d101ca04c1408540d4000d1088030145400f90000145040a84011034209810846500110307503001005000384c482da03104103d114815443c0040c00c2040d0065400518400c10b0101428404074000e082c041796010044400500307003680042861308a91400c006c02c0b0f800030350f802c0f91400d60300704441080d030602080c4072040510103030041c031802080e50015402441c0300320003514440315001c0003c0c041814540198000d01d046003092251100c1808a0901105001d045030f04c100408484440e00350b65511201e0b400c43e400003100f00e00d84618071407020007850703802c819a800c20800f0811481240c0c0200b045403000c0d000c511a01c404040640801c104044110350003408144007188080c080f6800202030030100d4801c0f44141f84868030f180304051440000c042e0444050300004004086040c507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 504816258 1250 504815008 504815021
    0x302100c05160b03040b09010f02130e0f060a090c0c0206030708010e1e0f13020a0e09011a030a03081b04091506180e13020613032105040501140d050907060201 70
    0x4075000060083e0812103180500d100142c000342296104030045528030000f9400184402c0100300b0440d51620076450498040300c0c40c0c03190611000b08040007c03046018405154400c120042041c03111905280361800200306100e40c0c0360801845241e60b000585401c002907004550399100d00f50301d9850091503c140c000002e100c1141c0340c00012441c8000c0700381c055140d420070010390482081e40d84051403044c1201042d82d01961203480c03034030300248608000c90b1803806416980300034441140324000b50000003a03c41a0150181c0c49040a0310100344136a030425001a000b00030745202d100c0400d640d1840d41c1082c1c00800c07207683c0d96188a03c0704010304440c24024041410074400e421110041e1160041d00c0d84150050741c1088400201e40c00104c020350010703254000c02d0b240d2500d175400d00c0070709803584500040f92085d000741c0204100fa19080030200c41d5494680d1098507042c00c1000440e0300c1c10756003400085118061180300b014640300c0c0034662180380e82d08010070403503285c10740c0242034481 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 504817508 1250 504816258 504816283
    0x10020f071e12060525020d0f0e060712080105030a020609040f24050406140117150a1e05220c0302070609050307050d0305130f0503041508010303140a0c0201180302100c05 75
    0x3805c13140c0004580e00414215402e00340c44c100341c400c0f8000c4900035208080c804100a60000700016a2001c0003060081d850012440b50759514481ea00d1748241943c442541d00702941c00942440b2440241c90640c100d29100c040101010804400d498034429821020042c41c00007000f03800030601036818030f40720356401003018180000301514030a001030f08401e44000340c070712034451801c0081c9840e8080740d0718417044000580b1421001342c0d1100849541006080403500c425002200081c90303143c0740d092254002c600c8041401c810400760030320001800256000e006241c1c00748014000f140c1544646050f050181c00034564030070251525506040310369030b9a200b498500020300c0801c08180413450515544460101d2600040b41003c51450040d6804031400c0f00140d200c40992961010382c242c1224420748405c0003040001d45402d42038061030302040d0000d40d81c007900d00c0256110720300f4070660084c2060341100081c2c503600441c036408001164040072816094100007041410030602940c4030307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 504818758 1250 504817508 504817561
    0x10090b091009020307020c031b120601060818010608031801030c140301060c1a090a0311120909061c03030c090b03100b0307090f031110020f071e120605 67
    0x18246101d900409010300480300819400300009400600803c00e61480e00e00041c01c40340c28401048201d034090801c0c898a41c081ca090401603d100c201c0040d50314103982e0307540c0329a01c055840c5150784003038500030b002c414520f648440c00000d40010610041c00c41c07010101e14003404000030070000d404d8485a40c20f00d010000c8d0b03104800003400e90700c016a03066030b14601c0c00018111141c10000210903010300d10f40703400080542480349006000a10418162207901d4560882c040021055250052481c1d03410300e02d902040001014680341c01403941c0b000c2c3c005c000044280211120601c1e00050a43c110003199894212907411a0000309910081c48000c010616500d8903645805200000742b103500c96146001c0f021500650050300c0d14030280c00f625200d440d0b0303182c1d42e091001240040100301409241901000000588080358040d032240e102070017071a5052915841140803d10300e0841680c034048100b02091207041e12042c2c2498900858002c1800e00301840e2040d1a181198620010388 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 504820008 1250 504818758 504818761
    0xc120b070f0e0913020a1503200702010305061f02010b130c05160c0302060a0206150a030b1308190207051203072a12061a0901060905060708040e10090b09 68
    0xca03400b41000c1c200150548401216484081c1802c030500c8074010020b5001c59040c10100300c0d01e0080c4141c0000c2482c541e010b0007804482003008007410301000c0b4555940c2c03010480040554040d8201d079800900161076401031201a100c00f811800c2d4020002006035160b514918132440c2480e0311000068040b00304015800550300007170014460fa070000c0004404621140f02171240418070030b00110340181846a50396020180251a10f108603001701800c10340503110265424051520001c3c1c079401954403078681c480c608280e2100f1042d03039044441e40020411030045c01d14980e40054403414a8008281c2d00f410f04007000042c9007811325000f01544140114000300d4104c86641220f1383d548842c034029800c070b01101a0030002a504a00340c142107a900c51000c004096002044244150a00700c11000c200700410104030b80a110303590000e00c0f20320041c0210715010004017101c522545842e440c19549500c1d68980c5001111132000078071804e44200f04a41080c06024440d100c101d4488165 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 504821258 1250 504820008 504820037
    0x206010e0903070b060f0d0f0506010e0c0301030f050c04061203080105042003071112120906060f120109140601080f010203011512150b0408070603020301031101030504030c0c120b07 80
    0x1e9001c3c0400103031800045001040898440408210080a002d80207010064203400c100c07042a4000030b003102c0c1881450b000103071a0305040d4410740138034041040d180c50769107161100c4004100d9140c0c2500c95026502c481841030342c45100743d070010400e030b082055010006040c0a404040c0590005010340c2c105040c00a0801c2070f04080d20b0800e241541e2035460761507090781200c1100300c0010111161281d144042c040c0829013002c2c113000c00e004a48820159218040241c075484161800c1d40c005a41d00c1040c107607071a0001c407070034039011404c00004802c01c080d01c40600c00c44411503400000e4015038010b01c0400d40910002200a004c100207600e994502080b040c500c1409641180812200c0070f10b5900250701f5801002145802001c60f00c446929044444ac041d030081c0703d12002131190341000240c15000c1d000380d9040303a0b049081040707100d0100c4015006080000c2c022020009280311078070004001c4030068001e00352010028000017400c5c03400e40014130019040070144000d04441c56030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 504822508 1250 504821258 504821263
    0xa030f2c040c1b0b100306020a0905041a0306220614010303030e03040e150d150c030c0c020919150611010b010309121107080f210f1611130c0206010e09 67
    0xf0700791301603415221652a00c1e0f20903407142950704000d04a81c00000d504c07403400e0313010440c00b06444088904010400d00c200c5005440020003c202e50103401c9000020001e0010003628259030040880c2d8000c028200d580ea40e0490706580e2206200d07070420001030050540c1441906c40e1258417400451910307042c8002c3d8540d900780146140501c0130300c0c0340d800c00740c2d4480710b62030001e4550190482035041041010000641740c0100007000107031402d481150388900c15114000c40e41d4000d40b000c01c95440301c0b0b08158400482417074401703655486105099000100c445400010a00d0381c0d190240600d00044160079100010700250415041c5409800810310144101502840c0e0b810136480c502a9210020b04200c4203034080c2842e8000c2500c100c02c0ea09002c2400310644400b140700c0f01d01c00c48079200e005d5a600401180c0c944400c4188600c00d01c007008441e400054a0050150002c042000000110b009446004804249480b28125280d880d0100803541c007500b40e1018003181483c0c00d00c000d03079 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 504823758 1250 504822508 504822557
    0x10020f041203020321040302100507120209060906040f0303030e0d0e090601090807121406072f060a0603110904020f010c0c050303070c15080403020a030f2c040c 71
    0x15448040740c00e440c02058001c10807100d503404a061034580c02c48548070340614159088405030050300409014a0016400b445828410790003900c1700140282c0384402c0704025003100513125040641000880d03103030360b10704016000900006485248040c25841c1c014281c402501724180294802000700041e00d4101250561541c801da4106086a8490380120307000c00099101c007066006d14100071030b4246003121500e00d900e0040c0c2004a001d20002a0303540d8418040b92034400082541703000e10002041c81d200f42442c101002d0a0810344403901c0f4803103040040c10344002040a0f510101002044620814020110b0044403140d9162820380c0215000500c070005c01e41c10014030340043e00070884a04481ca0103400041e0850f078588803140351140160941d409a626205070180306030856610540b030130f43c41380740d150f0b0281115a0301a034003515250100d08450b802c0c000216211224005194900c1d00050000088800703400c1020060004459818034900100a02c8a00304011900c0c130004d240d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 504825008 1250 504823758 504823769
    0x20706061a040f121e0c0602011515050f070b07020606100206070806091009050c0a0801080a08040302060f04080a05070e060328080f030406092d1211030c0a0510020f04 74
    0x1c01803186458812a08009180f24000400c5124010305c18003c4100c1c020058501640003040620880300311049003400a204490f1420180c0c80c01a201c10b200340003400d10f19814252090030501075540351441d80c0c01c111000350050780500d04000642c41c19007500321040000340041c00f5a4181941c008000030002000c003405039200b900816102d002c0c4002c1c5100401400c46d0070803041c2071244400c1c00c0396000406840001e0b0300000007240020011560080d03169010300032a14140c40d5500b80070481d0403103054003e00d00e03018000028010401e0200c0d0814030b10800140007042c0c1403081240e2120005824a4002da0100803140d04440d410f1480303000d17280080c60703007030b5480901d0f18048605206082c040841d2030720110900c01040031030b81040007050b200b03441407040800c440500041e010300808000000c00955003800000c1000c4c0c0c03c02080b540304903e8500711034800035949138516400082c800e032140d4010360003942031003c02d0158000d074485021003946010601480c4680030300450196 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 504826258 1250 504825008 504825029
    0x7090207120e01110f0a140705010503010e04230d030608010e1f0605041118060a17040201020a0206032a0307050a050c031e0406021b090109110d020706061a040f 71
    0x640c10680c09910007092030001da40440e11780c003070740d80c2c3c045413a1240c0442c2210500d100034030b08a0300c2440443d1400c20b03510183e403814116880c014003141c0e0054040c20690b0205d00c001d42c0e0300134080c6448850f44076400c0490007440c041f01c500100804880ca02d0f0301c050740741c0c1d1502003080c207200000b05814000058585000c51307134400c10884200240324543c8126401840c1c07229410304130308284090191406185284d607420803030714040c000d0921884030702c640001e512462902c0190300030340c402500b00e030040c411900c40c0303030450b8040b90241c1e00554800d4014050701940301e01720825001a011031b42500b804030750950074800ea019045019860f103490a21801260800180724200141e40302c0c0c3c0c0c041162440008074a84200c0c00390344c0a402824018080c081241108111400380000c20701c42c09008402039a28080c8001d00a0054082a60407040c0c100420210b40c0c0311070000d030542038084d04002811614051910010102054800c910300c401800100060880500c0d80011a102641d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 504827508 1250 504826258 504826277
    0x504030e180c131805011e06080f040510060306020306030c041a060c16060f1e080411041d030a02070e1603020f040506070510060515040b090414180709020712 70
    0x2180826010580c100c8400380d450746840c8500ca130081d4012a040380d440303040c0715a8445421401004040721402440049861400880c65440000e0b52007035000340a0401c0d00c2c002240c00040c40c084d654070313034415503c42c1c1d0040184001b40c038003405440d000031403c0781d0801410aa542e110300d64030040c40d02e41c0713101e10808142c4942d03034842480070312804450494071126183c1c980c2c6001c0d01d070142106480c00000c0300e00743c05c09060712030302102d806489042e40f01c002482c0d40d207568900040210600c0b0b180c01c036031185205480380745100c2c00720f111203181a001d5501d0301090b52000789088003036071100d400e000c03011081c09690242400000d56035681c0f0300e005030340e03425401c442c1d03d544d110701c2c2c1c021500300030001559401d00c00c021071112030128007800c00f88a02903403102084032120000303d0700120303c401040704001036818035004010030300c009880411100b01c0c2d5013181d0341048045030851440c9110381010711414009000d007001070701410404500b070015a441c0c8010075060303c0c0c080010301c2418407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 504828758 1250 504827508 504827527
    0xf011428110c0a0b07030f0203131403090d08040302030d0912060b04060e041b050102010c020304051c020402131802072a17030c010e0c030a120c0203030a030504030e180c 75
    0x304440028091074110f5100914901d414601e04404030b611900007403034405062081c004074022640248400300c1010860403894a81444204001624507414402040302d04440d88400416000702401405016100c07441c5005060a010440c10003108000007003806102c01001c0c1a84003940c582c01442c002425044034020400802440c0c11520000e01039604000c100000d44802240b4201e00d4003452a80b980d8440044e42a200214402c0000d03801c11301c0207202c0d6052500c915440c0450040803408000b2054000c036080303038041078807440000c180c84024400881c86c07500d4420b1104240c0d1046240200648621030500c80003500702c0010b0a01d440014540c0f40d2083c07012028141400c08030403201d1400346c04590303d030701c03c5110b140c955013040d4182c000240d000c18210300910025000d04401c024655907450340b00400102c50b418004900351340405030f20200080c10030450315440010303d9040505028126495001c580d6100304000c0d420030802403408168030b504010307801d20b0380d6122503811 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 504830008 1250 504828758 504828791
    0xc010905011e1407080c180a060c0b0f060a0e0601110f1e0a08030106140c0a0302060105010813050a02040f021b0607110d0509060702010e030f011428 66
    0x400060065802c000391007076410300d0401030344190300102e08100000c50080c0700b01002007608403821004a03c0c08400a42d00a02a000601c49002e140014034001b4180100060210a10390040360004074204d99041c03c020120309e0881e0800c4804100b00380502c1c01c48001102d000c1140641050382c0d40300d20100300582d002c1e4030051a400d5402050f00d40c164400300780c80d0750b14401c00400d00440510760351880422000130540c1d43e41160030004892840c0e003080b5058a041406510700041e1010402c10181c204a00740302d400b0307045201c0c0d40034141952401d8001006d501c0c024007076a41c407851503100000081c100081c480503460b410340740401c0100401344050001c0c001e4202c00142600d1400c1100007802000c40c069204150716103404151a5440760003a607110580d0751100b000c00d40c01c104007602458400041c00080740305260080200c4842400300382000c185001240180e9111848100c80d040100162039002806512042c0071090707002640702011401c9030025210341d990ba24002c14500305 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 504831258 1250 504830008 504830021
    0x70311120a1b05040207020f060307140c0d0e060f090103051f0e0a050702030a120b1507050309100f0906031503050303090d12060e0114030a0c0f1a0313080c01 70
    0x880c15a4101d004504102d4022202d2004010208a8640d408252850b140c802c0e140c0c22038000d4028440054800c040c08501c1c1d1001e4880300a000c694020101c0c01c811020082c2004400c50010784141914060064002c1d100614007a2042c9020300c0150a99100d400644100103424603000c00e550316102990505110708040300e00c442000d01c0c03030120711100c60305065802a62880420001c95560001c102d03101c0c00b17000c030801300054104800031342030f040f60340000c814000c008000b0f00c084014002c0340410395000355412207035030f0004600d00207036241640c10204205818140f1542d038100c0d80380c0080214145015042c10316954943d400d00d444000d1001c0341c069a803160031641c0e60300305002d100740d40c0c141003506500012508910b407002150580524800c030b0340c0c04401c200d0140d0901004054601c00680c0b0550507100d0b4049000100303000864040c02007160703c0d014404503080c00e800f01c260403100c15a2941d1080204280a2008540031041c0e04480e048910103032542a60410340303015044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 504832508 1250 504831258 504831289
    0x403050d14070c030207140607020d051c0c0b060306040503030a0c0318031710080a2d03030605030f0303100b0702010203040806010e0109060e070e361017070311 71
    0x74a80c00c20001c1504462100300c814066001c075a1b4241d0303201540d1401882a0700c0864000b4818000c0d40010b043c000a24002148141e0544405d8541e028440d800c166490124400140c000341121040c09490403801f600003070290040c00c510b01c1c0c5521080c2d620300c03015109a1855031740740014070707645100380c0c40039110f4005000307100041c10107401d0080050b2b98081001c00030b100901c000c24800c10070031207484222030504010b8444126181c5680022022085940e410504240c0600f00c021940c040100b442c20f100b07813800600c4a013441c060500d00322036035414480d00c3e0300400c10b1020000710500103408560742d08219590750600c0340700403400c60055601030314492080344000f00341001c000c100c060685038a500c0800c8a07a5a4400c0e4044803a010f544900c0420510590100c890901c0681407615294902c40c0048021500ca00d1942050300c50315004074414070300c002c1c01a03010512078650f00408113036104107585184002c01c1070300d800d29484010a00c501c1c1c0004822151120900c4201034030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 504833758 1250 504832508 504832541
    0x10f03060e040f110901030f0f0f02041506140a09030f1e0b150f0603040209040305090604060201050103051e1e24100b0414010c05010b0406030510050601170403050d 73
    0x206450208024001210300315074502031141c0e14243c0e805d0009905049035080850803c09883c82d403228106940601d01c1503c0c2d40907041c880b5005a00c4a020381218518000c42145400d480d03c6002003950828001c4180d00c0c0b02c040000041d01c3e54000c0d640c10039a41c104000050b481c069140c0714490f4006440d2000d551000089214248064244010710a0048600103183d0440c9031081186600104828550009090010802500b0018140c036802842402d14616091410b800603003d40c02c10317800000140c3d11040140200002442840205603544034409a110120a4803030f8492403a410342c1c04414602040340d19185c88100046581820714000c0d2440c51103460b568845101c6003210b8806181c1220440051985440c004860072030f04919410504410f20b0801120306204489013514599201e070000030b10343c5e50720310440c4000e41c8944020000c0914403003900e41550030040c80c0c1d50501000700784030300d0725000007840d4551040d41440e0a0340e9403000050010000c100141000400c903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 504835008 1250 504833758 504833761
    0xb0f090604050909070311010c1205090d0203030f07031d0a030335040515100b0a0c02030d03061d010503031c18080903011d03071e0615050907020a0f02010f03060e 72
    0x18130041174100659014071010001045070a005450312034030300500a014414402203032080e02c1c4a100505800080188020358030341c00e036000249150450684d0071440540061b980b0308064021000580f50904020328480d110550000a034503071401d44400b03014045088413050940d1041c1e00440300c03400b4a0342041e003031144483c01141c80c6160031202107072a84034031608014011084c1c0011071190f00c030303404dc0c0c00e5841e0900d03055404540042d08164203000071044004c0060b070f4140802082c24035282c2c3c00003405807400d080b074400d5800010b07690825020395001401592404001c0726000503000700880045030040b01284020040e44031881c40388070300004104100031004000f0300641404400900400103281c10862490b0800414a105e82d4820020030001034024441c1104003162900800c250302c80c5511640d007581c070b0380c000300f2101681e407102c2801a89841451a0b404c000f140c802440c400340590b661a8555868140203811300200c3d440ca00c1c44184070f81c10440c054001e41c0a00701e00ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 504836258 1250 504835008 504835021
    0x6060d02130e0a060603060b03060a140105070c0b130b130603090839070f12050f0304080708160806180102040512010506040c030e060403120b04020313050105010803040b0f0906040509 81
    0x130000b0b405490002401c005d400103803401c03c1004e49020b4540149240c503003034608030121840c0000e6183d0141800000c0c40b001c8041000220f10300010a10b450b401d90740d070303414080c04050301022500706032800700041c8400260188910740c1381c420f80b010b0703040c0001d041401d804e2040c51030003030010001000320180362060381c0102d040385044400c3d42201003084c0d42d40322201403e48681640c02840e6003d010b040b003c101e588582005801503900490659030300f07000701c007001d07400c50780240c0002020341e101070001c00040400300130030702400902d0b4081258003418010421784480c4068003142c24410b440841d444034540c00e40c121001010b0040c24000e50074130310598240600000c950301c504c114601028040028084d000e0461004040e0300a8139444c2e5aa40c0c05952641003458903006a90351022440091703220b910040d8003c03880604405100c5500c0e1400301d0a40d04140c1020f43c45410a000800418841c80141c51040c28082d800a403209686c20110b103050290740d000c0765200e01c000c010300c00b9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 504837508 1250 504836258 504836261
    0xf0a02010207031d03030f0706020c01020a0215060d0314070201090902040f050909070b25240e01290607064b0f150b1308010506060d02130e0a 63
    0x10030310321a45410250542c89003801003001800074203d17806030001c000c08004c0300750380d030001c0010707a100b0b120050505084815280c03c90704044d50410146e070040030f0f4441d0242c0418034040e4084c1017211201d01d980020b50b030051403c2041c80300b131210a0300c003040700411a070103523190714003a0100010031034a42e9580c44002d4004c10340c5110f401d00846220000c0b81d0040f00103e0b0440c16500007900040c540585c86021591041c1e50807040707070300d0342e5284015800182d4507201d00f520181c000708010155410402c20501125040180900075a00d480310544d8050310080c0b5480c82d080e101292840b404a18401040c00d510901c80d008268a241459442c410020310f0540380310042c8000300040030200c1960b4444070701545292580070400448400d61051100740c1145065080e802004140c00c0d0510314405403511941d00101003000d800706140307106142e45105c010040030004000e00060034000702141070762150304907102550750001a080382c0e60366420800740051941c403d940c000d51814124000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 504838758 1250 504837508 504837517
    0x1809042603150303130e190507030207140f0c10141903060506030f01090b040e010c0c020108090703030e2814040b0d0b13050118030e0306060d050601060302030c0f0a020102 76
    0x600c0038a030b95031901081c0c10004241d850300460f40400091250900d003001c6522840189840362a410030711594000081500805005811640f409602c40e80359140c0301e05e03504e40c0350040d0780c16644040c0c160001c04a0004004191039400e45110300e0006181c8001c079007964125142c8484500d00044201d40b044250320714400142c01e81da410000591140c00300241444251500a44252004010710010040d0341c824200164000e00009005a10000247c00c1d60b81005c032200c0802c0c0c0500030703c0103550708a882035601c0203040000c3d02c256400c0d0f641c060b10a0003401c1960f4001c041c05080305040c014503a409100001101030001c20580e511995411a50081008940258184134440749103003010900d401c503869020020005a989480d51201940c564a20640c1e031503481c4d200003c00c104620f10084079140c044d41d102007003041d100045c1440c2c0303c2d010b40404e004010484c018808540c01042c2581900c035603143c0942c2d00d4903411403100c024080c201e00d081201e00c0014855004070740550042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 504840008 1250 504838758 504838771
    0x60801030b070807020d14070212030307090b0301121e0506010b0307090603050606070609151a0a080304030f02060c1c030204031505010807150c08040e0117031809042603 75
    0x24480356a8200e011104070300c3c103407050805644510702c1003907118040c20a42c0000049148020704185890f0000303140034401c5484184035400000c00e0081c0b80390300c03403000d401404982201510b10f501d0f084002200c030541c141d01403c0c04400c0303000f8010f01d03403804200c00e04940d001000c0310410358451282c01002e81c42602c07681c022508501d00012124001d0181c00d110760720040030281445160340743c0b0b50180c204080e0440d12600c044d40c00f480c901e4218451001c42c040380420010b061040ea100744032652482c1e0700510025071082c0020070008582d003103000c1040781c1c1550895107070308841650514141e188503d141b40494008241c03100c440e49070780903008590041651030081c000300340800e0101e03030302030040144d1500403690510000b1900e003005021115546049415205a0740300d1441c650866008800c00c1c42020004100307444c82c0703416211300e2145a002843c9010301c810990701038031054841042c059409900010244083c201c1d03104584040d03010310790811052250380f50390550044405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 504841258 1250 504840008 504840023
    0xb04020f09010f020a020108070f030f0c0206071112030109020f040b03040501050412030e0d0f050405040614010201050c040b090907170703150b13093803010c0e030303060111030f0406080103 84
    0x10b8820b984c40003e0301c1c41c240c0e4040e110711125456002d8129004803462480c4c00916440307400d10040340301d1724414940c40c0025980584271a00708014002d110f0814a81484095070140b421a07540c0a031a4040700d0444910040040c1e40d00c00104050380b00c2e0003181d100d0300c2e140401100700320a110040d04a64415481403903440780c1810a0042a8201d0345080e107200850791010340e000747c01d14025108003140510700e09140d4101550b5400041c1524110380001c0f41002144c1e446610390b503024040c2981100c55a081c0604180c00c1000421090244069942c800c0c0095404680d085000f141c2d4102241c682c15112445880c10b500c0140140c001005070528407031000c08c000490342118016520310074500c0c444004003030728051955015008014102c4500d64084034a2b02c180d0061100c544903065070307058454211142034080600312081d000302c0300c040c4562224504080c1d81c01201700c030303480002400c000782e0308420f940709145580078042a40010420000b00881d600c0c0d08081400e049034801c0c0d18 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 504842508 1250 504841258 504841277
    0x1050a0605060c060406050405101d0106060f021b0a1517220b040204230108150106121a21011d03070b090c0a0621060303020601090b040b04020f0901 66
    0x70b000c014070601880c0c2802ea00b284001c54000740076a007100b41c116010300103d443c50091148440100d60039a0b03030440c0301001c0700c0b0045454610078002d0000071705141c100b5001c100c189a00280d20384182026490f103510012082034400c0c0d82d0b08500d4005414404089059030458000c042c10319003036198003e034210880c070300181207480f0501003440340030301110707004da40a0016507480c3c02c0d001c4c0151040f648140c4800036103c0101001d03000ca005511400031104095151200385418000740242c03e014a42940006004158100e8078001145414084c00070310344160b130700541ca40d2036001c0005544a0700c1c405a05401203243d161b04010074100300d008005a400044007451101c01c051100c03502c6400c20703c20100482d8101040587c4011b210068496420740240003801313140150b000203000c01c10b50180c0420440360342d82c0f209010800184200245821a14040e50b10a014071443c20855107600e05d121090b2190380011501c0b800107007055485002c407445c407064503000100d215002580400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 504843758 1250 504842508 504842519
    0x30316030b04090c180906051f060804110907120515040e0105040b06190923060d050a06050c071a01050103050606040b2a030703180b0a140c0c0607030201050a06 71
    0x10400008661007115590002d14041145d03000d4500c3c0c0e0903a568490f521400c0f000032580c140102885038074007006050b409440c90407a4032811402c0e401020401112000304400900da9801100038203c040310400187e40c6d0303000b400c4409840102d010300e0003034100300510091001c1034850204000f021102400781c4180865200e0032914100d4014007843d6060f00801c0b030900741410b00030107d100c4194242400c54a0304415400d44440050005203c03048803c040c0c1030201000c0e40f00e4000704200c0e020115075905483d8280c0c5c0303698540010304025940e03004a02001c00d854111004540e04c40c445064184002e441610052400d20034640070a04050016100380303000c1c8122000c0e00e4050704540e0800d101648505071205d4030101020310121900000c0e200104c0410261458620035038801c1a1810440030b07007000200e09900105420790701344912014281c00c81522890a582d41c450315440e441c0c1c0080d02481c0158510310240c100c0b10014035002413503810b4000a00c120400c0906218540d66170 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 504845008 1250 504843758 504843761
    0x1a09070e0d020616170711011103090f040e0712050c011806031a040203181b01090509060a0306090804080607021216060e061303120b1804080c030316030b04 69
    0x41661507070104922850200501c1c194002d0320b2100d07104001180028007070380d20403e40100c030b11a0000e0901000c0303240020000b071008441d801e40028a081940c6907100c04007590b032406882262485039500c0000c010a0f91600c3d44036500c1c007110401112107107660307480c09003d02c921501c1d0907100d60140e01c46040055001d03100ca590403140c906490b5002901e0500c0c00c50040204e1209004000c8004440c0b62440d91a800510b0061100d00380300768a002c0c1c22a100e614155076481d100e2500310352045510000e80e002155042102c0b0f040c1c83c9807a0540d19000004c80000e1960030040c405850402e501d010b0284140c06481074403004012145103445098059036540c191700030b1040d01c0c007400c01c07041405a5210a000034401e10880380032400104e03403140f03a4242842152115075580b080001c00060681c04044103d03680010601046040d030150040740c0d250191035114280c1d65299000702d41001003000864454480040c1a01e8803410300e07811075a03201c00140c0181000a0810900c107003185041e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 504846258 1250 504845008 504845027
    0x60b0901051804140a12080a09080301150201090812060307060801180c0e13024513150f091b0f090b04030b071709060f1005041a0907 59
    0x9052142c09840b10200d070420b104020022207140e0050200085030050030048650418481d85191115004820005100c00401003503d800c3c2c1e0f05010000c030105624034100c80c1500c040366a081c1300706600440c181c0c0501054074000340b100c000000c00070340003406d001c00b550040c80220165460185e4032002215419008e0045000c0048194058282c0d02055400003100034994200350842c60060b100280c14040303840407040a443d0009008880e40188006001c000b0700a407106c220a001c14104115001e1740840c04038038000c40f400303040006035031801106424006420014003150040c1840724058103400e10030000c03103240d038500100d09000280030302c01c1c05504103148060b00c0e8103900021610314180305504c100b8020750035008200c0744160300081020314000e40740c204c000d00b03101000030604101400900800003c00381444051100403484070b4002c055280d582e8030545604d0710103285c008295000c1303a4800d140c50200c100219854840601e040002c60b400c0865a491b0b03482524100070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 504847508 1250 504846258 504846269
    0x1b0c0b09181e041a07080a0b04111209013207050901050d1508010e15091501090222080607020105150a050d141906060503070e010b0d0905030d09060b0901 68
    0x141c050012000e03100c0c4103032080d070241c05540003485803404d060b514401d20106942e041c0000c2c1c0c105c07041009082c4035000b40d1280306c400355801c00c0070b004000180791080c0101004010814829400300317200a03025080040d04520741c8a00b600b211804a000c080416200700c0b200c5a0704406034001040c0c00e0140098610311b55040e15a00c1c80d18041044101c0105805210318414499410b40030507a034009220f5000016907143c011b10303001266420f502d04e1010010203c4015920594007281c000f45082c20030380c115041100050f8448071000c0c2c2c9131010203140a29109540d000340000200e0304030004104e40100400e170000c0100e0303100d01c00748407080141c10506541050055500b00020f0518085d50103407503000d110340301c00c1c0d0785e8404106402d10210603103815100b80103075104002d108891040800402c03080f4002c00120f480d0610b0198486014800d0101c403076400b00d60401c0c589131507005504900c1d80002940d9980000001d014014605501c055950a00d0090b03007455504005005c281a2813 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 504848758 1250 504847508 504847531
    0xa180b120901020c07240c1a040f120c0b09160608100306020a030209091005061e070807050a020a1502060601030902060903060108011a060310090e0304030b04030504050909010b0d031b0c0b0918 85
    0xa915100c12302d5021009002120309031500d034034903008203070111100f1070304203d907035200c515100300c1c1e0601c500e00120280a0440c9900581e01d490106400f400000c8102c03041c1e4188040990380d504600d407954103141d84041c000c2c80c000180c0039003c1758103a00502c0c80e0344088a1703c4441da21504082425200039010340c0c3d0304004100940081c402c01c1c09001d0303403544c0350041040d00c0e203111039948840c0c0b41c01000d012a4581d002c12124001c524180074043d000d803035041c20b036200440074914000c2d034612014011320f051607500c40100096403162011110308103000f40450f89107507501c0310f0903030003410518014094209441060380b294584241140e000d071900904040141d8104031851000b0700078000c2400481c07000b004004002502840c15501c00c030b01944840740c8803407034103082c030400c01c0005100d540c1603454030028030000c1d03a464050158050705881e01605805c001801095961603006014103440c94110000a06640c500c1c0100440c07401079805041d500501c60361001c14503015200181d040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 504850008 1250 504848758 504848783
    0xf06030a080315190608161e0c02060a0e0f0f0102100c0c15060302030111070321020d2c0307050703150b0a0801020a180b120901020c07240c 62
    0x79000002a68021860050040240c400303500060001c56070483d28160b140c500e58030800800390000c413007680c4078020022881d40719640c42c000034801d4002d545a050304019040c56a03800c648162018901c1a03400740100d940c031100c5090142a86460484040c420030010035810074038104203403121800981a0020803034031301107031030300c4020304084940b0808000d440c3d58507001284101e56100b1402c0d80d240d42c005001d0303081d40145429583c031004e0910700134030200051400130703a111880881d2004841480103902c01d0090610010340b00d507a84123021503042240290885541c402c1840c220388112542a00e80c0c1d0501a08544034002d08001800e02c1c0c01ca44420000b08440c01c80d40c0c12141081c080000f91016524001001c50366690481c0290b0381d0f0208000c10500d4100c00388440304e03040410000030f01860a100074587d445280150040000700c40c020540544094041c0c4031000e10390020f8910b01e585451000302040b140008000d02c0b92440c0c8031048104d40038540c07080312550040300c0301c185e2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 504851258 1250 504850008 504850013
    0xa0206090f1218030c030a0803040b0c07080f0d14010906050f040c02030f210c030f09070305030a11031312151103060d03230315040204082d03070f0b0f06030a 70
    0x201e0484800d0240c260044c3c03400b4031101c2e50701f07100380042c1622903601140c0f2404c2a0409075205400201110000e020401c48038002c2000f0304255215011002c0f156651074080b10fa070703500a0045c1c400c04041040300307000003044140c05908110181c03001601c00380c40b042e01001c204002d030341d03a1800000160304200040a240b11007180100050800c411607403402c070002d0304030050060303811901841418804414407089459000b00503070040e509100802d01e090458075895103922031090b0103000d001c0300050880b61803c007401521074144006410520f90342d6a0b00f2800c030507040c020000c813552403003180d01007110300700e44c858180c08640001d005415036641c90140402091590420b4042c0701110380406925201c1c0000307102008003254481d61641003002c07800c207001e111042e4881c031840c0103100601c5008400101c42801001850226400030510000c1420035169000516082c1c000003030310900b80702012100820b007520821503a1015614007410008124007aa0001d600d6008401c03075001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 504852508 1250 504851258 504851287
    0x103030e030304080a060501060f0c03080601081003050f0309030111040f14041b0306030c08010207030804170f030a150603090f0201030f0f020406090f06030c2001110a0206090f12 79
    0x94008040c1c01c991606441d079186038601030790f001c0300710340ca59241d00c010700000b41d02402d00d400b4902a070404074000c1d08696005800444010140d50420002720001a04c281000c01618011034005054810700c5200c103000d69100d910090180d4041d6081c10fa4032003034038219004480440e448041e00c03486040c10034904030320100b86940400e500c203854006020000136000ca002e02040102d132000a1114510f00c1c1429003010982d01c10861644103015080109412405440d805980001c4104400c5007442207a403d50186005222012801104002100c5540e0740032181c030040a4400b2442150368a50460944044183c0203120b250580c194400550003a0001e07035040c80c60000c0420410001300c0c03100126001544164005174248004024a61116480c01c1c0070781020326007801030036403030540507260080c03076500701403070740c1d0070401162401e5801c0d8441e500346d500b48044a83d4401060100a41d81c880c00d8030140002e024170388841850200c0002ca2140203400091440e081580341d109100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 504853758 1250 504852508 504852527
    0x3070e0408120708070f02060c0a0c150e031228090201030b0306070c1709030a030f03060801050c03090607020c011b050f03040b030916030224131823010303 69
    0x50740c804060021070070020340c060301d041c8540040d071354091061409442c010711700d420102440301507420000921540880d0b5030300f00d4000704081e09181d0048041898411800f20301500109041c42c50300ba200c40215001100030203499519044110301e03929105445040c8030840c1410807005c1c0040446120116070703035003020606c9401418005071940403c1d020a06000045555000180f0305100400400c50b0064100c8148030200d0016414100d025000ca60703100b96450000c0c082c000b042900c4130319180f02c1d400c15030103050003000a1100d810640d10003451a0030542d00039015025200001e11018400100302e503040760141e562a00301143c0c0c0055080d0300303036801001c1d10705006107280b000b5100c1007007005000a240382010b0b151342c5d143c44144142040035120742450100145901040541d599100b03014000071000020174070320b040000c02002c00d200c0c3c049018144c0705507250000b001c180702500d04c1c9008507071b000107000070b07400f0311b101c1170007480141d0160001201c4a0014404a0b11482622 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 504855008 1250 504853758 504853763
    0x5210604020712020606011124280f060608070e0621011202030c1905041d1902040b010f1b03020a050a050307060b06092d15120601080603070e04 64
    0x40ca88011078442c21080a071810f0a2409a88001c041c0180c9580c041c403c81c0080b50890040c00422100304c01040031881040040340c00120500040340b1280e03180d803a40b8196110406002d8a8041420090405800088901c050031450702d400090300901495815118400310355031200055400c404115803904410555468511801100c541c641145944107020f0111002c0d44941d4015600c1003603c3c0c070184010541c0201039480c1c942c001d840d4180e0345402030300c00032540800e0303460031800310300c10100ea00d452402003072160075174020b0502c0600541d50a003034001e03141480360820901c01500c3c001c0032002008006990000c00341c0340a4400d44921050b075100344103a40310710320581c170350500c0c1c803c8854040c0e44940001138258100545441008010745c0d09480741818020b07200009400c5481c4440020905400c110382c0c5680f8400e1200364180303151004040c175041001c03801110023142c1004001160110640001c204990700640d10240f080e80c4c0200100809400c10f8070700300c01c110003d01304 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 504856115 1107 504855008 504855011
    0x50903040609121b03030f110f030706020f19120c1d190509010f0609080f0d050d0603380c0a1817010605030d05210604 53
    0xc1a084805081c0b0345003000c4042d0500c00c00c01020301140001300651450b0100426402c541151703070252541e0b482e5817900b01544800c580d9600c0e4085e8480c4030b948140140700000b14203800501c0015030a510721818141802c40b000105a00c81d11140c010a20003200900849003170320940c05414054a01071518004003008c811112065400c3c2138003c90340030030815065864000c1001c0245006090b102d059130355a1040088851103018480009a50580014000c00000b44c41d08500144070003402c62440744030029684c50b40950f443d080a66102c42000003c2807a40c201d468145900119003410802084825241d45926032001c0c0140140a01440101d015407010b4490030005800c015001c0010441510030f4581d0641c4041c03400c5e603818016980c9001e064020004448082c0d046805040903800c0549050240c6402440c1e0b82a001180031032040c14810083d42040000c3c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 504676258 504856115 := by
  have h0 := BRFrame.cov_init 504676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 504676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 504676258 ≤ n) (h2 : n < 504856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
