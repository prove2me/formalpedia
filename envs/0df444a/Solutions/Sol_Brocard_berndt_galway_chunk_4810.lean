-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4810
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:48:09.364661+00:00
-- url     : https://prove2.me/submissions/89a6b9fd-ea3a-49a9-998c-8a2784286c24

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 864928057 ≤ n < 865107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 864929307 1250 864928057 864928063
    0x70c030b07141c021308030409020405030f1908030405070b03010b1c1a10090f0801022503050912100e0f011d1504020a0b030a050411090702070e10090e070602 70
    0x2103081c0d000c5550386051141940418011a5040c1d07116001da4001402260302c170080384003000801c41c03007094039261541c8003450b80003034201e40300303281c004d025005c1e010199050101d0152100b030340ca20442003e41c00345484112090b0001002124284035440340410039030f0044d0040d600030a49901595a20f4661a58003d440c10600d030714041c0060801e481041901910245d8a07401d080642d0748110401d4204400c0340d0305130141d0f111815030400420003069019043d00141848005005c4c01c090003030710b600d682010044c2d0310388064001101400498400c1c9004d090141d28001510101c9019008200c41401101e082200005250b80100c0b6910500c08081c09400d02c0c1c5a03a1454032405004804501034035800511020a420b8444400040441d03403180c0300031001d0030070458041e4a92a28003120001800242e9042c0c41c412a000e50903016454000c682c0c42c8030300155805442d83d1407400c07090980700c0700043c0114500c046415400704111602c1e11510078404800801030281c03900c0c113600681 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 864930557 1250 864929307 864929327
    0xa12022b060f0c120218040516080106230304020609030d0806280b0c0f0d020105090c0d1a061f020c09060102010204061b020d12030b040b1e010c050102070c030b07 72
    0x4200790504082c007600c540c1100c50711049130390581016035588034100d00e0031a90300c0c1004a155001d0b10b40303028490f41042190501c070b500c40701d5032a03e40b03003a40c03108410786003400c00219076180144261f01006240070035801075a0400c0c805003c5034101100540001d0401d1180464000081d10301000c0200610703110300402c040d90300f4a0310f0b081031034102101d8445120703c20301495811547c0083c9a1109810802000003c1826038055079004011440000e020305803c1c2c9042102e0321030032041c607419107040c0b92003610300c5074410420025401115802007015800612255110703208441c06914840c4203a500c0c1182e40c410b501a1003035155640c02c001d800303807015241a045a106120a001d6190071822003180a90b00c940350306004000703440015036200740400b00414240c0c802c1145101981c06400580d0008422107080c4800d4030310000b4050000710805801ca4007420130524100c4950113614a42542405000054603000d0b07030307444442d440e8070141e0048601a081000308468242d003c5540f20b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 864931807 1250 864930557 864930581
    0x6020f0309010609020a0212070507170307050105010603020f27060409021c0510060c1b17010b0d08301608100f1715010801020414040203060a12022b06 67
    0x1820042403610096423030b95880800c800b0000c00150351001d00408000640040a81f041002c0d40c0c500c0b6141c1640c2c5907000040200c449600709800403850b1800790080c0c07011884260003c0f410704030175014400d0f045211400c19860400300001c40812070320381034000c0003d00f600240260741c0e40c01b980001c1403490400e80b07014000510f03240034080c02c2d014104081c412204145800146003a0358240381c00c01d200000c9507a1003008403101c00260100e50184030725031100c5805c00802c2840c0b244420b006803c0c95071000105030040402c04a880d030407901c0030f824030420640880f1894400703c01504410311006641100c5101540c0d81110140c9134440080c5030b01c0302d0f0007048190b05602d08005031100c3c481600074850f00c00200424030400540c10469800f40311a2080004200d503035034103169000b58003d01801d41e24011444000315981818000c4074000c0c14040e15030181c42d071900301e10300c501d880b03d541c049034404a43c00e444500c0710282d95480d0501d01c0e0815440925912038a00881201c80001c004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 864933057 1250 864931807 864931811
    0x10c0f020f2a061908010302150a080103080c0a06020705013c11120a05011503061a0c0705031c031d2a0a0e1614180a0306020f0309010609 61
    0x40b40303802c01c0040c000e5200103048001d04900840028540303014480800240501009441c16202d41c0704000324100ca000365400b039940300401e0b12030756030b521410ba00000400d00c008010800140802d00412500502100b942c0803401155600016a8001841586c1c7c81e910380c0002d03403070360101220720410000000f0b4038401c50705001c0b4414030204400d04450044a03914003c400f050b0710790340101c500c600d4000c80c0d0840107142c05d499070030060000780112100481402d01c041c0050f4000c0c400c00060300c1c036041c40804280000c08100c0c0f181c0c0d2010344e101d9501d00402d040011140c4082001c00503409904400c050b0001020b140241100c060211030400a034400000d45000d0b000400c0c411030070500d0821100030880340c0c000d112905000404020b410002e102000038149940c01c40c041d00031091003191844915040303500b02d40d841030303c0e880d12003d1802000840300d03404000303820800640c6c000d01072154050303407a12040c08903000000340340b6038610004108103030b201c4288541c001400084c0343c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 864934307 1250 864933057 864933073
    0x60f0b0111191109010e10060824060721080703090c05040203041b120501150510080a09120c150603030f05071704080313061b03080c0c010c0f020f 65
    0x301540d40c1050942109000d10400c02c44000c1c000303003107601603464038040c12078a11940e55400013880050110740c1240a81c407018404101d092249042c1c4d409108a417910141c00440801601c5407103042c50122039204400700700640004282043c00c0b600395041f5000a481843d03c448050a25a401421481094540f40303903000001d01011880090b990f0948005840381d449140040c107024200d260425400c1154000041850240c814109603902c200000e01c2102e05494100b4150210b81c06465405240148020502c5101c0c91b11950f21030302411300410820301944450450b82620510440003901c01c40d1240140581407001f68074540005004200d40d52440c1c8004241a84d074400f20400c00c03000086071401e0000310100f900e501200040d486949030b079500c000c075070350341d002000181100b050900c0005400d4056601e41414066038503a501c0a280550380c200d43c0034600520105140c20184444d02c1102070920592149d032010361101015088204006440e0071008200d0304065440110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 864935557 1250 864934307 864934337
    0xd0203030112201503011509030210030c02122808073608070303030b09040c0302100306210b0c180d020f090a02030a11030f06010c03021207060f0b01 66
    0x810b025043d0b040445511404028010641144825a82950300600d010302c0c825a400d4050000c40c101c0f080a15078801e8513003c00c0c0c05959090b800d200207035001c0d101030f410b80788042c0240c201c00c03028002d900c1070342e03102100c10995601c00d4000d8000007031485020b50640c61030043c000784500faa007060f0306000c139291504007030040510b00d0083d0340c00010f4000c444d006c084208140303a405400310343ca21480c0c0d4400e4540185c10f540c0c002c5484160006410000070310304e54200402d80500071a080110540d0303850458080c020365140350f0024408042d0389410000b10f44841e40c6908850055101d000b00070403034241440c1072810000b8000f415403150821213100440d140d140c0402c4202001e81d43c9003a000901c0c0002080100198907003900711102104004900ca4181e008600c034480b848002c10040d1005148192140421544c1c0d8420054071800700b25298012812a074003144280b041f00c03014021707081004400d810008c001c94020391035510a2008012034016140030742c03000e04e40750f2901041c4075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 864936807 1250 864935557 864935579
    0x2060a02071e0201020c040e1b010c050a171b0607030b0a06090512010609021324080402060304020301090210022d0703031119080405030d0311181f110d02030301 71
    0x78911030108490b65060007164001d0003107503d00704008208110000f0142045500c1c0c070580c49000c4400341c0d100c41e40200640c04bc114007803883d50010010505445140d85179400507606201c8086c020b202404990001110300540100c0c0d41c40301d10250849040c1400e02070195880303400c686106800110301030110710750200080d02244e0301143d10360714494014034402d0042c2115040f83c40d6441c00024408000036002d4000d00458240c8040503100d0300402c64007009200d948940746c0c00090a50021502526212020f1038005000600016244e260f41c0e0009601030800507800300580c0089120110158078100c0e141c0c40000c05860054419100120603511280140001010322040c04c00414446200300200d04040806507070f108400e51441c100b803402a00603104540c460300c141d80f02540c0c403a2103070040c041704a004094441c108a0000741351040074000e414002e4000310440b8418104c00703d110518a00c00966489401145d98424000d6040845241810040d5402000100020703c000c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 864938057 1250 864936807 864936833
    0x1513020409110f1e0d080c0607090e090106350708010605121c03090305130b030f0c090d140f070b03040204050f01080c061b03030a050708011202010e06090f1207050102060a0207 78
    0x1100c405c6250b5405184c00407031406400e43d45041ca1041d50b04001d80c1a801051007011b507550100c1d900065681d40c22990f00340c61450140745001042081821540b10100b59001e401c458010038008040000f120b01038642022640314001f03da454a4003040036007046c1c0da01d103609510003409805c0d540e48a02c441c7c41c51040030204242016aa094500103040c4944161409484080e424208070307642d4103008600d80c2c105584020410100c640803900e903035595000c4039000c280180c150f81024a0940300c9800304030300700a0002607401402141c3c001d802082c000500546454621281c803802d2500512040b6000103103a01280414400140000c10340003840c0003120750211121540e9100007440480c00d1803060200130068403001c820320084a469800c01c0c5d01c03c50301c981d6101a82d81c1d844440f00c003444405107001c3c1c0800e41d454a4040281003c01c0144115040601101c80446205c0e011400103400b04240142e513402400d030a010640e13040c81000c0e00442c08200950406c405500e41145e40703014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 864939307 1250 864938057 864938059
    0x20a0209040b0601210c02150105010219080d0e010e01150f1205011506200105130303090812010b070b0c03011a09040e011d0715021513020409110f1e 66
    0x1070b000000f4256841a03010100301c41c10f1130405650b40000c594641d0143c803070f09855102600410000d1440280d401c084207040b908141e00401911100c040300c80761420030302c0010b81e20303048104040c0d004840c050107400207070007040303000254029a09540600716075103070b8a400c10100d04854100000c1d000004001c040c2c0f403026002e050f0441e0f05180050040c070001c0d001180c44802045c1c00a02d1a4109143e4403103a044515a154000009100942260811070301302c0c0d0155510307040500864403d900c8140000e02c1101d4851070941c040a0010780b02000b40d0000a50450002d1206c0420881448140c0c024221641d86401c550500352590381c1c0318960544a00342031404101229139a445030454807003060000020090211950100346565052144150701c0d8894104000303416946524403a010000e294080c1c0b8000466809a04503140050050071003400d8041c20800982da4910071840240d1188604041c461030039001d10041012840f4480d1107201a1905840300200c90780607c0108a8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 864940557 1250 864939307 864939323
    0x1b0603071e09050307060e0405101809020f04050c1b0d090302040902041503080426030901181502060f0604050709050609011403092d030d05041509030207060f020a020904 75
    0x4003540460310590243d000941c184200480010042d4101140c00803405040d0b80a1120b951f03846108015006540b048001740284102c4540c000081c5501c080c140c24401031007594604c80510001d82601c2c03007920b0005070403100003410b4000080032240c10040c5960000580b00e003c1040d03030098407410700c503c00a402a030319901c40c0c608550302c0b684031030306a80f0424208610261641400c250a401c0360240840b5100c0800c0181620388440c441400c910300c0c52d01c0107501e02100c0d000115000740310300c81400c1c208515a070000c242c0315a81d00600d0304040c05a402800145000007285002140c0589964080c62509040c4140d10364008641000ea0b203096503c1940d40c0e0b81c06c2e0048070f49044014201044e11000300c1400411180460351100c0e1545009806a4008251200640c445030f20014a00b00d40e00c2040300f07003207000d40c681101d036002d401400c0034107000c2c140c6407021003a2070011108a005800c004824031a0981000304601401d000380300410f40808598003258600c007003d840540080e03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 864941807 1250 864940557 864940607
    0xe0f06010c12181502070503100e0309040b04020f0a1d091e1b0706150e0f0a050601091d060316082a0406060f0807051201030b04050f0d021b060307 65
    0x141408924400804c038602c00e805010400c214000c0d19681b581c05024840d0090160312440144140a5141010804c00156140c84103090820004080c20002d864100b9000c1c40401b040010715030240049200c01d86500d081030310284074203201c0010041060740b180c11000305102c0501221480d244200100c801c0442960301c503000010040e2210203955410460002080d8040200f680c016002034182101403d61b60b90700e0321600745d0224811a10400d144003114006014042d180c0c000640288041c10706882150712184c0110064540190882c6407c03140350034080c0302d040821046071582100d0104600c0e1a0030074410765140c40c05010006018070b20400e80e0000034020541c40b10030241e0081c804c018042e50341801078079600c6455044000300d01310000041d18a0f0103803003224070707081d2030f81c0f4200010f81c00c40e580c401da01c00e00544240d48030310610400d42802d010400c0b00051940c42900246000010343d6104511034210305600360103008240103001e04d55420400c40040500c0000d002d40c6d042d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 864943057 1250 864941807 864941837
    0x10e01060804020f030f070611010b0319240506120a050303060d060612030801060f020a0c1703091806030c0d0503091011100f0509010b010e01050901090503070e0f06010c12 76
    0x1c00c10705506917140c025481c6c0403000c0800000c11800702c40d05610781404000800c0c3c126422520310100483e0503400820a84c0c0754071a02c50481e041c2c5d02c0c8540c0c40000903420603107681d00c141800020341c00403190703505c05001041c98210051301c010805000100091010356840a40368040681118001c881181c808410030580da0480c101a003a02083c9070b04040321814000d1080e40280f14070f10200c0d00110790138034118030102e031000855801004207450fa9107001c410800d5849102402405404144400d10041d41c414002490500b541d000300092420040d00b090b0130111400c1405104114541e00d40c80002c1001c0300707a401c0e00204036403400c84a45070280c203a80c1d154001034005c2e45406580000510a446580310800058030584c081000c0c3e40c4203003041e800ca1360308048590202c0e20f0b82d051807203150300c02d40051201400614080c500079a884001c03d142207115009114124a5202013010b00c8a85121072580a02c1c01d29080c48034480c191599201c056240076507104101052a0301704030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 864944307 1250 864943057 864943069
    0x314070501020304052b2705030d09030201030b0307060816091203020a03020c090105010c2402070305040e060f240f04170715090b13030f1514010e0106080402 70
    0x1a581000080d90740380f405191180d103c601c1d5030b45441085042c81c03200d400c022a5001c000c0601006e0791a400c18503181e82c4410280340014000c0401100c18062000c0303115141807100c0c03030180f9916140c000c121070440c800502504e8032541d03101d0187c0d22401040040a9000f5015500701500c1c03803d80b116220100c401300c0308000c144e001000b02e0003001c000d04040607400622089035078040d40c01e9940c0e9541e0343c003c10030f2510003031003628002030603040300c0e002140b4602c1c2404980c41402003000124007824040d00141d810810003900420004901000400d5040d04083d03030200003225031001001412001448410300242d42540c402c04100000340304540850071a115011103a40b4aa142e55480c0e044484020403009a00d80174001c01c1e100040c90718918282c05400040340d15000005400e1917078801041d040b0704007e01d1048200c071800408155416459015a801041c041c8955802d18404d1170955500b410f016200700e443c80010070581d201842c0d81415924145402202900e84d4000110 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 864945557 1250 864944307 864944317
    0xb030102210109050601020105010b0306040e0c091305070f1a030406021201090c031b1b02062811190f08090405070509101b03211b110c030a0314 64
    0x302000404400114804036107540c904a0720350b00c01c103200742d42d100710049013a00d20a201e00c40500d902031002c120f051405030070508407981e50104864903840140c000580d024400d880840028203044581e6003884020701c0018080c0140d06d4950a090345030081c4880c0c0404a4482050b42d030380b010000c00e003003200310740440e948051110b0b030700181075840d944500c00038003029450f4800300f450a0f00b0810050b00b907003e001000308480d2200d019080c0e11703001034040c601186408a03401041005115255510b40c2c11007100e9483e0441e4440c164521114040c0c10304142c0300e0130314510303070207152021248410224880360943d4410008484143c562529081d5800b445150b550b1050401c0c0401c854540d000000d071500300d508541b04c0400c055200c005031a0000c4100d0350b00346104044060b180400c0c0151603007010040c1c12140f0400e01c00d401c468040c200c2c1c1d4140c40070b001c2e0034421800281482e5103c60300a0210201a0151003502c12007000a13a94031851a0018240701282001c610142c031800c054070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 864946807 1250 864945557 864945577
    0x2060a090b030403050909071b06180f080d11070807031d0303190807030b0a0905040206070b070c020f061801080403200c180106020a0605040f170706050108011b030b030102 76
    0x81e140d040c41d20700601705802605030103024004900000c1c40e1740e0700ca005080c440900410214038181c9050702c1c0c0c9000b801c190344ca0341034003002100d200400941d9480e03003000300e1030080030403036101c0d240ca030840400d40c0c071000348100c2105070074004403011078403040450b0355580d031508140300c15060071078020082d290b51000180d4503001c0400d6600c074220380800304030017510807951030082c0c5940b000c4043d02119018038105401982c1388205100072100703588444e4020f230004004a040104a0391008501d6200321150b2002480164006085041c6000c0c401882070049644034106260003280d4960038000900403410044694040307810b046c014040c00302021401003400100006401c03c541e0f54001c0444554003610035016034422000b0072415480c16a011580070b492002c4194903540003a000142013a1400b0703942d2140b4800041c504010b00d5542c000c1d030b0340240d848840030300b016000c88030146d0100326164100b1050142c0e0400303012101500030514200051114055400310b402401203030018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 864948057 1250 864946807 864946829
    0xc09010803030711030c0c06030a18080a02070e06060a0f0903230c03070b1905130312031b023f030103020a0b16060b06070c0e151c02060a09 62
    0x104240340044002c5100b1441d40e200c200b000301c0145000790f80c030300c10030100d030340e2680084006400d1460114002d40d003120b080100440d9240e00c08401050b90843c0c11000c031610000003403000c007a590141315980041400009000040c980f00300440c0c854030412590404014000701f01aa00364002d00c40400950f81060400c0350494601d10701800e40341180d00c044c8140d03c981c201c1078405107000110035040d1522001c5190403e440b0050542021201c8143c04c000d002050003404541240900c02d02c00031400b034603071009401d4403050042c1c1161002400403030700760003c001803410a6000a08e05103089101500d442040c20a56601700c3e21078118005042125807071940f208450004801443c16240200c596400d456600c0030a1107031442003223135508032401c01488420102e8029031002401403c0504610310303002e91680e131090141c8294122840a0300a50240450031001070101036010400382c401a60342d50f0001c1030101c1c0240e0000f0001e1007028005569180c0610405030400100102012 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 864949307 1250 864948057 864948059
    0x190f030c142a21040503251716171f0b04020c07050a1e0b070218070314181b01020a0b0708060907031116140d08010314030a021507020c0901 62
    0x6580c2e00c0b0001199805401000c01c0080c1d40001c40f020125000c07100c00400405480c4002041503c1c4080044e280c41c004641c0070b003000601000f41284d071200ca140f000080c0000c010313841c5d010380d51412030790024401a13004010203c81d12a00240010310048104100e40b6030a5001710010081c0403c298a40d8000b400441c21102d0b0000009079102906d904607210421075443d080050003003030a85c079008422a110b9282049040340d10b4000380b800500140088d203030000d9198007804034440aa45260000f90b6031103000c1e0720b210039414000c1c2c0000f0b02280081148110907111507980a02141030100d81d42100070580c8640c0c000c100d20003041f41d01049030011443c02d590050942e1800315061400703540000000342d45548644520803c01c15841c100c0c5003041d0f060340200b5489a060740003203d4219490000c3d070301203002040240642c0c0030030754501c1c60b03a604520300b4440128080001c00751942c01409151581c0360042610601d007070894103044441d03640c1010407823500c96440720031038200c102d07100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 864950557 1250 864949307 864949387
    0x206120606130806160c0807060b0102070b0708180103020c030a031a030601180f0204050108010e09010e030d094809020307031b02060903090d030e0402190f030c14 72
    0x240713648695001d424040711640141340036590381c101e9400c0142140c6040007101d000035120340c401c0400c0c44043c411038841e1519507d14003201d500226080c2c03184000410038450000b100740003181e02030400c0c641941041d081748200c0d80d84c2d0003922903070750505440c4c0412040140c254185400581001421104030b0f581d507040415004182c003509441050605108000742d0885000703e404548041c1d40d4076416a10b45021542c41c050044e100d02225500c5050300340b1038074000c0002d050112144040014403910901d00301108400105607603144001e0100d641c079a961120700718050944000d02080c00080c16413202c04040400341d003144000c503102009202d1300b554150700c02010001e01d04030f0320105640c1880107a989620444010000b684100007940d4a03042c185017241010780700782008500302c0c95140000702a038120015803009080c2e0310304803449081d40108a40c0002c50541020007552540b064000c2c00c1c0000e070346803150460780002c0e100f1111100d284807c0a540c3d030030b00e40c0c05070202d224070f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 864951807 1250 864950557 864950563
    0x20913020a0305060112091703090114010f05010905301207060b120c10110106080715020d0f0c0305070c12030c0b0a060806062b0c090c03020702061206061308 70
    0x2540c02030001b690017088010184261081c03038600c0743c02036100d0b588490100a4426190b04c0204407900315500e50f840e03010200181d03100380b400b8040c824640f0060fa8100f000040c00b42025074030161040304110120a035100c21002d28403055001e40100d04245030119460a01d000c2042c25040201f0400082c00700c284110b580c0168084075007191450034407600300d11550303a10110345180603445001d20885018460144034000900f032044000421803031fa56030034040c10807030b20307038080c4650307078500103001c080b240c0c3c1840b44003502c075410b060071481e003803501d4001030840c4c0d1007920086c1406030000740302080c17100c8055020f005188021044c40201801e00e0020680e402d5088111b480081050120b969921140a0f83c000e8070403400c001c04083d41c80400700044504100001890750081444024a88041c4002c0d550598018511103080343c1c80c0c1450501200c501d404140c0800d481809024010f03650101212003a03000c01c4101036103900c0e0040090801e205c0c0218200c5101c62400d00010013030008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 864953057 1250 864951807 864951811
    0xc02031608010f450b1f120809010519030914061e06061207020a12020109110d050c040f090c050f01050f0d0b0d0c033003020913020a0305 61
    0x1c03000074880e00d0092100c03002030703c030301044407080c0302d200780c180388000004481c1c40078003c00c03000ca1140328030304010001283c668402c00240ca00300c2d611010807241c15070b20035414004003038440114260924105a00306600d29180c002010b9180001d8070030f40750382c4200203403842001d6410320700c5195502240d003c1d0003000690300c00c40d029500004106540b0801003100e500c1000c0008103182c603a11a501c800c0c6110380018a01d60f881042032041c0c02801d0a214511441002150000c000181c0c0500740324892010700a0320074210380c14515600c000821055801c214100c09484d8000d00005034685141031100305c0d103c10f0340140c5425081c003865102504000740d064003030380c0700c0700b0790640b00c400344004aa081c989541c040380c001c02c800c05c88011202c0041003c1e08400c20700058181c51440003c5440c142134034152068078100e40306000384132110021082020310340103407145007042c40c16400f141c2c281c4160140140356000c120345555484034110152a162a04401c40d40c40c2c0a010020b0018002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 864954307 1250 864953057 864953069
    0x30118110409092604180f06330c150902090f06240403030c020a080105070e130903200109021302030f09030a090b07031b0605161713030c020316 64
    0x14141c01c803500c0000804007000c2d01564452481c43c05041c946509011a0361440c60720829175035410b00e0a11502600c0388c20080d009115013a00c0300c0d0000e150b504107858560b15104040c031a644640e142e4142c200c0e9800140c903a204120b200301e2418400c1c42c00080c4013811003e074000003050100160329109038403041c41181e040340c4200140c0c403101d465140341800032200010841c4208400c1c4007190054030050482c1c1e200404481a503906c4030182c500307680083d1840390208112100100b0f151410401010070003c0c0007004204051154030b0081c82c6003c07008110315440545080c600501800390480130200341c000d03104080150542d01800000e510460302d4a40700e071844e20214170310b148040200c580900342c640d104040141414443c3c001c90f0721509003101441103e1549002d0180c0313803c17205c80c000740035080000340c3d49021900c1c5000e0218202d1264104a0807086c14a22580883d10a0703401c00504901506058a00e1505036001001c4e050040e6040c8100408845000071400c1900c050b2a5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 864955557 1250 864954307 864954323
    0x1503080c101d06040807050a0c0e060f010c022d0604060e0307050a0303080703020a1701080a0501050c09010507060f020912060103050d05071518060c0c0303050f04020603011811040909 81
    0x2400d0300b0441d500d042c40d000c10a003541100000c1008140301e40007070400b10380594107440700c400d881c0c6d032620096040d81d4400d51240400e02e080184519000a01500554081c00d0040482c0305540c001030f0385560192105c0704404000c15082e12103502031100580c7d02c04040e2281e503589032502000f4069001510f4220712030b2050140104136030401030301c008212640350700e448040751103004095010350040680b0300c08106101c00150a0600e00c0401107008248140142180c0800e5050113429900020f116a180794410840580d203030f40d001c1f040b43d00c2513801c91000108042c0c10400360380a84542c80c0d04036030103910a6014421030a01007440c604030391058044403000c400b000340640d95801900c2014100074080111071308801c8203a041044420030025034080118041d5036220708503070080c91110001543c07120030703804254262181d01d411007024a5070340300c40d140075400100c4601c0140034031402e44049110800c0c0a0300c2941243c20300701c02c002051a2901e841e44c05000044c1880c0c601038800d40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 864956807 1250 864955557 864955571
    0x6032a05040c2a03020c0618030d0509120f1b01021f05010e090c010c0f1103062406070f111516061409060402010819020d0228020a061503080c10 64
    0x20f6401076180746031580c16000391003003103a140b0400c00d00b60840e003c0084680c9425801100c44d98003400300d2646590aa01c0d0b107529690b00e2010b12580ca000b280c00210140e000504812041c03c0000307584c408100b03018034003c0320140e0700004038240155004104015440404450042e08298204078141d400c1c3d08040440c0b80d550b21510703a40c9055901c1810f01141d0310300c400c1d5001c2200801402d030702034001c00c8a00554003008020900d05201299100115403001480c04100342c072400260383c11127000c4458a0a080c3c480c2c0390b0302038041c5500d80085c00c00c21420780d0341c6815110b0700601d80a4280301c0303042d540c4400020301252001070a00e4001c035051461b01d000c06004240c42d1407418020303140c580050000d5511540152542c00740030f800540140c1c2c0c0c8410004010380103000904203078491403c0542c58807101501b0900124050200c554510f040e00c601007a20355000900c034409940210011414061f00729244070003100c6038202034140d0000245d1070518500c0001c100750303180100d10b0100021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 864958057 1250 864956807 864956867
    0x30b0105030403050702130b090a050601020709140c03181219080f0610020c061305040c09030201081f030c0806060306010603060b040608060f0402042706032a05040c 73
    0x1031004440090103c4c80c01d004950250920404c090040d41c19504c000841074158400100c001800b04d1303190320308584517403c108045d40d050024400600c020340c07080c84891002150b103000781a00a11010841801000140001c07800c0c2201030290604074050b2204440e0070a01201554001410900c420b00c2e2900c01861040c41642c100348100300010401c812511010200203c00c0404100002180301d0321030100c0301c540e03a09008003400311100344000e801c14030303000c10300007950001c0740602e05004503074808101503600070306c42e1a40145c0300c007030910b206030b410324000100314015000540b80705224071000c1317044200051114007484044048640396aaa2103046050711454040c079104520140320421015015503000768000400605040300b101e04c100208089811942c080b1001e80c840c200e44c4c9014602c0c55504051803070800700107100c2c4505589510591a243c18184d01c00342204480d40203d1b41300c9850700c42d000c0c080c002c00034011401040001800c0106010a21500741c0d481d00b036070001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 864959307 1250 864958057 864958067
    0x2a0f09060c03120b06180405060303090d0803040512030109020408060906160e01170903041d0f160e031e0708031e07230703060f2f0705010f0507030b01 67
    0x12240d03590740301000d032145503030100c903d01034541c1c8001c0041d803102c100350f200ba45d0f4400a09200c0c1e83e290398900c010410f80c1c003008140c03140680000d000380c004000f000e08645403000006d44454202c0140c5a507500c41d0300d40b061900309440b442c9006c421001c8000f081240c0580c0040c0b040302c500d2003c41c0d0243d104d0340041d07500c2d40c4d002d880141105a420000204890089031600e420001c14100703c0130f4801c0781494240c20314070032210101c2c141c0001905202800f40192000240c1d1180c0c1c910148a1510084607049540c0c0a4810f07101030b908030340d99050305032203440c030800c50403800390544201c4601c0e032003192081a10304d10421254020f04202003002d0a00105072044200000420740842400c003490f84141c0d40b055000342c40c68030540c0b2490036982005080e401a02500000a080580c030f14140582100d600d00f1056085a040c00c0754a0320900700c00080000e031030007420f9907202032440710144001600c81e81c10000d003d5401c0081454240702a40c0c00030744102c1a5480a01038150350700011a6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 864960557 1250 864959307 864959309
    0xb061f0c0b0a0b041b1710180b031c030b0f03100f060f030c03030f030b0f10020f011d0d091d09070b0304080a030f05091f2a0f09 57
    0x4040340360120200e8019a0002c1e04072103903642c000f640d408000041000c1d5000d0403000d808010311900e051030940da12000354034045556400d12142403c041f400842256a28807841c0204400f034104521000340582c4405042c034401070440b403d04550711903000102c48503c0c405400309103060422002401d001c08990b98002d8000c024090b090002d1202c100281401009207600564a8401013440c6040600460103140500100c0d0f01071495481c005000d81c8420300c1080405081005448113511201e46c1e46000c1003045912095503004c0120492030002d007160416115801d045600d41051110104c80c0c00c070740444415607000e450001d00654103001140708180c1c4043c0b4096524902417040e48007d900410500140c0b44030641c0c400c0e11680b240c106031004d4500900c00101c05610b00e4062050050ba40c12140c0203020740e03e8031074050384d22606440d14140d9201c100c61043e020b880d026901144103000d285810f02408004c00d0b003003c1c540a4540701504c0800c001c25a0061000c0c0107401100c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 864961807 1250 864960557 864960619
    0x221070f1b110901030312180210080426091c032003131d070e0307060f0c050102030a06031a090606010c0609150e1e0601051c0f0b06 59
    0xd59a00450100000350707041c607106440c010345a00c441c12107a0356000119008601036990040700d211444241402c88401c90300c0b04d00c041102d0307160380c401078076505020407102a450401c0442030b81c83c3d092540304000d118000b482019820203459441b503020001070110030b142901c45020420018096441c039405040010300414000789045a04030412169000c1c03140e00c1d07174207507424440c0e8410180050305451b00004808000100c14030003108000c0e4185ea4401c2552800c03981103500709001c20386400c0030340241000c000444440c1e503603081c000c0701002c8840354002d008558a10744164140010031140c0812550040918000d008540d0080c00840c090010100502199244e090040d1103d400c400000c4408035107501015000c240361614850524000c9000410b5280010498504050800c01c41941440c01d45800702d044060001d11141511400c0c0c8654240c2c3c19400c0c000300c0040c034444e400800f8200701040c00410082c90000302d500500003510031400c100c2c9141400c3c1c0011340c10340001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 864963057 1250 864961807 864961817
    0x291c0f060f0b071707080705030406030e030901140a020309121005061e01050d0f0f09020a09020a02120f0906070f02010e0f1804020118030b060a0801021c0e100221070f 74
    0x8080390200301c030038000d44000750913580340800c155100391130703a000000c2c02d980d00d0f0408501005800e415003d011030803041e0b40b02662620007517070000b0700350800c0d00b1904120041e001c60f040c90450300800445120980c010084042407035000c3c107071952028030a103101c454074105000301d07105040900309002080e203800042e980b06204031004481d0303904611041c41d00c041d101d00c00c03071406115600c25a11090400c90001c00d100c0e91500600681040f59400845e03418810030910740201c1d800b080d1422803001805482d43c0e51811207083d01c100e030103184203166004200013109005c00071252400a070552007031302c0d1000641401d400b0814071410184240b50009094600103107a4000c140001e548284141029070302c489005203090464004d942040b40c650300b00c8424048140790012032100141038180095180c08198181c4802101a00c04400140780c2c40d0380440e0020041804a28800441c0900c115194445c0c03403001203008001c2c0c0403103c8250b0320b440203e9203d52040600800400094a030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 864964307 1250 864963057 864963067
    0x111131d01031a040501090f1b1403100b0f040c050a110d1b2102101a010c1e05060c0306010e120718020c070801140a06291c0f060f0b 59
    0x1940c200070b030f006004940c80e558514203e0001800030f0080c80309a801000c032a07022803002482c206030710410790045050614040d16150407980c0010f041d080542c02d5200c0420b000c0b1645000c101d500310303462520b551050401400600b000c1d8064003421283c20140c0d1034882d0303284182c1c00076841d030510740020000924140c0581280400c000d5204e207510b8442c6009840b5001d801c0441030103902c16069082c0140c1040d45c03021182c4200f030103101808451991541003025162001901052a10700010811490303401c03c403000e07000001000c28070640107001d540c0c01e40f9000400501540c4100c600d14080f8140040f59499030900d0319119181441c44001410140e0408100d00703000300c2454040906c0c1a0208584c0020190a01c20b4000501d400710000c40e030395418114200349008010700100d0400e01d40a010004540804021500d10110104603220820000d10f006010b204030b03c80070003c850b00c008034400710300c61540646d1140c031440c90100070103500c0381c40111411102c2c0c81200344508042c80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 864965557 1250 864964307 864964343
    0xe0102160807031803330c020105060f0108100603090f05101b05130b1303080f0403030801050d0f0201030f0f0504210219171e030f06300111131d0103 66
    0x50114580e844603c1c99074401c801d01b070103000940c0c0c912101040181d44480070b01200b810309401803810340b1402d0a2002c1c40c0c2c0b0701104681c49203001d6101714010180c940101e6410b11403c2610b2805058000090726818203050210802410f214002e0140f0f05a04007070381040340d84680152043c0040010624a110b4602044a441a00700e024200742e6080d5400c8008009201d5130020a141350112440a07200c0e03246080251014505a10040c02400c0c80c0d582c1c000000c458216094405030f09080002e9a60315585801c4000c0407511304c10021149040180424412080f101d03200300d000e42c4070f4014010f0a002e4003262146401070600d40c0b004010111440001c070380300c0c0800c12a446100a00d81014403038030305454015444400c82000704d5001090040e200c42c0e01007015800007080e10782104004440300f0f4610070301082511400c1d9040c610b007041c13099640a400420710701911510300c0342c0741c9500d1751003031a00c2400343c81020490f0014181e090b41020034074003d0345c100c0b41c020a0250400001030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 864966807 1250 864965557 864965603
    0x2505150a020c10230f120a0c030e06040305130b04031a150a0e1f0e070f020d0f030207052a030c030712030c11040507031d060105090a0e0102160807031803 68
    0x106000c142d5200500182c207085e810b02001c1d0140b41d0110300b419080d030900d0103d42003283c003d40d80c550205800c105207948000c0c40081c0d0785410603814500300341d6565201c1083e1043e8181608071221900b80040c0000a00040011401500a14216480103a124005140500907144641c0b0790848500c48040194080b40c0d404660300c01f644072141f940c80401400403d64088050f00101c8040c1001340501c8415a8002100202c02015000805003984244405040480d441240300109500028100e00b00b09052110303220080801c40e80c986000310810a54904540c0c40d64154001c4c4a114100e10452400180c84003c0303558020b421105d10107a42c0341111240c009240c291045030004a514489480b6480f440f441144030340c0c1d0000b080e0110109901d0030350b500d601100e46542c070040050089130f42d4095050b4016440c0d1400143d5215a02030041c06800707056207480c00c501a01c0007072018020508004c0030458840e98603001d410340d45101c0e00410a56034040604114a152291200c0030501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 864968057 1250 864966807 864966857
    0x25050d020303090306090f0f032505010b040509013e0702010c0b07020607030c0203030f0105040f0f110904050c04140d02011b0f0b07050702032505150a020c10 70
    0x1d02941c2c50803200c040132918000091711501c145074003110040f42041c00a005c54441d01c640c00c409145013000242060303d41e141030244240043d503100c0b10300300810200350b01c00c050700c40001c0d100b4003551038070504050003020821608040a8030b01e1003080bd607140c900400c0c0310003d042c034011440c807510b054101111b5030440141281480000c0d400040404c856160007441040c07581d0003040d16280100b401030540f080600c0f400d041d54014814030030812414042c650550314207a90028008403481e90f1a4007410f012841117160b80d18105461b680044010000d00710031409450910450b101c0e0250451a480343d44103000c616101e4860045462601e8048403a01070300500d05804200341d8030030b5040006540403001c031026000240c04004100c040c03d0025070207641810554140315003600480d446800d80f0b51046108003402c3e40c0c00d980715494005050203840c000c2c0c680c40403034501c2d440c040301c1d9a001000309000745c4140011100c1c0c602d0032200b08200d100081e81da40c5141403d800003c00e0621003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 864969307 1250 864968057 864968059
    0x807061707050708040e3102010f0201061805060420030c09060417030c100e0c0105030a1d030d0e0d301a0f0f01092d09060825050d02 59
    0x2c10800c00001c14000320103040a05040080e00080f41840751070403204080c1c2c69062100c0c4d61281001080c940d62241c1114507080d028204581803610b02c0c04101d0040040d9040034102c103506030742c80741210300c09030702541c49030406403820000360802c44d844400903034680002c8050600108000394854492101410312100c0190580d42004d445208809840091124404c41944040382500031f6060401619565a01444007041400000f280c4070b034444445412160602c40000302080d60b465481d8412080808660628140c000428906039102d50011421012903801c01588203070707608000c0755140c4403a081d81c5412a28010f100441860203040400d40003003007100321a95422803a480c000c08400b8005c000400d128070805104100302c1c1c40c0307036043c12405080200c4001c40d05ea42c01004060544810300c582d0300ca0000a8103006440e20300e58403802d0000c40910ba130005048e80c44e504200c0a0b108043c003a52403d0381034540410243d461502c000c0b8400141c00707006c1010341000703110b000c1d0140c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 864970557 1250 864969307 864969317
    0x91c0f050913020a1b020109090c2006040b0c131208070b010b0c0f030405130e07030c0e0709050301090507060e033408030c0d080c0c0115050a0807061707 68
    0x14038080010b0b20462846124060356800107610303002c0c654011034101104510002c046500806a00000c0451119004207109141e540c2140c2c80200d00861400c840b012003c0401242c0007480e0141079155101a80c048950301d042d20b020426001090b030540342e4602d803500440350554600302110340e9868803200186c80f8007004001c44404108a05c00c41c5010341031a03141d4599400c07503621068584511140003006a4005010511480c0e0711040d900304d812105480c0400d5107000c0410310350905040380d00003407604008520000708114142c80c1c541c421581c5844001080c0e80d500305050a8692001c4000e103103800c03991040c404c40e402105a2a00800050304642c40c50305483c0e070b08039160085c0019644080c2c00c0000401041c0e040c42c00ba040541750300f0010318140042c4030411765680e47e906440c041408100d400091080040710151081d01e1503c2001344014001286413103505e50b81d6000d002d0003000d0108020a49540000e00b80301103900325640d000075404500c140b400240405003007902041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 864971807 1250 864970557 864970567
    0xf0c180f06120f061f120609060e03070b1e01030201050313170703050d060501050a080c090f1806030714030d0809070807030311010b0a0b0904021b0f01090308091c0f05 74
    0x207a410008002044411801403180f401c041210901e58044042d5070510f44600400a201001086030b18400c2c0d0381e4032400101d004c04849c0b0300304002e440303c3d8200c00f042c0d01c4042414001c0c070101900301806083c2080300145014000c0181111880d402d00000c0e002c94410404510807148040c034480364039000307100070892072405441d03607a800d0340710401c03d500046000c81d8030190b9a410f4420000280002d00f0318a2030034804100203010810300030240507083c40c5c04542012141c035081d68152054100811200c80c1d20b64114a40300d801c032096400c10302a10076400c01207041c42c442100d03020f0300c2d0070041c010002c1c3d1141003001c65042900801880e52402421000611480204030b9500613602c2916442461100300315280d007182d0348404070302c0c46500003180402c00b1081c0e074006c80d02c084005940250b0740718548a0200380342400704020601d941710309000c0c07060545066100c100602e03c40d58a4400360b860320004195501c0d001541304034401e40311903404075420f0048054880d02c0d411414114242 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 864973057 1250 864971807 864971839
    0x12050f0105090304080105090c0f100203160b011805070806060a021212160c0809060c03090d0c1a0306090a0b0a0b040b0a090b0703020604020f0d0b090f0c180f06 71
    0x940c1d81580c90000581c0b0118040c40814030a019644c0c0c031441100040041001c4240018898424465045c0c0583c03540f01c2800c1b0018401d00c00c0710707035001031800c411410906518115005441c00d20807400e046001000c64030084100b406064020100c540d03840d030142e1903010402c03c05a100003e102c5c294443e280780c40140726103850151000c0014003041031214909204400e0224601c940d1200070403407000b10340c2000907400740c151001c0034001d4030b80c0354455540301c080501d9031141c04103079548050f00d8011241003000048540066505041d0420222000105103003081c1c0400d03164154440040c00000710040000d0344400f0200710b004110b456032903600c0d00000d08035400341e00070200b802d100003144a507060f0083da41038000d040800e0850310f070220a0320000e46903c0e002d40000d12070406221015103e82d106400740803296080b200b201b940b4200940642e9403090182c1102a20b80203c0d181420390f40740c03400001031401c0458100341240ea540354050030300040c00525081e40301700618909084 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 864974307 1250 864973057 864973061
    0x20d09050604060c090f061202040e16020d031104030f050102090607120807080108060f09010e120403020f040b0307170118240c0e0904060e03030c1b030304020a12050f01 75
    0x50103005402411050619007841e0003a50351404050302030100358541041810070043c2e940003160740d94034140d00040d00513020b42e4082e20840e8414540e565034a024001e21191a222480700c060140d0216940030045c2c401c1a030a5800c042ca9402028405200c108040f956180c444a00c2c1841b80d0001860700e4110700010b025500445000d0300d8103044e074131003212002e82003050380d40c02902c2c5081480080d85882d80c6c0c260b440800030425081c0c1c4034480041601540250021030708403c029050300d074038000307a10021505400a11042c0d201e1005440c00042c81d09017480f808000000c050060660541809941d0300b4100820a90314100e66aa00d020329400040c40b031400301884c81040004c208820002d00e0412021000111280d824034000c061002607801c0100c001240c1030640b4081425616428034100424a40303540b60103034000002044035219610005055071000010183c0b9003103a050070069483c0400c0340c00941140c110a024001c8032441c0204d8801c840c030580c115400450382c9140e080c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 864975557 1250 864974307 864974321
    0x1806050106110610030f110a15170f1012032102090102060a0b100c050a05060405010519090308060d0204020c0a03030b01020f1b010516121206080a11060904020d 71
    0x1c000780207040020881d02c001e00c08260488103108500030024110b4440700300c004c5084000a200c0c06031740e0350780300040d02c0e15000e560081810310403e962010a002000e4107825090024003400070141001803880301c00b9030002401a9502340100350080d05107854107080d100b00c42d006800b40010f46205400d0440229a8041820b8800328096110750441c2d0019141c82c0028002700c0300c586c1004804001a02d851012040710070040c81c0103203402510342002414402007240107003c42c02003a0420081c424150003480c0030780a140c0c0c0d10a110800b008031081268902031009000824280c0032034414034040c1c908180c0240002c2c401450108140111803400c03d060038100c001c241c480c503810059607014404507502c0d8a02c040504800c15860030094126202a05000d05201000c5a0300d4421400c0e005030365820340c0c0c00090fa40b4070036417410000d00706d44421091000381c5401e01002050881d404034050200fa81e00c1a610b01215011804000c91500944941a0065424071021301001d6180c0a008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 864976807 1250 864975557 864975569
    0xc0f08130905071d03010911060306061204080c060f0106121109120703020415051507030507020d0b150d0503180112092603070804060504060603020d0503090103060609050f0418060501 81
    0x440c1c00004001c8041c203282d0404c0c04c0c2c0320742d24018070f82c030109810300e0210b1440704003251800e0360795890390f002400b24001e00c0749040b01c0c80040c2007003000b0001004024890004803601b12076940c0d03552081442059401d01400000600e0f201745a002c01005402907400704407942d1200e82041001d5000c5800514003040f02000c0da80710071030030000c2d07003030620807103018190b0701c1c5030a10840c0c1088003085003a40503403c800d840d2a400a145807e16100f03406452940354001c0036017400d51014104414103520a9900501c4000245d0309c606030b91603d6018010b400d5406409542001c041c1d545070b228040750128801c1c18044ea14075030500000300d920030781118070301c5048403850480d40700001d4034081b42801c192505c41201001400016500a0012640182d200d074000c6415a070314503054020700042c1c3d0000b500807014401620403c4804005060540400e0340c1c10044640c1c0c4100072030300c024052081e280c01c09129030802d4032a0406410043c00d402040c0341c43c4040041d01d94841007200c200364003117 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 864978057 1250 864976807 864976817
    0x101214160f050313140709020c150c19031e0e07140402130e0703020903030d09020f0103091226090f0d02061b0315030f1b010c0f0813090507 62
    0x41100d003508200e40190390891441c146040d8a8035007091444840b900b03901500340f401031700d03070151182c40c01c10199000c0d000b8000d0554a4400381303030a0035079824030807071250024001032000599082c069816a000e02070341c0418500c1005110a042e001800142d60414001702c031545041000292400390116403007422001705440761070090b004d01004240f54a140c4600d0042104400c1351300c000d20600c050300c914a200d8030240d181d801d000e42c0248540d01069400d8013010030050041c070341c181e10103903c0078000daa0380c1051413040b000440031903200650080901000c828154040c911070310202000780d04240c00c2002c00f900da0b107410b000385641241e25207595482542c0980b11003a090103030b1183c02c03113940000d2085040c42c5080e5401e004403412100d520450200008400003824801501e00d503901400352910101e4003070364207403600201e04010a20012865140320b455116901841600d50080701e6400d10804c00e5441055650000840001070301e11440c0c00301d10740a9901c600c1e40200b00f6600d0b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 864979307 1250 864978057 864978091
    0xf1608030a0c020a051e030d0c180e0609240409050601030203071505040b09060d0c09060801140d0206090109050913031404080a060b130906020d0b03010209101214 72
    0x24240540d00001555003c41d04a190b03000001703140007620413440c4800c81240041c1003000e888162943c00b481c120406450b04028880041d1500000c0d8410301083c60a02c1c50745903515503240004202e1b0a8900780e400c0b00180e800a030020356481150150f00d84600b030304080080400002400380ca540c0e010036282500100c00402c11482c040000e50020460884880309a01d8040b60244c2180034030320800902c2031001480c4040f607a100000c031521020078410402c4000440b160040c840307081c50090700041040400080750034404079810995a000003009000c50110365404c0c000d03180c0000400070305112045802207029640d400700c80744540505e801440340c141c01c1d81002000e410745e01c040100940c0b000c00c42480782c40400304010310b42c44c1d008140400c1c496000e03008030b00010041c640e030b0501986805a14010480150000e01e85920010424044146164109400c0303208403030165600501d10301d41d20703035054000c811001000507142400102451803078120141600f007110b16040078400d1180d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 864980557 1250 864979307 864979321
    0x9060b0a180f0e090d1814030a0614060f01020316021519020a03180f0b03130c090e150601080117010b0310050402040f060608010b07150608030a020f01090213020f160803 75
    0x4540c5c0c40c00d00d09460102c00c0c006030000801c0901009015521410700e21094400ca85c0c0c9042010040c01503224030704002031001201811150783c01500d11034818103004419080640c070003c1a200c480381130503101d2100003025030801ca002040d104681c402170703100707001100405000030300c60394940d20680c000c2d003a00405840c0041179040010402c09041070491400d00a105400c4000020f40d0492021182d0307a44880c0c88600005040c0e840c01094046071202c0413548600907049513441624480c22a071000500f503080b10131000c412503120740001c0100c80104040c52001c039200428009000000940a40c01000b19040900c4039501e140166292020f20045041034480c0c000d10003002c65003007065038108180180030f51018450b1301c00c407450116504050080c200c42c0003880b2001c2c0710042010b10343e10b80d003a0340c40b03400a03d0f03100007600945510240e421810301407001410760007440800203200c9401490001d40020503190303480b030410f21036520101d0302048a200c069002d6041143c0303d2034401d07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 864981807 1250 864980557 864980563
    0x30503010519030506060603130b01080f0d0201020f03070c0317090a03090e161107210516080705041a1003090c0801060509060405090a02060a030f0609060b0a180f0e09 74
    0x110ba01c014418484010000f2034004501d454001d101200c81951b80d4886040602d882c1c100202c018010f1141e000c0009400c502c00198503038424406000c1c1c80c00c2c013520f414281d08070702030340712200b88200c4100001406184a0041c00c1d40c194801d040c15040104020034000419100312183c3e6195440140c80d0030074181c006c01341d40020b010381c000c079803001d240c2210f0340c6a40d00300075a44c10003404804d8040c81c83d030500a010703d001801d81d4600a4192040c600030007100300206030030917213150280c00000890802c001540c0d806650844004140300c034074003000d100045c0140300d400c4126500203c440c4a00380d0310b106036000c45080694011425500e00d0909210441156100d61042d80c5003050411094441550040d4400c00440d00007070142d441010050400040c0d02c002940648005503140c401034244c0c4c07010046c480304500800c18142c407813401c4021a200b074092103140e600c040c010f08109620440f5110380320100d01100d000c0b00d69407074404003c1c50b1101e40080321301800900402c49508010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 864983057 1250 864981807 864981829
    0x7170408060a1b1d0618090c040609030809150d09021f0c020405060f100513060f0503040209191e050a060303081306090b150913020a090b010909090305030105 70
    0x199408010802c40c6000c01c10000203c140310405004030524100d110040301821089000c00142c44140d8440341022403c40412150002500c950011030126010f816060192405e6644944984211704e0460f103030301a4681000e44515031020001342c0700e09402c0242000390040307060910010a2400c2d00d88100f01c143d40c20b51082c20100780380480c0031084c080d4000034640b480791701540c0008950b2150740c04600c41200c80441e8940100010b0700000d007035076000008081c66880d00c1542d41501b612900112110601e131085800001c00c144013180252400c40700190b00003004140c03c011244000c80044141c42c82803c1072aa0140d40b000c8010b8151018014a507200c0302c0d0780c20411070182540c0d0090605030003c0c00a0740e210030509080010400142d00c02c0343e659800800403019850102440a0008202103032a8040c0303004d03030081a115003d075061401c0041d8000d1000204d541803004550082054040290421881c0580002c100c0d07401e11400c04280c0c001da441c00c3ea60341c188400e004480c426 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 864984307 1250 864983057 864983071
    0x5250f050c01022808070c06020703170702010e090c121906081f1e05101a030402102a080a03060f030c0311041e062103080a09080717040806 62
    0x71131003041c008900f654540003a4640c801e07060380504100c0e0308080f143c6015807507005000002468000c1456600042c4075002c40c1d1107500500005441007400c0315a0b4040c1d402c000b8003140c01148a0fa85501e003400003a80d02120b4110182c1c00c144d000303542190410002d41d401d801c505002495024900c02600400c0060485040100082010402c050403a029144180c08625641d0003083d04004c0703111340704054000070f00e082030010741000f81040e2049000c0341701e50341043c881050b03030340701100c8048140c0b449140c000304085042050302e00b065408054072403e452310311084101c580ca2180720441c101000c94000d08078561034045030794000d0115201900b10701e02d40d12141408100246001c0c684100fa268001003001082c40c40b03c0c0801c0c09010708890031803d081f4103203428004a04980d10160449611081c14520861440148040404221000740015a1080004003052603d82054007100e1080b02c0c0503180c083c15031551540010541150740c1840c0d0002410842154100603880c1c021032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 864985557 1250 864984307 864984313
    0x20f1c02040c0207031a1b180f01030e1011042d08010624030609020333010c0602070c090c0f021203280e0d0e0310051605250f050c0102 60
    0x20854032010400c0469105010110400d46c000030318a801e1661015041c10690b8809078684556400d10407011031084011400f5920078140c0b01410f611a014200a82a84002904031007000c21300281c0980035021100d151554201b20010310280d07580401c01314802d90f6100751b55006000c9080c000e07110401d9200a035203070306100d42400100c0f00442181d00300101c1c42580d298485c050b900641c05480c0b42d61000c40307051700c040100982801846009000040c43d1031845103c18514060204181109507201e40054150190480050047c0e401000310b5409034600701142680c80f06503805540d0510000400900001005000b45404201c0300740fa0010801d20b4a0075071400c1c1c0700c61521400443e0071000080c04848030041180d80541c084000c50b203540041e945600011640a01034002196810340603114007071048100040c03500c1114010b04403155650312045100804a40940003c0110303080c882210b200e88001500c09900d00d15018441c00c54688040f441c0d04200341230002c00d6800d42c1c1990 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 864986807 1250 864985557 864985559
    0x803040b09061305041103070201050a0c05040b0d06030c0b0c0601210204181a01140d0507090203040305040e0a05100509130b090a0b0a050609010f06050a0507020f1c02040c0207 78
    0x902800c2650204142620007a403618036003046280c080c2441c1d8401600186081910042d020b80180107500c04c1c29103400900c4030b40c80d040300c08812200c26241c030000083c814030040c09004400307801003100b10b10748640070480c070791280c0b50300e40c2a0f046540718140c00c0c01d00060100c45c00c070301030204600402e54403400350503404a60281c00000c00c001e400c001d1290b60b41e0041041d1001d01d10441c46921078100907144409540c2e80340500b00d07154203000d648215031031a60261018500982c80107040c0381d005d0040c08275145400100e03c0650009402182071100034000800c451807062003051003164802e001144506003400d0f071603014000c03a0480c9001c1d4941008010b0101001300042c407025034403440c010b84641d1000c21590412101d07901c010620480d050501070700804941180e405034000f01c80d10b00c40340e42d8450310039883c2c4ca0548542004600301f40a00c00c549030166000d0055140094541e50720041d0b04030000f00c00c1e01c1d5003038004101c0c114185240081d070030280310b04407429a140c0018000c0c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 864988057 1250 864986807 864986819
    0x18020a0e091506030414010e0c03100e10050405070506030411090c0702010815012f07173712020105181b03010905242d0714041e080304 60
    0x111810305401040f0000200d000c0000320303041c1c0c008120038071000300200a4490342407601c1e8a890810540309110b402c0c00444155030078420b0401d9244190000c1c964104010f000302c000d06001041641d00b0301400390001916110400190f114500c160f50050914185000300108402d0151a0b410600f2050240ca070050b600046000d4001a040c00c0403d6460440300040340e000c61444620040e2514000c480d09887c00c0313010107540c01010820548001e66110b9810008440c2c4184d01d20a0603844003050540c10703420101079251815458180d07540d0031620a5502c031120321004070440e200004514180d800541c20b110300380e0440301161610768042420940c0c15640c0020b08400000007504020100447c0e800754000101c20ba848010b5440744046581c42485e01c8c0002502c1c045031000b02400240985840d12a00b2044059609000e107204142401c0c00c1c03100f500203041c4810b00c42c2c084030384074000f0a4680540300402c1e00b0f0000b10200c46000c8203140720b070805540300c1801903009100600c03003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 864989307 1250 864988057 864988081
    0x206010e01081903110c030d0e030f012d0e070e1f14040c050717120c07031b050c0a140a050a030c15180807060e03030903060708070201020418020a0e09 67
    0x10700d80600c5d080854203000e94502d0300740025240c1c0e003680362180b206402062500440c0c440c0c200103003201941c1060208802c00c9003030321110542490116030007291041c880c03a6450000c810001d00d5000014031440310b014403440c02c085a04400c41544051003001022001300103403010741982c05101c124800e04c0c01c92401d80c072801100641d4425034541201c070380003030300c07800940c0c01045d0401c0c81503080c0c80c42082800210740c070211260307a111444000240000301081c00300c0341d040b0f42c1580c89040c5001000c004600300d020000c411a0940500d00d01c0ca401030b038a840e003d00180c2008840b007201003550004001004100d68009030184243e024104041407618078508111415a4104034000f500c00350300701c901a8100304079800020703403c0c4000c40c00c2800001c8040640e020398460500c1e035141c0703038100340d44c03801751419442e819407220b400105041d105110f890782040050001500340780d01d40a008400f568203101d19901c0c0d83e4082158810755502c0380c0c906047c0c480988280c0c02a041038445240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 864990557 1250 864989307 864989353
    0x50d0201140f09060f07020108131505100e0a06051e090c09030313090f1112040210031e0905060a09030f0302180a0803070b01050a050f09090f07060206010e0108 71
    0x1114000102e8401a510b01400884142181c0140a241c0e54a1800e440c800f03181c221607001d0f400140105c00042d03000a13168034001d442030700b04a0071694140103c1d4400d0282100404030080500030380b100051021403030310781c280603080c40c980104945040c1010f00c54419180242240784014800c4c0c03581c900d44903a9105a04030a4084040d940c03a03c5074400300e482d611a040402d009400c0702800080c07855481d6112080c566a00942071080031544041054140248210100051034050100d0014605001c890068942c3c0341404500c01c0c000e030b402e40700b221225411000c0c1d05a2520040070410105122aa81c85000c14030100020052524024040421007921400341540010100d101041d0600b4000d04107a00502d025070140d281e285c030b2038480c0c1210078100c2c0c201c0103210020406180c0305c100c11064500150401e010001d1000030006d83c06000360040071540103840d860395640e4001d01120b000b61106800400390341d458182c0c601000d01c0142d108900ea42c100384100c4c1e0254003d055004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 864991807 1250 864990557 864990587
    0x302150c1e270301180b0103050106050a0510080712150501090504020c2d0304060f0807030e0c040b0f060a0c170301060207032907080a0e071404020f0d05010b030a06050d0201 77
    0x449880b0b03010086401040c0081d94100120654248801080702e806078560680b845040244122951042070000103d40c902655920013075824810b21912f20407003809070721045e1403401c400801015003409003141c0351103048001d04400000c0030b11941d42c012450500924098030210318200001e9129a1544c44410241e2442c0c062030404c00108083c44c4070f44258407100710f098036911651060b0141c0382c407103e0720303145000c1507012001448090181c895500c20403c950050208114445c04000c001c0620200807540541c1041e00c41c00c0d1038540314060069a0000d0b2038030050300b01e99041150300c2024807043e003c002c103410801405807aa01140c000200e0354040c061030892070b1901d044000e510040754010340c1c000001c100704412507901203a4130b8000e840002040100140e481c07501601da400c0303400380d852154883c003540c060508003a030003410b100705804611400d110f201c20322030080c2c1e8020f0f40140b03e801804010302c0980705041c861200280400c13a00030320582da41c3d03030001e011000e8540e506 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 864993057 1250 864991807 864991867
    0x513061706120f010e06060109060e010215060a030602120a060512070b073e0126070c020604060806040b040c0c02010c06060f080a0c0f0e040f0302150c1e 68
    0x95a6280c2e401c01c5000f50b0410808024001000210034059840e0b00488005000801e00200012164090786140425080c1a406041aa100c40d0a5151030900c0a080305410440b500d5000012607a40c1c03010705420307082e0440105140c00c0444642c001c0c1c41c1b450304118428090206800d85019002981c2011240722030320080c2c0782e00c040d003030458600380c0045000811001094101407900305200c40c00d044560080d02c50792031404920011140d03865421344520107070fa6600c810305812038408c07620300d5001c2614904400000e80365800308139070307402c43d60045002c02c403200305020b41e0f40340c0780c052140340a4007035a00300003100c4258002800d07841c103604041e050001440107001441129001107000d0503040861801050b0303901021555066003003401e4600751800701c000f0540741e0f0300b04102021180544040d01d015246c41d02c500b000403182030012821341c400c2d4080030a083c84d0010003684511058450390741c5800085a000240081030711b50313040840741c02c02821051441411003400c03030901e90300c11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 864994307 1250 864993057 864993079
    0x5011104080d1b080d1d011506030513021005250b1512060106020d410d0c110c0d0230060a020a110a08030a0c030b09070513061706 58
    0x105083d10320148090440c0000003110050022240c01804a00d0700d520700c6109194a14280c4078200e03200348440d1003210700b840c0340421205200f0381246820280041216050315140d50002d030000c7d11440342c131404074401048003c0a40c1c40b000c41031440391154960000c03204007590380c411360072400a02a9005013140500d00c050703038444d40700d030b441c54001d03071001c9924558596202075528042d4000c0000010418481c41850141e000d04520134000320704000304400031840d04000c15844081e12850744510b00340400481426036004030704511300d03142c5980c0300c1a401c0003030880c140a0304c1c110035402203070710003460401621411a240b035510b110748002e1503140b110110b4074101c1260620340e0100c6101c0c10003070280898065004014032200b03901c030615164189680c103134480c0301261020303204c1401400054040b4416070400d030a101810701c0e001826a002000142c1d440c1002e880c103100241010403680b842220120f030341f4000d0442c0d810010044901c41e440c001500754000e00441c09000e1030b0171 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 864995557 1250 864994307 864994337
    0x911090f0c0d02540303181f08010e010503210306010302090916110d0c0807140a0c0302120c030303060f0105120708100605070812040c0f080a05011104080d 69
    0x181d0100a40d0b80750101103400801d1a40c0d001e000108080740c51010004000b40310760941288260150904c80500a94182451070040c01609034202050079000035800c1c2440703c2e0104954800c1011003165180c0040c139505148180b03251690580010303020754041c170101c1a0050500c0528600c964600034080d070359075507000040b03010340114040e164000442100b80418a0383c18801d0058100841c0d41d040c0a010300c290403d030792205c0c40d003601c1010406822180b80410100c9005016407030250a08030328000070000180c5c64281c0e070000588140140441c1441140b40c005444411801c040b030042c2031090102c00041d0312440050308251241c40102800e1600d81d010f54240d8030800301d010302032011803510030006407841c2c008485074400200d80480114078180203800351032029400c8540142080c0492000511100003c0d00a80e182c02d003100c0300043e94403c13008801d025003090070203000504154034010342902e030b00010140c0001c8041c0000d11040c200000c00078000d8446140120020030081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 864996807 1250 864995557 864995587
    0x6041e0b03160906090b18220b0a0509010507020c010f12060e090f0c04050f0a0510050604121a0708060d0c0b0406051902122b0911090f0c0d02 63
    0x6210b002d200e554090700012603c1c45a0311400c2200c1c0c0001090040c0c004400c06c01440402c0240d00952203820741d004560410a52880300021809201d09060520210b4440031107104c02218581c00d417640710b8040110300c007001c0c011250001140c2c0000d00c40d0700117800000e0406020b03e4074240411600c00b034402045001c80c1c000200405150405d02400d082c210f004c07a4a45501c28103d0406120701d0440d4085800c040c844e41d4850b0324440032006941c0c940102541c003404010381001e2501450321000700d41d40e60780c04003c01c0103041484003801070500300c0c6802c1c8145400300072081c0c016000e040030018065008403450f03511101c210b03220183d00e4103030b10b01a40459880d03008505040804038010a0258004004154254403c9610300c41002658400c9950f00407480351991051014070a90314964001c00c9020f41d1001d482d16a4200010302c00401c0003282c40b001c0c0192064058001d00400c507040a1080503003215020760704007840e1401c2a90b1050354440c46c441400390319070010b0000301540c4c400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 864998057 1250 864996807 864996823
    0x50108190c090b06250c080a0c050409060e0105010f170303010b090625050c040501080d2c041104090b0105030f061c0212070614090a1809080d0c0806041e0b03 70
    0x40172150400c1940d000032180c4a10354860864010940d1038011030708850004144420943c05400c0d4040c80f410b24080c04060f0041c500c0c01c4440030703150055040780400a0143e180684021038144600b2460000842e08040306c0038000d13400380e0000c0005100d00003580d4101c0318006020f8480f59526110300c00c0103a6007031018503506041c2d10f03001c0d6000302003000c04581001e044008403018410750742c86000480e194a4a05542c0003c117102c2719a11320030880410040b840f0000b80d40d91055a004d010b0041016200314009500008000080c28400c2c04d4040c402c0e01d40e120020710307000b0300b54601040c4c4001034882c007400c280c2c4109090060708050006514000207031703070740c00750031508203403400020b041e43c40348540a00c80c08030340c07500b0400e060345040206903480d91000812010380c0e50329264444100124111066500d60303111a102404120014020450000515030000e80b15a01841c010100c81c400342c2403510842c10260303000114441840040500450743d50005984903400340000e00d00b04070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 864999307 1250 864998057 864998077
    0x5030c160503180906010509012010180c080303040c120507090c0f020f0111040504020c121902152806050306070c0201031a03070e0a0b0310050108190c090b06 70
    0xb0010f07540c001001400b084044800040e42c0440190f00c40d0740c0156094010748024034000f81c9461070b20408040c004d03d5061501900700269201e85507403440f24800e40b91500004c0c005003082a8080302000825001c00008140c1d54000c1c40c02c0d070402d95600700e032800961080c607241a8184980009214040c021803000b008410003c0182039149c07140070f0182c0c0c81d00302400000d4080e8009440950303906000b01191514009625460301d030602c8100070080d000652080a03e12581c0340c041c0200a2050007130039148046d08486920320708014000746030058541c9100d612030524020301440c0c0a41101c0c4c0f00d146180f410440110042c0541100018086684023941c18030500041c00202a00b040103021100d000381e03024041c50000342c0070303000303050300014149401d80e000040412020010040c0544c00c210100d0b404510804500d000900d40b065031340d001c080c22a80c030001000350303140c2001503d0414019060284461110381c90320120b050191080104a85c1c4170200c04040e692400d003241ea1400b6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 865000557 1250 864999307 864999313
    0xe010503180102070308180706050d11070f320705040905030c0a03050408150103020d03080603070b0403151415360a0c0c050304050d1a04051b010f05030c1605 70
    0x94617080080070a8019211041b4078400c03210705480e851000719080782a202c103921868600401c00150f80c0041c0108290700c64112800d0040d40000359418405260311400354240107c8520321281c01d9401072032100f6143d01030885d528440e40500c40101e0b6500c00c456040341c1c006007082d42c0e130925504510800110344411f00a04141c00c0403d50007801800c280c484d00c2c002c8039030a00e00e4500c00704c01c480382800080e50001c00035a0042c0001d1180340c0841c0d1000010701903444030ba03507600301041d4a400c241c00489241091501d0840c4072070b4184110000601d400c56010b4580c01d04980720409074002100c124020850010076010114a9011604c0240c00f01074840c5040c84841500707180d441415280c03040c1c003e040506a143c014840c0b90500c90560b0060041c625103840e243c204240d504117142c084030100e0346000c01d007001c42e014513110b41c801da0054000e02003a0b070708000504807101841b903901c2c0c1401442841c07103121a0f0b000050382d9200c03944043d0240d2b00c1081542c4000515482980100148 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 865001807 1250 865000557 865000567
    0x114010306031a0114041a0f030c090103030f0201050f06011e03150f03060b060310090e0c10110c012318030f03040e070801150309020d0c090e0c0d030e010503180102 73
    0x90204090f50499000e024094400380044007004141d411201c0d02c407548000c002488030b01d5107800742c15440300c80030003000c031041c3c42c0c41900400c4101500b40c1c401c0d404681d02424401c4880d0b028060b00742d100d2541840152549851400030344070000c9081900424454000c02010160180e030000280700380e05842e03290090307510946c41005200341d00040350b02c2801d110704006541000015640110326210203820710504041c2041c000709070340001c03c4a24410b42d106c05c03a040e2600304103e010504560744e4024080c083e0f07110303941b81881003007540d4100b0100c245003080c120407030f0b072422076440b401c450300316a00c00c60190540e4128900a0422340c1c103005d4914000380750080080100120307005904860500da540c3c540555211000f44583ea140801c0300300c50341d1400340309900020019200a0030b14003019050703210422481c603980c000c040034031741e546c042c003840e840100b080004032002141c94800c200b90b95603008002c5007000c10b002d4148603020011aa554942038184180d00003000d000b10b40360 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 865003057 1250 865001807 865001843
    0x8011206060e010f061805060f0a1b0803040629010c02040e030f120f071d01270501020709020f04031101020307060f06050405090319050d1404060b01170f011401030603 74
    0x204c2041d1040a02040d40c1c26035400c140154081d4200032224020314060400040b066044100d50041c09100b0400802007020140c00c603090020b456164081c450b425200d02d02072500f04c0c12140303111203034890600e40b2841080324491007886003125038001c0c0f03840803400901d8404a8060209040300302510b010201c7c1000754496494041c3c1901716904120040030703200c0441c000c0c8044425210746d80000e0000007210700e07512056160460000062400d17031281c68030380c1c400e008460030811407000303032071500c0c14100070a603810040d41001e00000d55045244c50301c5100e4614481c41a448018050f00700c4145440c0c40340c0c003d006550045420800a006c00b4410707130900c80040c60039000d858459071402c0d000c180900400410358000d80410007105200007140c450640d503503044083c18680480e15200c5400d0843c00c101c401a00441c03050002003003943c3e8420024120011344580c83e652105641304110041c040e4120841c11540540844c2400414400040b0b02500c02500040c01a1480a03d11048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 865004307 1250 865003057 865003079
    0x6020d1409010906051803070219080a0302011506170103140102040b030708040c0b0a05031929100305040506040f21020c0102060609091b040b1203130e0708011206060e01 75
    0x43c0b0b1098500b0851075a881e111a000700801e04d00783d4049034001d000c04c50041c02c010b11003001428402c00000c1701290b40e1a480340c60640021400c4005035164410802a4017001044001030725060a150000d4107402c0c41070501560148400b0f00b86c6d0a500185142d012400c1d412240a40b80c130060b81c030344c0c4c0d161070640501901d0040e20100e46107050520002117048001003176900207445565003070f00d980c0311040d484648400d549840710619507180341c4910080421458401102010b41094032120708c2c18042040a41d89500004185401e1000300700016501250030f40c1d10542c808880f403e070242c0344c14041c00400703800710310710410303d050100ca6a1030790300001c0103001c0e140240d00700c8010341d17151750a00c640707098241d035401c0142c1e01020048640100d0f007007000c000114043c00c0020305048440018500040e01034003100203400000764440c41c0c441c0e200e40b04004e061002c0d196000d90610b10340042540105100b2030460303d9007031a004080100d20381103040103000d01c107065021541c4480c14811 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 865005557 1250 865004307 865004321
    0x50313030b0105060a0e01031a0307180f090f0305030a02090a141c051b120d030203071107180b011b06020301181b0f12062301031806020d140901 64
    0xd0715141c107a0000a4038034048045030307040c441950310031245c65070200c01980a800341c15a000c802c1011440b01003480d86080000400501c440740b00c0440320300a980d968005c9400c7c400c0000b004d9030608500700082408900c10780e140580c5803401c40d07a81da07180f111600c028041c0c40c100f650700441480c400224a0707002460710401d04803c03211080150340e43c900185d5000b42401c80102207801c1045d0b4903440340f002c4814600d031658042c02c0314107103c0b00c0e041c00d40d050880d00c090300c0380460381c04000c0c00042e03503120a0322401e044001c0700500364030703040c05044201c0c8100b50b40102d0040e502c4a10f2002e00340d106000150641c00d10402c40c1c4140c411500e440d0002c1d4000b4018550202c0300e80d0440381655079140600300b81d070100450a85956440b44800b100d6201c00d018848040c40f1003c081c2d508600800d202d91402040f40c0403140ca001030703400340014140020551924105401d01e4800068441c003420386105041d402800140d0b40c0c0408101400a0f2009142c068030400017481001400c0301c06421220f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 865006807 1250 865005557 865005563
    0xc0105010906060e040b090c0a030e120d061205061b041d0610092306071b0312052a07080109030c060b1815030c04181202030c0d0c06020705031303 65
    0x1c4c8810b20703000c0c180800c840d40c4401c2103501980c0e82000c5098040d102000741516025454082141040d04002d103140c201006c5000e002000d001481001141c03252041d60301909042d0701c079031110000c50b1940380d681c3d02c02901008c04150324180390b80c901202641114000e02001c5040500c606440100700700c105011a201c5001b201e501c10f040c030034140304070802000e03a241300b82468000841240d6124084907500c00c05900320710104403840109034505000004a01c14a40103e1014103603d03014038100d041c001c2200901c80140842d1010050040020905210141c0b00181000a240b42c42e440c158030b41e4021001c5520384010042130660044401030f415020301000d2020031510428004030303549980b10304800300341e144045904400155a4580b5441e0010100c0c0c001c4000c21000030700f1984030000c030020b29031400b0480401c0182500b04c20a0003c00d0b40003440c1880e4500528a0f110440c0c40d10f158100042a1009000c021142e1705480c141600720702143d072a101c88048190b0054101d000035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 865008057 1250 865006807 865006817
    0x908070305131805160207120b040204020f07150c0e06070201081306020a050909180c06130801060f051008070905060a111203071407051f18240b0d080f0c010501090606 74
    0x245e90003600000301d5404441c41030340c1c0300c208034105895003100300d44007510483e4403503001c101d2072125442400c00380902a000d8800c41c2200d231025500b4004561300072200340203004201c2c2401c2c22a40e01d10007903680c940d4081c2001c402680e104031907407601e0b21030444000c00840c0b002c5a2070207055805806400034076000ea400003103035140c040341d000100480844826260380101314aa2150800302e0103002c2d01195900c0c800c05484d201c003046425100240c007c01041ca10480d0100f001d480c02c8540001c00342a14104803995080291004004103c2400703114001d60000454080152007000c01c17071042d20003031040d0b0300000c18058504001c0d5009448110000d0501012440d8083c15142110b13400c5900000400c40c0b004803d41c0074501c00b50600d400b02404d0307610403d90250780650100c0009640c1320b0070300c480ca03100f910440c0140b481c2c0060000c0700b10510349943e0708941d4031010742d142403182d00700184c2500c80a03044620b40720f9100d1000044165405c100000079070381d13015000503003622040e40320 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 865009307 1250 865008057 865008091
    0x10e03180109150f200a0b01050909070501030e03070c0f060908121c020d05090709110a021e2104030b010b030c090f2b02130908070305131805 63
    0x4494602c0240075080300322212201201034940100203a06105500342410f2040318803107010010001604180c0c008030703400c440c88582c104049048914050441100c0802c10360801ca2007499984241e4007a441c10316035184001c2c02c4418040050b6807101d030b030044403107094a0300c501c01091012014030640010500d080c40100d083e06002c00c51050340d26191603a181040b0764545424100790710b90300d15100c0c3c15420000c400b082d24250042c944103820420080c9a0340d440e000d006002c5683c45000014404400d1126019840d0b01007407400b01607800f40031041e07031400042489810810001015051040d44130300c0388007042004005002128042e01e100000c0d6a80d40c001070f02a803104540e104049181086109211f103070091401a00007005401145c187d0301d5880054200d103107407000ca51403940441d01000451600002c0034030020002401444004020359400300b660040700d00c01001e00001080d1030b00e440305280d01003401450103207401400c940b0000c55210060070151515070f40001400382c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 865010557 1250 865009307 865009309
    0x60f020f070b090a151112091606030c0e040207080903030301080d1b0b0c070507270e010606050406110a120c030f0e01081803091f120b0f21010e0318 66
    0x844c049516004a81d80503a09994081349005150a411008a0700e000f44015107110840c04044d07131041c555a0001e03e18081e003802d0403405000b1035403120080508105141c080740d644491641c44c140c000392005070700d5407a00c2c5884902800b80c03400c0c09030544004400019100c0000504104103452a241d8a000c501c1500641e1120100c083c00601101280000b00703e58282040080a820303010740d06459102d070303e031480540e903811032456a40308401402600441403401d4400c41815014500c001c0201c5450404045e00b5805a88264014095000b1070351096003024000101d40c640d1040c403019000741e40400140c0395803008481030700001c20700300e40c1c2a001e501810080c0180385058454038030700e503244000e507150007881c0699420b49000c148260000354551008015110042d0f8000f5120790b1188800141a10100c00e1480040343c100303110070701c5540b900005640001e10030764222004030600c4890300d031007906080300e000b403940c41d0840e80f01b60004040003504130218192205101011100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 865011807 1250 865010557 865010563
    0x20c060d0204260c010c11090a0b030c011e030504051c080a1a0102120c07080714121c1b0b0703090c090b0102060c0c0a0507060f1218030c060f020f070b09 68
    0x11250110f59000d06044c480e20740c0110001c011043c402e42800c00700705602d40c085440003c095804068540d01c80a5460040c41d09000f11740401d0f0081c0b919651111070302d44210a02484581164141f6550380082000c0c881c0500a4294400701e000803400140d8122100400f417181c01c44900031418900341b1802030f0340b0b10102c50140c0c241416401000c01c81d24151000c02c03da4000f4800c3e13403241c031034803d0004007003d0a010f00700080032549030740c4100f40184000d010350120350542520792500300012200305203441c0241000b01444a107403920103400d241e603035450b0b40b00c0c1e05500a0a005030341da0030010360541c560403481e006ea00c0780c03140203109035450143d80c00303a90705008098096008940003400421400b8040e01d0040c4001d0110352030381c0000e8981c04d080986035042400000c0c2c1c01442c3c0c3e03803002d0b000141d4a1342103060f207904000880304c00f00e04040056030a480142080400001d103400d10040350040c3e8402c0d10074041c110741c2d8148180280f141d55010707072412a03070b50387c3c84400902d0010001c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 865013057 1250 865011807 865011869
    0x50d051e120601140d110904050702060f04080a1715030c03011803050705070902030f100503060103030f05130509090c12070e0f040f120306030605090601060f0f020c060d0204 77
    0x180d405950030b4070b8180c0103603aa40341c0c03080440000f001c24441481300c5c2c1018000e001c0060800c9102c1a07841d8003c500384010703200000d0801c41554400018440c1c25907400141d01d50003031300032010039156540c641048408000700c22081903102000002e100241c541c40c442030100500032011a0800000e19080c103081ea05111011078400004a10070340200340034100800c000781c41941600e0a2980b20560071089030010346040c80310350703480030400091001740d41559014110440080101d90302d55600240380c034100000b600d0411201180882c5000d2110318100e0141000500c000d0491030940c80d010351311540c0f55101445401e030542c444c0c1031540042021829581c0048000281c0e80e161010500b01c600090320413105100a074501e2008166101c161034800314440d6000b0800c10f103141070541c1a02d00c0940003280e903800020040061a41203402072202601d81c1c20514240004140c050742018100e2680075089400041e15908100503640180199018480b141c407041e54000449400c041d40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 865014307 1250 865013057 865013077
    0x1503050c090607030314040614090313050409031b0b1902040b030c160b01350d0305060a08030408010633030b130f20070c21050d051e 59
    0x10440340070503050031401801042c3c0241408210b0074200c4015611104049400b9180035680f5221000303010401e030300312034000b10100000c43c2800c1410320303202c50482641c0300d82da11960751950700c001010f004088800c82021103006820341c40300c85007080d03400d14030201d90340707003808030049007004160140b031007520141c0c1e510410032411603075072803911021b590002074004e40c04451400e07804002080d0150302d42c007030807440401076282c45c01c610482c81c15520719595400517034030094030b000005200060001590056180c085010b0701c58030302252110565401440321408001030218206505400200444210560030754a82c41010b8807100d40c4520501076140300c51110451030901842138004031a4101e005103552084500c040b07169044a0464a2061b2000e441c1e91b41d6038a20750600c0c40590a036529001c07500d241a1113036490400c003d5460203080501c0c84090071400100103801002010254007804841c46008151009881c0d0742100d031680007005160b401c1c0000b41190901030b80e0b10604 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 865015557 1250 865014307 865014331
    0xf0a180b040210031b0c05150103031209150606020102250213020310050a03030309021e010c0b09070b0a090e150607031110022209090b010b031b04030b01150305 71
    0x1c55a003044500f0100603200c0042646a440d44941010540840b0410f0360568580b00300780110361a07d1130402c140b207402012040c0d005001000480c2d00b080006043c64180d050000c1d002d101890400c082004400c0381c201d00a10f01180400c809405600074400386011910b08001c440f68510400141c921401000f0341007440320000718101c109a401541e0400c69840c031410365161a07078046440022554810340000340c55140b60429814505a084050a211240c84040340b030503000191419034101002844181703400d000815a600c10312092018040003280aa502c200446000f040c034031a5000e900e00903142d140201d0141c03450b40384c595070602c82c05441c40341064010386055610071103020407400d042c05800541600d040172803000702030414070400c41012028902440740a000c0454100130307011841c03c6490004245403940390b80c1141c5003070700b0180d42e80c4d451742c10454440b0001e002c2c0301c0011001003000300070481e00400342c0d0f05954040f1a401c1908001050460643d04155644c1401d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 865016807 1250 865015557 865015561
    0xe0607050703121824110a050a0219030908070906180e0f0f01061802090604091104090504081b0a02100f090806040503090a06210c0e0301050f0a180b 66
    0x1a002e4224541040103030500003074810040c4ca900f00d50031520f03140480b41d04040b012220040c8000d0b56072000b014070142801c1181050050350a2202d21920f0781010a102000c1444104548200311050429a05910002c071107015441c001d0300c68080f03409464040d008940300411680c8075441031100300c074003248240580c0e003a00403204004001e89001030525001d04140c4039659501006a420080142000000c0c1d961400000d941d10110856468001d9401001034600d241d4801042ea4152801c03198000340d0902c1591107421544030700d9016040d424240000c02081c040f090004d03241a82c002c5045010f4402800d82c4d0649400ca03c0000030342c442c2001e14030190083c8654204a41030440d41031101031a91984405440d042c42114101c03001d50000520030003034203040010703400515180c20101d03959660b40c80442a0142e4103c011182d041d5244080d40e200d89c8aa00c400e03000741c901600030001420103100a0142a80807110b41d10303881d040155016440e40810304040d690398000d1000d00043d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 865018057 1250 865016807 865016813
    0x70b061309020405040308070210150e100e0c07031b08070f021311070212121c090602040b090405010b090607021e0303030f1e0103080405270c0a030e06070507 70
    0x248030400003000e40c0d8103203039001600c0d00e125940c0554040e8072290072a1900e040e0003441c1c04000e500314000541007400d0b040d134001d6101d601c1e00607074000100a014554607030703a0540c0c120f079166201c000b004690320207003d4880c40a400801030340d402656405103036411070785000c11f0071090423002000c0355010000000800d504200c40c407040342c07005100d420443d061903c03440c2656102a2000402c801c0003910104510300058603110004c1414054911200c5100c9500724600540f01c0c600d00490289116405039049a8800002d941e4010800c46d00c5a8980000c0c22180c0c2140c0c9200340114038080c008117080501c40d041d14104103006141a00d0044a542400302003003c00d030f41150000c26002c0450140d80c1c061000e188a85908010341c03089190003140c50091026091022140d50120340040c000300d040202102d054136001d81c0c60150700d45103407030481800c50030400c4401e04e03000d40005008002418200804a030542580c0c2809805075800010746c9032034041e292003004c103d04210840c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 865019307 1250 865018057 865018069
    0x1030308010b27030a0c260705010f110a12080702010f050c0a03111b010902010224040f1b0e01050103060602191e060903020703121106010e0612030c070911070b06 72
    0xc0c4400c042c055920a01d086c0d81e03520801d04403130b040b102c0000040102c03600c44540c600b13010a1052100ca0041602034070b0503002801a091100b42d80040000782d08100d50560010400d02010713036400380740c0403844018500d000f0076000c82600c0e00c00055082c440046411501390007400d0040740079400051a200d250142034008221403c0c0c8184040010300081200135480310100320608524800800d02c0d0482c1d00c002800d218210800c4a42411816541c504c848101880e03070382d00652040400110345c042e030400300006040300c0740e103008440d910240800d40345010b450f0749040b150207032401c5c41b4a9031101d000344e881d02d441003411801d200650b0135540c0400c2121545044c0c0700100e0513590605e012689600081e1805184c0c20741c09a84a00d80800c1040f1034101c5000080c0c1c0186007a254142561000070f4884406202d00110b0060f4003010600070b039110542100c0c4080b600c02200d545040c641c940035101c02c91403103000821450050604509010001200c0d80a94003038a103d1031039588100700300c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 865020557 1250 865019307 865019377
    0xa0501020d09230306010b041716090518160305010b010c150b01050f0705010e0c0a0503100e160f2c0129120a1d0c0f030312010e01030308010b 63
    0x40c0440c0501c42100d40d89060145c28081c01a1240300c640d06d41c1451510001808000e003038560a03444060030798200c0740900e03403c0c4185d40d000d500100e51504c40d03408404c03981c0c00b80c0104901d1400740c122040107080e2441c25020441344200001d1045d400a0401034405150451025003e0390420000d04048007503a4001d003000001418981d0414100d401d10305402d42019800300c035960354805440b03101d5801003202c1d91024100316008031503030742481702003030721006181786084410ba00c0d00107a000581c4244000700d0b041c800c09281f070040326034490707010410030008d21844d1500c03d0a850b402e80462182540c1803100949185a1403041e4a08401c9425200700310031006041f516a444000e0310700419001020f090802d03014032150342c20800030200440b910120302c14480301c0218483c800c4041d001c0340c02c40040c8421035000c41c031010b0000102e81140310350350b11000d0161000b400803e40b0042140d00c3d50680b4002c1e40c9060190fa03c8441050103131007120501c10440c00d0644c081c600c190003600303002e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 865021807 1250 865020557 865020599
    0x1a06012118080705070906030f03050319110405010912050a0212150403030236040f0204030f050d121a060c01090c060906031811010c081204050c0a0501020d09 70
    0x16100454007800584500415011150110009207490a00c0410403507003000d0115001d04010b4245940d680300040d160a180080c00d00401000191740f409243d1b85270100c0d144485018000703c100040c3c18001035000e8010305000c124407120114100181112000059a1080c014019102c56401300a020007402403070300303081d01c0742104164034484030007640d50003244251400360701c1e030300401404410000708001d200d0340305640c842c0c2e9181d41e02214007075010f080000c0d60000340c42e03409048600064416074001030091540d50491208111340020803a0484880b030b541c416005140c840d02c21309a40400c4d40030201c042011209944916182008100ba44500f000000e000b200700e41c2c41801c00f0882d03900140200d010404200551a018080d90905441c41c0c40d004103c41819a14040b010325440304440c10000000c18500030000d44200f10b8101e6040d81c040f04103d403806241095403244460a4640600d4002d20005110750000a4a03080241c0c5038913944000c500780300c035440c0030b0007041c1e00306 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 865023057 1250 865021807 865021811
    0x40e03131e0905100b0f1e030a06060503090d05030601050702040e071d0c0712031e0603021f02030f31091a10120225120519031113121a060121 63
    0x47e030b00c85040140d07215154010000846c4c5a1030119600d100711078560348400c051185c00c10820008000c0400d40d8800b21807907040581e22502e0700f1004031240e001380c110094100c2e00d80b07440e01c040c01c180044c1c0c00c401c6840340d6440050104c6e001c10704c44a428420345801c3c004120500840f400070b0023801100f6982c410515000680d151085150701041041420048840342c1d103003824000e5090414054031004104640103056604101d03000390351344941c0c40c9100c20b03e9404100d0b01281c2012032555007900b44070b110411645004d041051100c1c0d1010700c10401c071b007858444649105c480300c546c0702d4076083e00207224a80306160b0220684500d51200c035070307058495081001e10350b10300420002c160303411509105410064603924201303103030f031802ca00b8100a03c00c1c02e1001c0c01c1074020305201c80500c0f02c0f013850301150003d405c9501090b98041c410300d91f041000603450115408010100c400f03543d900400400d81031104403610200c900380d040e00c1c424001105280351060681e12820b00c40d190311803007040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 865024307 1250 865023057 865023067
    0x61206031005040609140606060a0e06121608070903020a0302010c0c0503060c072f0616150207060b01030c020601060309020a0b04030b1e1005040e03131e0905100b0f 73
    0x19550482d60b04540440d020b0307540c0c207400710600c01e0000a40d1042c00c00c0c0c0307006005034184007000a07a2401540e10307110030090012000ea040f6210300c4103440010b2002c000030300d4035080c60a41e481450000280715000645140700003045144500701d000116600601040015070540c0c00455415100210564801040d02c40c0010282c40400c5224800c0e600310000603218038141ca01000d014040c0c181075082e03d42400a03000b13041420a00f4030318150000c030f41c5d441c5e44400b00d680c17165041c0c440d01070191420003555200c0540c0580c0350002c21255209940810002d42d0303240064003203400358080040181d0104005000040c00790384541041c0340020124202c01e692514807021039030054004640c111034480c1440304141d103051800b01040c80b1844000e40301d1819440c0401c5c402030742d01c603640c4921784417000c038020000d00307104960b01c02c0380541088201984803217000e02d05201200021035000b28036000000c442c10a4450b40c0c0c01010b010f00001c0c001c5241c64940001c81e000703103030072904003101008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 865025557 1250 865024307 865024333
    0x30d181a1309020a0914130513080310050f10020607080a0204030b09071a04140d0309031a0f010918080d0b0603042a0b1c0e192006120603 61
    0x208020040c414000c003d65a01200040105131794031030b80c0558035000345150310308941d0340d500e03148a48180025000203150307658008407884c1e0340d0095401900c00c100000c20300c5402c0c00b0440000d8182d420030750340441400310070070a000c0000310f80070382e6100507040200402c0c612442131902c03a8001d840d00303102500f456207d071111a500c0c4000e42e9942011b52220720104100d40a0503615103031081c001241c00e0900346060f209401c0303440b60003640c82c412029107018100b09802041d20501a68000d8680b6209092440600e0606401030303c0001c10301c02500c00000b010f40c00c13402010489001c1e112110000600d50f40e0380c44d01c07500100301d00e1b0015510758191014a0321404060b62040e03010b060281c800c100100c040111200c1e104003c15045604c1041c2481141261812030350300c4c1c02044943d0401e0444646800c00400011055620600079001103aa02800291101c1d0407603010341c0c0d541c01c24a0a285a200e000e6100c0d8010981008040c451310690007031182256900a0000d0280e40d031010160b5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 865026807 1250 865025557 865025587
    0xc0303110c03040e01050906041811040f061202010311160807080d05100315021306111006080d0201050108010e120a0e150a1d01050306120a02120705030d181a 70
    0x2030013441c1c0910b41c030343c01004145842c0c0340e01034008030103644c10444031580100301c0c80120340050018041d5002c1d2001072125031a1503200190084030804c04002d52501d4911000402441d80c40c00e90000e828076407010014205407046407880105140740060b2024541d5408582d600152401e4404c03603030601c500e450303110060240c607105042c0401040c80c09803c2d131178055200404a144410a01e02c148003c44580d0781e1040c0c948240d0f040c42c24050700c00a8943c00c03a41c908001c03074418000c0c0504101000400d00c4000803500b19120050300207008503038075980300500303c5000c009001c99030342c0512000010300800c400100340400003032a201071340c8035508004c124241c42c0e11350381e25084180081c0322a00c3c0d50b40f04d10b033281d00b20808001060043c44036000245103002c0508183d126000d4544416040f0a0030403055101e6940980b81c1c1030190a00f6102a1b103e400c54420580a4041c10300c17000e207058850b220052001110201040d0600d0800c0c1d01050701f181021032518145a0800078004451004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 865028057 1250 865026807 865026809
    0x90621060702060108122b02070c080706120b030601090e0a1b180b010c121215090c0507050a06050703090203030d06080c0105090d2006040f0305011a010c0303110c0304 74
    0x50b00103140c0c651424070014903140280220f800d14210901c022070700c03a01d2003020300c84841e000004100000d29911561002441146001045d6000e0f8078400140c14901040d10400c03a43c95450340d5030340007421100203040d2000340500d50340c950400e03001030260301d0181d44a401110344079070490708000c0c1d6954405d5100d06030440b202d8120f082c840010400703103564003100229030061140510a0550010000e042d110052400901261058800e41c888034894908049508071050b01800040a0400c00e0841160107001c0c10a51368101032034216054041c40c00c90741100c0c2d2003001041704914079140c220007440b002d00b0b4401050789030034090380980d034208054880c1d03600d0f003000010407503d804040c500d0400e405591030705209050002c024255290701e001a03055070031590141d071b10f201c107503031003c0c6013090702c80d61603405400410045858502c600c403e0003a00d00c40c500810441203212003160341e164540c0c8030280010140d07034400340002d00c40c0d00520b504041200040d820300780f103518a1420340d00030b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 865029307 1250 865028057 865028071
    0xf1203060302100e0d140f0706080402032104060e1f0e0f091e0408040f1e0f030b061201060b0c0a0b0f0106020a0803180d030e010f060509062106 64
    0x12500c0c28400d610380740890565074005418192010201400070450075041c0550240401e6039486205020801c1480000695880c1c401513852050302e9002c003400440003038a00768064480c41403501d819010229058920701c8900c0781c85401d0615042c0b08076032032200541043e401030b4200d5801c541064201c00360b0f8410640380d86a5403400180790341400f2038092010b20251241c100d150502c9180446204003800c010b110040c0d5006030b41d9182802e100702c0c842d0f54448406d1760b48811000175101c2c64600d400b4038413207080311418801175a407120300d400c2100c1404043c1c8000d201001290040c906040f02c00f4002d0507060000c00c0056032283d0314001e43d082100c2e13005a41c1c115800f0700c42080714100c0d1181d40202e0001952000d9418024029038944070441d0040c0402000404035030032142d076040721412a104241110881d414490b8020090f1907001071960303030b542c200380310f01c1a0050303940034600c1580c1020303004107810341c0c0310320802106040c0002d088000141801403034811110500101d48110a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 865030557 1250 865029307 865029311
    0x30605090a0902011b0b060103090f0b040f03080903030702031602220608121e0309210d0b0d150f0b04020705010e212a06190e0d08130f1203 62
    0x100f4000035017059081454448502a00c080420000321a2414030350850028640014481c07440c0c9408150300c014020013609001c10f400401080152030f524000b203840c440d9503040129141c02d43c0c100c0c4d4034002619900090381041c807264040c1594107001d0038005000400042c04003c1d010a1016200d100a0601c18540c2d03e511050002c03200410890340c481104030009880c0c84410324180349080c03800d80000e00e1004000020524041d801c1105c2114101c2c000513165160007060a0015142e11486849503198144030000003103241c001808103045800c03d002e02000c10200442d90010206418515801c5a580001d01c2d0300d620b4501c0076000340c9102d203000082034032aa400c5c00e850301c0740e01011030120f8030446d403020000380c40f0700b800d441c0c0e128140010304240b06044c550111003540c1102e51b80b21070340300340020000b0500f00c60005100480c00350701e01b0840c0058000d49503440b10106c1500c407003c41c81200114500100500001104500450700940c210130540c0c5c440d004025002007680001e6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 865031807 1250 865030557 865030571
    0x2071e050c031f050405071a13060c02010c0b190e150a05250519020102031608070f1b0614010e06061303030c02010e21120307050415030605090a 64
    0x10030203020240001c800500e030780308400103010407242c005400e4600c43c41c1c659001c03c3c104441000840f000d000c8480220350b9842d403030101d14501e500079540e040007264940000080140c01645144140364069442c440080310a413681199040c000d01013075544c2c1154000015071003400c0c0310741039072008100080e0245034002c5040d9800a10080c0c4260034151400c400e010030842544508203c0c498841c40728090501c4100007a6854001c4000035120300c100e240745040201d44c1035008500c65606110720b003028880c040c074110382800301101c01c0300c0420080c0f5022006180900d01091041c0d02c040c81c0942c8060350383e42d440040d05c006006010b101100c5000612950082940a5500500644d4140c3c102402c54180011b50341c40b41c0700140030b1000c1c0542036000d5910078150a007032414081c00030070814048080d48443c07000c0d00795403030207240140b882e2810207182000449000f032105558103410030341418107804007500070440c1d90080c565110000202034031181d0f0001e10515003507500203042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 865033057 1250 865031807 865031813
    0x110d030c210210060803041a1e1207020109200321070b010e10051e0a0b0405210705090c04030510140702031204080a030605040f0207051e1f02071e 65
    0x40c3d5140c4081d800d040c14400148020940001954211805040d80d400c520720a1102c60f20b89210341031840c050170300c1800c0c00c04d000740e01c05801004140000203100c0c015075202e400c102e003240d1884000400c14540005481403680940050543d07000d4000c0990303021216034410754100030715030300741d011311030310041400c10503c8001a20300e401000f604010504c0b0746000322001411981e07601030f081c402d451035500c0c1c1002c0c0c200702070454403ca10207045185166250305401c01250081e12505228011215035801c401d2111400080c021040364001c1c907182c0d0810003040303840f14004041e03500c0d103907051000101051003003102500c900166000054201c072004450210004020406d00c1990301c2040b91400101c00e5060042d40950806142e0761501d00b6240e00702d0190440b0341c040c0343d20504040040101d6881c0340e00400b8460710034011641401031211404000000206081c1103540050548079108a58109400498040c03c01c0c010319000b01130360b400d65410042031100100300c481d401c64000f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 865034307 1250 865033057 865033063
    0x11130207050a03170709120c0e0a0906060b0901120b0f1008061903020d030807020c1008060a0e01030213020f13031b0e0123030f0d0203210103110d030c2102 69
    0x905109200151300c0c2e071a05043c05481c5100e98400e107a1001d520307a020b181030088a00000c006800314104d40566810101c089502034410300c241500c500d0310381a00014150040b00c12100001410b8452040e22044a44440020071484524a411180418200d600790750350781c02441444c0300380d0311031a0890400c034050002242e141d00d01f0525501400000b0b10160f9214140d040314140e1501c0d0860355507135400c02c103c0c2081c520001c0c0300e410548007000b0b200034039000703034005210740425510008015921104103200001c28440070f504000c00c0d040c10380c0c0c00d46658006085045600b008103103028402c2c0b8402c10041c6c5030340d106640907e542c100c500300c00a60008035900030442d2806e10b5a01754104400d034003000303090a034940f011005a0504000e030b520300b403103d242090070920507550602c0e4510000f0303440782c3c00302080c010001c0b070911140d850900c002d00c02074117073b03604414204030044c902c0090041c944803520040d4240004281c540e0b0018030000c0c41212060420081180480304160020345 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 865035557 1250 865034307 865034327
    0x31c0b010305190c11060c04140405040201051c1107141005060108060d0510021207081012060c0e1302250f020f01090b0a020105040c081911130207050a03 68
    0x204040c00c00c03003402400402c0719190004000a960700043c1c0c07a80c0781200340da00801c3d80130f00034401d0080031b0801c480091100043c00442c1e003111070b20001025001c04100840300125402401701d41e09014018100d408403103a1a00006000c00001e0396081684104d94186c000200403145251f007840700c001c03450380a003c800340b6030220010620441c1040c00000e820094020300704d5005054a0704141309010041150f0109004025000c6607128001007288660590442e20324010032802d401294017078401040041c01c5401c68554402071540d660350321000361042903ca0420040e9102c0017040544d1061003a580c68015140011ba8615a010304c44007407141108040512001d944404000b1a0500822181051741201c10344002008480103842003800c03034101503c4c000c0d010038080c100540540c0440e0040b030150301134480b84c81c0e48041441c1d8400d10011407881e00b0b8030001114000514005019031403260003010810380b4140548190120780069500b03444541c02400d07400103058008003222 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 865036807 1250 865035557 865035559
    0x3021e0f1903140402060f070b0406050601030e0d0507080d110d0e010506060412020906180a05090c09010b1c020c0d080f0606130b0306011e020d020708010e07030305070c0305031c0b 80
    0x4010f001d00b140756094082001003001e800741c940024040700039131070f800449011035841050820541001d0401200410048440f140402c6c82c03d00c91407440540022954030554443d03a5491800015a595044580210b581c2612041c0c0796200c4101f283e29a502030b008800c1104d200041e0743c9103484003075003075604c0500f0042c011602000140038000c605016500c4064068501413100c0d11803e020902c0030b51880700340b6004080c00c000f07001404120707801c514083e100300f0045031082c2d0a54005c0008a020a101740388103000200102e000c52201d540c1407601221621070014204200001031038104000e0800e45000145150100708204040c501a02c0c6c0140c000e0752514141100e03006460180415800303442107030b80300800002d1041c0e00c142d50f230b1500c0409000c2c061452280c10540a550784201040400160080b0000890821014842c0c065000355960040031b0661840c0c5060786d040d40110b45c1a1343c100e034110004004518100001c1c03101a01c0c14000c4200c0003e002c2078a4201e07240b91144c2c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 865038057 1250 865036807 865036811
    0xf07080c1305090405030d24210308041410060609120803060d140106060e041a0a1404020c0d0f090b0403030f1202120103030201021818040303021e0f1903 68
    0xc0c50084010600e808142c1c0d01c142c8218a580c0c0361400c0040c551f001d0075034000c56541c2400000010b000110748440b00180c0b9110240d0941600c4601032488210030b00e00d42240c0001c50741107807000c0307131240380b01036006801400d2621100e0303866242d0604104113003000540958417010104003255000040c2ca000b00f024144170300c10440c81d9031320310203d07101c05084148648081c0c1900400d001034020200c601c0b03070b140b000030003003103030ba980002e024041c050a100340300e1440c0200031080301c00070120440000c00001c221501a6080200000e446000c03074035459040341c0c0c2805007505024003049400714101c0d0940300c2c150608400d41c07000b008200701da0000d0100d45028403007040040d4000030400b00811060a00396101c07480800c000300203014010b00c154070f010090f0700000500d5019801800c0c001e04009a00700ba1031121024050880c0d10800c901600e51030a0b00020046071081d8041c05229290420fa0540c640c01080010801d0708080300b00003c0010018822400c1d0604600050303141c131080c102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 865039307 1250 865038057 865038067
    0x41e0c020d1106043903060c081302181302030303010f03020a150f030c05160c05130606020c0402210412030f0506011d040f060603060306230a0b01030902090f07080c 73
    0x5c0d000901da030741082c440e82c2e0440001142c0041c5031000c01448010000320703000a082d80d5900305030002e0403102201c64003045c0360a0100d01c01d04111841c00040300d402924540c2481d1807042d010b064139900030701c2241c13401b203101c500c40e00694062001314020001104149062801d41c01040824815a401141c409101c2600141e04541124002081155a08000444403110f5005540301d200c0c1a41d041011035003005003078100405600c80c50240c0f141950000100c107808e17445881180c0ca18000c407800347e441105001d503d4074141d00200b100b1801c088000c054115107842003083d1501c292012101a00003080c1168256494850b0a200b000038140038000d6003400000078140c21200445003207024900703220b8250350b841e25000800244000a41000000e584450003801007000b8001100c4050070040e050420746168029a1003050402c50800010780f101c602010003020305103031250601d501e428107000980d0b00d00c5146840364503500c800210302d14120b0380c010400d010091452543c00001c0c05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 865040557 1250 865039307 865039313
    0x4050c0307090e0c040302220c020106180b0d02040603031106060405040c050d0c03150606021b01020607111203070503070e01030516031e050a0912050f09041e0c020d110604 76
    0x941c850460300344401043c05a15411102100b80c8107903000039401580044017201080b40072004452440603843c010003010840b4001203090b90b0081c07050102c80d110403241d00c000d030203241d806004859002840ca60010801c3d1740410305590999009501158100d48160800c450034031501c2d5001004903410002840c080d502c4040e00c0426014040c002d03032a000340ca008200580c0303d150099504071031411100001c60404002901c690702a000050140644528514140c421180084c440580141000c0d980d4240202d440030403c900b000d0300d03071103050240c01c507c030758010040d07020b071510756500b0baa17a192000014000d1003100c09014101445d103000c00c0680380200d20080001070092401080b188500412481c4802c00c40340c516401d14984400c0c0503910b00c15a0241d05010f1180d5509140384c801e00e202550b0074040c000751940324180c01c06c410416403400d503110002c51101e0480840d0903002020080b41183c9a024109026a000380901e0342425040350b0b00e065071a013100010842460956 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 865041807 1250 865040557 865040567
    0x120120103060b040f090b1006020708070603050402180106051b0c01120e03130e07090b0a081b0f03100503011107080f0d0b06030f041a07020c010f0e1e04050c0307 72
    0x40701c06042c55989002d00c0c0901c3d540e9400040c1c1e007032504002071007005018102251281c1059588010b00b0383e8000001600d1030022550302c3c00ca4004a0280103014503100003a809004002c1040368403a842c032018541031175241c100c80f4081c0019646160320750031031258030b800c0d44070041c403036651550100780d01007034982c1d0001031301d030107079815041c04290340906222961441c001e000000b6038044420101144850101e42c18610660b43d40e60749029540d80c69901c185e1501c5640030680004034040d0010381050301d03a04803100f0159490600c0c0d4940300700304540840c0760f042640c0c607041d840501001080f4a240034044c582c80843c02150080c5010050740c4c0e416031074415101c580c1c040e043d0215141c0d0102045511003c1c3c00900035104039900e28054401444811084a040321a15440300442ca45400c0e145400f81c0b10301903130b40042c00b2119007d001560f030101056501e508210b4a5a83d21095844410f01035403c5482130056610030b10a0408100036900300901e0200390f42010710403c035180f0b03841 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 865043057 1250 865041807 865041809
    0x3020d030f030f0603150507050a02070e19020d05070e0603070203160c09090510140f0c0d0b040204080f0106080604081204050a170304020f0a18110c0106060201201201 74
    0x504041c00509402002034018044402c1411416883e0a40c0001030010301d01d1603211081c40700204002d070b9545e0100030b44560041c02640d00c0180c3c001c40d818029826501e0049800070250b240407104c108a5444c0300701668000d0b88941042910b4130144800c1ca5085141017002920854400b0306506c0e0110000750b4a0060100140c41d41c06c01c044241c041c0010b180c0c42502038003054005000001c19818080c5d514004410101c115502d4541d9900745580041c030124041c14113540e10ba4116212401c0c1e080b111781150a0f001c80c6140c0c2c80d020000c9136511407000b0401440d1141c003410001000b407070304a007114181d5110050581004040000040458040b0b44004558002c441c06a8440303040107490481c03c601d00a04402483d40c80307858a03d0b041c4090b511507842100c084006008800920080b0384561040c1700d44007542694142c01001140c011001c4061940c076900d00341840c4403241c9007500c81c1c692140c00940d41d50704180000f051a4640d0320818141240d541d864100c0d100b0000d0700b4a401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 865044307 1250 865043057 865043063
    0x19050d08011401230301060c1b03030c4206060908070323150414010b0d060209040b0603041b0f1202010e13050906160e090402040c0908100e011503020d 67
    0x14a000d04100440520304030000d131100904c3c1151603603110800174016000581003900c0c81b840d030a030707842800d0f10f101d4900002d1b42d0307150b5500a0a95500d917500100f0480c111a020640380c046c004281e020350340260003810710020046841c0c06040e1b0001c8820403140c550700001c1c204294000b0520203041d0018059007201d6000210768450024a440c150100b4110305210405003d07811010700b108051580c0c4601850080c0c2ca181003003090b2190407800c03a42e5442d00140c00c21664194031020a02542c003401d074400300500f0200c0c41d00c0c0410001809039104171011507a841c1202040c000070082e00008001419100b03c038107184d01e0a000014810292100b00281086124555100303e41c0740c80c5190110310701e46107030a101d00d09001d030081c0d032a2101100c9403040002041280c0101e40d00c00c8610002c3d5000c00b61031540079464503020b1002234040800100140110300100140b581010842c3d1f29150255150000306a162817134090300f5985112401c56002440210a1003da80c6840901da0010340c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 865045557 1250 865044307 865044317
    0x21911070e010314070e13031403010509040204091104090602070b0106030b060d0e01021209210f070b06040e25060e01050f0d061a040302040f02041d1819050d08011401 74
    0x800c24103141c81c040d0b05800540489058205214082e1f400f48140309901d071203500c42c45000340712501d0b2103a0a020034030a5a074040000000305016041c9544800003290142140b41003c0543e480801c099401c006400c0740e025600141c580140600d004540b800b400315841c041c440d4545120004529001c4d041c030b83c0030501c0d924411490317410001d44c11170729080509003904141d46072503501c054440c0c4404100c0556680484d4009082829081c1202c000310714035151941030009030345503804050b000510150304a42e43c0c89a80c1120b40d020010549104104084a17001902010341c4c10320740300140e4440d1080c030200d118500c0306607030414151038010030520342d1151500a08808200980181e40c0403415034004640d0704401e035221031006105a034000d460903c13049072540f07003c01c02c902c02e510811042c1894084202c4005a1070b100c5250000c10580c4055002030841034a142030036841038004913075495906102c010881c0a00a03520290302508040c440d030b40c900144003860900206640381046 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 865046807 1250 865045557 865045583
    0x40b010c08040b070311071a0313020312040e0a050903042715051003021206101701032d0c090207240605040b06070201080609070504080745050a090204021911070e0103 74
    0x20702b007800411200d40041c1101c10002c00c40e2907500a41c5d0040c0580c800321056000020000ca07080d01540d402011001c000707600c3d00f0b2a140038a91b160384071015100c000d452820080a9100c040c0c00740750316090300b42c0d0181380803501c1c290030004031084ca124010b003818010300c00e80102a00c0c030040c20703500c10001d841d19a5401c40b20759040700d8040c0705a00340444a090100007005000038000180c040314003182c1515004982c042000d5103501c411100188040c48220741030054890540141c000c0340e124102c4c41d1040700ca41c8005c2c90502c00d030168a000384542d0781c0401c0003d89801d005554202c40243c8400d8079100480d0002402190001d2020b8010358541e00810340540c403c81c200c40c010301150058610740d40e00c41e0038005007030705d81c0c1c0c0c42080d60842c43c41d48034070090505800c01c0700100003401c005c0184400315841c8805000004c00c6400d140340e6900e0800d01513200c80c001001a040c3c0d00c2041c1c00700107200c40018207501401c0341c40e00c8296000c032031f05000d20080000e07107d06403500440540404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 865048057 1250 865046807 865046821
    0x50d0b040212070c050c010e1f03020f0a21051920070605041b0803030f071806020a02040c0503060a031401110a0f0e011805040b010c08040b070311071a03 68
    0x1e4403410b81c08188060040081190b40d0340c0c460407010131984542c1c15148459040401125042c0c118071480c0c2d0700a20790043d40e001060340005810410f5840d08003d418003c0c84107070700041e034110485803008120107105442140c13406a489060700a11860100098108034a81b00ba61520503000380603219941c074500c1c40041000c100c100301844400790516075412007031070301e80c010f05010780b4112002c5400b0b0301720a0007101145002c1003903840d64802141140d840b29021800c94001401e02002c0c04075011400600d59a5499400040c0c0441c0d001000e02d0f0546206001c1104e1501041208114040c030070f003c440d50312146484202c0390001c2d080001c10101108803401000403000e058a402c80002e520308000340c0108104c00100744a031a0f066104182c0c1c4010360344044000c1c0804103110b52804240700c10316080e80300241944061511254195407035441c1c84040e403103500920300072a40851610f080551180320318018405e030501414207580340020751040301644c0c000e0302a00b20000300005140d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 865049307 1250 865048057 865048061
    0x80106050d09140303010b040306050f07052d04060503090c0a0503030414010302091e12010911090c1204060b0f01020106080a0327090504060b04150b222310050d0b04 73
    0x20b544003c2500d60f00c1d40c0d0741071250381c0c07070b0300500c41107400b6130520002030481e8044084407480340059072102d504c3e08018001411014600490052050507481000070500c0804006000a031070075031100f60b5607041c42480146000f02001603280305401c41c10023030000e920044180c1d4100c8606000c411003045001006030041e002e02010a900070a03c01d2041d23015906c3e2400301c0710942000d44486000842e954007a41c00d035020040040d1002c0501d04141410341444c1002d2503102038201c0c84039050004440d801c1041078402d803826200c03241c40ea003850040746441c201030050784200340000c00c9182c1c64401c0e900d4407100d10000180c24800e010087c03080c402500c00054841403100c8050081494440e260440181010b890a40c2c0c00741c80c064401c02c0d07505107489030f5030a061a0044d07a484a600e055030480080d40b000581d0352980d8090f2550b0a22801d03c54541d901030130201807190290300600090307804c1c41002d20a0319100352552119a202c0507000030031039281a0041c0004603d00403401c0100780 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 865050557 1250 865049307 865049333
    0x40c0c06020a092103170709050603070c0f0302070503011a0d15060b0d0203100f0e06102109050606040204270b09090c0f04060501020706200105040c03060507080106050d09 76
    0x2203e2910f90003011030a130056150390300c80e2080e12201d000a10035410140740303104c212050408145401001c3c0042d10300038010310350000d018548001400e03100d9549c102c9800c58814100c01507401a401404035107002c0c01a01c04a05016800140803a100400204031030074011010b404418410841c0c180740315581c000b0b00240080f4045141e8075544190303a0002948219207040e4050000400031900610002c0340744121a860603500d1403d03140c580c1006000c241d0304080506010310180301d075500c00302c0b0000080c2c6406c444074000030004075500301681810002002d02e44950310400040c4441e104c08010002d0049003100c4005040f102c6210290007044100ca03001e902c5075440b410041c1c06600040c840d000b802007030300e0290002c005d40b4240004e44006001c6c070750150700000f6017400381612444070307103d0100742041c020103204136541d10242100c03400c3d0380954200042c0c0e501030051204500415804c04d9081c0b60406035907141610041860145805290321542ca07050f08000f44400d10340070903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 865051807 1250 865050557 865050569
    0x70b160b100e012c0105010f0806031e0c0102011a090f192c070509130201030603170405011b0f0308280219020604020303071119090b0f040c0c06020a09 67
    0x1161561104d600c0740e15400310204000070680c07448048a03000d004995500c0c12a103044e16101c1c4181311500c800e4803174100c01480290180704011070065403ca00c281d40d50340300326104000d0800721480c04002402c0d104808203101c207121554501200a468500131507602c0040f00c1c490641a0302e130285038903010020501c6e501085814043c00d40748104807080c0308205001900c400c4001541d824400940702e4601e0300c501603016000b800099218900c0c42d8600c828907105140014003a5203c0d500c00c0b0102074034406481156601040c148182e50f0011041a580984c4c1040c1c1d6071120710b159984807440c0c8424400508011040c0b0106212001c00e843c0381f45450841c4481180d19050041c3d400d000350414240060081c5503540382141041c0081b481d14002c0b500034000d9441e2451036200d81810198026110307030401c00381c51107040d010450030801405131541c18404150050344104006610409103110b901c12403508a0214141e84c03c2519090515404600582c90744941602541c018169602074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 865053057 1250 865051807 865051829
    0x903050a0503190c05060c03090a0203030408060f10151209020603090d0206071103090d02030304030b040f0c0504020c0d12020c0a03020709111306050d1104030b09070b160b10 77
    0x581088030200c007524050b589a402009800a0f04030101c1c0e4035800e94a000d8010b0b0000b1010820421246004540c44903120302127400c04c2c102c03a400320b86513a1065218101e280c0040080c0036502100107651074100c80c0400300c181c441800d000c00112840f03092507a580501070942c0c60b0240400050308400f007001c0c0c00801d0b40b621791511140d61038403208034005560041c01000009900c290090800b0030000c1c880e80011401c1400c0c0006002210000c0703401070b6490720083c04000300140c54815081d02c1740c1e101c6c3d0454040300c01240351002c0d050340507410013803080780103000c00310b0b2844001515059001040c60000708080e200580480248950706101c0c400f4001d90041c001410b070009041401c64250300000c01124001b507140b02e0300e074090f02000c25446507100c2000c00030140706901030001c603d82d40c0000a100d000d00c0e085642d82c0d03482a1b004444981044c800c001c0b1880c02805010003c050208090f4a05080ca416508406c0c40400c4001c124090002c0858030003c042071805000d40145040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 865054307 1250 865053057 865053073
    0xa0c0f06111201081605090606040f080d1e140901120501060e09150117090f0607030c1704022107090f0e21030a050a0b0a0306021903090206041203090305 68
    0x405030181d402100c24003058440b071000042c0761384000580078898005400f02400e081d040c5001c2010f054805450700341d10040900010800c0c00c1841ca000008000e0b0300010141e101d070611025020300307504559201c00b941801140d045254005c058504000551018681d8400300b80700141c501c050b50400903481c0d14500400031540c9504200384044242007140c400213981d4544403018182c03007000c541035000403400e030f01105640403001010b0f600040ca600640d60b10b0400c101e4150b1800364126039440000791180742016805400061014010348000b000368105c1c905038011501c0150b10400c0650030300006284460100b0091002c5005840510f200740404020f12012402803d04090403113a64000d41c810400c400400c107900141d01e0103030250080c02d5950b801000e4008020003860004025217800801c020380d0341e004031030000387d0310230500140c50b00c4803036444024402171428a2800d2510740380081015079198010341d02103914a403000040e0321a075240440d9403c1065000801c60303c82c15903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 865055557 1250 865054307 865054331
    0x306120a0501200c10050417070323071a0c0f04090507090e04050d08070507061d24010b070212071d10210309120b19050603030a0c0f06 60
    0x114034966480744811003810f0005140c0702070944030300112079009600c800c5c00341c1c0002c0004d40216500c43d0041c07000c01104080308001ca0380760b6100d030908400040300007907a8603010a40102ca40c2c8410102014603041500564039200600300440c50301090340d6180c0300144c03080b505441126100780012040f56200c5684000d402e003d04001d07503803480400d818240109440002d02c4182d407140380c1110092040c0807004205a54180300902704000f048410170440c808122103006d0381e07095444001640e29010503070f07016103003080c0400206401d1b607a00340286e44080404554110b0642d003001c40c03a00d984690510015628001e8640c203150140603003000051038203010801144084041c0714200700c0c41e52038110640c48189075004541020080b80c1c1040000900040520380603031190070802c1c89592903800116001030005011101856204100400003040c4c100505010182140034400b03400c0070f0300041c2d100d018502d041400c0202c030f000c0d02400d01c04807031009030070703680c009900f0490b10344004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 865056807 1250 865055557 865055561
    0x290a05040c08031c1d06130f06020414030f060702251a03010f0501090b04090b0a0314010e010e010c050a2d09090b01020714060912060709080d0e0d03050306120a0501 73
    0x40d10310412032501e80f00c011604001170590b03006140d44c10141c06595910f0a0980411303901da001942c0302c80c02001140c0028045100400141480000b51001c02d41903038109803500190400c07903a0a500880c0c02d01405030340000b5200d145c62070b00c050401c040810002d4442000304690701c441910917483d2030740915200d1000c0210b0507078000780b8501d084140c48000540e040c035103d100e041081d000800041004841d41e600c001c0c3d400c81d0041050980341d959465210f100c00031a035491180765940d0311200c2031a1700c24402d442403400c058009200d0045071070341c003905601885081c6410302c25031000202c14206001c440d00a01c40c0c550594207240155540c000f802d0302064015031403454902803540c1420360001540703604039500c14000240fa2008007041c44680c2d00500025900000000c40000350f5900c148000e07442001d81c2d588068100f8500136006145c09100c445c0841030010040c2038034003036103411a41e403a1b101e8150500d56035988980021074003501c108a03003100613008941100c01004419 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 865058057 1250 865056807 865056847
    0x30a0204051e1008031204020d060c0807181a0a05160317010e0f0402060f040506030a090b060901060e01030b1f02010c090801020906091002070e13290a05040c0803 72
    0x4002842c416030700d0240b901100e2580c0d0088002c2540103014102083c00701c071505d10b0b440380c4050075090740303016955102010383d40c46d0443c1c41d01042150080045007544001280c103140f0440c100d08045510341005580038680311055443c1350f250000e50496500c0c0103004540c032000300c0403000b584450413420001d0070306071101d0003d8500d805000000444e044126042401030b600c0c0740500c00706494030b9003009030641c0445259080d001c414400012940da07002c01652242c0107001003c5440641494084009200180b802e03101e0000c060052043c15400001000190801c0c280026520a81400201458180c030018030740200c90800386e144d0960706410210114440781c5400c0301554580360124280c2c001e900b1010b41107107041c414015241b400130560721203075101e80184d0301e11036181e00903504020011688a03000d11100e500f0358080080b50a05031003051301d400c2d103a40c00c01e4802c0314841c002c1c05011b800c09000a85aa02060900c603010807100003c1840c10112a82c1e06000030b054000a044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 865059307 1250 865058057 865058101
    0x717190c02132304052a1c0b04060e01180f0605010509071202031801180b09070f050d020103141005040b060702010906050f0409061d1f14030a020405 66
    0xc0b07201582c1064001e4051924850f031840310101003240c0039800040e408100030420b076072901c0360381d40c16841c0c603125085000c0302c9480b00380d881c070f9070070508002c0c0541e02c098085099002d5649162440110340c4003a0140c0d0016404030021412601100f000c6000d0080001a00e000a1098564600f0000b40e64007001c8400d101b00c4003400039a9840041058030b000444a0304c0100c2d030724030f9150900094550045500a03407005000d00c0b40003407595154215058019811041c01d4000e14082c24030a40f400282c3e4400c00702001040d50b1410100f442c0c01c0155148140c0d805492440d02c00811a8001d03007040c00c411142e5503c8800070301d0040a99440380e08030b403040e10b0080d854610704c51101e00f803910031195000c0c1c06854940c100c900d006000ca030681d220b03210160003000280008924080b00d40180c13401010b80480c0151070021801c100850140007502c1c840380001d4240401c9042c5c2c075840a00c0c000c80d00c84810100320200c1050120342040c0c040b15000354444d02d0101040341440742c400041c45d2000d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 865060557 1250 865059307 865059319
    0x90906090b042405060703030f05010b031f0602070b1b0d08150d0b310b010e0606130501032012090706080f0103020405040c0e0901060510030b060717190c02 69
    0x1c964074083c4802c80c0000084003075521103141071049081c010b005200c42c9210785000208100032140700e60072030f64207802c05452000f00000f070000c400a0381119041141c0302540b4078885a1615001a55a940070300c5400310a0070045003000328042601900e504180c0400141e030034645603040000c1c14000d00303c86c0345c10b010f0310000c3e1210140c01c2c110300403500c1d10b0303010407002140c0d02c070ac13088401c0800c203010380e0000b6090364051001308c26220811004540c0c1c0326000e124140d505002c2c030302d003d100c00141000c0c059401840800480301d6585c0681c802c0350b0003820005112400a10344144c039083e40300a1100742000003c07292020480030000c64410010a015a00d83c00c0e10b620040707030090b03002d6643d0700340d2900d044014001752400358402600310b846895080c5001c1c0d42ca6500c1411501c040301c20082c580d54480080055080420700c605404a95140c04c2280091510006403580600d0f0030203051301140007a03015152301d0110440c3d801e038800781800003003001c00300d40040c0040030b0b41e01e08a000d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 865061807 1250 865060557 865060571
    0x5010e0a02030f16050405062101020304020306221b09094d040f0912090e0c1e1e13060302160f0615060e240306010f090906090b04 58
    0x20f02c0100d04410203002e0b0407050f500c0e4620b04030400000d441c010380100e030b01801c50142080500509104102d0b465a014009a142d2409004150401e100240060340f03000360510000c0744880e183c0840d06420303a100340402c50649c01c01d01340880513180d0380c11100e20740307140001c0501440803495200700303d020601440da10310741403000c503d074040d507010b4401c1080c1c1c0f04004068a11140f90350000e42c1d4880301a1000803036002d85056801980c3d501074058944c3c030444540c04c0d820f03540c0030409001a201a0348159654248400540d505114003c440c122421000c180e4200c01083c00d801c4071844000c00520400b030018115000e0625800398001020510045600046550082c0259940030f2012400d8401403540c1e6201c0055000c0002e1040701c80d55075490008208400c0c1d00b91807809459580d0724948808802d005200780301004d16903644610809610102c900380004040701e600034001c0c41d0403000740c507a0354000d4803000c01034bc00c1170740158103101c00410390301c02035441307031022200855080c0421 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 865063057 1250 865061807 865061833
    0x10e090a061d1605030a02121c030b12010b0603130507080a0c17010e07030602091c2913030e1206040303202701050706021902060603070f2105010e0a0203 68
    0x3243d00e40c42030b00d400d0341106000303002503c1c104900168501000c0141c030640440b06076070703100c1a1544c400b000d010030341d42e0b00c6010032814860803c0300c042168100030445c444e03621000030068000102403200000d5035681190030000c040c0714440007402004105c0722100f000303203040140c441c2180151604003031904004030120105000b9145545040405070420300d085403907060207548040c607500e8000d000c14403a201c40785c0e6031080c0300c07610a01504040c820700344100c0b10b0510456a510340c02c60503000e003509101b8039050f051000210b29a060420000b8612620301244050500101c15001401010200028580c040d000040c5086440c0c0e080e1940c2c05041c0c0c080c0041d40280c400381114074442d02110b441907000d41d0321020038950b0504205041074101d0344d030402070340d00c22050000441103610b50421b00315010080c40d0741100e0103c002d0020641041003d6800e031180d4800c00038070358120f14200c3c4905400e4031240d003c440d0803600030720600c0c11000a40d95101100e2804038041c0c811100b0b09055 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 865064307 1250 865063057 865063093
    0x90c0803091c0309060f031d1f20090109120308150d120f020309040204060905100e1516020405040605040b0105040510050f031c08070801050405040803010e090a061d 73
    0xe070b541e05884840d00582040700031200f4180c0b801d848002e00d59151084901c001440a6081246185a0040410a070b00401c1c00e1402c203050b40d400000e4a0505403007021110f010081850461480b43c40c03603484002c45070040f100b400d001d60000c00c8124407420154181644204480c7c8640107001100e0701042c0b144c0c060015500d03040201030030b50800346078510301740c0d8032440d041058002d07a44102c9003050749601c0044c089034480d60060000c83d850007010400350a21520310b600315181402d18000491400c0c022030488003c1e42c1c4180c5451a000955038841c1d80710100022845030003400420451500e45070810042100365020b940700f24001c4000100c614090007610302c1504401d4010b60074034500400c1c000100c1309030703000303a5240c003c0a080024014148042c0ca0040036195038042481c2040340f0060022941030300310a0040d801c0004000206180780d0031641120713802180c409103940c85030400d50070301c0f4400600030000380c14480441004014156045644204481500d034880601a60300103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 865065557 1250 865064307 865064359
    0x1704061d0f01050f13030c090c110706050901080903070c030b180105161407080703050301050a0b0f03010e1e0702030a0e010206090c0609130e0a0614042004090c080309 74
    0xc005401003003621a000480c4c000340c030001e012520765014a60720b950360682c19200d590017140b02c80c2c0c0e88214000c040741d4081081c00c041d032100009070003494140100104036203d02050b19042c49140d00200c1c1040300e0407c00c031008540c03c40141c1c3e5446480740340c1441000425203503042c900f425034241280124061150318003031055074000c0711160600c24002d81c0c002410303e10308580300c641844600c0c082001c05000306040c074401d40e1001d640b50704107002c02211a8103038000100091050001298440729a82241d0564544156400460b41e82c0105e020202d52104804644400004140074070582c0000c00f809081401d41c0b25040503a00c40d000490f612030044501d0b11480d4494003241c00076061020040604d00c80c00b520391810185502c03d031034203030307100801808e04a510a00c01441440b01c688114030071418501c405a602c1d01b0b0903212110200400b54400440c0c070200b494040c03040da00d80c1d12410000744d0148010030443d540e022103039180d030824501c2a025400d510406070b04545a2200c40c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 865066807 1250 865065557 865065559
    0x509010c080103240f0e06091606181502010b030606011103030408031b04060e0102121207120b04090602070b0a0b1e06040509190c0206060a050d1704061d0f 69
    0x529686580c41e8401a501c0001c0c690030f41354542c0d070241d450700b00c1c2c502500c410700001000200354104002e621601d40900206004600e0308a6101480c1d100328084a000c22140c0d1844c001d4082c40501000c502d00c10900d5104540c110001050820515010b4002c0c2c4071000c002c43c00d562950352581c00549009000fa902070700182c0003000090005800301c0c004d960012148504141a44500c1300c00080c05e0303002ea04003001084580109054a41c0d0401207821105c5501c80207500700409207142211640c0e019010300280a002032055044111035030001c0d6102d4001130040c050307406281081030003503005820503142c0c0e550660000e00b2029040c082c9500c82980a404007040342002d4801001686501c4400359000c28104000130f05590780220313150060b034440811100741d80400c0c403c0301c220340030202d150040d0340101080101580d580d221070b40841d4010342e54401d9040b69842c001221034049903203094003500224020502d81c1d807100420004d41000300c4400a400d806408120300c40c0401d43e022 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 865068057 1250 865066807 865066817
    0xf081e25031a151317010e0d05070209060d120e04060503010212160306030b100503150615211008100209090411041e0c03060e0402030a02061b0313090509010c 70
    0x45a0b2070038561115540301189248050030f10910f07820130200e42129601c4038002007003518004046580078483d10507504440d4004040e0b2500c0040050035034080d080c0c02a1046041030001441034a1f050000381150b6400b40403206c10116810025180c070400483c40e601a40c5808008500c0381014070865484966000c0602042c1d41d40340c403103600a0030000304007401c064580340004002460889000d0260714a0204d101c180c03030400d01410b15025034141c540344c440c0381c2d50046c03205540700d21401040f203507651041d255030b58284400389002410480c000d400c0c40490740d010070202c541c030201d0f0b07402607550120907a440104d400154078140d00400d107802d60300001803400300d0002080081428a0b2183c05030000c60080003040c034280c1440e442403000c070102600c070725a042030343d03030302d440740002900242e51b62105500f05038000c00d581e034407003150090142c200002d1000c841510705d10070b2901c40c00403c040f030340d8540e103112041511000c0352056207181c604000c0456103e41042c002c04a01910903915 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 865069307 1250 865068057 865068101
    0x61734020d08270a08070807031407020a0302040527010b01020c0307032a18091b030317060307050d0819090b0a2a060603110108070f081e2503 63
    0x150082c080e1584200d00f51074851030700d0302c0b00061540e4000e8100e0328045d400d401c0d00c640c40c40c100130308550022424120700031010410000180d80310044c42c01903035015900011580e40700044100c80703c3c00103441500c120030729003c6104a00d8150041c0f1844002a82a510036242210604d0b59420042c08000c000c40121406c0300440b00f808402101180c90380e4088015003603a45c0111074035400b8083d041400c00c2c3d140c0c003a24043c412541c40c0c600c280010f8010400300d407803454900808500c600d1010400b03090200011410380d5800700041c5010b007a004041940c905542e14120301564807480c1091000c010038400b80071858018241d400031500110481c07071900c1c0c25032008031038007440c048032056400303a130850310030440d807600c9284c61010f80705842c00a031050860400c824945c21040e600350420030904100440581e101192000703c4c801820180c81c0398a514400108a00300c1454084000030284200709080801414250f0702190320003442c0b50052801500b102540d500206260500c845211 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 865070557 1250 865069307 865069351
    0xe0c09150a05150c0705030c010c02040b04020d020307020f100501150503060a08060c0403050c0301061a0c1507170a0c0e0d08041a1209030301061734020d08 69
    0x24068541000030700845545440d82d000616407100b0140b500800400800c141820301010410310f0043e03c422401803510000010000f46030880a09000780580d4865052080320748958040d00d16075054104159201e180510000399107126a4004861500c10040d60090405c035620406040c0c03840f0700382803950180a68000e031000d510182035a41c0080b00988001500442841450302a070502c1d609159254614208240b501982e207205034802d92424204001d9084c0402c2601e44120108141c10b48500482c4c0049050003080740407164603030300e940708101e400f540c04003002d0000c042008440d101c036140c02d030800040360681401e2901240c80424115542d1900ca00030341c20302803084604074501521490a9031800181002001400c40082500880a04a0b4441c00d80c0142884010360540d890b00600404c00b2295030005010800c011010400e880d03012030718004400316403071416102a139805d42c5044a000071717041e0400180540c9007074071a1107124020a900a10382c40512030391740e600c055 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 865071807 1250 865070557 865070581
    0x22030308070f090311060a02162301051206010c0c03060203040303020a1e0906050c160b03090601170c0d0c150806041803080c030907031a070206060402070312150513020d0e0c09 78
    0x20301f00e4150301c241c0c52503100c0e0042c491807880150001e074848008010300d14124410b048008c2d5103440c184103040c011502c4040300d0000311980200c2c02d182540103202d041c107080d17202e0401c581000e4000340c0004100024550540c000708601c020a658200d1203246542202c0510441100c2d00d0300000c11100d01000001e01c100054184a030901007038800b403400007846200a800c45600c885200f1402004001043c1010303c0114010800030921121101c00352503620703103d122600106100d0704c0e01c00a40c0051000030761015000d8031001d440d03090485888100074107401d104882e11445141489a46204001c0784070390080703a00d60548603e4800d80311618081c0090300005d1a042e00c81c401d111002010411600c000e01031008088094405801d02c4000241828802001d82d4040c40c01040f0400000f9408496034250011700c03000001c4d6448884040c0900000c01d0340800d600401c10304072050041182e070300808a2222a800030048000300300d048503260301c80b9002455101c403401b00011070108a41d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 865073057 1250 865071807 865071817
    0xe0a05060d150f0303110105090c1005030406150602061f0b0f0304111f081e070c111002010e011503020a30111c0b0a0222030308070f09031106 63
    0x2e032140c4071119448001c1c800e03803403507076510a50028501850741482d5000c2841060380240402c400b4002148000380071903185804201880100000080024203101035503001c0e00350f42c00c1d250a46c5960540d240d5000303650319816100002180003610744040e8a002d41400320007101c505524250810003451454503082d000248240c41d51a8005520740b007513034410710207001450f000101050322100034a4000c2c201e28000300003220b150086035401c0005901048171503841070039803600c400d07100c10a00e40034030f4602d100a10650801104900c1c5100e041d010342201d0b03a0460158000c100141c9581e0020241c0056032101a4124451081c207100000b00b020b80d10790b050444c822007a00b0180d042002c041d40200b40f0006840984451001d5459032070055001e21182c206401c1d0200034010310b85410075002d0001c0d00c0d5124440d40015480c88004480301c2030001c1020501255260507503034240170f024000112246070008618038407420741d181c060074440b8160b076002140c800211511400b0300000f6400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 865074307 1250 865073057 865073081
    0x105070206071d041410080a020d0f05010f06170f0102090609010e030f0a03200105060907030c090e0c04080f0706090e0c0412061505030307020f0d14100c0e0a05060d 73
    0x201210f0700c2d015480382d015203d1603050700e0f00c07124840d01c0c00b402c2d090360100d5503412800440d007041d210070000da9221205850041c1d0000b20101602c072081c507029004000b0301103120682402d011000500822000c04804851300c54402e480700b90000b645240d00301d03c115040e190340048103000c0505103500c24041c1c0d40c40c2d290094100c40150140103042c0c0c1c0b030070340880811000661440e610508041280b10046a0916144001d01403424580001400d688000300810105960b8a03a840740f00c62181c01900001d044108010701d46045c041c941d1100303584580100001ca100d284070b204209880001c007502110442c1c0c2c0c55082003820301010300c50030040901000720b868810b1001040c80d0740720200a44001c3d101d1800000d5100d01c00c00030031208080d0b45c4c803192003508148034980c050380705c2403a0001c00c55011198180110304c07528010381450484c004034011489944100fa0f450051030b4000d68107030040d5110302c1165a0b88000308034414078035000e03ca80000d018850840c8001d801e070091120000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 865075557 1250 865074307 865074347
    0xe030a210608030c0309030d1403070e03071d090105130c1e0f0803130803041a0d0608030f0c060f040807110a18020403170c030a12241403010507020607 67
    0x2e91a8040e0b407554120203545002c0e03030800203001e040d500c2d003041401e000e1420307802c0295428030f283d40100d6041c000103004c242802800e5544c1440d5680c20700c0010050300b440d1100c2a44020180c01103140f8020031103030500d0b198a8007020070300311140b40240e80030150340031003d95100f80c00c040f00201150244504209015441d00780484d1b400300600d0100080c01d81d45004680b103201381010340c2184001c690003002c454004120a0115200c40b44080c13404110007140c0d07558410222001c00c006141396403103403020f80400304851240303101e508000d200c1d07500014120784040d200d610101d219501e050f90f00070020941007005000050480d541c220131800024902c80c00b581d521004403114440381002c04d0621a40003c042c0300308440a00c40d0044000012016030130008840b1241e592031244c4c1078500280015160800307100746030354110700810402c4a409002001c00c400708168007840e03030302640300b40d01624456505030303040500c10340303100c0c5800d680281070f40c1d00c5900e415641c88001544600d0400c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 865076807 1250 865075557 865075559
    0x50405030d0f030c080c0901031104180203040b010b0a0206060f0f31051006050313062a080f0708070e0a0f0801051014040b06121305010e030a2106 65
    0xa80d0500604104480c1a107541da04060740c104000c04403000301040c02e0034021014203001c4203a10f0307041031300c0034400d080c2030000d5060309440310f01990380105d50081c5020f003050706080c40b21442a801071809030784a50701840147e6240d038040c0605004d4900c4007001a4460400603a032031401c025000e0344d0751000b4000703805d000480c1012030343c0c688484407010104001a04003191391403901c040c0e11480b0703078140001c10440c140614980100c1c0308510031082085030100c0498041611a1921409a03070703c1101003080e0015424454641700031402107041f06803080d0040da00c01c07030150b0800792250040c3e0141c5101c03a0755105040d0b0b031000c03020b400c0c48100010080048003d8607924040c03805000799130040e00e030301e42c94810083d0035100020003041d080c218100080000c61090080403410300310440d004600031165801080b40c5010351a04030b03840182c000c06025900d4140454854001d008800074000d00401c0b41c04203507a440380804910004a48080840a8488042e16925800d8506901150407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 865078057 1250 865076807 865076809
    0xe070c0f0204051311011713060e101b03050f13060608030a020105161103040303110c101701090608030a030506190602070608011e0e090f240a0504081603050405 71
    0x8070011180c5807161a015081c800c01d02c804c10522802c48442440c048180500c0d209801c41d80d0302c1f003d8052404540c41003000c0e0100300054010003502c0340081c0413100640f94903902074010384003035914400c01c0ca21040312031056510078020701d8801c8130911889182915402408000703c008114140c0d2265560701d408121130009000034403204990f64004039a90400c0790818030454292282c07041805004040060385103804419142220380600f8440b10800084101c0c600f819428030940c2c1e4000c510012920540b50416040c81281c40c18040c0c241c00707070381c82d50b81503411215a07001c0e1004580c010710400041c10b2190708281c0c0e04c20b074040c140c40003140e01040d080745207107469000130b03000d600801014402180d0210380140100919035003036044141100501d0f0000c8524043d05004054400000340c016104001c60920b6142503011038800c1140c1c54100d0541c4001c1c106a248103a00700d4004c904d0050320f034040c0324003039604031604a10304a096010f580c5080c901c01c600300c0c00d1040500c800102 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 865079307 1250 865078057 865078061
    0x20d0203120f04090e0c011e03110d0e0f0c1f02010212010b071709130e0a050601180e03040308090d0c0f06080703050c0a1e09032103060f0e070c0f0204 67
    0x30060120703869901c650400003070310195810381280320640e6001d070100b40c036540e900c222002340c8058070f60312a00d01d1500c0c040f030071000340ca00707401c9501039444005031040071200c00354000111806003a06030b500a404504c000c9865803d40c1203100e0b07000d003081c12080c0000b00074019024a100c00d5000051a00300c20b082c0d0065211003d038404c8004640100700c2c01c0a1101d056903980303900b030401c80b0482c503110701c000c0024500700490b5206100769544403061a2541810003520700c040b03404c001110015a5106405c0500c000a03d95003605181007c4062211500c000140d509230f03030744806014141501030703003400002c000e03c40095031004178598002a00d2400d000c03400c1c018003942e0b42d410f80302e8501054040c040d104058142c0440b04800c010644d021980400030950301c114250304200260b54000045501c0c00968001a0038181c00b00000f04c0080b49050f0400c0200c410307900d042c13101d81c1e035558503042d08031020b12460008009240005640610640d03803001e0b800e200d030703030040150b5402da004541 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 865080557 1250 865079307 865079317
    0x80d0f030e0118050c030d080408121504021204020a291e0c01060305120705060610031b0201090b131203110d020c0a02040f0c09170a120504090f02031003020d020312 73
    0x15117030000c00f40d0300b0301ca09040c0100c1d51010b41c2401c02040a08160703681208612846d03242e01e921801081c082b90140104214407aa40c1c40024003e54548040b00c14581d855a0162000c070b1007000010400240c034016411402c858440c2c44040c1c860140000d9102e00d03a50703201c150000d0b0200342c00303120b1070035000009004c1c121004c0f081000041107030561030300700d1070242600310b80c1280000521440c0002440000c83c0d551180c4107460000d10603d104206801908a0300d1600113000303090203550b02c405a0550110b00c2090141c0d2009000e07894000d205203910325200405818404c00528058005020760010f164612544684514000d541d03045070049800800f0702078626007011408c0c60542c9002d0280141840e004c00042000e1182c1c071038007a014090511488050403084100c0001c1d071072091140e154040d4010005046410000c5001070480c0d10501500d0308441c5098100c0e1081c01082c400e50f03101c1d01c0c1e507040c0c101c0f0b55401c5808001101c03907140c2089070f02d40310312211100c51320b040c200508 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 865081807 1250 865080557 865080563
    0x20306070203030712020403111002070902040b0909060906010c14121306200c010f2003040e0a0204030f150219020105060301060b0f0904020313050f0a0b01080d0f030e0118 76
    0x50f46074201140300600810803980700c103110900520051000c0b9045a442c18002401220020149029040c06a081107070603400000107a10210b400100b0f010360358001c100d025011210491152740d010104016041c0c10303100c140c0025442c1e50303002c0024000040e51021042144125540c181300c2e11001680c0c0c0e401600303e10019900782c0c908100664000060a174001c500c014400380c003000950780a503440031000500da0400012040701c9003c41d008006003600300310038440030182c50324a021450b903a54414072403000001c14150014001014920a03682a0380c0d1200e01001850391a0300c5035202e03036080d00c40d10000d5503403c002ca0920f40c5050410f10080c11129000407841e894001d08143c00c668095200c018024020000d03031110381c00001c100c0f0000081100d00507103d4031400f0b00c1c0300680e065070b02c0c0146180300300e007207000940000040e412001d52141c1d1140c40076a894010141e241c06900b9904004103280301d141c54600c50080c3c00111010140c6000025060f0240d41c1001100c111b071031040d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 865083057 1250 865081807 865081813
    0x31104090f0f06061d0603060a050a0209150301060207050d05030a0e18090c030c03010c1e0207051203040e01170303071218080301080f0601050a03080a120f02030f06011103090603130203060702 85
    0x4005c00c5181c005c050b44a4922504010300505d0030101094807500000c3c01da111003a44c0310300244403850035a040e5030071002c01803c50098213120350b01003882ca90027030180101502c1400000a114a01507a80000499000001d50708240f05010180c6410001c1003600381d0118a11306100084840c031000c26109001d118010030b882c4001c2414142070920114030180a42d050024000e4100e8100d40e0b00305090b900c03688020144481c00c841207041c8031503900031541c040e00f60f0311000b01c01c04000000c0c00a0303444c400c4071100c046e60307115195841e02c40700000241440e0414070000300c40500880038940116016007000c150340d18107404015a903074040400320350094001c801401040001c01001c50075542d0000141042e5043c100024803000745440001c00c19000082c510f540c0501c90529460180da000c0401d01a00e05000096000780d002101c05143d080d0202c00010390075840748003071805900f9400701844c90f244542013403010720780c0f00030030820418149003810001a102000454030070b80140d030107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 865084307 1250 865083057 865083059
    0x8090612091b030607091e03080325020d12180503030c0711030c0d0803040302030f0f042409091a10020105071e050f0d2a090503010501031104090f0f0606 68
    0x80701c0c0d140b4488401540280e00813420001c41d150040ea01d14159440980f8050008540300480c4c3e10083c0302c0d4100812002010042c0101c0002c007485420500b81c0410310003100d82208103049070380300340107001c10001442a200600d41009030b5803101d004480ca0316500003031821940c90b0640703140d1055a15541c901400682070040c030a91100c180407550044010704150050400002c002c4280321101500380340340040410200b600070000c0f80d07854692582c40365150a84540c00107102d0704a40319002c030809405507160102290401039000c0b038065a1a21407015090030380e008000d1404600b02c034850a44041451803507500c22181e40c05118103940041810320b000240142500d4212078101240b5040c080c14096298010301541c400d215103d0b8419101c0d45844130510141180e1681080e200f4040c0900c49004009000c40855810054442c14207071540e5000b03050888030248400790203c101d110841394507242582000d24034500803014010380702c0b015110400105403052044984e541e903000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 865085557 1250 865084307 865084333
    0x90f08030610080c04030809211c08040302071701090501090c03060b060c0a0305070606051e2d04020706020c070902030f0601031107060c090b0a030e0601080703050a0809061209 78
    0x10580080c04407624000340c0c01e0815403002c044c2c43c016804014008000802e48030a980c84050219014440b0005184101e81000380f12903203400340602c01c072203404c104c2400703824128012901d0341e0117258075a008000c40307498007515900041d02d80e07200081311354032003500602140c002d000f0214880d00800d0042c105a245103420701c00c486042800600514040c4914501c23020301080d400b081d44d41604100e2f03540c06441c98010001d0901350407082d8401441d1701051911111480d25000d40582601c80d088965001810300d03802440340552001c1036040c454141d61a03047c50740242c040c0c14440c0c00b01504280c7c07102c2d03106003428490307045aa11558044200070050304d0f80c1a820b81c000c8803e08080000d00c080d0821540e0034071a84901408454585ca017000403584100c01010040c0b0004202c3c584919480f5801009007c60620080561042c4400403d02e05000308480c403c0ba60720200514501c84140c0e1395001c15045035982651107103044c810161855154521107200c2d10000c1c010b00358a00d10b0f25 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 865086807 1250 865085557 865085569
    0x170106080d0207030809060702041d060a05130f02030709050916240806120303070309020108100501020607140d060b04180c05090607020a051305060108150d1203090f080306 76
    0x240c4282034903800030700000e030300640224001082d01e402c12041a034918040c400316000b441010320080d009407901e0050000d8044400705460011811320655140c1d4030b03006c07051001c0d220151520780c07080d551643c0d488001111050312419607031019040da24220358440013070b01210300840702000d03582c001c00e90a610401107891601c0c0601031060702240000c03030411681c8240e460b11064542071200c20b8001c50096540e245600860340c0810b01265076030b15050400501516006404901060071741012580d01d02d01100700105503081030303000300041d43d66100116135110031108680103c010801c24102010341d03c1c0140800342148004c0a5501c514050300d409a00107443c98440409281010b01c40d0903d500c0301c01c84016031011580151a11440d000180b02c0b4041640b05981c0b00818a00042908030103812441c401c00003620340b1256076596a60800b042c40002075010f90110100754414001740541d09580c06550701480c002a00010940d1129030b49403006c1c40648000d040407040100b03600c2e0038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 865088057 1250 865086807 865086809
    0x118050a1703160305090109050706031d0309030604230a0b070f0813231608070f4202070807150c0204090f020d060e060a05040218061504170106 64
    0x440061a5103402030301c11035400c8101c40f6100c200350315074010515100e425003000200075005029100310564900015004205809000c003419014101301d00c001000401990484070001d80079194a941d90303030b558401105800e10030310426440c7c030080501a03108019151255100b01c10050541c10176042c0900440310440c0380204000e0014204026050344812460b0798030340c4500d01c4603e2885065460713048030321024450307a803803040c00000c600c101d000c1c00401c2c0c1100c40d081c00355a41503403160900306200500740a601c400080400002c00070705111010a040011704283e00c115001005030f5445044101710044001130344040414054a00c05115450082c8403035181c40d0f58098005a0140c10020050006072080d592550b0150910259601c000308c240d80c0203044040e485000d282030f100405100c6a0070fa040d1041e00001400c0260030300c40c85028a40040c402d407045c4010071003000c00c0c81c0d001813156401071050600b4030102a00400500302400b01743d41c3e885034a01264040d00e00f19002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 865089307 1250 865088057 865088093
    0xc0a060209090f06100e2719050606032e030609030e03061b0c01020f0c0d03050109050121030341070903080d0b130f0b04060b0910020118050a 63
    0x11403414800c04d036860111031a045445030502c424951007660000e4000ca0908680309040881c80c0340c0102091241e1121521503880d018044c2200c0510060a0040b11012114141c10a030108046148065004c18028a41400786c0ba0b40c0c2c1c10300819403880100781301d42e40c401c807403050700c40300060205501f240302c1c0c62040405078000c0c20103242100c0301c0f1002c40e80100d002103480c0400a00c108200f0000c0d0126200c151080f141035980f1041d4185583da035511502d6503100080c50310340081920303445805041d0488903103941c81c0581007018100c001101c1403a910860074186e4030040c02560000903015107845648070016680c1000445080c400d07002c4c61044892510024032003006013154010b03030703000b040d2500b0010320350f141c00a000e030b070360b0040000d44041c0713600514407084040c1550305074002c8940c4008182090040c22500414401030384c0c0b140c042c403e59924140803681d21424510072664082d081c071b2001281654041414121b03244822001f501c0ca034200b00341c00c10901c0387d8902040380c1e40b0301c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 865090557 1250 865089307 865089331
    0x613110d11010e041109011d030d0207170d0c03030b0111120c010f051b07020a0b0d1505100207060503070c0b090f0f1c0309020f030d1701091109060702060c0a06020909 74
    0x40c1031004101c0901c00c0301401d07814411502303811000030041155001100300c0280456a0b0650514000303035171800e0328810f004d800d024104401480c4807011079880b08a84c00740e1500304040010356000c1d00504200e481081c1080030001010350b000c6400c005081c1c0d90250460030344d9a880a01071554295444038044440c01414403003441440c260440b00d800143d01102d01d06500c0e07202a2001810641c255070041a000d40701280080c20701d50b1690040701680310325043c04e1a92941d800602c800384ca8240702100142c0c0060f242040b50f1401000215442020f03031804580340c003400e903a4500c0c202020744207195241d10084420000000401448684511140080030a0b811110140007030100210300d00c4209a02c90540000719200c2c1c0812010307048004003610008074580e4802040ba5245140d050080a008800000e1040c002d2241550b007004450405140c0141d00e0309014a5600c0f0084c100e0b0400c104018024203520b040c4103c01c18948500d101580c0c9100c0710040282c042005042c8d80c01c901 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 865091807 1250 865090557 865090571
    0x2a06030b030313120203010b0303030f0709050103060e130c080a0c0518010f0b07170c06070207050105090303070803090a1b06020c1c060509010e070620030a020613110d11010e04 78
    0x100503180901191a0311144c508120300d54808a800340c08641038080e0544004000d102000b41c800e201c0900c6050640e0b0340c1440a40d07218011070541da13040c495100090041d4001c60785541e00044032240300c9011b5200311012960382c0b0f18452500c1c40c1031105949400f54020180043d20300264150080003121110003e1541815000200c0c1c0005108000c058000007030a441041b4103903501507020125407070244c2d1108103080480d40c036484203c0b0b4640040c01100000300e1315602680c15a08415000b40c0150b09000440d983c0031078507030028100b07290b0351050400c040000b820301c400d40710010703011000000c0c00d540f4255000e0700e8000d907614003500c5240610320398004d0103040001c401c40103410000c080388071f850f20400c150051580c0201c4090f60f000d8103001092042d082040403150000d4034508104a0303c000c242c0c203459000e40c0c54503900681011012480013a080800d04140600500e04c071b0001c822100001541c004002400301c400d442807088007522036810402c003031a402d2050b0380074401c0c0c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 865093057 1250 865091807 865091827
    0x2040f151d0109020901050f07050f1501052d0d020d02060a0216080f100902010c06151404091e050312090715050c10051801060306050a0c050408192a06030b0303 71
    0x150007505000388001c48d010030803d040c00700411001ea04200d100381594926140f0310000074600d0030900540c3e005005181110b0b070994551401c0300540e81c51141d5040ca90501d10040200701d159900c400c3c1c0c0c1c085542e050401c0980d031441c000f008800101d03001000f00106101c003010003111241c0c030503000342c8c004040342c40d14030030003007030044660f80342e01030001c0c183c401c920050399a848208000341c0708500d00304503500c210201c03e1036401901e040c007403070040b21a00380d0100010b40d00c0b00704008020109000315090240a030391405601c3c58494030540c1c3c14003550f0b488440005000b142c803a107243c0e12580042221000781160f0a061803103916200c2e1501d0b42001441d035449210402d200003450303603030380080d07421a4580c82c2104850141301c02030060f6641ca0500c0c4000e85829a4203c41a5140181604820340168125000c0b0350b015006000782507800e5064881e03905961405850124040c04500c1c000709410526070300c00f004007011080400d00380b000007001c4500a1142c180a03034030030444600300c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 865094307 1250 865093057 865093067
    0x601021c05030c0c06090a02040614010c020904030917070504150602030a0807050405100e030c0a0f06030f11040806070206090708100e0316030c1e0206040302040f151d0109020901 79
    0x1000268245169243c86000520240f4442d0031080301c0140076500a0200e1100301040440c0d1082c021541400f0071511000b8203003014101700d45960205a8850143d00182040343da41e0764014040c2c10032601c0b541c0c1d0741a503200166968094080207030803003d8140316520701445080020402c030040b131824035003045800b96581c40f07009010741c14407012900091819100b50b04880281201400d50a0070651b8904080d101361100d00c2424030a010784416807009080036000d180440709642040e110340d915003c0c0035001000c01100b00b490454450f85c426400c80c0d445001070000305040c070024011450012002410b100300034090b11010380146804200004001410000600007480002840c00070f8052051452080c0341c2e018400d141c070780e031504080c1900113003008103103409225041489011444078080c007507101c0800a62154060100740701504040e480300803416000000000c140007011030081c00c5000d04da00890000081c0e61200c0c0b006801014050f004120b40041941805054400600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 865095557 1250 865094307 865094353
    0x20901030c240c020d020a0302060a0309030306121119091401090f090507230411040807082a060909010f081203100b0304021512062107050f03030c0303011d060102 72
    0x205c80c44880341070a041d9951000c0c41e40096600030111750340c0b40400c2030043c02901a150094010070f207490300020703400006010b01c52500d40e00a032080501d42c40441000524040382000044086032100c0125180020344210504c0000d041d540e2031a81d85004001c00c1500c0b59091208011400e1110b88000160001060b4040c2c80d00c661910440640203509809646108051268018103001e586500703100004000c000342e031460000e0341caa60391901c9145030b841445c0040801d12104201030701d00140d030071141d011f1036090004c2c08146420803080000e03103012000c2e00700d1000682107035002c00148000700000003424100c042040d0071450320010f007484402107446410440b000000c005030455641262405600c42503000e4180c80b842800b006280c040c40498505004030a030141c640310b0341c5081603060100c50031100003400c0007400d110921520500e038070080d1f1b40500c02400090f018030024000346000e444050150a441010050070030000d181c090021415500104805d5100e1103132900c40d11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 865096807 1250 865095557 865095559
    0x12091b0d020d0b0c1c02180a150806012106082127030607110c060c0c130e010905012408030406031503020411030703110301050607110d020901030c240c02 68
    0xf40e00750350346049110f280c8a2140701c083d1511030301c0d210801ca00002c1d4044d0200c5042680840401d04881040c810400803a01420031805e55141070106504e02c07505509a0101c410f140815001400000190070741d623003c0700382c40090703485401c02c0c040380c902000301841d07021409045e052281c0c000008900c182c401c3c428125020500e190f85080844080140b0400ca0b61300982102e5140c503250320001e208c003507002e6400482e801400b10a48503842d00070250391800c51141e0282c040c000e178650070442c110aa5041c0201c41a44840e8000050903007840f0b880c0c0254082e000105007e109084480d0f4000c00c0c03222648e803092130000b414000c00d40d00100355400da4217181000515090724540b1400341d44000d03840294882c1c04c110000820700c0301c4001a6005200e00e840038043c0c10056032440c01280002d01541d90098014820131010031a441c01c80c00c08418040e00c0340465012031340100f0f00c521401d0700103440707001001a041001070041840c003400e410804045185e695403001b002000720b08844806 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 865098057 1250 865096807 865096823
    0x20307020127320303010e1e010909051e01021b0714010c06020903011b200d20061006110303010501082412011d1501061412091b0d020d 60
    0x41c020085200070b10600e001c0f00000d1585500d11075505542d40e41c800d002e46c0d1902c00118000c228100300c41003241110000801c031300303c22603007801708007030040551a4054602e03102d995100155051902060b04000010100251380e40c60b605240c0752501c001c5404d01078241e0b102d580b08100078080c0708000d030407041c400d181000e135480481c200f0401078001c81e1002e50340f40d480c2c2403994a1490140d109408100c0d101e80301e116049061041c0913031040300c603485201091b00302c42200300c4464440c50344000c4815012071380c95051884181e580d031812034101ca14800303004482d00b00384076a03a0400e40300c00c0050355541c0103524544c100f00000b4080d00016015001d600010603030300c2c0302c1044507170707803c020540d0241c05045191244044c2c14042c042004401824045400601d89201000b04840712500c918004214880e4a400811038001c005040d903400c54540c144018a000c6080c00300017801803d188000300321404030f01048100c5201d421800c2440f070605c1403200c03001616060340b030300b8940b9005040303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 865099307 1250 865098057 865098083
    0x3c1401111b01050d0216020a0501050903060a0209041e141f1e080a0309470403170403050111090d060b120d1206050402071a06041e020307020127 64
    0x1a43e1901681046000650002c80c008400036400109004403e000f110400c8a480d9500010340300c5114803a07c15400d508400009105c190b5a034005041c0110b0140c0001803120b00000102500e8400d01140002d0b2604c7d500c0010110300a10304464001001e542020f0420403016200d100c0702d8110301c00c4a2105c0c0c5481c10311b100b0034990100090042c8402401c3e1200200f05160040031800300c0e01071360b4000102c0320810064044120141d240c401348000c41d0054858400d00241d203249000e01e4004c1d40c002d010800800001c680c00810030000d80040c1d002c1d0740700c50852510f24251502c071041c04044440030b00029030656580204a80c1643d0000070004450b00c25201080c0c01c40100c0e2101e40342489116000000b8a500403c60100300040c80002c0000c41d440781c040006074411500302824400c0007120369210303003103010206504200c000748000b40c68083e000c040040d084e00550200300342507001c400c00c121980c080c000c1c40c40d03803000d07610070300940003412010896182140001401e55026454 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 865100557 1250 865099307 865099309
    0x3100b0105120705030f010f270b04060f080c010c02010f080a06080708100e06100512010b030709051f0b0301090c050405190503070e010608013c1401111b 68
    0xb2582d00301e205080308041c5240440d800b8240390700a0b945d110b03444483c08000200c00996003280010b540444031018640040720805104088940c0301003c0456a1144003000585d80d503c0760340020100b00c03518a02c6a8540001c890038103050145403810f0150b042c02202c0180e0307200555a03031080c0107007000000c03510395039032410041c2152f4103c800c01c0e00c03d507140402c1c0d82c4070000c2c00c811a0140380301c05110b401c240c42e14954407a90150744001c01154248010b010600e00010030303095580740213000281031080280080d2610002da4082e201c00e40c1c0e50ba0601c9520b20103405081d843c0402030001a91241c03821800340003900c014810750b0115941c4945554483c2c1c41a012540200f40007454022520540c00c502c1000c0c070701c6881428070034407501c080015030304491040981292040e40743c0c031960784c2c6450301803403c482e11455070b00e0090f00700c0c81000784111402541c840b0a1040c03001424200c17420f100c03c01302d1030032031202c3d240e05010215101075010342c40084c0c1c040b04947c005010490020f2048 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 865101807 1250 865100557 865100567
    0x1209020604171005182e0b060f031005181902030c0705010501081006150f0e120a03080a06050607050307021917030a0e0f0f0405092401051e03100b01 66
    0x1010243c00e0742d080c001400105911031341c030104000c050206132500c110130305180c28584140f000401c08507030b036100702c1c0240404103a0b1040c2107410018082910f00095200c500c0980c6d070044901d6010030300c0500741400f141c107140b00b851080705070541c00c0380658103144140000c144046600e605001c0c0d0000300040125281005603664a54458000d20180d6103401c007090310750005002c0240060b2034680001041c092494541c03160f505152100c6403a94043d0308200d80f9488690b5805411090441804010306010802c840d44180a40e40c0c2c0780700c0e0b060028030042510000c3d8071079032040c1c2050248002080c000700c1290441c03541180c050720b08501c8000d48443d461096444041242d100c0d03961501d00441c0400100744130140c80c1d0303400c007804126004001100f00f42450464001240b10000021070505d0f5100d140c20004c4a004c640c8043c40c100c1e9018140c440099006940c0f030004070040055040041d100300080780300c0f01c00c550680c0c14100c046580c820708007900341d16080d140d4050815a034068 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 865103057 1250 865101807 865101823
    0x306141c1b030b0f0601030504030c080f040e15010e03010e0d03021303081209010e01110d09050c04150611010207083727060503161110090201120902060417 69
    0xa2420660340c55564146454924801c44828141131349480c00075007658881c3c0320761885103030306440d00b2070b40b400355032224011a0031222420150f070310100804608100f080130f0741480b6401d2000354140c02c2105400042c00110b0091502d40242c2c180b180c0003407012004200b03d14003000f24980140c0700c070318003034140e15210040c1d403002c0e125000019501440e010b03032859280c46180e813a0028019080d00014030760803128030f20710f040d07401d2000380600c0034440342c150410740b052800348013151210100c440026080751481d1a80024511111208221094000c120402d10028150085003042013540300d52420b48140705070159007254080303104055140664104070352181282c2d5000e24100b4034640039041d80c4000d581400c030000c07003084169911003e261610190703126552054119280c0f00c5260101101d01c03034800050094030104000b90704410805002007851028000c00c081200740005801c070310442a81180940c00c1940050258503004103d60407921210042100700544400050808200b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 865104307 1250 865103057 865103093
    0x1b0506130507030b01030530040e060607060c0e19050a170f0a0308010e01050904200d08030405011b0206010b07030c061d060402130b01090312170f070306141c 70
    0x13100c002100b80600022a01c02405c0d100d038001700881e1003c518200580940d440700e4040c1501008244003a0308102007840c0c20450181c80c00c1c0c00d140043c1d442006480c0354030304807000210107200307001e490320b442020301203070240381420310702e00608000106001040b18043c5807071800092040c001c01c1c0104000090364042d0b00410740307041c08001d15009084174000e10800c21280e80120001c50340749065440c16010365803082412481600900e1203804011108262035132004030407091001142142c40110b124500c1100005012000306034009110b2039540401c0045521840c0117014100000f000c031030900c0c2c0c1608017007801c21035a15005020304100e00c402c014082074842c800150010010b4124040c5108960301c2d070310710403e0702c030040480340d1b1604e895000038240e0404001140c40340c041d00401900710302c0c0c4400e80c0360b41c6410300c1803c103106440d1450f148803028100018203601d80b2403640507082d04030140d04d103214510b0010302041a28604100c41502001000c3d0820000e42c4504c900400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 865105557 1250 865104307 865104323
    0x31b0a0b130b30060105090405041b14040f1b030522080d0501051c080c010905190c05090f0f0a06050a060909051012080703021612031b050613050703 66
    0x94650780d942400001c42030f142d9500805450392850351000080f66124040c1a9207881c207010340c0c00300300f101800300070380180c0d002601d141b5010105070b0790010b4507001e019010121004901c51000b48011940c3c451282c980307152501e4003485c6812000014101d40d103c00e407401141c15141c401c1c10000d51010307040e4003901d806818403200c00300700c040740142407a001c003000c040099aa0340c07000c1c00400420040b5404400e440c1500c10000162070b20041d01032103203000d000080410b1341d6620742d860701c080c105120a00a1080810350200200b2507025000b4200a8921580600f01060005001c110140003004070848110004a50072204d41c0300d00024440203103110401c56031440054446845800f0b0443e070745040c00001101c003003501007048110340c401c0e05450411a000c0c0c0342d401c140c0d0000c0358100d045001e012a601c082240410a90001d0101c0c80360024480d01c0b903280161524001221a41c203045481071201c010940100c0c040358444411174003058401c8061620600300011504000c02c104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 865106807 1250 865105557 865105567
    0x60d020d1802041b050a1110090813080f0a06020c01140a050a0608061b13090f0c0306080c030c040e0a02090c030708010b04150c0c03050f010902031b0a0b130b 70
    0x107110070144001402a2400c20541c64103d03045001c03a807040c8501c2021600802c20400c0c0344d84078002c2c6028130f099901c2a9400904406840c0d4143c550318030003910419004a80d2032920b140e0003000900406038030008040000481c2c0000b0b03200c100092020307000170f0b404547c81080c5030003900504030311101c0c0b46070020030340340a14950005010540d000d1a9140c50150041400c040004c0d40030b014280c08582c1018214804280200c560b10000201c01e80c04115240041c0511903402214481850700c0400300307406440e580002c0441321164809540c0ea404001118100d86012031000310548003610085030440c0c2c0c4151075490140c0c00780c80250008402c408100e100d50a00002d1402840c242e900d0310310690b603480d0307034000034000c1d03018080e1090408a090942c080c080d81502190f00d20a9107000c041e1682c83c0c5820341062003064442042d65110b03101201107203020310040402401d14184030910101000210780c401c0709078058900003150000308844032101581039a0020801d1030b924030f550f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 865107913 1106 865106807 865106831
    0x90b0d1107050307050c151902010204170303100e070206070516020d06090b06040509100f0906020705282d0501020a051c020408070302060d020d 64
    0x129511880e0030203914050000e480158082d801a5495044c14109182041c940c4440c2d03038881c080c50450080c50062130b0302902c034010030b0540c00248134045680c003640240301e141c02c0001c010b16602c90b041890000040210701c14019082c0400e42c040c1c1e58484a00003640c240c80050260b044000007800c400e12610180c086a005454010002c41d4660041409000407500a480694481d1551010300c0400303002c41c5c1d004401034500300050301d4202c080030340307490075100900c0086840314400c0203000865040f200140350016806c642c0c420082c034026685480c0f000f540d00056284010003051000c89907a845009500020110904101030002c1d4403903d400080310340101504042c07107004100248040e0008000e00d88800e5607411144c40249002240305a642c0b4040340100000d03c070300c3e0710100740d01c011241e040d0340e8651190814011400a80104c5507440740c0145000c12850003 = true := by decide +kernel

theorem cover : BRFrame.Cov 864928057 865107913 := by
  have h0 := BRFrame.cov_init 864928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 864928057 ≤ n) (h2 : n < 865107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
