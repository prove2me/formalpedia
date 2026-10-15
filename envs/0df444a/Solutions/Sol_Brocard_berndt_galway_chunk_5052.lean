-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5052
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:35:11.590501+00:00
-- url     : https://prove2.me/submissions/7b6cd792-3006-469f-8b74-e41b7417f1e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 908453237 ≤ n < 908633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 908454487 1250 908453237 908453243
    0x4030f08010b0d020903070801060f0e0703090c090e0c0303031f12121803020312030f060901081c090518041a07090b5d0a020304030207080f030d0509010207 69
    0xb51524a1002d00c00b03001e034100000c65641030042d20000640078209210b060001c1065200901441d450060503003000b4000034001c20501d82841e404a002840108a62058808408000941c18103058009203042c0d1010001900341c403000081c058030035049409200148021071408104c40d85a0b00a40c0030500b8003840100081c550614520000d401010141110070304007426101c810307600c0c1c00080c030300f00c010004070154141c00030500c04074500c40c608850b40300b50240d4076100da0754940815980d80b00010200f40705046a1064602031440c443d406c41c2004001c01082103860b80d0301030300d180d80c840405480440380049a404286a603a0074054001e00c81d0005440d407140b80ca181402000703040d0712040c4d1300b8001100600e20307001a80384400301e038644010140b031040300140c6000103009a00340030803d4201136094110000103101041c003101703035008000d481d000d6100e850750301d0160728104058100030940d0042d10340c003001c1f00c0300000c040c05c9500030480040c885900c801160500300d00c90002c0213 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 908455737 1250 908454487 908454509
    0xd0c090b1c1103030d1e1a030c061608180108160806090408041706010918051b0f0907080603161412120a021c030b0105030115091a0304030f0801 64
    0x318021903111a044100705502405880c54020b491079941d044802040720f411b1102c528194005100840784100e8004101c0c0c140c505c0c55022010000170f5584038541c0c15544121800240700c5004050323010000e0a4652107460691101c1c014144501c0c2c4643d501c82c1c4a002400e4240000d4000305040195001c00e101030b2649501758a4050600901030310090098860041c100400035031102980351040030011800b0282501d54100501001a12014a03401081c82e00b0040000045140469200c0706400c0c6400c02d01d40040c0250040340700400c8180003158041d82c0c8004200031560031001e4248281d500724240c5014281c041140d100344101806020850203c1d40c2000080c1e0914840b00702601d840d040441c2c004240408055105034030020400005030090419560a100705040c000e0340381003281424441c0d903160000003801070005100b03e05030780b2a2007013003c02c41c0e0300031103403407001d0a801c030304801041c0701000342403105a00640d8110001200d058a1820b4144201400d41c140e802d61001c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 908456987 1250 908455737 908455789
    0xb0c16110d0803150109050402030c091c0606180f1a100201091202071d090a02010f0e10030b130e030f1e03070305180a0809010503150d0c090b 63
    0x50050040840d0424a4101d1003025084010410450140d403060a43c04003e0b440c58411100051400e041540000e0080b030040c0184100b00b081107051340c408020070307100030048a401e15812807102c11207010280500f890410040359119035142c000d510190003800034003d07140130751500d200710f030081e07030440141c0100c0400c003e803213207007090b4001c25508151002044140280c1c032108080600941140056403040030100000940d5101c90156014880302c00300403443d01c0902c0e191119242480241002100a50740c0aa14060940800305000241070015503503010b200140c010700308030302c0040c0314050309500512044014003a1801380f80940d0b01440c108412610740410a81080700b03c40e1100c6010140402c00311302c454003440c401c1160341d5020031982405a080e001414801592450b08e410426000000c142d02c0b20450310065020301e0013039501e565201148052230b00d8402e1031a4000d05c0030035141c0500120a6141b002d03515100c2c1d00f0060002c03020300704605400c8030245e5517442412900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 908458237 1250 908456987 908456993
    0x5121c05030601050c1618051e040206040f0902030604061e030213060515030a05070807090b1309020705010f0c030b010e0409080705060c0406140406080f1807120b0c16 74
    0x50742e00400c043c10140e0400d40200c00407030502c00403103111110702034600010130545620441c80c40703400e1b055110411580c01c1250310003c411721005020307616687c100001c503045403110301c1110300400044942d81000e940301c0801001030b51003696581c0c070072811f050000c43e5480c1000070103075640ca00c9000440e011071440c2d0034402da025141c020078007040c0c0d80d407a00054135101c00c81d26000d01a00000703541e980f4508074200c0c104584000e0203c80820415404000040c3d421440000a44103142e92840e100c90203407140c1c0d0905080398120344003150001c241c040811805411034908401c1084080c404a60304203821170480d00c9140b42580007400034004042c550400c0da00c40f003540b90082400d11f190a540e510303140e00c1d1030303011744403580c1c0410700040030003001e40d022052001003c3e00c280001d140c80c1ca0214020b0001d10040e0286880e04070300f9011510308000a464000c0c00c10100090310710321541e6081d209802c0c4109002580d958150314000307810840a402142c00c818041d003a0b803038a01040781c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 908459487 1250 908458237 908458247
    0x31911210a081b0d060512060610031a100c0309080607120902040906091b1a070201031a130c02070b0c03253c0305031f1d0105121c 58
    0xf40c400d518440e01c03801c8242d00d200361000201034003880c5a1010403600e1900081c4404417200045204e041c0d002402801095682d4032140c9500510628001c1070009101903e120a03140d92204c003644192801608100d6540240450380f4041c042e44820000e19a80e5606a0719a4002c41e60000013900d40d545683c00a03d00d58001300c1c03410b0002c0d20000d00140e00b0340d5072004a0320f5001c0203440307a247c19803207a00d15110500385040905440f1109a20030200d4400f00d04007402406002814580c0b10a50643d18000304a20f0001e001002080c065060400f0024080140079040d18000140103440000c94801090421189071103081c000451038401801030f00d4011034005030413407010035412150000810745214400d2005134214038140380c1c601c2e000d004003480210141141415400581c0e04002007604441580d520400051601c09094074030500e8103074800244d0054419510741400210503000c14011440c1680c90540365a812111000300b01c1d81d40380c80045400004a0403030a0302d0703040b14456 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 908460737 1250 908459487 908459491
    0x1061101060f0f1a0a0518040b220608070f1703191d01171f1707030201020d211e020705010b0424030b09031911210a08 53
    0x1a40005111501c40c2d4110305900e034a503002042058102d4014491020000c19800f011041c1010b107030b1030304405140140840c01032220b445e0f02988504580c04040d10b070340d006000c0e2180700030329105211a1403503090b0048070002c003212007181d14220007c00d818800003118402d6034440244a01098030b49200444040b0314422480c120380400d0020090103181a1764a090300009a00c40d24800007260f8026981403400d210703014100301a602d46201518418110030b600505805001c0010880c5a01c484407041034a43c0484951003000d001d07882001c90204100381940e100340d09480041f604018203c4000300c1880304106114070404041006540c96401518211548061500c1c0e9001e50000c1030102d0300a40815180e0b41d44030701ca03804203840e291003078803c0c100407052a800740d071740350150b103200d0f41d0f0080c00010890701c3c3c40c00110309072040030000e076003640680c000b040c25070252940004214040c0650080c00e607204241d1030707070114510211a00d640c1485c2c41e8a0300c0c24110790076000c48500c180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 908461987 1250 908460737 908460767
    0x1e0b0f03041b030b3102100201110706020c060601030b031504030c0b04080c070b03090a030c060f05010b0a02120a2708010623040603020105030c0304110301020d06081608060106 78
    0x1c41c21607109242c05007002100250f0084ca80004540380552410401c80c2c0c045c0b10010700a03841c00c103c4000090155640103007180c0581d01c070080300041050a0b4014800d00341401d05840c2e02250440800000c0c0c3c00510240c032009090310400e4540a0054003660342c10390740349030300d42c000c0d107003100182c079807142d0f1554010b01030301d40b196003000c0c0780e200c0242c03a035000c0e90192510100020038079200717442001140700810703244001c50315500e449220240c50349407402e0010100030b00142d0000a1007401d0704001e40380c0000f07000030052542c3d9540b850420f41d100301d02140141c00b4440459004e919104295500080d01d0b444403940607210f030340583c2540b0f03456542f02651107802c0101041c1c0640901c1110050320348900740c428614007003031940601c03180012080e8400c2d81080c00030320040c0d0307001c81600c0d00110000d500c991251a5880e01e01041c00726001c642d40c040d807011403100d416444540014007115803100540301080040c0c044044210601c1c01190b100390b11200041104e988951180390b0844c2c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 908463237 1250 908461987 908462003
    0x61203020c03191e0218220809060f2205010f050901090510021c0e01020114010f090209120d180e1b0a0c050a0b010e10060806010c02060d151e0b0f0304 67
    0x40302d500044001014100d195041e201c001b00708074140354400c0d110301c000c0c013003185583c8901c00b50340c3d51280188140c106960003a5008a1000d081c230700d0280583e9001100d19031500301d458102410441b400300076100721070000d04805910b0503880e0140381180d50480d0103070340d5015503034104414405103036000c0828608501c14030500c0c030b48a00115217040051070480c0d07105134140214000090a43c0c444102c282c1548403a680100110001070b0914011108080000340c1c40b500710400107500c0f1190440740f80300c5400b482464400903644a180e030400003044981e80303544036490325001c14282400719080f0b1400c4988034252030b4419034140240800070081d140c030a51008066a50f6400c0642400c0300702d075180c0d4404014080503108840c0301ea40010720003018255545046001445160060318a80c1032110304903442c019902c1c0c3c002228081c0b080f1440038031403500d000409141103421845072500d011800500080810074046916003100c0a80860720b051003440e041e100300c00e90000e48211403003d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 908464487 1250 908463237 908463293
    0x150108160525060906062c06120f0601060906090b0c19060609020d0209090601080402281511060106020f2e050c030f100f0b031009061203020c0319 65
    0x4400e0701806003c13034031604020610368604600100205490011061070340b0403400003000905900207010740c840012582c0039121154100642d00b405d0806141e0039581c000c8000119003e5000503d44040301d00665a042c074450f42e55082c0d0200d40500004128603411500f0b6070001c030481110744a442d18040c51000941c55a15051901268041c0610340040c6401003079002c0c90f460007444040e44a02d080c2030036002850640e0025001203160407a100703d20032035071401c941d07110351250340b01c000e0010500207403001c070004140a8810021140e448a00d84102400880d06070310108180aa5071030307940c014542c16501903000100602107500e031202040c02070740400d00800c094000e0f140a0801e08426503a241403071810520305810040000c80800049003042001410b07083c0d00e48100c4520766400c0e500c83c3c4601014001c1049241d0001d45001c2c1440c1e00030074007861400410345020700ca9001c503880c5111000504d61079441d00319640d901140084410008618034010320921411401c050290300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 908465737 1250 908464487 908464493
    0x1060516030e0a06020c0301140f0417041e051c020a090f020d0609060e0a1109010c0201020f010507020c10080c0406030b1f0201020310080c0a031401060e150108160525 74
    0x40c40a6034004401079008003981030744c87c00c0c00c0c130480d81040144205a000d524189170b00803403800d00a07000070030b0b0081c2d41c1d44003a8451090707800e590180003455218108440500d06107c52071a89028681c070911358070109422520440d0400e142c0903502a081d080440d1514280500a286500700ca0b00c00745d8003000403074040e01079441040003a14100100081007403c285403201c600400505208402d4500b0a420000012000598104107824a0082036200079480100d0600c44000081d5050350300b0681400b174416000b04003800c0411054900f0540c08440040c01c54001c0019540b0385984481003005200003840390f008040079000c0030f1b00401d040960140c1f00c901c40d404400000700140d5010080c48110481000c8a00c014042c0300c00500309001800002002d5801c3c1c3c1c480103143c42245081d50401010a41041000340400f000c002414608288010381c000e8442080d80d0000e2042c0700000d200509580e8501021383c80e40d82c606041a0030034403404124100c03201d09400741d410b07400c4a9000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 908466987 1250 908465737 908465749
    0x22b0c0b090d090503031c091e0f0512090f1504030803010f150e032a0a0603230412081b2205030105060d030e12070b0a0e0901060516030e 61
    0x40c1e40100018028891014002001001c940c4c1010340303e90403c0112015021280a8481d1003605121001030740703044d1864524400d6140c0d41c824054002000354410030310054040c60466640580c0c00c0e12001d003081d90383e103505071188038082d0341d00075000c4190503818240906150100d1076851055460252661254030554100f64401500d11120580c20b20650a0300c0403441e001c0321160800c41c40400b01e050020740c4465038001c100c03c2040100000100c49046010010344407040603100307840e0540c4801c0010301800d6000c5031100803045800101d6401100e00040d54440d42d0070440c1341c681168806021121742c0720241542890b4055980b05842403010340008102004200444148944a0140c0c02c10303000e0940d40304a100b039140008110003922004015903805034140740c04800c5100090004100d20403000c20b40485210780c0c000840d115944400424100c900b81c3c440c91039105c441800c0004680007406030070009101405000c0b42d10070300c052000c0c0c0141c07090a205089480000c04103103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 908468237 1250 908466987 908466991
    0xc030303040f050c0603010e0a0b041506020a0c050d0209061309120801060f0c0b360312130507051c06151e0e01050f01140a030f0c022b0c0b 62
    0x400e851400b100d41c0401600300400384200905441c111b007075614001d079403041c242005084c0e204003a1100020900c035501c940c0a03020f4000b41442c03813405541c80361802503803024031000c122000500c4400100c3c262404410750322400da4018072411195403503009200d5100ac1d80dc0100e010381e6100e40d0720302d00280400c120440301c24999650560b0f03035850058002c000f0301010f403d01042c0950310591304041160341002a9100c003000841d50030041c02c2a6100281d000c240c80c4000103581c8007402e00034034441c00f000030000503400e010308000325222010400200c48503031400802c075510040c020007881c1090621030840303084031904c0007403569183e202e20054569203550006210b0150308148401c080a500a607051465001c00644281c280070814590360010301030607100e41e1221200304500d038407a0702c91342c0402c00040109600c1700d02a00014002c0c0410701c1203803004904100741d261200e40f000900341048583c8080500e181520095148010582e0346554070410141c1c55003040800c1031085a14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 908469487 1250 908468237 908468243
    0x101a07030320190f0c110103180b152416020a0909030c0201080a02090f090c0720011e05121909050a060f0501030f0303051e01090c080108011503080c0c03030304 71
    0x840d0800700b80f2000707180a4103201c001e000c0c032261519620101d002d0421810002d003083c02d00041e6110421240b84d40c0345900c0e20010f081c2904002003009501030ba105110b13030301c0c2c1d083e42c076002d00022131905a0021030f0002040c100c9024180300c0d02da80c110b0752024401c031107400506000692915160444186e80c00b00310141e0204903a1300d011821968854900360b4480520b1504500700310507140001c0e00c3c0c48400903c40e20a5071240003080c4114001f0080780c6189070711180b070314608a100c0c1c03940115642c010100c140480d890080103502411140780c0030300380640d1543c801e842c01010050f00c3d540b01d103001d00508081c050540009403200440d00c11003d00d1030062000744483c420074075010341607403500000f10091904002c01007001030035460410703800681c14240854144da4a0182d5030101c2c15501070310710080004000025250095880141a028255105051aa2507000c07580c00c0e6404985136480f1032100a10402c08500d403400680320001240c0c040e141e0705e818150000b40b030764005907819 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 908470737 1250 908469487 908469517
    0xb15061b0d05040f0512010e06090a26040905070c02030d23071707030507060c0c02040c03050c040614040506031e0112030c0212010b030a0605101a07030320 69
    0xc004640c1042041e928011040c0c40c0c901d00d410304041c4100c02c50040ea01c0f480e405003011402284224100390007480d100064070b0111650b41c58007031501d5954090021007582c540c550f10140814080f4001c3d9400c801000087e920b510300740c03510400100510740201130804011005803080010380c3d040c08140d814801c1d96648132080700f080c5034060f11007a100c802d5801011070170001003001618402c210f8404c2c104003100f4135100da58a080a580c41d10035900d00a06091501103107810300c541000c13140110728002d0b90100314180103982c0a43c00c4035400d8840c03c41c11402880100027103840340e20018480045640e1603814076940b440480c0d840d410039180701e1384241b4500c1204002c030f000c502100f401400c1c00060315000320030680300501044000000607000d6020080d4030003803440250000c1c00c03600c10103400c54a55a4550031320134024070058031142d00c901d030301d03c50000f20204045480d03000d2041c0040824505a02c643c2c043d40104821a070b854282c15002c40c1d030204101c2080040c11020404c4844 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 908471987 1250 908470737 908470777
    0x108190c050406030e071203080402010c060603030309120503150616080c0102030103060b0306010b04180902060c2802060f07051609061a1821011121130b1506 70
    0x1405170307145428601c031140c1c0008030400c0f20407641b04444070340507014205100c83e5115030004846421929401518860400c4000401c0540c0b40d400320340710798001c0c440c1048003070a0150803541ca12041d07170202c4145190100b2140c13149811401042910a6020680d60300030300c0e5079650b40642c000c0030741d10f200e0b40d46c040010424031119001d15890030b90f0481c082c018641c10708a0360915030090b03016005410a03402c4060b4030000d1283d01c00c000d202c0c1c00910300c94890004010707081d0380f2034141c01541810507000f40020f0341401081c92511803940e005100d1030400000c18203140003600080c07002c0e9a275200c0d140000b40049480b0070414042d03c900c1c1008a01c1034100001c1203120010100210000107003007040303c20300710b02001f461141c8082150700d00c60300c03800115600460000850307100029460400681c00c0d04018030300500d45845e88143c0c0707009000380c80814007a1507038101e034081014012a851000094020300f44564070121180569481c2c042180c041500c80d04180d0310082071074035501c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 908473237 1250 908471987 908471999
    0x18030b180102120f0903040317070c0f061209020f0a06020a0b0f0601120b0d06020301121e0201170a1119110606010e100207030f0f2307050108190c0504 67
    0x100c00c0440e0641100a51400030300c0085507201c1c4200500460003810200c01242c4403d41c1401110010b50f00070318080c00c5421481c0d4400c40c2ca60258504903040d1070400000640000380c1c0d03540030102c90382c9032030f011032515080c0b02c2180031b0007208008a03484108901034001d980d8411502c10050802036004112041040c5003c401410021342a00305c4114407000700001aa80100441d500140ea40c80100302c4400f420040b4900841c0e040c0000c28003800400003245551181c828070b0b07421707805442e298420155005010800c0075040300040e0014202e07034503020590130144406a04002034090001c0d501c42c1745008801187c200050516491100c46004005640d004510140c240c0800002d801c0c28200307400003901080c2c0c4030400c17900607a10781844414450017800b14400841d0803802d005060304503860008084d003c0c000b011502503566007004403500c9107090075074a4400b215401410114200780c01524405001820305424680b25129452080190700a01d60600d12648955488608200c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 908474487 1250 908473237 908473261
    0x50103090f050f0303010e07030b030a021c150c030609091211100c0e01030c08072003090a080a030323060415080102210105010e060f030a02091210060b03010e040209060118030b 78
    0x1c8c08102c1014245800c040c040d0b034020868004056040b43d40ca04881d5010009400c800120340740506030090840c20061000c0d01d0303421004610780107039000c0008546405690702120710856024001d991298000190a80502c0140084500c007104075501150007841c0803050b105c00090324400114020180c81065800d8080d4964240ba00e0a01c80c40c5c1e03223010b071401000200e8034000c002c0b4001082e441c02c00114402e00859010f03003c05043c41851f07070b032251059942c0d0742011400301c0000f4941fa560042d130383c08281c2074101841d5800390980c00354503070b030302004040d0418803042c0383e024441102c00200e5503400d200a010345071700e1410355a10782c100701e915039982020580c01503042c041c5010b080041551410704841610074141c0c4811784a40320021101d00038000d1846c0c1a4001e44d4680440c030034140001144c2c0d0085003078110a1004c9916803030700d0141801b0038403681d66000c41030303408100146840c242042c0d1118061402e0038211840701541c80303d2000355031080d2203c0b01c4850600c00641880 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 908475737 1250 908474487 908474491
    0x20d150e04020906040204081b1201020f0f09180103060b04110f0702040203100305030c0a113114010b0a110f030a0c030c0501360c050103090f050f0303010e 69
    0x1890402008600d0985400c0a12100601c0288545020000142140da5540c142c5016100c840304a45201003400d042d40c0301e4408018965202e01403c8415495050f014021103c203074400c0e01046040c15035440c6404515000a00403075800ba10801100d0300c1b580c540d85404d8002d601502d40420300007000c100707100c11500c80f24088c0540c0c5c9020420030a00e04090012111038070f42c10784006a8a0b5120794507011195070942005200703002c00148a4480e0400081d202c0030b40740038104a090048d042810800600c2020000c030000c88060404071151201918a0f06c02403c4101c00214a1640c020f000201120090300250500f0801151400a0b00c2d440f00249441203041001003a4003640e99481c2a40ca0042035a00c8003004064600c1c901018460360380c1081455010700240107150401c20400030300201c45c04000316080c0d45448084448125403000000c4c1c0341c0120740041c0a84c1494011005003a02440c10b0703840c43c0041490400040d07003004600c0fa103481c1d20011b15141c0d410f0403c980d008101c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 908476987 1250 908475737 908475761
    0x20c1207140c01081302040f11030601021c1727070801060506040f0504181b0501030b030a12110304030c0806090d090f0e07200c01020715080606030603010b1201020d 73
    0x1a030702e201199800a49203a041492a05900c4c210340682c80040c0141441c06903082d040c03420303c0000b80c8104c0502001d54085c0c00700f602610058822212107041c0e040e50b0104c6503000235802405000d100100050294120500070a04182104114044c0c005400e01c0c9460718108e40c041c3c402084100030a108000162000700c6402c0d28140c034150807002541c00c18000c1a201c1e5540d0b1810083d009440e15a41040302d5010703140c010b110104041c84544c4401ca81301d0603010074148200c641c1c0d50b140216000001a900070010344c1c4025288000700c403015003224159502d44002c200101c0440e01042d2800001c0031401d000b00711a180c042d008509140d12081083c0c03e00000354428080929000701607403d54210100e2041d4565612000302c0b0b2000c2c5082c241e8000501c444801d1039414808940c0d0302c00600e003078084a05050f503a20a07901e0000d11041c40000003007100b40401c4031490040700940e0400300050001c40c40407040c40c0002c001c0d8003102c0340c01038560b6000890031145000e41c06015084c6d89 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 908478237 1250 908476987 908476993
    0x72001122c0d090302040b0a0317130e06010f0309141203100e09030403060b0312030c07020a15021018080301080f0d03090209010605131e0801180c0b030703020c120714 74
    0xe500c030b101801492443c000244134036111514040c154440000711001180c02884261a100702c030108031940b50b0100d030155010000802c0301084100007403882502650301030b52104032400820400300c00034a80358000b1207000399a1588400c110001300100d15000b4000042d503541ca04110600c0a001e0540303a102603607154800c02001800703500032007541c0889030413640c00708805030444002401d08907460495100003401000748034200d8280005002030500c04c2c7d500200817903c860303058050507041c0e940c807070069000501c41810b03148a500b001d45010b02c28228400d00341c3c1c0b250744422031500b098000d804c02d903000e02140120000308002102070410681401c0120303504c250007084045205002d10401d00500003244491b8090200c3e48600400405080400e20210840d08201250341403184c003810b5030034111000c88017441501d909a0300c1e58003481143c2c2e200e203807058410030f941008244800340f69080c04000108101840108440700305c1c2000c1d6640d9548038900350038510368407591525903038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 908479487 1250 908478237 908478253
    0x4050f0301090501020c15011422020423090a05270f01020307050a081f030b1911180105390114040c0b1201050103051008150109050c072001122c 64
    0x81c542d26511070703906604000ac61080034170382c0b8824004e44919032040d9182c00080b840c2000d0381a1606005900e000e040740c00c01d5080e100c0c41c503003900f0b660080c4d1303100e0105140fa0800800208980411f60020b51b078440540d102d03146000102c03422a0401c8036410085100002c40b28822a071052099501c840c91110281040b0780c02568800040d0b114040100035440e0540032481344540c0c3c4540b040f14426200d0305001da0f4146d280b0b04c5030030390000a1030b10702002054143d44025800303003090740e2a00824001c0f40e46514040e41800c00d21200e103610781c51302070007401c0240450041c00e00400140368900081c1001e00d003428030f054000640194050444140203012a00440070502c1c0a141100e909107001305160b2036101c2051a0145154030a50562203071042098104c5490501e0381e040711400c40003041203564280500c00c6500c5103600040c0f11042c182e0380700210300e0070030f0b01d000f10880041c513086030070a9600305010300300c5681d85803401d802509001400040480100000c16421044003d00200c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 908480737 1250 908479487 908479489
    0x2030115020f0a11120d02010c08060a052218050d1715010c111e2106040602130315020d0c02280f081c0b01050f04050f0301090501020c150114 63
    0x600200f400107003540d007003040b00d4280d542c031940c0941310701c020101950070300d01031110083c0c000c085400c060808128a00c0000c1c07250314080e00800200c03240170304002500603051540b03084408482070605841640ca240340c0848101078a00405020321480042507a0300c0e090201600017003842c0304013950300004800300120201038203103400d0343d404203007001b01851542c0c2c5442403074603078680b500d83c0e0005106442600301d250442d000045c04401a81c00350460a0b080d55682c0e04451100c58044965000d8000b040c001840c03a03005140700c0e103000d10000c1c03c030364482e0b03200d095000d0312180304007a4a401041070010350449102d000c00300c138000c2c0000d002e00750001340342c02e00c04095800c080707804c01c1409241c4001d201980c241e23981c1e0240c0c4942c8203561403101917013421104802202c00c0c08840d1801072124003950003030040318050003800f0389450800740740c1010050100c0543c1c1040390903540f60a0800001482400540a20b9031000c024103400c402c2d540e45483e141e20141c0c84108251141c0354402c1c01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 908481987 1250 908480737 908480743
    0x90501050d0b13060221010f0302010936090b15030c150903010203160807031505091e010311011202041a130e0108100e0c010e0105160c030602030115020f 68
    0x411540a10b02c00040c0c0d036003020594001110b104040c0296000241010200d0110516900c4916512004a003143d0700c071041000c16031280e0200074080340f4409010702c09450550019203071030171803424900c6100e0311586202d1a000c0a5000079900944030000c0b03104100c841880e03d60f010804401105103405020000781d9a11001d208035401440340e00301c2050521880800c541082401500035981c0c3c1c140290f036051281110028400014000300100720030034442d0140031180c0c46180c96640142d4200300402c0003c00020b031582030a404040c84410303080c2c50b40c0d07100300e009501072400040745500000001d465001405031140d0150704c100703c24030149000e400d92002d03120300d01403940e481d03c1c0303400c2d15510900e01ca9001281e205400c2000010300c0b160004100d403400580407014065035820307100e450307540d02d0081c4242d07011540b14034581413103501c03403405800b11440c2515040036234000d42d00c980710a024940c1054541c607800100500114a0074a220a8a81070610080440f03000c10005561 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 908483237 1250 908481987 908482009
    0xa0f0f1403010e070b1c02040806100e090616050c0f0c0406090b091504060512060a0c050a0e010c051614041503200409080406030f1505030c1306080105041a0109050105 74
    0x104040c0046030020301c0341e891b1110800307000c500901c11940d8139101e0304419551a0101c491070b540c49180c8101142c440038008845001d00c0040b0001e102c5034460310110020035840a0308802002800d0140701056202000000c88074074945000d04640114281480255010741d0014103c2174141441102c16464906140e98046821aa03001541c412100050081d2146d540404d07800707940e039400070302070381800701c2d185024030402c103070030802600581380a54180c024140c03050041008070707060b4403987d402110148a0280709030213440c50b0a035601c0313440404500c00d4100420200304a1040f100a00341b500c01d00846c40d01010403903107218a5a614088200da00c05900c185441400c04492080e48954110f280c140ea80b142c401c0d901e0765240c54009004106c41c4000c4c1e50314a00340b480100c00e035840c01d40e00d0b0083d19000b402805005202005000103180b80c403102e0b42d941a92000009031b82c91082c42a0740c0502d00c02c42c0e207450031580020203480c2201c0180c200f01c1c81ca0f490000100001e90b1418a182 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 908484487 1250 908483237 908483249
    0xd1814061602100b060f121906180c0e0306150901050a0326070501020a030f1506141303021203091f0203030402011b020409081b2a0a0f0f1403010e07 66
    0x2142c0c0a002001061343c5c0c0c061440344040d11040803944407802100001d1080c4540c5002c0008200e104028401c2c0301500c0f1507220700c0c4c20300010b000090b1903021035500200019206410001008002200402d19200e000c860707000e00c020300c00900300418070b01000d40e18010003081724607044041c10364030b1300b803201c041c01c040750003850600c0d048240e0b268056800b42d4120302d400100031511f42d08118000f0300500014082ca190384e40c03919109007400b0182122400907a00c443d620401d000452075000c10381503024043c444407400d540b500000c010f0f901d4800502214030100055520340c0a01020b2003195403280c01003482089400d000321800e56800815aa8070540900e00644925001e0221030b01411031054041e4000f800c1500c030f90b040c480910000c184107034041c82c0b00c02d40c11100600840e00c0d8a0071020105171070b502c400e01d8692078241d41110320320300341c00103045201e026070321015850031030046d5001c00d1a284070040c04018403a818140b0010403170085d0001c2c4900304006601680340c00580c0110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 908485737 1250 908484487 908484491
    0x70804120312091b080d020c06130e04080702012d05070305040810150503010e030904050414060f150418030f050d060326041a0d181406160210 63
    0x140c1414070804181482c0c0e1003050302003081211a04100c03910010312001c441a0750250000040c0d00b00300052036010251065020780101d5806804105065004030b80300c401c04202c104011070701c00c1d50410028004c91282c110f807566202e052002510626150300030901d41030904036403008044920481e00c809800502d4a590389004038a0b041d110b6005581040c52a8410711400d000081e03420362111624040050b4a0710032203958404241c2a904090300341d85a42c0c1042c007244d4043d00b4560403840c0c2241c49101d01d001219601c00d20a450300714125844075441c0c5041e0f00b0b10560042d12040703c0d51400c030690f01444050f03c0c511000c01145a410380041c00c100f001c180c501040c51080083d01c1c02111250003c0c06000d039241495030a802c00c6100068401c1c1a94900040520420040b10116052020170907810802100319400300e0300403d803007003c5503485400018105902c2e480100d1118421400185e65443c4600f400d85882c00081858940b0744401c3c0c041c0000d1500000d24146a01c1074100c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 908486987 1250 908485737 908485769
    0x3040e0a090b04032111092403160e0f01080106050c1c0203040305070f0608130302010b040c03020c0f06061e01140a1e0207120809010e0d08030702070b070804 70
    0x4034100510312003001801c0440745105200130540e0002d03031240f49000705804066003c6440d2984800c0340d86007004584c028000700040f072107a013803903990022407121041944038400c0c40b2083c91040e60340102d554000c2010f01e440002510350704480c002d1200300d810b90301c021b15220701100207404c4c84010f0180c00180180820610810360742000025403200306201c2401a403608400065602d8009000843c6d880c0034145000c11000c98000416089851503681c0d0030046d1508490791050040c0c0c21026800c554031940b40c0d003641e031554001e05400d58244e07940141c6d2003009261840c1000c0d4400d0341c5c03001030741040042c03002030754811001315002014800400328880c0380b100140e81c19084248840401580444e4016403c1d0304000a03086560304059610707208542d80500b00c1c0c0f15622805400048241040d0341c6001c036480502070000d60f001030500e0146001040b0000b000303030303409060803100081d000080140700360341881207100801c00f404101c0d0601e0b20903690550240200e0003002550710600d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 908488237 1250 908486987 908487001
    0xc0a06020d1509060501021207020a03020609030f030414040f0b1014040e01080a020301050609040b0103080f0f07060905010f0c0c06020c250515040e1512010f061406090303040e 78
    0x311007045115110850090b081e9100880c3c8003611080c4207003070250184c003a10a07090341e00403080310203440d030060030b0f040c0b001d0440d400c2241503001802c4403030301031140801030aa00301d02080104050465141003403e180007100030002500c0502c566254481d007882d420310125190310180621040003810310001900600101d080b0500031030f88021144500c903000010796402c0400c48030107242c000d42c020310041d0744840a0044105c01900c1c01050100b41030010004154004044d0540d0910101a2880c001200d0601002500200c90544042c0c2c3c1c1c1e8609842005400d1261075991300079a002030124400b05080035100300c0c551600a44450780002c2d2078500c000003804580c5110302e08403c406a804c8071482c8540e02407125000c0c0c0d5029082000b54401d1711402c1304103070307021111644212a9544d070703015100354602c0d42c80100b035500501c10390aa200016428000ca071100c0125000004600380343c00c000e241c0b212040082503016100c00c008642c1c0549000c021203040c0d0302102c05811003a12428 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 908489487 1250 908488237 908488241
    0x90b13060213060e190b03010909110a0e06040e0f1f093002011118030a0b13440708160210020c0a120317010f060f03020c0a06020d 58
    0x1100c40081d140c0c0d44400400d03102d420101c0c0ca640c4c02e0041d42c03080ca6201c884038902c60904841d016014403510309000401080d18160000c1d108240301d44218500b0b080e8680c042101304100b0380210040c800d10508120450038070b803082034202101c400c01030004504030404d441e1030f090b844851542c0f241e4030400e00888121075812480c0c0305684002540081c544022000280406d206c01b141c9160100941e20084240b0500076000b000b400c00c00390f68584500003002031403504025802d40c0e010b006540986001c500304581041c880c841d11010b0392666005480d00c1d04101400740b140c0c89980b0f42855000d40f9007480d07440c903110340100f1000c122031158103588802c00180200e02001b42720000014a11001104032424100c5141c420380f417003001c0d8201024207a0311002500c0c0f03105d810540c1160308000400350610110350041c02805c11410701c0000c80d0b0020081c0500b604080c0000300040030130000d03a64081407603040702425160450624500e900e82c2600e0781840e0701c0c05400d81c1d802041403101c0c0d100503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 908490737 1250 908489487 908489497
    0xe010c091e1805061311030a05220506090709090809060c0f010606052113020f010c080318060c03100b1b0312100b040807030807030311030103030e030709090b130602 73
    0x90b0303030800b03403000314410b604041c10007103408a010385240055601159843d0140c6844d070b04c007a80c0e0300f03811951102960801888010701e007003808491860600800b200e45000841424081c0028045501c0c044140b1032410215500c54056646402c007010041070500d800d80340103180c11a201540d40045010880c9400d01180e03905c1695441c2890000f05140c000c0000d082000100e0a044501801c6121095401404841030b02d4410911440d070380041c03030207034030303c51502c1720505203101c1030100e07619412440c4c1c200f11023140161001d402d41e58081c0c01d04001c3c5650000d0007010b500d01e545844400e480842010f03204000d4034910128061401182006000a110f115003040b692116000304085e01001390644813500c00d03044401c03010460201d03000441d4140c074140d07001800110700e1640c0d400d5242d400f04000758100350391080014041c40030200114000c40c02070780c40481e03881c0d0707050806052022039842950540d02e8409107078000b40001c180c50768001c809001152810b00301d8240034011b0706c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 908491987 1250 908490737 908490749
    0x101802091f02030a12050603100e031c0504060506150f090103140c030a0f05090309060903030927070e0f040513020406061d0a03111c0204180201030e010c091e 70
    0x700c040703061025980040a08002e140594a0800a10788030b4102400c80b101074840c0d64040d04012480c2d1000300c0c10f40c0152007000d4190046a1410b5a07039101054681c244800c031041d080e80710010b1106020701402480e0708281d00300d650303901008203820315503072611402440d060748000200304015160b009600615611b003013a50f40302481c0c9450508901640d004695030042e403490108a40c180c070102c4d2044a03c500b80c2040110b140c03044610400107642c015003241603241c40f042092002c245c8401d2800080d981114100103e021644e09070f000700104000c101b1010800d0300042d00a0503a00e00d189000f103e000cd580001c1d09803a00401c0c000c160711503d00281d0064144400080c100c1d40c00110490b40c0004228034881800c003000c10000020002d11020f41015401c0a12000310310b00107101e50301140812401289175251a4041029076206141c1d1403054415081848155601130158425550415008000644c107241001d05481001d0003000000654400e41c14002000c108954000d004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 908493237 1250 908491987 908492029
    0xe0303071d0901120b070e01120f0f1109011b020f04020a0309020306070206060a0506070803150d05120403030e0402030f16030b060c071508041e03140a030b010810180209 75
    0x2840b01c81e0b404072400c011904807005c40d03090002860580c4140e00011802c10142e592410600032840410064802e00d05081b882c86c0da510f000c3c0160b101c081c4110400312440fa81d40c60b071144200000509042508154420140341038440700c001070b502e444001010007022500140c0307440034a60b00b01c0062005503c001d4041c4a444240a107081d00024994440c15040f80e0f40c8920607126400c0c0221030140040040c0074030014800b041c0d041034120003801c00b0359070203002c06204c58a0398407124600ba0b2214a40c2040101c000380030320074503900c200480c0413040c1c241d806528604092202d1084640300500c09056103c021081284182c425002100c01000040c013254603169100f05407501d441940c419070b070600d07081101c500b049034080e066661045401400121f052190105514414940290110304000c040c036108851070402d40040e016505107650f0010348a80c4040025000c000060102c04102c0310759801042003c3d45201c0300001c40c90048400f50311010f0120114900c11189280b0342c000384 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 908494487 1250 908493237 908493239
    0x100b030118180c0801060602120f07110d14060601090324181a01050117010e100b0a08090606040605030a0206070c0e010e090c041a060a0c1205040f08010e0303071d0901 74
    0x12036403c00c0540e94881c000308120350369424240d030354441200150034004814446140e910700a8005841d295010b9491036210b0445034000848950640030221010726041e550105a03070700c100a003d501100a09000700d26604680310172085090801000c0b805200c5803615030a0f00f03015401280c441069107488d034401e4078107850480d903170b0480d8041410340002c500300005099807050203c5201482e080000801c00d07402e10124030200500181032000c4031107030f41000551a41581c0080808200d5a662202c1e41c0c1403178803d0600f0404d01420843c81242043c000740596540401d5400f080383c1e049503620340d592600d29040480340c0c1c25601c01101c001015000003030b07141001341e43d03030311a520103070589062482c80800c2004541c11218545102c0e4030034a0030020505080b0700812403001c940c140304048004541c0d9040c1c0140028088400140000c1010045030740b0030300e041c1c0080c0038008020b1204010103500ca955070300008229800b0042d0802c0526155042c000d640305000e4009000b440d055 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 908495737 1250 908494487 908494493
    0x534030b1c021315030f03050c06070908060f0610120915050f1e01030b040609020907031a1e0103050c190305070e06030709031101020c030a05070303020105100b03011818 75
    0x148041c6402a80900b4003c001440c10800c2c91040309488a000c1204902d86800d51300d40c0c00d40c50052480c11130030b1110402c01100a204c04004503481540640e8403508402d082c01ca00b00e003840030150106907400c00240c18402c4581e01c00c590b110325200940b801b0004850701541000103001200d5000e0f106801c0300e421f61010400b250013240c0301c0c41d030144520a00741c131004004403282d00e070400c0024a031581c220051002400280800e86c105028101c080342c00141500012400342043d6210300129540781e04050f940d840c011000e40c81c040e42119102600f40003141810440301c550501746040650310000960301d600082c05443c0607000308400c0302800c42c0c58003006401442c0c2541d00c60041845a0340c1c2c03480702d01d41002261f1050600b0b90b00e520602d0b2031540c400a4003401c030388a036410b501610010000c5910308100d4103080c240548000e1a5032403450a001e804c642016189200204a0036024007031201903608136411110300b41005001c80d920503a1050083c0320985050003400316000c0c018040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 908496987 1250 908495737 908495779
    0x3809070e0408190507210e060d0c1b020604050d020d050d050c010614030d08042d060c05090306041538010810030312020d020c0f010534030b 62
    0x80c01a040c040d504243c400841c081d80c45002d07462008080c08040721410305900d02141603110541c00c83d082550b283d042420020341c09401c8840440d4015a0718000048900e91141c1c240c070000000b0840380080300c0040d00883d029104500440d8022a20341245400310b403501d1210603002030b0440c0075906102007050b401040d030361110030990900d608002022515121080d1440304280780200201800c1000310001e503113803040100192102c484e0540388040c4028a01a4681908a900c90f40f0604240d5850710b40b0442d030440c1c1d04102041414042c200c1c0d40e480c0000c005d81c003d43c000d901010884040300044018149820600303400d803203200b280c80c00c01c4c24018400814080380c0501c02c607070380040ca001183e0103582113a140f0b00d110805041000824094940c1c1d0540146900c0c025180c1120105200180d901000200101d6804a000b00b0348550342841030075002007058505002607041c0040000d64040700141d030019442242400200b101e02907030015040c1240600141e510710801b03029020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 908498237 1250 908496987 908496997
    0x13110903030f030702122802070504021c0510030b040f050309130e0c030d050924040b04060909020c030d0c030e0d021c031401090903050f13033809070e0408 69
    0x15100f00460701c0f06c0d00807003609a44a80152600340c0701000b4000002c0b0070039030341c0c0f80412010350080e0384000c030744c9841340e0000349504900c1c0030801c1e020004200711002100c0c030040ca0030041c1c42c2014801d0000590002c4455005500409070940c100a2400d016040d84501c1c2642540b24501c080c2e010341104e45a00005540558681a542039154001c141519541d4401c4c94500003002005041d1140c0341121b0349026060b40c05240c4170983d404219040055030240d040081e001a0100e800c10030b583c0d208111001402165a00390300380200c81d614290380e402980310130341c8419100c160814210384a80e0007510340d0f440710301c11503000c0c8003510f00194448450841c86031000d40b4010480007068024010800d45080040b00404980e1801c4690001042c01000403020410100105070030020490302804401080d24840f181c81442c501e07003143d03414401502c2c4140301f00300714400e0a6120035041032100d000d0b00d02c0600780b20343c0e5501c000a410070303c060700241110010082440140210800682 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 908499487 1250 908498237 908498251
    0x20d020303042d08010b0a06080c04122a080a06051e190e0f1b01180602060709060e010e0d0c150507020a0f0317070503040b0a020c0102070e0613110903030f03 70
    0x1042c032a1104c4166099400ca4040d2980265070500d040018511810f07000da840610300354400e04003a142d00c0641561500c2c0351080c0c0350017505c3e98030f1441500201514050250740b2402d170a56152501d00c203a0b458175141d41c00505200d5440c0001b03102260701c000d01c4105d102c040405000c1c0c0c3e19000f103007450105000b042c0d03076214614028020601c1400040c0d40e00340350008800030b144a91000803e03191205512005178100a45075034000d00281c8940e1380074014010a030040e004518107000b00815110082e40079100304080c2c0b49011201d40d801c00c9075900721b40b5054842c40c400c4401800c0c485c00000b101d41c00125200c080000484000d51f0200284c0081803007110010015a51804850b40300300f294000a8500b00301a2150928403000e9401401818418010f4a0500d541c03150071307a004c0d800803000500584c05c021088032081da414440c07a8080c0c960343c0d00010f400c1c1020008034514104541d404110207540b08203d440840303042c03042c2d40e00000c00600300c90351640055411003031a04151401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 908500737 1250 908499487 908499569
    0x5060a290a021e2a0609130b0607141504120804060e06070e0111010c081603060e0f090d170c070f0204060605070c1d0703020a170c03150616020d02030304 68
    0x1140c60310001e4940013140c000240701d00e0404a40004111411928000b41d804803550707030b500064992541c00150440c2ca018211000c2201c038800000c0d81043c0f801c0041031498500d07902004005904020303800701d140300d149004940c507038803440c0100050606803c4803565114040802040d00d510030807841c940301081e078a5030443c68038245080e090f14502c590b0000400c600c0710005504080c1140740a2020340e5501e00403484660340c0c007101440700170035200d00000d02c141001b0801340000030043d013048044681341038406842d017001f401c1e50a4030082c041e81a41580000c07104140101e10091503056a00100100602e80c1e9600c00509180d01c040400c1ba100e003070900f07000614409020182d1038a41542001c41000d9032699001c500a500003c030781c00a100101c2168a4104000494244190f500241c000c2d56414800c59190000c0511107101e407064504202d101b04285d01404d010311420ba0599403944100c01e04e10019040d40a01d0304070404031601074004c407002503001105840d10705269448 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 908501987 1250 908500737 908500783
    0xf01060e1611060403080c1201060c02041b1409010210060e0a060503030c0a0305031e0702060f09010608071205010209060c03090112110319180605060a290a021e 71
    0x81d280888019402d4206401100000c0c0119010711140360b8802c0c3d41e00d0000c2d141c91601c0320808015039082e0440c1d00010b8844202d141141130521a0144e074410400b0a4010a00b078081c000308141c034221111403810f00041100c1d52244d008202c1c0c2c407103801c81d405044c010360340c882d2105444100115907008210703052901c0003c40e8207001c0125882994200040c00407241c9607101500c3c60351000e00491400407a181b258040c0011300404903000d00501c1d4081e0501d8284404480e0b0700303038805004452140d00d00312080248113800601a82210340e80281101e05840134100b8074020f018098100d43c02c0341c0000382d0618a074001100601c504402600e9060034070b108004604216100d00060849084082000c1004a0044a8010034000c02c1d0311011a008541c9491040d040764000780848240380c9403410710201e80340c03031140080903101079440001032001e545510001001c0700994003611240004040d04858424825440d1143d0455500905503102003802c958400c0110800014040041c1c0d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 908503237 1250 908501987 908502031
    0x1101030203010b0a140409110d1409070306050406061a0301031709060f070c1503150510020a030503100806070f0305130c15050919050a170a060e0f01060e 68
    0xc207403810303105020490703070801000840941710080746803015202c140d02480000385c40c4005018105803903500c0c1c4603003611602101ca01d8001d45020810343e401000c11039003001440f620008418003240d4002c2004203d548407403c0040040019401c0480c9010b4015011000031109034000c604030fc0c41095010b00c2c0b81000507450086014000d20350707070b000360304005248281034000c018000c01405220192440f50340c52014079101c440c445144400701e5201c0c0343c074a151382c8540e1000e0000b46020344400d61242c2c07001c4802501c6080219004042c840302101149441da00d0349250ba018101c0403048403040e040940018058101c0d6100e40e0300000d0400f00068221001c032140380c5802c50303108106441050400036080b400c00d2030300f190601000024042c1e0155a910421840c0d1b00c6400c811019154034284400d00c001e556031500301b5414445d40303110002881c2c7c000a00d40f0320703e80d00070500091001010300080d0804001410b044010340c02c01d0702c00b1a440341d50521460041401c3d08800c20907142c008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 908504487 1250 908503237 908503241
    0x150607060c020102073c0515070207051c050c06070c030506042d1718030118050c011d090c0909071805010c0305030c0c01022214310b060d09110103 65
    0x30302e003c41001b2100410003d1900a04100700b03800e031090090b541d00c03030064111364103111030865407000141c0c4895010490780c2031980c08485851108a100b4400081c103880e100c4d40d5044444509002d0300d0009401d1701401509080d15000e1075001059500a003018144100d003451500344079414400f0800382c0024030304040c2503242040340d01112510412000707494074540f6800800001a02d10002c0350800304660703080c031401444501c070001e071003e582011f0400314540b000d200b03400c2c1d045c08a07c1e268540102c2c411f102c540c00051080303441d03400e01c2d41c0d02c0d240c0c10954058601c085411150301000d100245800000701c1e14609803007482c8210301561000110344d122030506c00074000c594104042400c42c0f12a030004c044c0d10812400152074810b00700c91480584110360050790000386039010612805042092281036100b044489003205072423140c01d401c80302c0c1d401c1c040040d51b0100081c2504241c241e500b10342030103d0000c2a560f21074044001420240028000442c3e205607560020315440d0b01038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 908505737 1250 908504487 908504543
    0x60302010c020f03030d0e0709110a02190816140609010b060a030504020a05180103030806030106180903200d110102120f0c090a0f050f1206150607060c02010207 71
    0x5039a10740c0c000d1181d07000e00c0030a0003080c802c150035000030010200d410f0110301519541101103002480018a4004588100c0c3c184004c5003590b02010030511003440d9000410000c0216081e903101d4146c1458131b0103240d00c2c0308041007030380414000c0b1150b4080c01076032071a00c804080f101040e18181d0f510b291101d0308a81085010b107900030018408000054402d6006a9100f84050502914191200c0006000400e641442c0d540d0440d013070014002c041c1e0003141c0ca46c00c00020360081c0710311810716806803070450156030b9565002c1e95951000091500c922000d6034048a060300100c0704103144688940c5409404600303102140f80e1300598500c4c010148221080d84c150000d01521030340b40e040b55581040f001900000c0342c5e0a0a003c0e58005175290707c0090024440701100080252a16003400062509031611600c40c28100392820314098001c81c201d944544e040a040505604900024545003d00715000d0216032070040c079a02840c1d015030003840018000c00b035520341c55001111090701d044407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 908506987 1250 908505737 908505739
    0x141014161e1101080708190f0204030605060109092a02100f020d0b0d08030a050403050d0c050d06060c0209011403120403120e1207031e051c120c0203040b030402030f060a05070e04060302 82
    0x54040003580741c50303c5a00b1b007187c1c0b2032001c1e00446c3c0c2c2c15440d400b1500344d8210390800c0e1100c035590f07410b204213582c01000c200020041d066060003000a100c0460305031800d10030b0f41199600e80d011012143d03c0c424000080040480300742002000c02c0f80705000000d400101e444030a051070a02c0340c0031103140c003081000c5000e9100383c6052450365009490405000060412400e014050050585480490280100c1000c8559886840e56600341c1c10f4030990302c8942c4020240b21300c114111000d81c40769a02ca07030548414107850304e24903400e400420b1500e420880c20a10865000c80e01004201e403412200782c07094506c0d0703074001440d20044108180c42c607090351254480d500403d01000042d80030142c00e50791860454070300106501e1a02c886080101075101d100c0400c50300d28040e101d2580040c0006560f51600900f04a0b290100c5c070b001e947c030b114034000d2600c0c100011000404540d0204401d1700c0e44400c8001b42c40007800c0802c80070003e01400d54641020401111402c0120300f42807040b43c0403260 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 908508237 1250 908506987 908506997
    0xf0a02040b0d0f0608060a020909060901050d0b04030216171507020a060b061b0d03050906220f050a030503150301110d05070309020316141014161e11010807 69
    0x100d100c0d1080b0051950030a40494a40c44000000b00c1d1502404030782d00c41d0460b00805a55140c00f0800c220000ca40180454854000f480040c400b9440d0915075080081e03002202c2d207080e482d40d04007a4544803140003502c92507040100c0206100c61418081e41c4456a4101280d100c202c105441c0a4080002c850200050744a80107a1001c5100b9030460304c042e40000d0301140c80c2081d103405860f190032100c00020b201ea44614844842e40780d042c802c0a40c0120560090211420548109a458400c00c206088800803001560741130010304d18840b8955503000080350f80ca9007203440c1c0a000380d04200c0e1909111144580b81084504041c02180d14000c4009a25450300c6070385850b18000b000013400c100c00300b554950796030006882c2000040c20000c1801e800030070721894144d0142c4081e040701d41040c0a1084e01007291704041c2c20058002034104103d075410f80300d000c807002d003080e03c50043c20043e01e0210f100901c0705001c00455201c202941c016006c40c103425041000540b0013010507184000012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 908509487 1250 908508237 908508247
    0x60c0203060a05090a030f0e0d06020403150908090d030504120c0e0709050114180409080c01110403021f050c1b01110102070507050120010e0304090509061e190903080f0a02040b 78
    0x2440f404160202c0307552401d00f00801d44c0300802044210300c0d510f108a0ba030a4bc005000c1c014400700d00203a8150009810082c44002400d648040b00d0b8012031107158007032107080130103100309070181d03041d20083d1031700d40741090f501c10725400c05250000a074440d260000810704041404248035956a0055070010b858041402003210200900d590140b6440010201c04a6580f050742d81c0b5400390401c0700f80200091501c44421100302d80c21035500d050f038080307120b00070042000140c44800c10744c0c80380d5a11094490711905640b1b4141c6151059210500c0d080c000c0e000c0e5910482002d1040d0009150280e0794894140f45854200e8200e1150f01d00185c000e50004004005540c4903010343c11102e02c00900352000480740d50300c042d0a480100d0720305607068101140610016000d880703030603070140f011070003004107040482828505c1c0180040d140c2404583c900028a80441e4400340881d018406204005030496403d0003000000d058804d100781c035886038007054042c151030090b00c050340c0307030300064038901 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 908510737 1250 908509487 908509493
    0xd080708040309031407060e010e01020c0f0409290105010e09040f03050405060c0609012703081e163e0f0102030106020a030314070804111504060c0203060a05090a 72
    0x4100c0140114208241424040005030345c40441d102c001c800c90009018550810790b010305004a190300242c1080303c0010a00348983e03000070b03611650034080e5404080c07501d0540111703000d0001c1150291048a90b1603a5400f40400c01041c9240e1802c8994402c4a030b0344c07a8001150581034078410958040c28140c00300b804100e0200e045a0064400d090440c5841d60301c0e00030415a8120100108103500b001c000c02c660040701f801050628458200031407000115003031071000200c4050006000c02030100c0000701c12001c01c012a0380080b003110b007018054074016641090011260720035070000342c850500f40350000010540f03200360118441c91520f0070391000125012080d10072039804005e100310154a03030110340a20041d8040c20407507028000807800b41c1000b90540d100b410754107040c82600d0041001031a8070501554000c0c0d40502c40d40401d40b0714800050040180310f60650f01904005800902550484500040079100340c05482041d500d0510318000c99804665082040d001082c2e01400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 908511987 1250 908510737 908510747
    0x9091801050f011838040b0f1f02030d09060905150115110c0406120219180c03020c15270d081e04080a0921080f04350d0807 55
    0x1290181004038240356100b003130314020303d14070710b0780007260a041c80b1401c1517141401c1c06443c0718001c09669021140412a0110300c485105214070728402800c0010018404c1c0309000b101d4604403040340a0040b40000d040c640700400c023200c81100c262007800080c11503583c01602060403240c88801e40040700000c258150b900d8100b09010385070b680940d6841d046c8a549612419028224080d0b440e0305040b170602c14400712814071014004a0b40318210f003049040c0000200c5041038514200206040d020000107602034042c07281007071994000e0300708009039180c0112016115040d85181120508604071418110000d2620004019000010311032441030003150520b800110790344005040c640e990500c0c030744041040d1801c8850100014524250552042800c0c000d8000540e1503405240070500c4c036403c01d038041000804000000c945ca02044140605540040c85405020aa03101450003007140508070080082101040300b90b100c44840b00014800070040d149890b0400c0ca901e4281302911 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 908513237 1250 908511987 908512001
    0x2070303051608030f0405010606170a090c03050105071205070e0a050f0f132009090601111c020f07080304030201051c110a0509011e0210090809091801050f0118 71
    0x2808a0740c41e45981c0005200700300551085c82e103405a1900b9040920340242074071703c59440041000541006505140071007910340c2c8d0014905140050311480da031070058503403d195440508254607000c100111943c021220310b140c082884400c1089607038842c0c0541d20441a00039143d00302c210302d0000c0c00302e410115101e00349030f0700040c2090302282544000500004200e84d01400c0c0ea521581a10880c1c1c4051041d0000c0e00c100c5058142800d100d40003140c0c101300014021410440141c0900c204034800340b042032003507480740d5100c2001e452401d00c040d58646500000c0c6006108540e400a01c100000c030036034082d00c1c3d05956841c074110380c41e4100742410810800b0740e222035940c0c039410800c800b622001440d90b102c46e615140d4603140c4d4a80054618038081d1004502450b0122851840135400b09486101000c940e00c001411507017401e18200b140900b042c80b980110100040c0042c41c80000c144910810400c80207106c0b82d070302c1d921884116102803141c50494141c0d028950503450b09034000d28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 908514487 1250 908513237 908513257
    0x140a05100b2b0f240e04151e0c020c01020f01020304050c060307030e01061508061002060a0c0c02090c03011e0b1e12040b0603010f02030f0a0207021903060c0807020d0207030305 78
    0x403900260155404046070704031080b01d0305003981c40b0411501c04ca20240c0201c0100b03030410443c001ca00e017940b102007003d60109480c40c080b079541c0d09443d03111000c92418102c3c0d28450301d03082000f9002103001944d82c0246210380340c0940310f8020703804003c001c14004c4912070307603000c000f401e00400804c080c01945d030030190050082c59290004048440d609110700c1c030040c440c401007107509401c032070006803090300b02a0080d0b000e084002c50540c2c28039000a003080d000148d00c0000103030500d02540480d80032a101400961201c00c031028480200766000c0918140d400c01c003070390001100702e02100040d0b2840e922414054100610108074400d41c07622000e00c00e00d181c0c0d4881e03450800400c40c60396007414100c80403500c0035604c2d001d1000301d00f002d1182882c02c0c41c9032102103195080200d0002c900b860000d00c2e042c00150005040d40443d00c0c0e1800d840d0170781401d681d10001064032844e1040140c016010b05a000a0b91203001a140c07601c00100040c0000080d0003a103a21030031520704a0b02c0c5d0340102050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 908515737 1250 908514487 908514491
    0xf0509090a4205090109030804020108060406051504031103030a0903021903080333060702060f0c0303040303140609060105030415110c030d060902030f010e0406140a05100b2b 77
    0x1601c159007155100c00b4590350307a10070060204400d51030a80864401620404003a85407404a0000035040b41c5406e4201d0b40900f4a020720369940400507020f400303180c01441e0040106042d20403041c0300c00300603005032403280d0140c42c590445c1100f0b0540d01d00607281441d001a086207010009420300012160641d88403d0780e403802c0c80e03103d4130703500f0899005940c3c7c1100101035940c000c600358600785c1100010041a0346580b6918444800901140540c810192003441d00003810540c041c40343d4100ca803849002c00a4a40b80c0c500f90402030000c010701507035140d8003900c00c0001001d901e40340c402c071482208140c607080d085440c0c1c0c2d202c05141d20300d1300107003c00295540e803503000f040f030f5024040c0c100c1180980c019540d0b0030061041e14181c45842c1d22082c2494014402e11034000400c1a00324150303070300c035a1221403c2d6280e0501c8000751000e0401d00700c040355048107010480390b2a8004502c5124101c00140e2103030303550200022240702d2030701545418882041648200c02428003c50210490300c000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 908516987 1250 908515737 908515793
    0xf0411041715090c09060627040b030d08011d190906060e1807230d05010209040603110405070c030e040e0c090c0406091a0702060a0c0611040f0509090a 67
    0x595100103001d84203080144d10401d510300307441c0b80816809a001720203807203950420b15181c560300c000798281d6000207940002ca015050441d00c89501c4009075000050444448102c00c0d07070b010709417101c2130081000e0501c0551802050707000c00007585000e8011202507510a10314034107050b005001e826405c80362981c691a0000d240036030807400c44d00442c503200380c00520b05908060075141c407160342e04c802c40034080084864481c07440200b0481d0410010b0320410303550203280c0f4006009100710103001c0c2d4005e180960100501041050310601008103440410040e02c6c0d9407820307a0804142080100001e070800c18000310b9042c030750450407509000d0000ca6031850560800100c0d800c904496101c0c13841000b050400c00b040d80803440c20003c207101040d89400c80520404140a8481c68102034010140081c40140492041c2202e02120750016070030001007406070f80403c66688a4401c480e00c1c914070780d10100701740c9440c8400c94000c0e80388130700605002429941d074580084142101400c2640c040007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 908518237 1250 908516987 908517013
    0x5150304030c150b03010c030e150403170109051005040e250f0806070207050a06050703031508060411011e120b0105070b070c050610030b36010203060f04110417 71
    0xd003541c1105200c0420803118081c1811b08507400c43e0130100030076003030071040448528041080210868418035100d000c0e629810300740e0384c01180d84241560302c0b00010001610720340650100e07000e50241003a601d00301e55a00d0030071050ba03002c46426840394002007640701150507081108254138829003101000d0560310803400c41c24640b194001c0340301d0341140082202540d81841007801414007210782c100d202e4100300e001004ad020300d85004081c10742c0c4100b04d004e007841494005d401031900310206da107640f404d880c040c46484030001c02c140c0894801e013503002aa050705210300d4000103035642e503404440c2e0302c2010314015001c036402281c1408410400c2c080402c0e11503540038460170301911440d0911a6903d040340c94130200405224095a1040050000442180f40780360080c0c83c06030707a147d1031102441484050b904c424036406420003070b010b0364480301d10190061846203008071144480000c8400c2400240c4001b42e0420b10001020002404080d401c0340104a2180c0b00340d048a80b00c06140d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 908519487 1250 908518237 908518253
    0xf08070e0411041a03040818030304150e03010c020708030d0209060d06170c01050a0e0f010216121406060f100c06021204051903050d0e0307060501032a05150304030c 73
    0x1c10b011420324000142401602c8000303050b807200011806520b0f1542c94262a5a07205005005a0b0341021503103410724034090350104140d50103442a981410f1441c10455005400c040004030700700c1c025428103103080000c1d0700215a001c101c9049202840c501490f501200000f540070901c02c50744000c051001001c00c0c2c0c2c20f13110781030190400281c00403030124020051480c00c640c2c2001281081340403c815184a6403003509103421140a0301e450411341503103030051782004400c0054030a4401043c0d40011700344e4054580104807405901e9000c0100844040039407100b80844816410404009000c111410001c0c150041e240c0c00c2c2c07402c904000c2440d92000140d07408050340d00d01c1e490100d0f0078002805010b010b61501d5070418000700102034160b580c0502580202c102c0102596624200200071001c00c0c802c940351103034021002c021541c1c403454018030040188250160004441c0c1c8484a841103000450007030390401000310700c0303445046265580d1984010400c0b0f0801070300c01c2c246000a40c0c11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 908520737 1250 908519487 908519501
    0x21c1b140a03021b18060d1515060801080307170c0f1f09030909020d020c03030a020c0115030f0b071116140121020304060914010c020705100f08070e04 67
    0x24a018150a038400d0800a1070091840102180030511201004d1242d4804140c00b00c40c0c01c0c540c03140021035843c00000b41e03200581d20303c00b42c440f1a450721070204040301030388100018081c52006564407529604100c810f51000d004680700c69104015640101d050103000650040d1040c00e0507103000c1c00c3c0501142040522a0500c0305035005c05000c092121040a66488040c1001410880104541c800900c82496803164085185e80081c00560b010100d404507045518000112035403400c092a5600c004d41c0a00680104c075481d201c20f140303001e90186802801c40c1d030048070100c01d904041e2078041e00c40e10054034080034000059149003420500740f000c4002100c10300c1514810501c5c10009080030203504500604000044400d10720419142000184041d0507180040c2c807503680d460100000c05080da005090840f0140020745210300540044031020890b90a1301c2c0c403d642c40040c0f01d05c2c01c402400703003130100c1d5440d20501070481c4034040e625406a07140c9001d1140c0f5518a020400b190b40c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 908521987 1250 908520737 908520773
    0x706090504060b2a120403080304050c030105091b01031413050706031e0222120c0e06131a0423251b02031e060601021c1b 54
    0x50004100900e01e820700c5450b00900b4800c0304189000c2c2240c00c0c5904003903040030b05200012041c1860f040d0f54800b0803190b480304451051455071181c680c01c00c1c2c138180d002110b0488061040c203450719180d04041c02144e00400035000289554107210560160513048201681d040681d59035005904401c03500d03c840c055521000e10a06800745810241e0610043d90000420325003420001c424544103a0a110b505076042e110050b02c486002814003025048011341c1d44860000440104200e0380da8000012081d208043ca2700c10a0b5035425100b0040d4000c44441e540700ca540079481c640300342c503904500d02c0c1c0704607048650140942000001c084071510b0051007030700140344640c01401c811480711542c0200010b03041c800c020020303540d14002c2c4051000302c4010001408140c5540d41c0361810f04522040e40102525074004401c0744c028100d01c079155080c2164811072010401039400851107042c050951104900f039102602c40070b60b03541100000c3c0c00c0c0d80489000c040702c08038958003549400390072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 908523237 1250 908521987 908521997
    0xa06020c1e0d0f030809062a040909080a180e060d02130e100c18290a051201050402070c05060a021207110f0a14040506040603060e0115090209010905090c0702030706 73
    0x1418100204141740c000d10019865220a040c0103426080141c240100d9a168041c3d255413900010309240c0750143d82e2200805a040c00d6940c000c0180c5440600034548643c0c4c1c2e0200030521040880e188485075101d04840c5040c62008030b4100d0a240c800040340c0c85c0040d103070701594000380d424007048415040881d0341580040c4201300c8880e9079030040310226104da142c40340f00030b00c03e0518144130003c903216402c1c2c062040810045106840704040b0700d43c0d02c2c04041c0541b141c1001002400760f505c0700c1c030a0144144202c0020585160900c02c5c0c0d04070301c0d0003030140480b02d400c04051184a0740b00e43c0c105030a5201d41610a5003034a48800145402441010301c005c1a0035004240115000700030556441303403040c144140309019200041c4046410102c402042a440700c8010134000d0580c3e4102401081c01c01051100643c015001400e02642840207001e403da82e6462075000c07402034000c460300282c070f008810465840d0001c051a089548022680d1510386160300103441c0400e146c5c07011021031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 908524487 1250 908523237 908523263
    0x1120602040b22050a061b0303090b0c0304030905010801150f090b070c080709020c03031609030b010e0f0a0e15040606050d0b04050f03070f030c21031a0a06020c1e0d 73
    0x400351103c600b0003014107444465041c1c0c144400134000c1400d903000942030031a10303c0b4180a1511a40040d03c02c1604590031043c2e0341045044071105a00440d41074020aa44240c0080d09500c1a91170504031800200500c0c2c140f84d01d018202c902420f011414002c1160410011904a507440c000701043c51083d50060803007460308103d1414102c0319070020a000e40706004000d04654007000300c035030140404d8404801c4016061302592100c00642002d056803900b0380011488800412540c0d004007074501c0c03410802c0d40c2b040c2d007020a036040c180020f1125044801e04020b20545098250780040c070541010650545035008110f0103000414251440461442848244202408025075185044000d945400140e44907d460103448100003030402c501c094550050080c2c03200d9454441400300000c104d90801201c006001d00200d03505405d00c0341520304040703940c2c031381120400111009034018064495076001000840300070f540400b4400580c01c8003041040d0f031080c55009081c1c0c42640801205 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 908525737 1250 908524487 908524537
    0xb070c0513060e0c070308040807030207081b030f0d02030a2f010506010906080f1302010e120c1c0b131a072303060906060c0a0c0b04060816050301120602040b 70
    0x1044000c0e1044c0e9560108100820109520091155000c0e4001d1000c0c1d94610aa00d8101e1818985500a10140c040c90fa040644044d417000080c0d8516011021100c4240c0c840000300c2d224003400c400d020250f0300411641000038042e15581c40b180265807031464030500e45022008290b41c1081e00d42c10240d540340c1c100031456030458030060150115191040085c5044445601a0b031005848401078400101c801d10840e0b100300380f4681082c3c406008841009140c00c0340310383e42e03140c050350340d4443c6001201400003503030503d628005d110340008a594507901d5801d40b2a411030040304054582046441820980304a00514103015000d166500200100380c8815030012661900100c40755000810500c0a241e40722840550004400c03144965540742c00700e000d6207804102075004080000c80c000000340058000040c00840b5042d07103500700c0e26628401c103162101d40c03454440c0d0100d1010300c01031020a00080da50322001c2d105040041c581a01c86514180030b4000609165074015a842000d4071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 908526987 1250 908525737 908525759
    0x809071706010914010810021813060303140a0e040506150f0909060a03150c090801150e090c090c070827010f020f0717150412080702070f0b070c051306 67
    0x1130000e050b039003c1c00c0d54140413880303403500e0342c60011945040c2c0210301000891603a080402c030201000b4000c8545441a45c4007001a0103070344400d6002c22500745144c002c1529050403203c141c076481d2f40e18940b03c800a020007004100140100d60801808070b40640c0d001e170310078001d02030400112010342d00d8010030300c100015100c00034140c0e800740a43c910100002440c107800008000078407000824101000c0100300e51800995200014075801c1c20721101c00e501000b481c0030705483c080c50011040348d41e00d51a803599589913562854100e040580007990b42030014025181d514481c0350b881d8035101c1c92041440056000c0c020204d140540d05145032920341c2c105030069201e0001d070000e0190741c40c031101e5040d11500648680e052841101c0c0c4400c09060090255040c0c0c0002002100381d1410142805408058041d400c00301080170200030510107800014003004840c540c0031003290303060a01c07003400321980220b6000c4500201c0080c010415584849840400756294080050028a41280303510f03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 908528237 1250 908526987 908527001
    0x9040e100c09030f06021b12040303020105010b070503091005091e010f08010b1902160303201c0e120a0b060307090b060f0901050d0c1205071e08090717060109 70
    0x7844400b0004100140c81480305600a0b90001700050b140c0a1002006c0d035079042d2810400f442e4000c034000d00c5400780341c11011b030003500e010794000c0019070303240c40c3c244943e07100315200900305a00900501e1444e1520b040266490140c900e061800c090500c0c0109000c0fa5100d03910584659004100d0740c810350303201900c1696402e1340d01d0704e105d2552418030b400e142e82c414542407080e000e040000e40081c00b03000704050b19440f081c0d014401384055980c02e0040420f8140303009000140b40031072011600c05400204080302c4c005100c3d402d00700d030083c0a41560015060310019800c090040700410002c2d03414488444110301450002682e803030800c04050514020350401b04040d480e000032001d903504c034201a80d004c03d0001e403209984601410050b20300d03001d92000350804174100140100c02c5c90780030f00c07134030001c030b501400600593302c07107020075641052046420307d81c3e10300b42e8442d503035418410740d11583c000380c00200303607403c03241c882c05d4035a07030b540242c21794400700c3d807064004104801d0b032445050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 908529487 1250 908528237 908528261
    0x61e120106081f03290901060f0f0b0d02090d02120c040507020a03140a11100b0307061b0f0c08011a1f08010b0708040b03181002041d09010209040e10 66
    0x812020081082c0c0e5550440718000988440b140c2e8881070b116821070085000c1e819614402c0174502d240c1502414003901150140f40302c1c03503110050005078001180300341000d503024251105e0501e640494202d000350019802c0715030210841d004040543c85e0002d11035427201c00d0f540900110031507102408152003025087c00c00711743c04215800d010aa000303800860007030a001c41940c1c4c5040240040b601c603104440d00f41400d01602c500d811620100358440e4501c06030640940d00c035030b40d541a09441c084040900d0b08006a09600108001000b000d5a070b4855481400500c074007a46410344c2d0390031281b1520045400b5000b0030f20183c0e4615046000c224091194040c0d400e26003034140009100d000184641039203054049903e00402c503540303096401900c0354154041d12403611880c5081005169074140c01e5902030890960740da40c106000311400d07030301055170070806d50881070101140090018185255554240304c0178045640c3c03809110001441c082c014480ca0200012000490fa4007007802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 908530737 1250 908529487 908529511
    0x3080702010603170309160518090c0934141e16110a0b040e040309030203120318010c021b011e08040203120c060408030603190b0916080705061e12010608 68
    0x4c005030f0ba1409c2c006080041030b038400014070303203540401c1840c01e118008016440175058007040b0106159000b02c010f41b5449510070b1204072140c00c500c01d200d21100c0034240019000518841422905c031340141244281d21420a50b44c3c466800080560342014140040f840918010703041030210fa0701c841c124200e0111601c3c6061850644000002d102d588a4507604c070030481d000806060065074a40000d507005030544a5000f5000900c00304c03503004856035180035041100002d4410741c1445048400015500180801d07048e000c0070f01c2c200301d20308450301d0400c091130800b0300309150804804d0380e601e104e617107a041c3d0300e0805204241c1171101f034071000700c0300450a02011500290000d00c1c2c40c1c1045d08070850f00e8bc1e07501c0c2c0c3d0340800d0400c0340c0500000e5007202044125001c12405e02e4005226038160703400e035800d503960040f101c05a4641c900c2503414581c054001801989080b00080210071130520140075000c801c14a46526600b10314503000c0314400100040016a4021081550004143c400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 908531987 1250 908530737 908530739
    0x90c090b0a0309030507060203010b030a2703110703141e06070f0c08040330090506040b030702031315180b031302010504052d09040f0308070201060317030916 70
    0x15800c0c840c040d0310340450070152114044828503014800f01d91502e0781040d0250740c6ca41c1c41d1005074486600035034180b074000c1c0c5000414050f44512000380150b00042138105403070b141840e141200c411760115010243c50003020000400980c0041c0000e01404c44035020b040c8004e040c003520002186002c4807008103401441c10400c0581e8040a41c00c0701d1209420030314011101418000e81078003658000402065840813081c102c00c12480c2090001c1d400807a1b50100034102d91011903031807241d0b118143c1c0202060005002d0030f10080065a0700141500c110390400c14a039044845040341036005030400220101c0e651511540710701d1003081400c00100040c40c2a261250b000c0940c40002c5c11560410503d600355011a8400c4044030000d2100038010b0f20703549010303d450040e08100c4454229040100300145c81b031410300d09410b61180ea00119905640202c8e51419a5072810040912085543e520780c0400020050440c007040344440d00d004a4aa203440d00f825458400d259548492100c48894 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 908533237 1250 908531987 908531999
    0x405060115120e03040f03051b040e0c01030b030109060603080d112b0e160509010806040b061c0b0a1a0102120405100c021f090e0606041725090c09 65
    0xa5070b4480502040c40060070411000056086011300d42082c0c0c8140400741c1c00201f84500000d8480c240000022004c1030255071900b0001218140c4282c1c41144c3c118980011856029074041c410108000d07001040031415541d81008644040c0c0080b0741c000d4000c12049444165403181e00e0f141050f641c0180c4c900000400490451001d5a050400400d5030f40d1804000901680098550055450482c2c89244142c60080c0200c00c1600400c0d001e0114030000017646080040c070b03240600e4002d0300001042c0c8400701808000902d00c1c80d28000300440400c4400041d20880d80c0511071400d101000580c07100051210006155100540d41194801c04001895031001d10071a8200c4004071104101c40364504c00c00c0d00c001c401d1040c06540040c0300c6040203000c9101300501c0c414018590350b55a00683c0f15082c0780465002074070070b82e41040041c403051014400819007180c003901c0c41d03c1281c402c00d491004400c101c800207400e4410130700c41080c0400000c1900d00a004281035181803030410300d42000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 908534487 1250 908533237 908533247
    0x70c020d0803070c05010615020d02030f2208030a03020a030b0108060f10030f020d06030506162c10030606110d05071b12050609060c03040209070c080f04030b0405060115 75
    0x180150010100101182100c2c0c09130481c07032002d690000013404007559401e204200c42091054800260180d042c16400c258404004c540d03650100e14411414154401d040280c8503412800c0001c1a91141101140c801030030006052601d00780d94016035a20000c900003003c9d9619407a1060510088030300703201c002da840921814000100f541c0c484502c0b417800800710082d100c01606481c003288009501101c1d480c90b40c0080c1c0589000384201c034802e460310441480d0b03500c149681a000103400c2a0f49203010700a0031081120f441c00c285054103004121f90000340100010145800800d5580702c08122003074120001c2411055400050031074008015005401032082c005d00514400316070910001803d01010400040d081d038121300c3c2018402840c1503035441605440092079441002c000601d603201d020300302e0303201c0c65014140325029160500c080e1080054114112402c9009204a05243c5d222a010b040114029003000149081a003455801c14006801020104c4110307104228256002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 908535737 1250 908534487 908534509
    0x9070e0103090c090905031b120f220e0604050601050f0904020c0a080c060a0e0307031b060b150406030513020d1e0503040b0a020d2a0f0209040317070c02 68
    0xe003000702e040c00d05458001158000c54000394202d41c40c04480e04240400000640082d10390340c00c3c070400c0a20340305000d0740d841380742c182c0169901e14108040d000395040f0101411030340076000f20090400d104e56080078144d400f103812030011039030301c01d040107464070309401084d0f001007017820a5440e00003040910861840741d0405d0f14000c03900010344003850702d410070603810016003007038019072200c8500f0346507a210708c0300340c0c1c82c180c0e000e0030042103c841210200850300d0b415810b841d0301c000c400000641c80c655002010003078400b607540314142038807621000145412200290f403400d03074070342c10000c015040311406000d00e48080d032440311200050f140c000514883c0da400c0422507170106100c026409031400509401000b50002290020703103043c4d550058101e4040e580c0035941c01a0b0068001c03118159890143ca42c500044403070701c840f902c0700d46101c001460040d01400241c1c06a030b00401c100d013209640841c00541c8010310840d6118180c3c2000e0741241d402c2c070f0310050030220781d0002150341040b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 908536987 1250 908535737 908535739
    0x1618020c07120609030f090f0306051f0303111b06070f0f15270317090f01060f06081e0f1e07020f060a060e0c07020f0613031109070e 59
    0x40055032020001040106400600e01000d040d016040285019800361504400032008500c10403245c1c2c076424010121842a40d60110060060b01e2864840e0f40260401a112200034505924100c0715206140d10a0016600070f454030108100f104036003070300c0e10000303140464180043c61031000c3c1d2a0354a50880300b0407904140006909140c904000c0203103961240c000313012002c800d404d202c001c00710350003451655459400d105010f81e803041c80d103000c005075804c004001034003c41c602e00d020f004030b001580d00508004101c650100a82c507c0e039007100c40a0300180d28400001500304182680402065880001e07911101c100c01c6248050b03202c400c00241400513980d80380b10008440c051805140803510020303c4880b446030034940006501d90014030141f44040c0160340004201890a002d0601100c070600384605803691611001402ea03003014900320391004586a10102c3c0340d84803805404c1c0511041d492a00c05851031401d06184402c800900d402040c00504100c040e0ba041103000030441c00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 908538237 1250 908536987 908536991
    0x216050105070f06150e0901050a0207151a0a06081008071a09031002070b06040b0f0307050d05030d051609080d050f130306020c0a0302010e072921091618 68
    0x83e4500d000d00180035110100d040c1c019194000003903202c4050010782c050f410110003008692650721982d001d038420003102520007a0401c05030074072a580740d844140c5c2e19a84a5059902c51400b400280903c0000e5115500003108101405003486d5540769920081c1038020091061600e400d90540b009a944d40c0c80905030b0a0110304182d082d142448088a03d182c1000700315980c01c20b501d0940103010b81580d4940c041c1d0315141902026013005502807081d0400100201001d51603c0c0402842e07802c807a80c102c80130b00050003010a0704946000301c034007643d403405504020320350001c2c4c0200702030314a6204013815886442d00310603054000089900d48210030800a83d0350111022072075000245900042001c1c1c800180d80c2902d070400300d0750050b400d100354000c1c015400e00c010301030394400481c0251400e049600050001c40780c40003244009007424420050b08008424000c8200f8003141390301b1044110000040182c0c21105004400c1681c42500390b02400e0b60604840140b484501c40c28520155 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 908539487 1250 908538237 908538263
    0x3020c0d061803050d0b04060605091005040503031803120a0503220f050607031404080f0702130606231315170c130b0f0906030601030e011b021605010507 68
    0x1103520b030400300d0031103406280242c01c0000342c40c006080d64000101071501c90f00d040300410341403809000715030489886550701c2c7e08107880c20b0104844e810b50b21010b8800c0c171a00700800202c81d14144040c20031020200f01c2c13041c60007050401d25003000b0350384101201d569004c1050751403482c1c000054a030484a010070310000110514401106c2941811010740304162202c0303080100007000034490301c100306655003407149000c132500101d0360380c0c01918002d007100414800901c4843c00d41000e004c081d800140803520720003241c002d0074122000c90304100001816091640081c01e40700c5410489201c18000d001d141c00d0441c941181003515a004110703006025500d50720505100e90500e0320404200700c0d104c0e802d030070b08240106050380403000b1035020b5104920300182c140b0b10315040d40c04030040d111381c00d0300c0d0081c0c4004205190f403000f82445d040c5540d40400c50759483d000d10482000d0303105446010014200c40030080e1506400300d004080784410054244626644081951100755015041141203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 908540737 1250 908539487 908539493
    0xc0f07120c0b27180928021e03070e09010606030b0d020105030f06033d061a0d02040e0a050604142701090b0f180a081605280b01090903020c0d 63
    0x2d0540c2e280300130402d4031002482898a0b011800c0341c0c180a10f40c0c1c95074074a181034050f000c5013041c0340b80080d41c811008141620a100c02020405104c2c60060560b00300546407148800c1500c41514803821390f81d07450034140000ca41520403401281c00444298041d50345e107074002040c0e403000a001070701007801640807031010f840401140c2d0140d4220131040d0b0440030200001c0e12000c50001d1222301c004400f2206410601440c130402047e100a0a5201c0040111200050103030b40f10004083c0309942c03c106c00110182200082801211006401308850611008100665500400d014418100320b82800840f0050202040345c0d540f030740050081d403400300000c60340100b101c3c10000d00300e007010303408101e02083c000c501984103918a042038596010040101552000c40b400000e1401500304041c250400c041d00920544500c075000325401080e002d00c001c03604c50604c01c41300d5100d03c010352640c001c00508403c0c040c05003141d01400c2000840759107000390344204c81c030b01e0580102000c02e560014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 908541987 1250 908540737 908540749
    0x10806092703031e060f01020d08100b070303060305060a0e07050f0114030421020303160e040e0106151b02030706051b060c09040e011a0103020c0f07120c0b27 70
    0x1c0d841c0c40054a07140e180076070a074507007030f001540408080003041000906030701c1e05412188840300c0690040c420721040703001c240c03808000503101e011030070a800c1c0002220300340d4000420700d161290350301080040c40c510b4154a488406802e080c102d9050038006100303440b000a00764111035003100c01210380309100c001640c0840c4a604000712030740000040000b40510b0b0350f800100e40c40c0340400e124100380d03d05802c82e00d03408280d81c0fa0041d21500c00318040030921a54502019540003080002d050031400c21060031101250700150304100b4210134000c0e11a04402549200620f844492012080c154002615240c02c0d0140000b48440811440f00002070400344482d411410740c119a41030a1004003500c02e5007054102a119030300300030070b4440d4564180910b81e640d04400c030710305007400c07014030040d8049d400158034040244a05070301001b030804108214030040428014051000549040a44044003660030400c8036540400419589100d0500c403900030300741041c2c052694806103c000340b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 908543237 1250 908541987 908542051
    0xc091b030216110114031509131509080409020a1e09030b190b0a170d0314040201390c050603010e0c0708070605280b0d0f05030c0109080406020c01080609 68
    0x82003410210410103809680501f00d4040c5600301d840d1010756440800c404200d29103050b006100c400d50090310000310606400100038944503046132410543c88025010072a04801a1800002c4080103040051a5510760356001e40b078841c584482000d040d41c07941d1400c20300141066a2088060f02c0040032a4410b030712034042c00000800c030385140c45d6039140401140340000d1440c543c90194410810105001c0e208920544032a88414441030b0b5450f00151448054080c1010090001c0c1d441c010760809182d40004410229030380609a190150510001452240e0845805401c3c20001480400c84520f54254420744201e6107681d04d07501071400c5010782c007441100412131801d00c0d09103c02c09805441860300f254400440300481140b00000400340e5090107005504001040c4011002c14120555400001d0140089038900550702d80f00f07500716044804140c844503404203043c0507650f03061051403401e070383c240b806032442c4c2403440010f070748500083e11000702030155000e004a4880307560b02c0e42c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 908544487 1250 908543237 908543267
    0x40b1e070305070b01091e05040312050106091805040507180902100309140a0209150a080d1107060905030d030e19110307050414040803130c091b0302161101 69
    0x40d444454526000d4103a420007078080365902e841d0070000c91440141e101e0180d002a500c8400d000700d0658071039503401000f0240083d07007089045146400540000d01a19008212aa4409081d689000649d501d6074502c0b01c0412816401d0005000c00302c0e2001408800303564001200003620514400b100000b019032070340c000d40251404100003a00303a003503400b0881150003610054024214526034503207072801010000c0d031122503070010407000c10320300c09208140070700a0001d10302d05854844040c5404403020703546000403030700a0440b0340300da4240901c00040c41d80341070400549080400103034950714104283d81c1007550742c1845900300e0404001300a100601220038406d091458207041100c0d440b80401306000703202c0c003180003c03036003418859161440b100400c2d804e0780f03884694880141c1e52000d480c030750507004451943c00c0410032500f100d1000300034440000403c244400c1c210203040045800501c18144140703d1955141d51004002403000e500101100f81e4200c080010780700005007407116 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 908545737 1250 908544487 908544547
    0x2120906030a050601120e03092106160306090f0e1203090a1203020403080d0507031805030315030718050901061202030d0809100c02010b04111606200a02030304170f040b 75
    0x48043c8102000410714440150346003081d0040c0c84ac0c1039204546105075451141d409a00021450f0b2500100c80d140141149004202c0651324a044016965907211054029503541071140c000ca0041000321103074036585003001d0852501150003904ea90360300348003800000110a510504504c240d0444001d07543c070a451030303160303c284204440180011150000032030310300200c6510030350301307840e2000e010b542c00310040d89540d49208401d00001c040c618003d4051089a2011564248202600342c0c0c1c1c904400001565240c643d1445080d5071740766102c0585482016074002c09a1404140140858401d04018807130b501d44001d91882d01c0d801c0414842c5131441d000c59212001d906400955038120215400e00400f20341115510709840340b00301024414100051040004a06412010002c82c4c012b07644010790421000c00d44190b40710b0f0500b0001030b00000104410020003185011800e0102d541090520b81861a12140f40c40703280a012146800805d045150340200d006a10301c141e004216 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 908546987 1250 908545737 908545751
    0x2070f140609060106020714060c0c060a21140c090a1e06021501050102061f12150c02010e030d090219031b08030c0c040c03090b010e010602120906030a05060112 71
    0x2154072518140c94901c124000d801c00082c85900c00500542034600c0c00303a003160f6544001080021550050300351080b113001c0d02c541d1412565614002d0082902d281e141c0b44000e100c80000410b6502c2d0384440056441d10300382100161202907441c10b5800015900d5460342c448255000801c06c00341036200c403103220f0100c0c460100070144d90380d0f20000c6507401d4003180c0d203898003a03000360f0010b582401150f00607804000004c41c00001c90990690714003100c01207060407038840c0d1194110a0700302c41c00303440c1107500d6012406c00d510540308022914801d80b00810918402c207510544034480c481c50b0b20301068035800c903402995241d844141c1c841403283c01e5441c41d03507542e02e400c1901041c01c00c00d00011123040100010b003000d001c821a038484011a020308a864041d404120041010305000c1d0b0130541d40c2d4121200050101080d10b010b0b114058540c4080d61401c02c00914126203205c0302c141c1c0a2091104550588a600540b5004030311907801040941d590360048824070940c0882c0389070310303080c040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 908548237 1250 908546987 908547023
    0x1404140411130204051c170a0e100305090c090c1c0e010c1409040923100c03150323030a0306030b07090522150801060905060409020303040902070f 65
    0x400400c00900b520302c9680c1c481c540700000c04034004c510509820041000c0b100d40e01c5007100034014401c0348a4000601e03070b1a029281c251894010080e040007007150811801c400d85840f51082c1c01c60b0f421032070f0612003458203140035515510840013840c09001454041400c12030003e003514810701600142410048400c1326207405808081180d600a500e000310a410b024450740800e82c007958000c3c5410711b07082440b01404020151700b8070036100d801c0300c1c0511303c6c40c02c00c0801800c4640c007201401811412000c02d050421200c1c1d280220003403500d0505500c00e03101d07042c401c4008a03500040e18801507203c91903c042c0340d43c160818031042d4000040c40c0d0703003031070b07015030208060f41d01031001030078240d031641c1040d40c006030740e4020076502101b8052018083c4245042142d0196200240442c8000d05002118a511081d03000705400743d440d15014441c0c082c00344100e582c0300000b21030a01025030644c02194a0744100e0007025001a00001c82105002c80040d203a0300c001c0d0b2003208140d03a022403103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 908549487 1250 908548237 908548253
    0x209120703140d08010e0a27021201061215020d05040f0606050a050105030c030a0e060a1d12040b0c03040308130503210a030e0f071d010f0e0114041404 67
    0x1000032550002e6405118142040000d41545840d0b8580c4400b1401d900b000c0c031400c120b0a008056040b0141c4885020421401440780c010851908001c40d80c1c14400d80d104100f108064558009501e0380742c01070410070010300114141321660030052014002c11011b100c14041c0c420303020303101c4555003410180005c000600300c164852a000c1c000410465840348100000c0c40030f40d2040c9070009401380301003610031040d41e0095400c4200e10500281218441200c0b0381000004c0740c00101c0b1035a204041c00c3d00c415031080c0c003a00310304218082c0030600c3e40224504028011401440c4a8070700c082090f280041e000c10072240030b5034000701c00c00e07207440000308000c0321294907010740f600902a1310403010240c4800103569504542d81c5c04004e043c507000726021401400c92030b031815000e02c2001d00c942161803050103020701429404583c0020ba24090181c1900358106070b200101903014003808000d0b80705800c1007a410340324458640b400004000c0006405030802c80407030010200d02506102c200b00c054 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 908550737 1250 908549487 908549489
    0x6072a0507080f0f210405061c0c020d0906030b090424110901090b0901080f06010302040302060d150503030a080708190c110709020903030d0903020f0a0c030309050409080a110102091207 82
    0x6802250100308072141400c0c5402d22020711655905e405100c2072000c3d01d00030000d4440100d06540125003000d0a014180503149a044c040740544c0081004111441c0d000b8038807000380101e07082c02d004148401d40403940b0b848004002a10343d1a114605034080206040c003a0352810f0f805a0500441c15880031891482c4d001d404401e000c83c8590f80d0002c3c106580409540904805843c0c01101c0d60324070194500318140104002d04055082002000598a110203000803401112001071800f02100d01c005c10045150085840381c0c3c0107000c00c032a155406102582c2c080c0031403914400f10b450301d00716001410117014001008508040460003407907072101302152a041070308101c4502503a91600c1200301c0c45504000c5405810810084080c1051600024038040c0700b44104c9668032079015085042041000382150031400c441800c009255000642c0d1000e8038045800300201020366840d4441e0b481210034078014030109001484011800390305640046001418941c504200005815103078001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 908551987 1250 908550737 908550763
    0xe010e0d05030924070c08091507302d0203030907050103020a09120f06060e15010201051608100e0a0b031605060703051c180506072a0507080f 63
    0x44e0014807403120158011000b107100c10181c0b0352203030748079458210303800d44080005840082c0c04011821494681900d003c0b003524a001c410744c2c8810003850f049071450318105d00d070061204808003082e0861010800c08030000c000e4100412002d010703d95065640182d8840c2c0030321071407510240700c04c0c00c1d004802140f0814618055030031040d100d0f00150100d02468002e0740010f4a814800d02034008902d640c1a4594015802a04001561b80c2c0340000d030b400c0ca070410045030448105025103000c6103880ca811030b81007400280a5460624144000003160603c10782c1008041c80200301c90705110060040581b65880500c00a0300e0704200c1d44000e04503107691140a40700310380481d0042440a4600b00035a603000340314620300500c5440403600b9410005610300c0c282d90000701c0140d000303005c0c0720314a90610008120b1a20300898140396007001001040f1740b0a1000300c030298614907081d25181a0b8030401e106061005c44d1390303410402d14010a036086200d49100306856800e0081e00041e140f00240c83c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 908553237 1250 908551987 908551993
    0x130315091e0305030613020d062d03030e0904030309020306090c01020d080609270a06061404050609010306020c0f030711030601240f110a1203060504020711040e010e0d050309 77
    0x840e4010307084151151503805000140e0600100307465103070010078010000001a000b605051030010300c1011200660710107200300a502c24250601c4017282c4001151880c0305c1900b030805071035510050152000014040d01c115204800101018083e030b1140460740e40140c2103a84074a840c200e400c3d81c80c1080c0311145d0243c45504180050030784104071041c401c0d00003030800703041926140c0700c01108407502080c5454048214076100c0e500541002200d500300d0054102154003841c014481c004440d42d00507030380c0240d08101c10483d007900c8092500e411071781e01c614010303550a903018605040091003e2081d425020004501060143c5507103242480f0b1004c50550740a0f90ba6050086440e80d050780106030020088040784120038060014901011aa82412501e066a580d500c80c00c0002d0381108952085103074034500c000780e80c90301c59031002e80000e44003189881d01d80d031241324150710f003591090f1299407501081c0e080a00290440b0303503142c4010045509000740c0100213003176900100d80c1c1c1c859506c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 908554487 1250 908553237 908553263
    0x21b010c1a010e22020409030309050307050312010f120f0201120e060108010507080915072d0332061206040309060e09060901050613080303070f0e040908030c13031509 74
    0x2441c1140303035140380e04403030320780c2130180366030790070720000d4407420030305409040e9200c001c0f901188040c0028a16144a440a1688c03150312041c1c0a800c480103030410156007031800c0c13080c40100c0360b0460400c00d154010b1240744c00262540f004941e04012000c02801081c104a030450429000190950503184003100038001d9035114030044690307410403100590103a00602181a0300040d1140b11a0400002c0c0340807003a2442800051000c00210409006091214160002410307414428600f1400c54140f04454440203c0480000039843c00901e40280a460012580c1d42d9189a039a9002c06110300989119117811304000d00500268440e078000708001000054007440d08045980c442c0c2001080c0310348903402d14051045607001040803c0741c141030b03204045a011010000782d40324180307950320120081d80050300100285d25040005010b0341c01c10002400003405071040d66403124010314915150124070310b140080403200d90000c1c050034a120340039124405103801c041481401000003000325 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 908555737 1250 908554487 908554501
    0x9060f2304050c040c080a1508070605160c0b090306010905040c0308030705090d110f031c03022506050a05060d020d02090a06090e07051f021b010c1a010e 68
    0x20318515200c000d4048030100d0008000d60011000e1500640103000b11041c4040240c042003c9804070b041e44004904504101300302c00809003d10040708121514100348189400e000603950701540c080c80061003404600110074078200384da00c440c059046102d03200341d503543d52035040043d401075031280c0c040e0003494008240740d102401050701550344843c0310381d00c1700e196844052264101804c85000c00100704841c40030355903800c500c2281a0301a107802550f002a007400c010032012901074a40c000c2d080060100c130030300a01280d8041c1c1d100c2504015985003401042c8019007031800724940e03003000741c0e0815541480f200e640107a1140c2131070030003081039460355000c10600c0e06e52682c0c0250710100004100006081c06c00c500c0d600845159004903c09880b00c560300c0030380305942c0c3c1110301680328100c200001d18200300c103140c031121015211242c920241c2030094650000000890320ba1141c0441029183d200c1c461034a5856000404090403002c1c1d0400000036110a210f80140d00c11502c002c5001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 908556987 1250 908555737 908555741
    0x90c0b0d0e0d02153706060e0a05040c0216060306060801142202041206090b060405040c0e0613050a020901090e010501090911090306190c0309081209010e030a0309060f 74
    0x240a8540c0007400c0c06084a0030a50100c0381c010401c100204503502c17941c500e00c0b0640c94030301007000c803038050903000f8291901100440b015640142d0404c45410b20b40d40c0c40b9106c000441c0d00303469080e00d0104401c18412402c0c0d2401c0001c0f1282907004072400c40001d45a94560320000a0700e604e5564541e959030303aa80c421925610041d5015400080742c18280001611420740d209212100348000d401c15a58121801007580300e0101544c2403520780c10440200700c0011a426440041160300700b180c0c0c01c00b030b00c404640f02d001b40100c49904c01d14001048566941c41c90340d000a1041841c00e001902e00700480394081e4101c01d1840e4003286203604042120f2141c003017024181c1d0410303921859002e01d040d01d0500581030b20441c6401104040000c400d05071024419284103180c2000074238000111601c400c81158000b45802e001c05d45031809400008089800300c0b001d000700456031a40940318915124010201100700a00781d1000142d01c500701c40c2c0580050350701a0145004021803080f00c428101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 908558237 1250 908556987 908557003
    0x2210f0f0702121b0a210215010e01050909100612150504030503070c0215031005011407050a0f0212010e1614090a021605060103110a140f01050d090c0b0d0e 69
    0x22043c007013442032000d80205000c104102c1d18860044036801c5400b030b1220070020b010507001503402402801c00307904080c0c04001038010011a0009002c09600d02901c0701c00c2c1c0712041c09014414604a0041084108204181030008642140400416546006420350b525440104540040180014881d80c02262280c0c0b03202d590151620f40c40c6945072802251000c07203050301240c0c4070099640108540000c00042c2d48602044078060709aa428800054030048040c5106040d46104016070000100c011803442c05650303022013259480c030010701c00500d02203006c461507000ca40c80c00700c014414070000038014120101c1140e910076007544170104a42d50342d8500d02d1007074100402601040f010300b0542d00a00c81c1c159441c00b5030003d400641c4e80c041c1000004e03030098400d4a0903200c415560b141920f503440003040200f00f14040c8038488408611001d5419140360306100700410000310003241034010b070070010b510401c0708403400e45407100c3d04c115802c07100e83c3c19001450400b861820b1100080d201e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 908559487 1250 908558237 908558263
    0x270106030c0512010e1003050709050114030a030906052505100c0e030a0f031e0503150d0308060f040e01020c0a06060f0f090203220f05280602210f0f0702 68
    0x5841da00b0240d405d8540f1038094407150000c01c9030300c8008081201405444054110400041415450038080940d0b0010315900b4510a0308003582c1c034000a40c01158907401c840a6040c42512044140d1102184203180149203850300100c120b410b04201011480c07030207490640800f04114102c61030100c80342041c482c2450740543c81981600003040d125821103041307520178a840e2440300940e80c0c262034808142a2100d0220b07901006110184044188000c180b04055030080034683e000c0c0c82c0105448005014203005100c103521030803098a684d044517410700082402590380e0310045110540d61600c4401c20341d0707014a001d030701280f0f002810f001c01c022140300d01031004101e03042c51404402540f01030181d040900c6100048a42940400c2070340d07035010f0240701e0a80c01503841e410481d0509a000c400c00003205071340764510180002581c2d1041d900c0d50050760040e2190301c9400c100038240000b4945018a890350410002c9950400100c540b040841074540307003d60312115000d9a0381ca001034228 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 908560737 1250 908559487 908559517
    0x11a0d0e0c1003050c040905091c080403080a0507080a05060301062c090c09010314101b0f030501050a1214031204021305010305030a0e031c1e0206010b07060902270106030c05 77
    0x20450310b1f400c0d81200360000003810550381980d40d6034031300158414039025944040342c030f000700304410306030011020341e8001c40c05c09090180c0d00d86420002c1601d2002441040d200d83c0c1c1c0d10125146807400d6001d040640030300d41000b014416121115040f1030210300d03000380010489000244050808140c268807950060301000b8030740d0031a0b03110708410100103858a0144515602282c1080c00c0d4010308900c15503046140003440030181d0010b1a0300d00410175141070605003401004075454106180c0c0031120012600004c0191900d0a02059102624080220312020461741c2c45201d0b07020b070340d601452007200d00207402511070081000340d480904c0003418540013440031006580c01440342c1445c00100506603400d940140b028101002d5040c1848030008449104600c14070403405628110000d82c0d0004041c10740c5032035645900c4e07100d070120052003d0f40300e070311000031516000e03c88107200c458040d00120303440301010210700d09803003407103688002410042d440b003e0a02503000c80300c070603c0302040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 908561987 1250 908560737 908560739
    0xb0d050c09060d0b0408180d0506071103040e1501090512070b09040b060a0c02032a130213080309150306010c0b071224050a050603011a0d0e0c1003050c04 68
    0x208000440010b00e150381040d00d0800e020000307080740c9034031380c411071064044540342e000f040c044c440b03240100e03d6164050142980b86002003240012115404034443c0360842c2c400070b1000826045008139401801c628940038103100d003000c8210042c030840c407004e0340c403408996590010404082c03251200c0c1c403920f81103681c0030700444803080020150304101800c0441c3e0710020001142266118003520b000040e045150760f8110f18060240348280300c004042402844e18500150412070907070b0410910a40c254003c2c0301099545405440038544050545029560727904003881c2c41780c2c45259100e1040d42c44601701e400c00d206100031341c2d024502c10703034403410b540c10380d0395a1413003514029141c01d081c0160001c0c01c804440980c09411842d070015550000e4061110d101c018443c038254000030701c12980070000b40416242c80c020350341100e01151940880d4014140c081c501807141e1000c00213810f0400384612180d01c00012140d01d05003080d20107041745290120128103e82d002c1e20340c401902d0341000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 908563237 1250 908561987 908561989
    0x6050a051303020d060b12010c0512090703170c0729180a0f0801060e0105030c10031b08070e0d02060906070204180506060112090b0420040608010204090b0d050c 71
    0x40c00141c80701a14505219031681c0028003080e0020100321451519007042011606010010404c10511000244900d1035151400b5000c0e00a01407500d241041c00700c0010114001040010003c680086212110102c00d42840c5200d5010020100c6180b00300c48001801000020071426400f800302080100c0c00d41c1751000041c25130000d041c00118140ca038950a00316075440803000004c01c082d080031419545040c440a00352899548a82410480c2c48010446a01c021461011903241190701d5444484481e005070010012503821400b4100406581d84405410031182405416a91034401c0240200b07020041e1001d03070440003e400c540d00b0322820b001801c2c110040d0215910080001c9400b4a02254407000d800500700207030f54a40c0201e041c403500b941c010350b008030070204c01e040a01a844943d115095070702c0c005080140408004a0341021503145c4402c0300e1002d20b0001d101380b003007541c1d07103008078040c2d0450700800903901c0c0341c2007440040b0714050001c0e20034241d03c6400f92540c1e900c108 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 908564487 1250 908563237 908563247
    0x71709010c0f02040207050f010b030705030f06010e0c0c0d0e1f0c030f05040b0d02070c0806010e15181f120203060a0b0f0d0c0f06140910030b030109050c10080106050a 74
    0x44001c9070403503001d1046c100020000e00c028510154010700000714040c11004251410000780e0102d4000d030064403d280781d040340821218190707512101d500d26551a4100348224500c509104404103015000c5c14050300c0c0e500ca040381000460848403201100e0300c0128a01d10707450002e0100e00410480f040001c0064010042c2d0890102c1506084d0f0500b95620045861544181c80d80ea40325640025410100b00303030130501c203001d0803484004040703946c1040c0340d2661566000c6c14405111404c4c0844040994a00700c007080d91840d01809240d19081004900300ba00d00407441004440c41803800200786c414005102d422956001801041c13a85c41c1d2241e03140092920702800e0707030011041600d41c0d20945848141640c4644100d0514080701d2a00302c80c03880442543e040101000a230241c24800c082600d0142c43d488001129011000d510580c000e41c01040c0120843c1d4141d420f1031900d0b0306000003c5500301144038203031190750030180c0a84084801c04002d01400340450802e01039000303014414 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 908565737 1250 908564487 908564513
    0x50f1801032022080a032001020a080c0d180f02030d0242010605030906010806010311090703061e090b04141815040602030702010e0a170d14010b071709010c 69
    0x3e801440110b62182c03401814102103140a4003c0f4481c050580c8903161494000d2040c1403e4000071030401c0521140244041400360803200501000b040c081400025030b4801c4100c03010300c4081c00c00182c80f40c03600c6014869007103000d038400c1c012040d0f118699800451341807100044030111303003104c0c003e00c02803017400103440b080c0e801c01510a003140722040c010030b490706000e48090785405d512440c00079a06807814005811907880340d00080010400105400803480841c801105c61810569a0310700c2100144081d80c0b205440b00da406400700c0404840da00e41d074040c1c64800c0c07020b100c003a28100034041a0b90510000c6201c0142800c0014400c61444081505141d610025140742c900e40600441da0110706480540724285d000044c0680381c1d40901c0303882c40c8042c8003400f178400740506846035161040815401c0003c7c80000641c025103c0007944100440c90b24260b00380107651311905c3e90400c3c1d810071202199425030201045502e840c4400a660b02480c0594503c0d007110721594840c5603025103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 908566987 1250 908565737 908565787
    0x30a080307120e010905030c0f070f260a15391b0c05100f0c03080604020d140103030807050c0715200607081303090504020703050f18010320 62
    0x1072980343d040d460b4070a010304900c3c2401a00199161641e4a0070b460404681104105140d40a503800308400b0942602c203104480c42d09407150b20418403054030944844d9108030710807035805107d06500401045414400240520010421480d1031b250700c0c2c2c0b20400004c040c100c480e01902d14814407000c0100360268bd0f210f1540c41c004810344009040111095490300782140c442c0c1c03041c00144000c0c101920990400c152500e81041c60740000207024050582c01c0e0070203020050050002070345074a4640494090400c51002000200c0030204d411052071000c3c003040300001c0ea82c6001c5030780244201c3c259078080c02c1c00700c060301c1c549240448441e01c00c214003641c501842201d01c3c96685003040c00342c07190168003505c40a00082e11b8440d100621800d0b004140d48107032040d80b084080401d9000c84542c0079183d06480050f034440050038180c510b4002c20b40604400355000440e80340c3c1c240841c0d10707900ca02c07100383c9040c00000741d032007e840181e00c8254a80f02070048207000440312100e80030348401000361 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 908568237 1250 908566987 908566991
    0xd02100b330d021e0307121d0307030914010305010341060a140c0a2123010b0f1c0b0301020d140a150317120a0c02010b030a08030712 59
    0x4650380000d541c039003100101d04466a8045600481420260b59040d0803400300c0d01c1080c690300d0002c0c0d000e0300040041d51481c204550b124034440960b601500600d26030b0f1182412070741ca41000340b80040c443d0b84107010300e24280d2a00411020554001d00a585c142c075030001081c1d00395107440c4400c48098034100303075403002c0d0200459082c50300580041003681c46042d26024044901c0d05000e028180c0d03048842410314104143c080201030440101611705110382d900c1c3c101d1030803200e011203400111640c88100d100c1441e0207072003802d04800000e01d45000b9040c0181603000e81e81c401c07034482d2038003030440440c908110030801142c803840707882409031034220921000204a07085001103400c80c3c00401c00f2040007039886501c3c205140e509880a50303c4160000c0500040000c0c101c2035412960a200007003039004041d4040600f41644801e82d400340036403203484036a5141a00c00742015101c1c0060003005540707011141b44a504011810410442c0c000740909d2554484242c120b482e6005100210119a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 908569487 1250 908568237 908568319
    0x901060507060f0f0902030c0117061e10090302030f0d050a050c032b1a1e030f0607020c1201231806090a0209182d0f0d02100b 56
    0x58042c1c842c0104c41c2203403e6001a03080c0d028818140341c4402a1840c1341401000b500043c107048c40d0422547e80b00f941600da403113113002041c0e4607503508603981001591103c0b1142e6280000c5500c40044030490380201c044030405240d4440040d2190420400c000002d41c040146003401d6005400030201c0d00b0b0100100d91030507400b021a004a0254041c040c2c410001000b040b82c00801c503402005099602414030700d4050001000060f1064042c518104a48440c07004105440d0b60501480c20101e210340e00b0345900746800da174000e40b00d001c4e14508500c210807005008044040510900700b4440ca10400b145903400b128680c490744100c005c16505060b0702e040041003a0b21b50034080716008100800c010441d21003184100110301d64010b221012050075041185400080007030381c0c1050284071501c03586900ca5405401d2440c034000d81c01407071a8030400f0100c00c5e0030f00000464250704d80441c2d09880540c811050032206441c0080d41c0a680031030192402c3c50500c45032140e014005d9030191000d8026 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 908570737 1250 908569487 908569511
    0x6041202041508061602120c100c20030a03230a050916061e020a240603060603080309100b0d083907050316031e0501110c010e01050105090106050706 66
    0x40000c0307500d0301d1826810200700c001d00c1d070101f14041040e6000d5219508007210410a9599110110694030100f42c44503801c101c0c86002c0c4500c65407a51111044000204040d0015aaa03074411310b0701800007480e00110b0440049400301240c00041500413400080d200d05100c207001e820040c0c46241e0038064100034034690740030b6128000003000c2907100c424481210218840d0400c035500300c110195040310102c403000501e200c10b150480a00c1c245500f00001641070100020710b09a040280542c1c50040044144258400a54841d00d001c02c21074481c01e00e07440a007026110054091500301500c04481c10004256401074030142d420100780e004c4102082c20011500407403800d01800406454418458504060201c80701030801a4011700c185190102401c21a0712944005058105880e95014410b5020319900c60001e811600900c000034441c0c090b41403c0e400018030480d0356103003c03805940c064040c01aa8100d0b000108075020b503a180c490151202c0c0e1028808984442c1d48140c1c1c0441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 908571987 1250 908570737 908570743
    0xc030a17010f0f091a120d0908031201030b1018020c010507171302130204030615170d0c0303020c34080d0f05283b06040e01170c06041202041508 64
    0x50400c024008006d0301281c011f0103044550309400c40030042d001040002c40042003020f2042c1100d51021184040d541c41068400f01042650041580004001c00888000c0c1080c0c020306486140d0000030003a0380c80e694000c0d900010794443e203012204d51000040c1c120f001d8204100c9080303001510768004117281181c480100d90240e013048860a994207031481d500c50301080d00030301400d0306485001c11802001d1420340d039215000100c07810862003140700c008042c4a901170312903100e00e0030101d50160f889421001c00602c6854030040c001000c0d070340821070314415000301c9030032501c6840c00f0f048210703084007045070301c04100322001341132000400c030340c90460100001c502c070240c400f02010303054103003100c030000c058545140441d42240d45880d10351a030000102031a0454030082c0483d00266013000003c6900d50017980c4c452820030349103000000300451a0741815030700c1031419040c2c41c0320b12001010800503000741d0240b001c14110f211007280042c20164002d00400c05089030710a07000b961390200e075103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 908573237 1250 908571987 908572009
    0x30311212a0d06230f1201020c01140709060e06030c071721040b0612070b040608090708030c03030403050d090b09010e0c010816140c030a17010f0f091a 67
    0xc03962400920a1a06201c1d48145406440720301c2180c40c180d1050942200710300e01451344a4464001113844466030740d62000020f01ca001e02600964896004204160082241010345031181c0041350016195912404100040d201141c40f440780500008040c071403107400c014251031540008000c0719021444801700360943c1d000aa103125035032290b14040541c1c0200007880c2411400800080c0b00002c2e4400800d181d0020b0143d9020b10140c00c111019450505144c0c440d4050203000103003c01c00c1a4072502043c82010680c00715108035940301b080300e03a2445090721581c026007051001c600001c0c408d000070311166100403000308a10105031101c1004040a07600c581041e990f490201d8410301040c41a10b0300010f003401c020a580c0303846200c3d0040c000ca03a03821102009030304240304540c0f64500090300e5030300b00701108890700c400680700f000c0c15400000d40500103100355100005911203c05490400b030f1010b665048004030b00c3c3c0b17540700000e440170100c560345190400e08202065101d4404a403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 908574487 1250 908573237 908573311
    0x130302060c101a0625061a0901081621051b0f030105160c050109050d090f0e07020d111009030305150a12030f020f06040f03031121 58
    0x121011500001c0c00d8102d0f266080c9003500c2c0c58201e520584280e8507030060301e52002815000d940c0005e000c8101c10510000d007032004109611344030000003138150b9490340c0454030200391004203a45c0d0f00da0700b0696070b80081c0c6c3c145c00e9103860942030a010324072903514405943d03c0385249038005000c181da00c150074495107030301103004241340105440503880c14950404440c0390681c02003106040241e140d40c40d880d00041c21605000c4076440c00010080258402400e80703405c036041d1403021040348801021100e140c81000343e02120380070301003a81d00128510742d000e604160014030309806140c605650076a40c15680c40c610380102c270503902052030f003402106030951196230700090364070300b0b11800d40071074000386915400703040c0901e0244400d2800020004a0a400d0f0030300c910895800001289802c3d240e2195001c80c0c003800c4180002c100117501d00716940d92007528180031b021034003010b05501d4094460a41007010420045406003c41c0042d45500001000c01105802451400e60314211058810780 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 908575737 1250 908574487 908574493
    0x80f03060418030806010e0d02151207050c0a0b19050a090c0902160b0c070206040905070e0f0627030102040609030b010f050d080a030603060e0c010906020c01050708130302060c 78
    0x6024a0188645121a010032100307402d80411030714010402c18000744994148a461030002940340d450340b401d002c0307041d4003c0402400c03880f58200581c00d43c10140c8401501c0700c0328004503081d41d000b102541d030021580340c014107aa1b002d0380c403401c01400d000751140442d01011500700030203a406020701da1080c2601c2c0d034082814a100e15000200d5005507019400d04c0740b0500030303071100450749684511040c0c0c0024455400343c84061118946101302c000082d806000042c0004800d6810313009148070340e8143e21961a03046903603040c402600714503100150300c694100050700714510703c00c0d030b4940f01020000384000100380c0f490100342281e0164000001061629104100300700c03040403903d0140c544011492100e5203814040751002c030042d40c2c000c00c1460003042068906210b540103070000d54000c00d00380500d0341010f180e65212440ea803010350005240300000f090107400080d0440c400034042e51740b0307072500d03016803140d0b44150440b01220396103203481000007001d655044051710300541040c2c0a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 908576987 1250 908575737 908575741
    0x4180c03140a05100501052d21040c1203080c030403020c030d05040f0801020c03031305031e19090e0a0905160803040608150a0b0d1404080307110a0c120f080f03 71
    0x30700032200c0710b180c0c01541000410230540344101d12181540c510088484025404402c0600804409018034145010094a0b40d5600492a55050442d07030285010b5041042069201d10007049201c1003054060f002c1294240452400c1a4480045602a02030700c140c0350314103a0000043c0c24501480b0343c00c0002200442c050082c2e20090300031070001c000c800000c6207410100c0401c0da8480c0001080502c55020319669a010320905004480c061008487d0608000469000b841a10b4124403e41201100c4040284003401e0183c940c50056600e901100e00c059541c00c1005406012681380403a464012803401d0303a03c80411a1000024001d000090b648460400400505844000f080110b0540055880e03852640320311100b841131715203e00d04941e85240c240c101fa4054904465150f00d29856a0304001c284144100618040d01040d910000040c0e0440c00c0d0700d582d080300c0c110103407075015142c6003000124107465462002c24401c4803010b15100150b25034009580161403408040e200c0001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 908578237 1250 908576987 908577001
    0x17040f05011b030b0306010e060f12070603150603150905060303091c02030c0a0e1b160507030506090c1c0c170d08010b071511190c06050a0204180c03140a05 69
    0x75060808070980091911f50715182d40c80030a41d802410391030042c1281e21402800ea00c0d0403013540c002d010517004a4080c5999a54000e00038030310040302c003080e408241c801080c130301e100b802540c600524100d404000e107401d00e00300d034008000c0076110907410302c03040180c81e03c01d840744802c11405590403202e10142803002d0060505058111076030a10071801510180f1143c00d1614256810606c5a2804246d08602c6100504107109140c0c3c1541104901c0c00c01a040142c009000781c1524460005d03101035803500f0f1442c0ba81c49031070070b0101784c1c480603d030340c0720000302030110540e02c81c140906107019005036100c282c1210b04070200b403488042e4206641031002e03160040c1502d401040c1c0d5542c01d5103403443ca911081c402c01c80c1944030040c0725450300a0590400034003801d54203081600181c00c000b44052040240004d09400c608982c01800c20000403c41511842523404990107003104c1481080f144070010003c2804180407803e059131100c4004039840b1104143d44a070194250002d000d0920306 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 908579487 1250 908578237 908578241
    0xf090c0f0e040b07050307091226090d1e020d0b09010c050306090c0a2312010503070303021c0302160b0105121b12070905040803061f17040f05011b03 66
    0x50800a070021000c828400000c1c202d122450348900c26292060300ca80700c0300411202d01c0c0d010b5008900301c0c0001d044010601c0105540c1440d41039034011450a172584030714804103d4081c0b14003c0d41d2120300e0040107404942424080e40c040d80c480403407040792110344d50000f80310401c001d405403030024080b010040640401d101d02240740c1554144141540303400300008030340d210020110100d110012403050b40b0580281c000c084c0141d60662004480907020031440c01c1500151119903420401100015181c200440c00c002520307003603405081c0e03c20780c4101c143c000c3e01c1003d419800b01a800c00880c0e012040c08945490094801c120b000c04551402c0100400340812082d404007980100e800d00400c40c44981e801c5501e09015500c3d015200b0601150307500b00203880d445402140d041030104000c00030f00e14010752240f0421100441a00c810f48640440e03814a030b614440840c0c1203031038002c45604502c100c654464881d00c09541549031581c4c4071070941d80ec0d01c3d45100541001c050400e0555058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 908580737 1250 908579487 908579489
    0x1701021c091208060a060c080d06170c180a0504050f060108010b01030e0313150507021201020301051c0f03050315120106060f0c0c051302192a0503120702010f090c0f 73
    0xb03454041d10900700a000076211801e05c0c444e000034803040701400e00030483d5030304c02d6810307542099a080000076951440071a050194a501e1850f40c041c0700c0543d80e2515103a0b01d4071001a8500071164221398450107403800030304000d08184c40300c1c403400c5546001e4920800000b80070301100c200200b00c007800b000c000340a4484c1c200d00009250018011901f40075140d405140c1118488c0074100b00c445500c840665003403050080281d000082c108546100040c150004c40c126070080d50400c20024400803d003140b0100c20380002e22910b0f06901103000b0900c02d0020315044490700c64082c130b0000c1180b0025000c003240b400c404043d44d442d06800c0016a4000caa200c81d82c140c541000c14100c0515540c081c1e8010b018090f0130f10491050361a04440402541a14840b42e00e0156002424210080160803c1c0242c002044c8501c103038044449000d40b01480009042c1c0e01c03800035401c206d82e48100241c135000c0101a0030456507540719603403019084d400303001266070003800303050103080c100014080700e0701c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 908581987 1250 908580737 908580773
    0x5090a0506010206060112150b04050f180408090a170a0605010e0610110705150310120b04030c031404090e070b0a050412080f04090605040c0e03071701021c09 70
    0x10340410803019980108813154468000d103050000c090603600e01c40300601d881201d03810380c4c214821010640032310010040c01034405c00c5500d04402d00d841300404c403080c0300d1508966000f200f208049400078240b807018010341a0020031600b009501d41da0b112030300400f00c3d8400701c0f003030340645000303005d0020a1003890b0240c031600c80380100381d241a0000c50401840c404c1d1460030000c6c502c9104e500e40e142480480302400740240703078010b0464180c640098030341090791581c005182002001800840d04030000c100c085d030010030706140d503036903440c19075a821003410181c0a01106c0103891503050b03403000c000c002402c44080002984180a64840c2c81d0042d20f0700002c035460020440704120395041400e5400301d40c84d240b62042c0c21201032800089502808452040c0600003103404940442e05402103000e8420540d0708000400c030800045601001962a680c0c040e000301905000c0c628071150078104003003005001602d0403036441175054118182c502c204240306d9540d0944d400300444e2036101522024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 908583237 1250 908581987 908581991
    0x8031f0308090121050403030e0f0607120c030b1302031509060d141e03091314060f04181109010501050a09090b1206190e030c0c060a0509120705090a 66
    0xc115511100075110700c4503583d052104110560550200740d40300400900c0005000340107500701031a01034060240352103150468000c0c102907400d10000000c0c0310388942e00d10f81d41d00400c60f00c02d0903054000c041814025003090b4981c02c0145407074586000381a901d999035440143e81c0d10300700e01c003488090780001d00a44260400e0742072010b299135010506003110380100010703c141c00541d8005d132a0210890700c42512444c400c403110300740e21020015040701c00058805070300a00c4a600003c0440c1d00b020b1350a10180c41003400700d50b0340d040c00c0d62540114500604001019410007010072168200d81c00d00b2190000800030340718040c240700d1050750043c1720a0a0050400d0080b5801529241c0203005141d01540d841008818560380e0440b544091140003050361000e003030203514800c26503180a07146150f10300708643c52408250000803071b10502041000340108072010f508100456001174140f02c10404280302456041c2c2d123040e842400e040000004104c2c0c0341c501014020321080040025042074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 908584487 1250 908583237 908583239
    0x306210b0901180b090a020a0f06091208270a0b1e090a03030305150d11030106050a050a0501050d11040b0403121722060510140603100b032208031f 65
    0x607203581c4030b0107984200e11130343c43c0d580e1010141c501503d0344000707984100c402400140750010409800305a580c960b54098009031a046541c0407640c004000034540708042105044103d5203010410001581458600242c0c41c41000100382d0400c581124100c00000a18060800c5d4a8495025106c0000644505207900070000550707580003440040d0506845d2800180910868100f2400c2d98100401035405460039043c42403104008580c03003802907182030000b1549250824801084036030041020f0700c0075003414011580d64000e51800105591104007503040b00d04108040c0c030240840025243d2103901d181441344200d0b448158000034006c03001c428200800720b01464541c0602c1800c030b203810b811241c0c070108a41240c415409003201d480c2000b070280c0f10384001405001c030391292019141d14455502000114402694501a0181501030400010b4203010113554803c01003113400c680c1051071065004000d4000c4401c9442a900200304400d80540c8103940e089243c0013240c580146e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 908585737 1250 908584487 908584511
    0x10902061204050316080306040515060d1d01020f12010b07080904020702010c021f02121c05130609150509030c070e060409061b020d140414010306210b0901 69
    0x252258000704000d0381207000c00036042c810f00f00300b143c100358480c05072248a003980303041620140d00241d0707400d4842c2d410070010075520002001c2c071596100c402056a0700d4250300040031401800741c40ca0080851102500c2d1215200742032014211014507204503581d903000e507815030306001c10160401c40c2d6125080c0803000c04520703484140c400508094400598400301c60005071441c89218038000c0d480502000031041c80401110301200d066250380072980b4002c4a41c00c103000a024404041c2c0d003025500919021004543d00815041020320600440c54000f40c0c0b500803d403900c000082e50a0304003406d12107400e00c42c2c2c0c41050345c414490b81c0030b103007002a118003f030b445659a200382072200e481480803070b0f84e80d0b80e0b42e806038601580c041c90401c61a900000ba20b6500349162010f4800f42c007500e80b04044260144001c170042d01c04600d00513140a060818480c440c50042c2201810141e1314040401c84401c6100312031185241c401c074071002281c8610f4448502d041c0200b0021451741061407800e24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 908586987 1250 908585737 908585749
    0x7111905150709062604050a060c050a1e050c0a03022a06032814010e07090321170c1902010b0102120d090c0314010b040504030801290d1a03010902 65
    0x96510f240341004e0310071400403503450802a205605010070f1704117014001003040020341c804d8038a00c90303001403000e24400501074800740944042480803807514510380050100320b107031440d41c1c468035081840c1000d000b101c003103203407040071401100980c1c07005840302c1d91540745080e80320901c0190170617450090b40300c0010030348601000c0c000c0790400113811301b15884a451622905041e40105070704108083c0c800028103000380080c440ca04d4022000004650314500c101c1705401070702e401840080314414590003000481c2c150501034401c0050f080d802011810f030003e49140101c5800006c562150007007010f210101c0984890001960715103e121900c41c0d0300490b01c0403a120b4102030240d2145401c40d040d10150400c010002d040b40801403000c420418841085240c1070300500080242c94010740902080b0b900aa0707007d000f0a0f800d000400c403050600790707040140481104006000100700062121036041600250403441d12a80c0b007a040c907000c288443c01d0820f04800a1004079229008071341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 908588237 1250 908586987 908586989
    0x80a08010b030c2703160612051605030a151403060709080709090510020c0304060801120f0f0f060c0203030a1401140f121204050406060203071101030507111905150709 74
    0xc1044841d9000b081140e80d09070501c14024010b410b49640704810044a010014603014010100700320568034021284642700c1c69118402904400148103c484025140e82c0c00c02009203c0031903c550305100c5280094000d40c008002085181c0903c000f00f0040504100b0300902c90000c00c4411070303080199000000b9100c0885018090000340820517017015800c0503001c1c800e11240e540000759000701400000000e008a035001c3d43c840041d41d80f1203c40c3c0c4407181300c0c0d070005050314010f00740c00300229140010445220b80301d42e00d00f40d242e141e00d540f40000d44e800000d00c5401340c0c001204000030901075004800c0d4a280000c0141d00a42c1004080d001c0d00c3c9003149e41502030f070442c0505031300f1307611002c801c07240c0450a00308580d5a18024660070710180d105014090045061902c0000e8090001003940c4080754040c40341e051080400c80114010074005045000b0081e000f04960866102444003844190042d1304091600c0d80d5410000d00d009040c0044c01c20703114401c0c00700301c0b90b2540816290 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 908589487 1250 908588237 908588257
    0x1050f0a0b0613080601060f050c030d050703061e0303030e07061e091a030103021c03020606010c05010f06170708152410110f16030b060a0e04080a08010b030c 70
    0x3070104101d0012803003a001d2008060b40c100710346500482c40304c90006006040303c9041c1d450f0a920803001c00300722524000e034105940c455005000d5480755a04507000b85521801c42d20b0001441503807203815202c49155040008000d8042080c1403050580c10700403250412072000050112a2410200501041003160380c1c500030000141000052031040d11214000c0203680030308403100c40012044800b40c0e0082c40128400c2038945049040e03100c502c01065880b40c4c154001c0e044654968005403031743d40001d0300845840d540c03401c11003040c142e207102d0070000c2c050081e100403424070f80c42000751038141c56403c024140d42c80003188000c01803c0e8140349612220b4030000c24280190308003070b00c3d50f41c4404100182d0201c1441005030b04564800d8108400b0455102142c40f10174824000640301e00d10351050341d0011495003010b0005c038410849294001c0406031060b4800c55941b0481c10101c54162002c403030004002540f238030140d500c040341a0142c01040d41d007034594105200d0004031071003600500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 908590737 1250 908589487 908589491
    0xd030504020d05060103050615040c0509041505040509010902040f0603082a070b0918010e0c0f0409020406030b0a0b090f1c0b0a2702210709140402011101050f0a 71
    0x203011500c50002908040d079021049802c60f5859250003500c4400c00c035181c040c8004940e0340e0b400341d0729060107980485c1280f41c444c03d240c0b4106000f03120182502e6804c030018900d24a1002809888030b200703440c450004040001000241e501c10842592110300c0780c031000c24280310041c00071a16460858092420040d083c0792140401c0e0f8428101c0c03030500000c1201c1d4000d1000004011481c0001002c45841c201d9081c0d0440c0224124510707007076800c0c000d052080d82c1e660002151005680c1c014036280040240d0300e82096561401d92050b0781c819001140025107554529016080104249018090385803565007030000000201d920003064803009032182001101c00e0540c2079070740f0041401c107a04941600503a15000e00340d20041c2941e5040490404400b05484880e9280c0280c814510790340100640c0c22020b00d040e00380007498401d00c0380b100034045c2c07120009810f00720388501c80c0310b01c84107038002109203041d00000d41000d4503150209456410402088034074102260300a912070102c2c140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 908591987 1250 908590737 908590741
    0x80102130e10030803091507170c030a090c080c1813030e0a030218040213111204170408150c07151d03120f060d02130f020d020f070605010b0c0d0305 66
    0x200c0ca4802c00554009044028000240006d12002050320011814004148002a25440750458101e0024400c1e0750388511010085120304050b4070003103412005540c0b0129401160f43c85441d001c0b0402d9000340c0d0180d100c4004502a410040c00e065590240d5032800400d07442c1014400d461000c86107801400c21603241e02c0000c4036626024050055600501000c2c7e40d41c0000386d10840f20801a941a442110781000704c03c1d043c00d05028140da41c1c0c0d9903004490904000c00b1800820440c0508100c400c0d0301004a5111141c1006001e003004050b130100601c60726145110100080cd40505091201e2804200e40f00205080c800d41801c644d00001e000507224101c21804a14450080072000090000040303206003d0b24428a0702d0066200c40151111900c440d01000901070394074200070f411850f00880320b692601c9540c814600c41b07808400c054900501103590f80c080368031a100f04101d01c20b0201e0b0590910446200f00c078090690841210b1608031280070541c0d170707034a502c20000105038031400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 908593237 1250 908591987 908592001
    0x40b070201180303020a03140c0a080f070b130311030f031f050307141e150d060b031e090a080405151e070314181507020904030315080102130e 63
    0x5080c603490b461036140321600c0b6164500252120400c1d0f00680010398a000b01c03c80345002d0408491580c6000001081c4044469035021242e401403215009403440a020790008203084545c1e5a01c140155800080c030020186000381140c10701e00e200c00f81990040c001489500b8a22048a4002c07204001c0c0808041d41070842d000c5440c4a6081240c01d800742d04800a1180750000f600d92070303000100c94214800e040d480300040f118280540302580100c1040d0041c0703144503d0340003030440c002140008a18580c0b100e070b049000744d006882607270101686103814414403a00408458012030484040d048400007a00d405855010703902899105210318a445006140c108040710b03120312006054891898000d030058020341c200d144194003142400c030601c04c0d051b110108071114140e00b5413031011000f025070240000c640c4007032400200060104183d01c0540d890144581c880e40c0709a0f00271801c44040c0c0c10003800c0e0305c0c10707a010503400e80c018000d4140300855284030f10251021415000c2c1306030744201d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 908594487 1250 908593237 908593247
    0xc020906040905150601030c03090c03030e03070e241206010506031f030c0801060609030b010b0a030908031f06090806040615030c1d010b0304050c0103091104150524040b070201 78
    0x41070041092160705a14071a40d550a84c0300c03440748000340c030104901e4800d800d0580c19204882002041001c0d5a031051000074003400c5140d00d2060007a0480f10010b44945c1004800c03142903c040550407246071101e0940003000307401004000f01520300c01408e003525071800c7d940305018050144212004000140d03001031080b40e815140f0400001d4100895803806c1c0001c1401d850b01807038103a54200000070804a0040c107409080703aa0001d09051580e11704184445681c00c400740340d45c10140c4400701c0102082a02d0040c500072400b844505590100030440147d041d0590b40c0074105200b8000e9041101e01008541079505c6034000101003044200c00c0c1e4043d65201c99900001c0030500c000e0400310b12f600071b64a50500800341c1207c2d00d003459895440b83c06007400210340007852580220103401c81035210746c00103c4414410381d010140c02c07422100040c20380e114003404201501e00c10301f00708040d160002e4450442850b614206407150008030088005100341d005100d18608001401d100f1a4451 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 908595737 1250 908594487 908594501
    0x90d0f05010b10110709051b16082b0c021b0f10020a1412070201030e0c1e04140403020a020d03020c0d0c080d1e0c06020903030703020c03100605010c02090604 70
    0x10400e140c18442d200000c0c01c402e0304c41e02d05400d6403040d80c41c0401c2d03000c2d941c072030117008240304101d009010403040e000070b0720741d8000d408144040885002c9200042d0600c0c01030407403000c04211100e030030300b600404060261300c0f0840d108210740c288245240125004110a030082c0d618041d240380042495010030700b503003481c4801c25002406030118400d020307030105c3e03443c140500c03c40010f07110642d801201690f030301404010010000003005000015802a4820710100881c541615802445a0005040303070416600e96003070020721094441d80d52034a482121030403031040860800f14207160300d00940e503600020340280144803040340c040515008225000304514010460308807000035140502e441d6219106845052141d0000380b18854040e08159100d041404202e00358551100d50071100c486d040030003950703655420002c01c00240c07010310040c0000c0c1e0003500200300c20b0103541d0501d07190400b542e0002c50341d6498410140003581c0e00030089103520707804075100021a210440010010304107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 908596987 1250 908595737 908595739
    0x1c08011823060a060f0516060b09071d01020a0f060b06070b040303020406091212050327071508010b0d110c0f0721080306060f0403020907020604060b0402090d0f05010b 74
    0x41c40740e80c80c03100d1802828651141d41c05407004101e940c1d032050281c03061881a001180481c1042c84122605505103201480352409010b002c904800c00c0b1001c07070502c9100340d0386000001c0701465042403001c8c240c0d803400d046540a03c014140ea04083e1540c0060a0100d140108a2520303040c05092503501c240039a441c0d01d03000000020b4604040c90043e0080d4801e11880c0301080313042c4000919205480f40c0c0884164002000c08103032000312004a80c030f40d1005181c0b00341070350201016080426260625980c020113140148042400c198805001020206010b01080804001404061000b17010b9501c0303401c009001041a40c1e0190002159005418100c4241d1044003c02e0300003080010b107a4040310b8044411140c401e2114100000404e4031303050140a040c8100045105030030a08000c2c00140c8010716542e0510343c40e580002c003c2e07a001d40b03403c2e0050340810148400d11156200301030451504890462a0002d05408a4801300d901c0d03101170a20044040358800b80a0290007868003040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 908598237 1250 908596987 908597021
    0x180d03031112010503011104060e090901060b041706010801020408070618090504080d0e3007080c16050402090901090b01031b09061704030804230607030203091c080118 74
    0xa00c54110668034002482105d1017507080004000600a05504480603030b20346540c0d00c1d8104d01e9000038401c0700140980343c5907181d0b607910000a4032142c0c0070040c001034624407103010b521901030b424241c5040f0042c0c0020030240d1040004002130600050721100301c403c2c504068005228500c4000542a460350001e0000c50511041000b00400b020007002101d1604e0020030201001c0125655159004581c400074504050080c811701c0300d8005081003261440481c2a1401d4182d50320340c8541d170454034066500b50f026104001202aa10f41490041d0000fa90114140703a080000203410b410180f01c0c0c1840503580e440b82181e180d2080c0c008086d51040360f840440b045100210040190f58030780718401c0000d000e4035800c01040c3c2c90303542250140340c050b030324110681c54680703440301e0240f940000c107440f518583d203414602c16000d00c00107200319016100103840b49042d400d041c0c02c102a000c603085003201d98040202e113054100f00340c0d60550300025018280c04d90840c2822000305010b02e508181c0c0c0c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 908599487 1250 908598237 908598247
    0x6051b091314131203060b04210611132403020f221e0b1207051b0105041106030907090c02010e0307080306010e0a080706030203071b051c05180d030311 67
    0x550f0001002058410300342c113104d4900e0000c2c00c030300b210007a02400140b40420070040100e080402c203050800844501c0e040d840c81882d03910041111121701d645100820040381d040310b000325039120709005125403d030000b1064002680520915001c2d0094001e050303020882d00403482d410402c1da0340c041c0103c0304101d03010016410080404960703200c3e41c91510001c140d0584200c584111007012103c50218070343c01c1c0a402d404000f00458000d2480d0708122040c41000843c0d0000c45202c0005070241c00002214205428880b1207035010f032150901585080041c007601200020f8840708403a0141c2e40014070030120b41040b400760058117140040743c4804280c06051000b00801580200c80980303443d8068245441402000959481032102c41e8100e44c0781045800e010f40c008507440405450241410494840606880001441c003070350300e0340c05403000241200c06403038050308a800904080c1d0900703598030030b24811b40041c102824050750041628004050103900142d9004001c454429190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 908600737 1250 908599487 908599501
    0xa030504030e0306091605151209010222060801090507020a03080910060b22080307171e0d290d170a0f03110313060b2b06051b091314 59
    0x42c0358040e0304003906c4644460001303918030b0b1226940e4506e10050010030308041258108000705c22000b0800c2e03060f55000c000c1044100300300b92071104004802d0384110300c0c02d0b00f4080020002041604224001c501e8102402501c0b40c000a09001c0c550341460446820f544075042541402c0700303050900109418624003003507561004010b450740780c800c038180c0441501940b0049100c40650f00c680042ea40041084030007258070040500d00e4045059103c030325254015007000103401d81010384034000c80b40494941d5004107103002e04080c1c400c0e44101505a006441c002c440001688030300c0510440d01d1a080340100140c1000040c41285001e400c3e03a1210808400644811030804452000901d00702400e90346880107400c1e28000e158500004c468101d0740ea43d810000e040f160500e40d0700ca40c400320301401078485c082c2180500000c1d141c42281002c901d1a001e825600060144007628141c00440d8640301050015200c0b084022903402e4060b03411400e200008001014441018a82006c00c001d02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 908601987 1250 908600737 908600743
    0x1002010b120f25060f0c0c0b090103052a0c100e0c1c050705010c080c01060303050418092006120106021c0e01020c1306080a0c140d080a030504030e030609 68
    0x1403881c0c42c000c0d5840c030050100000e05010f0110107801032031050719000d204283c89401018070b10310ba5130900c1c9103510401d46035891450b01c0e6900201045100150320809960b00d4001d10340c00580c0c004040e00c401c0d401e980b400100c0c2c1c0c84010703030f28042c18000c0740c0007d42e0030041216403820302c0b5401d01008030525406203d9100d500c004405402642c00c5c0091001c4c0c480c044803032881729900b0030043d01032107080c0401165180801a010b0f00e00d0f0f1401d000d070003400002032246400a40c440c3d02c1e1f082d0754030700e070581d00c25014020320000c01c2e80c07515150722031010a41703089501c001e02d201988082c904885040010382c09016120100d00c0f00d031403440c00801e4103a00040c04220758a403907403003480c5d1201495400c884a06080e003665005030046031801c519801d00804101e600100d1a00202c1c2c001c4e29030810b01d1820521120075140950030366801c11011032246500c008401e8182e03031101d04070300382e5111400a445100c1251003055928000034052600c80c909641460030014240c888505003016100da0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 908603237 1250 908601987 908602003
    0x111207050a09020d380a09020c010e010b0102070f05090c0712050703020105180c010c050708010e030414101b0501140405012901020703080322030903030806030c0f1002010b12 77
    0x204080c54032403a00075500d400c5241000001701e03411036110807560340300203550b0401c0d0742050b180c004161403804204440280003410321350080b00700006c5c0d45410082c001d800e44641125850654210f000c0c1804a0030ae030003041d809440301a1038028842e1514900728006d03110310f82d400b4215504031101450829403244c024140c41d4060307802801281c441d41c00e035062001480b644e10650758000c09240e03a25501485007000118001d9040d10b5030310740d44820f1036007910714045884a00b604001010b0081700740c01814111070f11002c1d00e10000c103844101c0080d0052503000310710b01d40403140d49224010000d0035040700a00c000c00e0505483d10b400c0603e4428080c00441c03055609440c941c0a800c4482100c00c0d9480f60301680c1680281422440c5895241e15079101070f18010145601e0301d40481c040d02c2d41400d4107480e500c01da0f5034041a920310300700100407400141a180c8a81c0000d680c100c09603569455983c0c00a82c1202e07405038028640c2c0099005180782070380d040d044060580c04044001e40824407075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 908604487 1250 908603237 908603257
    0x30f0102160c05010e0a0504050a0e0d02010b18090c010c050a08072d11060a0905030a0305030f010807050915040b030d05090f03120a050c070b0f03040606060c111207050a0902 77
    0x1d405407640015141e01d981c0684260b081040c6c03000401c060329043c1c100036001640c0c5c01001403525042001642402101c0f500a40541c4d1240820421404c220031490994280049124070301c0c02c00100450322401f0045070b490401200d50201b10910034140145001254406480c1d40d0341c003030340d19010705420445c5d4418143c030091401030020545041140c4128079501c90030f8565484501810001d040c1c128071004c6080003901c2401281c0798400304014180240030b602c89544a1408009042007410140c01c4070b045038101701070070045500d0304001300c1d4100900d0302c0200d5948c005140840c005150007100e55505103d5900303a04880c54029004003000801560aa04400450421b2640c0d4240d50b40c04480031400030880011030b41d202c1e501a000c001141415590ba02c0c0d0b80300013004264029105904130080b000081c0010000940308020080c100d034201140d440483d61242c200e005030386140c280c018107001d00070740407800c0144600d002421000341302210041c0c84816401c02500801c03118 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 908605737 1250 908604487 908604503
    0x80609191e111003150603020a050c030c010515060c0c0f041b0c14030715020931060f030506040201031a04060306020403051209060301351507051303030806030f010216 74
    0x1000b80c41d4401d00400e01400507056003590300501e1b01c02d0440c001d6002d40b43c940100300d828880740c9442101840245103007a4450004515070800c40f405580b8403810310300b420300c101380812200d0b0700781c04003103a02101c2c22070440303d41f4041c050100c0803401404a085810602d9401e4001605086030001464503045002e020641d01d4521902c11865880c450004042c000006142005107500c11640043c00d01300c0001d0841c8000c491202d14240c1c00c600456121a61414481c0b90a1142940c0c2e03c42c0400811826035200c140d42d1440e141d050321200c0113000a410942c03a0718080b1380c1c00301c0c1c21081c042030100251042209a5903820450002d400074041142c09010790040d28030400c52520540300d07804001041c0b10b203145d01e00391089551103200d003080c982c80da10341e041d00d0102114101041c02c41d0a1082c0140c0b00412043c02d11820a1100030700384014001d0030302401a00f901c3e124100700c00d50b58076041504080d2101000246058030440b0300504c1036000151001c540301100e445184418030601d02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 908606987 1250 908605737 908605759
    0x4050c010801080c22050103050304140a0e0a0b040b03160611060709050d0302070909030c060b1212071e08070c0b0301081f090c1707080609191e11 65
    0x45410702001c1c4107000807a8085036001a0b80d28201504800c4400008124904e500480c404d050965800364800d0340c1e59000454100200c09020002c002c0343d00044620140c51414035100c00051003020b410301141e680d98800c40c84c076a40f50baa0151020710401421903007016071030134450402c00c050713008540018503c80551201c40100041150003041251a0710b200702e0301349818440d8001c0860020f408611844000246981c4035218146920303001740d44d480d1518002c0c0c217008050300e038422559405400e040340f440d90f0b07440300401c81c0711020070821040d0341e031440103084c81c1d282518104508944011401c841c4020410a00e0041084074814111035501542d00c0d881d45070385005c240704a00c070fa40c0102039030502c141c03000c607628501500c04810014503003a941d00c6624040a02e0303045022586d1807150509690001040a1402004150700400300d91074008011a224103114013004081440421540200012520501c010032039191010485500ca818602400b40100010390f000d85e12041c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 908608237 1250 908606987 908606989
    0x7030206401815060e032407110f2a030709090b061806010503100e150a12020d021c0f030206040c0b0c210c0f01090204142502030702090f04050c 64
    0x14031044010340411140d9542e01e0b1130380556042e0b40042e89140d160107032400003a94040d040f181030b9105140f90320403101c2460402c0010b0f298460303900101c03d042d80542084401c0b0540000c5504240c1403442010400e22242d1031421000c1c4100d061f502e074580500700d0045481d2425920041940b4090300f0440240d4581609100d04400d10751021610048903000060b2a54003a600668010205d0001e40f6800c1e039540345148101101a0f03104000481144106440c910300510200007030035902041c0d52070f00c1c400b40c2c0004c0106104880c02400780142404058000e29142d0304101c0c26a04131076079401081151030002c0d1107240483d0120340d4004c954002080e12070041c03090b076004954080081c0213480c0c00d07441030b400e034010601400c01610410042c0d844241d50502c802c2c0344218071300c0d001060f100e81e248100401e035002494009107021440080101000300111004500c003102da007030b940d460200500c104c2c01d44c42441c4d0080e412943d48820704c558086000074641c8224080c1c41130703c0140c20610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 908609487 1250 908608237 908608241
    0x60a060b03070f030b010e09160f030506011d04020409050c031609050d060b0d0c080d023007111503040201111b2e0e0909070302064018 60
    0x254020b0b00044208041c059003900a03800f01402c5030050404205900c481d40c00540110801c40f001351050703041320088840c064020800038040a0503043c02e01652804000080c41f02d102c42c80300c2a4010151400541c140e15190304503400f0384080d0405002d0f501c0c104410302c100d039005807800c0705000007450300d034510350307108a14420a4540041c00e584902450344c80703c0001e4244020349661040342e5400413000140003180000c01070044102402412855900290400c14402c006403074440c0e2185c42c0c0c140c011410950309200e1304041c030b40f5036218100d90a00e50118820003a485411110b81074105d000007400c080a540702da03200340d890341900d01300040c015460391401c024510201105421007500c0c0e00d404546c0003030300c0b18002d00d180001c6081d035026440d01094100e405000c9607203411000c809003031071000c09134030145c00e000400005255074041a0144248001c0d070741034090040c030202c0030a8610348600700303220074020380c4542d058003201141c14041d12480382c1c80100c5204101144429014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 908610737 1250 908609487 908609491
    0xc0f07030c06142a0709051306050405151e071b020f0d17030108060606040305032d18040c1b02040e0a05070909030e180711120c060a060b03 62
    0x8620300039400da00d45041030b00d108002d0306081c401d0030403d010a1303070700150031103900f901c0502520050602100c1d25a015090078099007018181038105030401c6000c048001030a031406510a03c0010143d4580c2016810031070405541c080d101c021805014118605c0d80a410b41c00440c0c0110700565115040b0070b581d00c02c4002c2004411408148188000d4a8009201c03656600003500301201d5600c80d40d164004840d0822a0703941c500750110052050380c20030041c3c198042c00035504903144c6411a1075440d034038001c204100107da4086010442c00c0005180020000e01ca8a0601a1039442143d0b60180d01c004021840740124684402aa08644500a100300d4500c48980d60620780081e2707024407002d800d0001e481e10f03891051100304130004030200b050400030068404001080031492900034210064420004d20480104000004035421605425000342c802e040481003d0407a0907506d0400d02d00702d0b0b041c82c1a443c041003030041d042010580c140b1440103603a00700b001e96160010102c40c0c0c041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 908611987 1250 908610737 908610743
    0x50f1c0f08010e1803040f0611010c02120d0c180605030f06011d0114300604050f070c0203250e160c08280c06180327030c09020c0f0703 60
    0x1910340031400aa441001d51801c0c0c09400c0b040c0d914054a407ca10038021601c1c0d8000b50000d480b00700310085858003803141e0030f40d00c0341510203000c80c010102200074482c050800c1740102945c0c2c50300820940c0e80a100491418070b0001c1141104035540c3e00041c0450304121028910380031403100042e810740c442d00c0980081d1071003120403040c00b28408011143d945092804168654003040420206119140d03c01d40c1c0c821075412004030888042c03168610541e014001e14040c0341410b003403001c1018003144056101c503551070210504119030002030f240910b030408011444040c0b0810200944070580c610041e51002840459a510740d40c01c03100010146082e03a800060380c05002000052088008000030900040c01c2600c13504000460136031006107491520100d860000100100300903070044005400040540c0b070702c00d1940e5200903011410b41c100351111180d0100c54030130800c0d0b845030707900061a0010b51545400e900ca440d620000c0d40800c8144000740305201d07503218001c074009010000e4a0b4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 908613237 1250 908611987 908612009
    0x50a0c0f03090804080609070f0e0705040e04020418110102071e060807121b0311030f010e0901020c07090c0206100b09040f0615030c140a050412050f1c0f0801 70
    0x15020811002003805140c12103d26404120000c1c0d90f950400c001805010802d02821416140071011079982c40503510540791100d80c2010003200c1c4d60010161011070700e5400520340325a0315440000c004140d224401d2900c402c41035102c07410711804000c2e61202031000c4c2c00300c5804030b854602103c46141d030131340ca000d9036940e100700c14043c1a00c1450f1094225080c5c5c2800004c4881040d005015240c0040030034503034042441e00540d07225414020508800501d40d1100d02d5030508034107503844030005005810b0311640d560080b4035483c50940c12a8003484191054440007510780c8600c0026060004c8840f005114400c003040d170941c1e048040c0c0b0b0480c1c00703c0d80510b00d050000c40502c8041c2c48440d4605900941e280c0000800f008030007100c1c804035070140d500183d26506050003070801d4075600030580c50303a03406000882405420008a50540364121241700101060780f60191a004000f000440d203801860b02030905a080d0001c071140b42c1c07030a6100c0341d030341240c00c01084440c80002d00c00c4500b948 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 908614487 1250 908613237 908613257
    0x2100e0d0f061122090203070219080d110c0d050a0507110d020a080d031a03070504110d11070303050703020702091302010c05031917130228060e04050a0c 68
    0x64000800355022a00c10a00400c0240720601484850381019800300102c540c6400c0070004c21034401101d4014064401c000c505500340345000941c0c402d1008004001b0a5080031300006101140003980c103401c003020014040c50001e2000c10241e41c014603840181441000310a91031503010b2010b80b00c0c084020b41c0e425003440607035122400701c03a510600382d540110700101c1d5000943c5030600000d029000000040502c00b50404c030040444500b60118082c1070402c0300013400c25600421448106c7e00100c80209094000c054155506e01c034a0001e20b5015280203202800300310f081000d000000c1c06034604000075038038540154140d01c10108020f500109101c00155103500034242d030a1003034010714042c000100e06503100791841d441416003c00314104094607a10403540442221080701361151a0205400c02d110207039800c22045000074403804c00710643c02c07440808070007021200742c00d01d60780f4655075035298000741c0640d908a08050180342800005203c81d0f204d8050100400b0705981c45101030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 908615737 1250 908614487 908614493
    0xf092711091504141e0603060c09030304050d03091e0b070b0c071b050a23010503071205010905011410020c040b030a020301050103151b052505100902100e0d 69
    0x1240c01010301200b0141c40c40c401c88543ca451040c182c03000b81a956100041c00c1c25800d43d804070101c010720182024400042040548000c24400d400ca0b03030240d020b9803500500710009081d8012904282d400040c4203d064013030651080080c0c0c00c507440440354810444c010b8480b0303409008607000704041071070200810303000181c4944481e607000311380c1c844e40c40c200070403942d52524041007140c001c0780400ca1000144254940561100f0082884010580c0f000001380405845440d031141c519041c00000310000720820700600740b80c3d0000154505c204519a1551100305c0101400c1c0140c440a4500e43c0f10364400307040c4601058400c900d240c00402c8444c0c1901d08001c00303009107070741050b094080c29882d2801a2400d004803406544161600400400a082ca11044503401023484c55000b4201c5180700c0758640080407100d09c400103442c1c1d450302005140000e04660400341c00104240f083d207101810254240d403201210074070031203d8640e03100903481e04a0f101c074981181c155001c0840030180c400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 908616987 1250 908615737 908615749
    0x20a091220040207061a150901091401020c090f160302070b040204050615040e09150112150204180207031413090e0f0304062006070804020103150f092711 68
    0x3420082c4003619084507542c40c5019034a000e045504103002541c0c00404030f150210400740900c45c1c00218a0500c00c500c0c0000f00340348880e100f107120540c0e41d4040001c09034800c1c0070b078a105203000703070021809042255038a004004111408200400f9804409290500c42c1c001c036051030b03400041201c40707522a90200001020044c14003a8010f01c111004901d410b000d90140c001030000e1554100f5500d8080c40c0c0034204044042942d2548410100501c011001c040341c7e08015074000308a0b14400e00e92046440c024890307900b0403042c000c641c1c4100400002c0c15001032aa0b68440c0c4e030341070800100c142801ca1280650441942d104074040e809025880483d8004c86210071100704403070030303a0600400300c0d0441d88a03801403c0000d200f05240b00c44c05162080b102c0481c60b41d280282040c2c030700345030018400038010b80000d04060f1541194410544c2d071205181c040c042c082040c0c3d228030741d200b01c0000200622031034222a5501c0304049000094203080ca6100681c200c0d0a00c1c071005680c80410103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 908618237 1250 908616987 908617043
    0xd09061413081b090f010b040308030c070804091e090b071103071e0b0f0103020319020f1504180e100e07150c1709031b010c080d020a0912 61
    0x301c031040940d0006801c2c0e00801680540c2c5040c1d060f155040b00071101801504000281100702c0d0001c40001002401070b007804880c212600301d201c0c9602d944405035040000d100700d200240c100b00c00400e0119444a0952001c0c0300700341d280c6584203492002c8900c060903104828005001c03903d40d000040d003242d0043e2031000008441000341c07031806800740d5511082d102403001c407446540130803040d20100501e01d030017160000c10300301c2900c00b190325550000e550f880b9038ac4c00410401100480c01401c41d11480381040c10040c005201e000c01000c000010000c0350090700c10080440492103403d000702000e4030480c0d8459900d500940004a804035607075010b001206481d948600c0f44080000d51101c503c1640c06031009107940b030542e9100300e41810001e5900c0302d5a90094400e08005441482d64009110007066482c01401d16085000100503134050b4042d01c00540040000668a496000b8980c0200758084564403400001a22100100058030701003034018100020303e40c9d0f4034800145e582c8124 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 908619487 1250 908618237 908618257
    0x5041a09030418060807060504240c050f0109020f0607050705090907230102100212190f06030602070c06020c0303030103031215080a050706030216061a040207080a020d090614 77
    0x2d2400d65607200b04100404030a034204070403941c0b241c00703100011050152200814440c58040e09040c24a041c0346100380001e4152800d0920b80d500c60f00f101800341d501d20001b01d8018058a9034900e0b942122070182c481c40f0130486c0b1907901d0b061814640e142c0340c8292101c46802c00018100d003401c21090000080c0d0140c40d040d140e22075000001600002d90301044030412105130f5a94101c80f000c000640351901030000041818018840d01c450b40c0400c284103035201e91152480c60018800a0180006003100f0510185480c1400c1011040c803d6680003010003501c10b413904d00700713182c0c1c40100302c0e1a07540070802654143c20801c010404203218010503101307440302038000070300300c0e02e0504544a04030055209110541010300c0c00c0303003400b000b40b0400c0d0083c01142802d515191010746040d440075000c0e03038000d2415035109280c00c03454001e04031000031800d02810440d5103807031904044409400c01070386480188100d80290f03903094480c40b2903030121200e0341c580c0c003090f120380701c610031715504900445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 908620737 1250 908619487 908619493
    0x12041815080c0f0d050a1a0705072012010e07031119060810120c03031706031009080d060e10080f1e340e0402150306060706020c0303071205041a09 65
    0x400880c000340002000c580c07042c9180d0106a15082003010241c1f4024014014803600344032550205852000103000200071345042c04d0054810000a50040410231040d041503113815031403035010500052400039a07014417409011450000100400d09241e0542c0c0e840c180c00d144400c0050b1801503150641090490300303104403442e2a01d07000c440e042c201c10020b0716a089441c0c4e0400a040d00000d90880684181c01100e00602c0d0100200766201031503068940650fa5514408041c020803109545c480b018065003030000c4c41c1e0714542220383c00c1040c0c6400c1120081400b00144844001a2400740740803414003402006040c0d888040c0104000340440031a4001c28180c03c07007060941854100303000810368600000c1e00c091203004a030546036003240035158a203600b4000541c0d0340c49800301012882d98103403581d980e40d031030204406010f2100c0c0201007034008660300040c202e01002861048640b6a506c0e1029a8040d62200079601c0a0b200600080404482042682c150f01c0005a0080300d920031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 908621987 1250 908620737 908620759
    0x6130905120a1202070b0f09010c0c080a1412040302070506071a040c0504020313030225090e07081c080f06060d09022205041a0108030d020c12041815080c0f 69
    0x1580c0140c1c5d000c41d8080350407081c1c1e042002403040040c0a15034100385140001c014001010b00046c0610300c0011024100f680049860107400788120a03010304201d00c0c178400c0d6200c800b0702d164890490310907282100540100714010626080100c00d841d0341541140341500b2006447c0780d008100d450151040d90340941c042d0010449803038a000450007003814045a00d164845403c00034100245182c3c0800508089000c014080140314503140c152468440001000c0348441109481c0c08082d40c0190542d000d41102c5040340100c143c8055800003c1e610ba40300340d03558012001c46c0c900300844500b5440001401410003601587d4031203030354544050104c1e0002948002507000305410f00d0b1952021503194030401003007102022800000c2008441703401c00d5941030104103074807402403015050034160f002c52201d000e1142040354060a01091044a5480d51070381440112490138440010384a810300301010120f0b030344288950200c0d0010000f074104e10a0000400024003800247c140d0300c0021000c2c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 908623237 1250 908621987 908622017
    0x102060921070b0c2107201c0f0201050f0705180a091118030c280e01090c110c10230f04080d140d18140606130905120a 53
    0x4482c0740208044d0003c40d8941c004400b24000454480078016040103202040c0154550080c5111484002c800d420300820041d1800f40c40c50001032100c42c0e01070303074403044046c030300c281d04030104540795106640240851307554441281700c0ca10091b80c0c06800507008002c0f8844080c85100850701d0070070010907003194681d45088200a60382c0d00703000718060300c80000707046140d1189690f510180c107109401811418001c100003070f10611070251542d40d045846052801c1d156050150340000e0300c1880c11400d0700d5611104c0180003040307854040400314000200320014040300207400f041d40c450040c650f01100344004822180c410031010500b00c401885081c8589100748400a8100c41c8640304415889500e0443c003540380c2894800c102042c0841019480c0c1e0f0f0103030807012503100700000c010101c2c40e111052940d82c0c440398006e001610381492201003407a843c0000c5210743c000e8000300d0b1175100101d102001d22088441c000401021a170025180442c0030904030302070080d6a0040c104030000218400b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 908624487 1250 908623237 908623253
    0x3090a062111031e01030203030301260a110111060f04150b040504110a0f060915091706010303031a0306010905250306060f0801050303182b11010206092107 69
    0x207100800d40368400f0081040b0300001c3e03843e02d04a150607110704c25640d403440e004a03440b480180142140403a0100c0d200000500c2d040342040c02e01d0008045890f040705c5800d041e0003042c88a110310340000d20103548510f640000094440c05040c400c034405c40140c44564400607100700703110105020320b88811150285582d540310b9035220305e000d1042c10244651b90030070032803c02ca841d0021100c03016411014449141c2c00581c8c0420f4581000c00502c0c1c0420328032046d2030046156110001c0c085035520284004640480e1150480e486a1820311400d41e401c0c180700b001c0b020110591340c05a21010041010703c4107070b00b050381c01090040c100200407264a0f0b01e100d02a04c5d406010012940f2040100034003940849600c10301056031501032a0780d411f00c4000f0740c80780315030790040b980e84508051b99000e540d80c1059040038080a86640d42c040c0c8105410281040468dc000b038a40800e001c0e034102c0310f54004107881d845050703054050101c4503482a41010360840303404003074650110501c000c200003000c103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 908625737 1250 908624487 908624501
    0x130c111609200304030e0604090914010e0f120d06050604030807110301022b0b1906090b0306090f13081201090507030902030c0f1201060902091203090a0621 69
    0x254031040c14490504240c103050354101a942001501c4000980c0ea080800c03906a0390010380c10b15050902c80c100000159070380c021500b00b001c0162601415400b003100d41c40480c040c0358058402404551800f844090312144604203443d1241c200080305034080c1403840042249081d4a207000440c5031311030b0082005500305d40c10441e00154000b80c00710074050856070102c003a0302c08a000350725081e10b581c0c440070840c1342d5100c005100186002d01341d14854092300b080c8040a006403c52032000c500640b06107007a8118869a004200c4a00012441109140450b4403450000d00f8603c41500c03001c04824007010020100c0007042d806442010004a8010007440c1c110b201c00c1c0041320650612100c0c03021188003803e2901414641155240186c60108614290030000c94400304503500034808640d178500c075444001c1565180c2480400e4030201a0302070440c0c3e00302a50020f020314071803981035a0740c0c42004030056208044071800c20100b8407401000940207044602c0082003007250719440c041c3c07400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 908626987 1250 908625737 908625763
    0x40305010b12060402010e010804030509090916050f0f0d150903020102090a1d0f09071d150d05070306023006010206070306031a270303060a050906130c11 68
    0x56034988080761820982e0106005007000207011036052035400a401200324000890620a0a500007000e250088054803c81d140c082c0c40d030701442c5030410342191110100600b03406240c01030180818103080540c050501c0c060090040503030a044201001011951450100c03040c1008801052081c0000c1c026001c0c2581b007a0005a11403040c6420000104010b4026290610801380c0250511200724041504540c0103004c00480381c070307003080250804a4903080102000351300010703200048184140648290402620328074104005c00070468910f44038840a040342e8496881800441c0d82c6d980180540380c002c004c0651081d60700c10140002d402c0030101100c4040b04c0c50204186560140038041e400710017071a0410104e0700f50b9030341031103016030450040700c015041e0000a429007400300c01820046291701c1c0901240e404496440c0d9250300483d0000d0040c41401c83c002458100b1903041801000014540900c17951f0048144008100325118182001402c00c82180d58003010b101030005901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 908628237 1250 908626987 908626991
    0x30f070e040213090c0f0315020304050d0c03140a180501020a030504180917030f0606030c16142b170f041a090f060c03090a08070f0b07080103021c02310204030501 72
    0x8030710300380300890301200c81c000f23403001b8010401c001c005000071a04203014001410a404c03401c400b400c04840040030261100f0501c0340005104400b140c0200300c4084500c540003040400c940c80300300490f241d00304940000c001c5041884103015800d10004000c0d1b0103489498000361444007515400c846040f00f2001c001b40c1e000000038005e50441025100b0b9015406546141c654100420203035628450042184030704000b15421804100d1204190030511400100312110742468100b114401c0c1e00703460382059040f0035144d84640d500d01925904487c108403501c1014580d60b041034040c0b6411000300100d03071308030701c12071541151840440414060740d02d000091401150b940c206901d44140a08058120720042c420000d50200000d0100b50071a4400c44840d151842c0f40307000b42c00c80d00c0d100c01c0205145200c0040001e0300c0e038004000c904890089031100000381c17142c403c0c0c403145090000080d40250108403c001040ba10001c40244100c40003145074600503020304601c101e1b0450340003190035135 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 908629487 1250 908628237 908628239
    0x15080c0c1b01120603081603050f0a0314130308010306051302040606080105010906080408071214030f22150513020424080d0f142106030f070e040213090c0f 69
    0x564401481c90302c3c188180f600700521811503c8140180c080d01d101c2c03600c589030044c1d01c0c0782050310440590b407a00c84034040864803281411405006840d008d40440303020065070300001c010380a0302c100c240b03010381c1680ba0800e143c0d0035900c1d174002604004061900408040c0b02110040c0c0704c1d4843c00c0018669a515070842b541418001455010039074440c4040003506414080810200801c0b640b006510800c280d200184048080e1000302900b090303002200004420446160000684588541d40c2e40b100f9110b000d12042208400b40c9840d04040c100d04028415171156280903071045402c8222a15129040302e120b600040039030307001501005403401405802d503130340140586654064003502d400f0b44072441c00d104008002104548586c41000720071b025910701d00d1144000c03914050a04030b81b44806000618150740111015079469009215005908240703503400320743c5000781e41008181030f409481d03d800b08420203448031012482c4599071280700f40050032902c0568001c00070003a0ba10995 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 908630737 1250 908629487 908629489
    0x605090f180a03090504150f03080a0e01110a02010e1c050708070b1c05100902070506041a150904140d080106020f0a0c05040f150b0702091015080c0c1b 67
    0x441c80700e80100040d034400c94408000039084541070042d04c03c00d80e400944a015002d07420702103106544480081041c101020040c041e00c900200550280d03511032550480b0340c1070045414020780c00070a20a0341203000032100645c440c180c101403141004000342c5000c071000b024041e28001c2c04100302c400398410328040218007020b009a03c0100a1491030030704041c00403407903804140903502c4410f0b140d176071100010b0303040e6150350011014101ca000300715110444da01e0400d598103010340e0180c400b81c4070660203003440640104a103100d44401200700d4681d102a400303220400002030811a904c004000d0240500001004495810000c690b41c440440d45040c0001e800d04c010801c01e080c031900310f003980c0300106801090210440d1001d84000031042c414101450050510755162806285d0144001030205407800c0030740b4915000300c0e45000c0030384420452a1a1403924030031202443d01c11101c49100a005d020f13203642c0801084880b616120643c804a410109104c5015180041c1c946410f905 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 908631987 1250 908630737 908630761
    0x1c0305010b071a07051606060e06040e03041502010b120115081c0c110414190e2104090608031306031e020c0307083015040f0605090f 59
    0x1080305004180c64201d050700d42e8480d012854990721004503c030000b04907510720490456003081201515050070440d1441c2c440c0180c14140700e40c03440c1040c40c401040c2c1c1c038a0030740308242608861500075071809140c1008540c90351000012a02036540e03e41c900980707a00d071044002074002c03100340006400388000f120711801524940250600743c1c00000b280015081d440b880d405100c0703e81c100302c5280c284524041100c0750f544220b240d009402c001074503c45c10240000d6900500c40c041c4490701c100c0380c0490a004940b52200b54015560060b002c00709203500602025040c220302e4401103190603107505401c010754a0a600208040e880010360120015400b18042c015100a00c1d003409940300c80091096001742080990582035030004006440980030000ca8500c03541c491400c58403114100b600320344400c0c00f510750462001d50094800303178400003120f00b640304807480a81881c0201d020000c0c000144075000041c14407a81d18400800c3c42d0f0740e8441580d104140750042210945030000090003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 908633093 1106 908631987 908631989
    0xc0c030405240d1d0f0c040f020f0309070e0c0705060f10091a0a0801060b030f060a170a21020304090f240305010b01050301180513051c030501 63
    0x603d0310380d9500840d54501040078100140d0080314080c2d6101c6550f9901c00c072441c0c022000003441450542d00502421010702c0c401810800c03414880d44030341d401070f100e9201c0d50740301c1314003080324044542e00a44d1001801d8161404c00103290754050307580c0c1d0050007818510044200051505145891100003402c4000007804000d41d5400788a511200740b042041c080d1104601c0451013200500032042254140c000052a581e0395800e512018000503180742e03408601c04d07400140201107120a00c03081890740000c5c05c0c046d0158070b403100074002c500030746214001c403050f02001404d80202c20354045030b02101d0301294001d03440000c48010072284650017805001c00e00fa46044540c0c108140c01542d104400070404c00070800019103580c0001d204071600c01805042e01020318400307400c00c5070090308100700b500c100a500e81d01d290415074242c5860241082415281219641c140a002c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 908453237 908633093 := by
  have h0 := BRFrame.cov_init 908453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 908453237 ≤ n) (h2 : n < 908633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
