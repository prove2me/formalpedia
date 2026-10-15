-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5217
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:07:55.986274+00:00
-- url     : https://prove2.me/submissions/b314d519-7f77-40d4-90fc-4b32c298d158

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 938129496 ≤ n < 938309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 938130746 1250 938129496 938129501
    0xc0e04061d091204050d0f02042a0f02073c05010f080c0304150b030601090f1d030a0309050304080f010c03050106080f0a0506010201022a1606050a0e060d 68
    0x140a0380305028075030407048480020074100a4201c50050f400303121140000200030084508540e4122130304800c0c0d0b041072805240c580d4040d88041e5000e840d180c98107506880c58454010501e040900703050114102000503076202c50303052100300040e03008402c140020b0320f11498800a040781c1c24407226040c2060011840c02c02d00d41c07085801c0c940e079041020070981d60082c4c040c505945141c1004d501d14a09000200543e000041000c0d0519030420807031114243c00b5032003011280009400c1d55003641e101c00e80d0740c0140a404140c88001803400f0500c100311211000c2504074a40f01401541c42c0c40b5840380210058207500c60706a8050004200000b10074a00704040c2d020103850340c0c0042005050454050100c4405070f00606c1488040403c00c51410200c01400d9031201c14500700245544071600100e0081c01000610100112611810014420305e0401c140101c00d00604644140b6002c141000b07400816104040201b0b405112010b50680100c044a1000002170300b801e003051501c1e00d01c1c405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 938131996 1250 938130746 938130749
    0x52d06040b091047060a05040803070c140a080604081b0a050d09090b030606220c0315050f1c020d080703031e0203070e0103020706020912030307020d0c080d0c0e0406 73
    0x70300001c0c1c24840c40500340c084004000c407131201c1c90500003508000c03c0c0000002e2009030402d229207000940f00b244180543c0940740a8100441102d45440b014601500540305c94020440d08000d5200c01070540d1400d8000b050a8034451005041c035500d6503511100d1581202406203540c10803612007040d994805c111000b25540940000d1440d80c3d0007241c00781200301c45400c250115410512940b80d2501c001903240e800000a4900006500044200012814813a5403003409a41007800c1d52180a81c160440410001c48250310120155554100700e0601c0090707481c0b1b500001e0341c1080302e001c41d02510f02602d1141c0007070405080d00c0803594846c1c00940c405c0d0030840110b95242d00d00402066017407a69155807030140c03030031851400e2003c0c0140110507002400340c1013540010350030040060b2a01522049a0044c01507205c0209807040d00c0c0e101e4004075021001807158482c032010240c03040a088040a0304885020320780008144040302074601240118103001e04000254487d49442c0301d03010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 938133246 1250 938131996 938132021
    0x20307080a05070e0d021909150311030a020102060c0f0f03460f0f021306120c120b031e030307171b1e07052d06040b0910 54
    0x15854001c18000403104007074100c4041166440d10038100e0388641480c4039406030122803035164000311012034082d00c482608250321083c100f4000508148240b5545000c1d05c0c0710350b40c030500200d880400e0503914010020060300507808130b00451000c00d485c0000b011140d40c410768040c13411070700031080c40e01ca500540e04220308041d0b1400c15200c013034182c081e40e03818081011f4640c0c081c90801e044c2140700000010411020b6503502503040103031080d6440603840c000c031024255100c0044a203001d121044511803440410103110100d85003c8080c4104d203ca104540c403500c4a801801280c070000f0070b55a45c0032900362007517451040000c400c4c2c2c11240f442007511002036a60385048500107142d101c4e4400001c64072031082041c0b100b06481007052010307005600709c40c1a246ca82514071031010000035100304401c2c1200081503014440085500d4443c0812003480000e6035621101c1c1d0410429070100010698005001040000d00d0036a8426046800c01049a004007000083c201c2159010390600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 938134496 1250 938133246 938133257
    0xe01050f0402090a090b0112051b072603071715040e07050406030521030106120f11030a05040606060903020d0f050c090907150c080a0e0102070b13030212060606120408191110111c0f020307 83
    0x3034103544503442000c8490021448601c0d0c3c100140c401e10300b040154036040c4265110907501d401c3e0b0004008070340040c8030050052100760303500d040c910b480381802440d507010001e8108802060140c110112812100240d4a8060250f03984a85030700420b079801d10340bc0c4244c0c43d0900e112180d1103100240d401860071000008a170b0500b45803203001c9855a07403111b01404106c84040000d030780d51210300002d1603040344050000d081d507031400342e00300001a1390280c5d00c4102d00c001d1004d80400011480141c030440d868007951488080b005456400d0403810061800d8010403018241600c100450f070302016040c0101e40312151510180410f5800200c0d00303c0e51852201d408000354504009003600e01c001030703000b41c041ca08020011480900c941000020401100c00100302040703000030403900511075107402100c0c01102450002d14100034018103100e00d1040d58800c2d42c44a0f02345c41698028050300c10210f1030114095040030400240300e0403003006641d60000611812040d000440c4601c81a0752171 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 938135746 1250 938134496 938134501
    0x40b09010909060b0f0c0f0a1b05040b13021c020a020f011406090f070c0237060816120926040e01050f0402090a090b0112051b072603 59
    0x10100344440d03000c0000b07141402410049031382484121541021941d140c2c0750385404407144280303400704100e0307881203500c2201108404c0c000c00700854800c1c2900105050030035642c4008000c04d8610000c1c0103944501491501078803820a54002c2c1004804840c018010044003c8a00226080707032103500090b820420182c0300c42c041c00c3c420074004c0c9005105585c101d05200b00400d10040b0000c2a08220101c95004641c1950084003100303009540240800495403420302c3c9414481c08918030305485012090301e030003442c146480391109584050340d8003020341e9a480748a04417804a2000802400700c0590451204007aa0213800c0f0480d0107101c43d040c50b100380301c011852520600d8420154101c00b40001d018034040710b0080c85c110380c0d0480b440d03580412681c0c0094000c0c0b14440c241075000507c00000070794a18650840c82b000a02620b5461210081d0600102034031412514440030a002c0b604144120394002c004d0806039004080c5040900c104101aa0344a51964549880c92401004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 938136996 1250 938135746 938135749
    0xd181b061214060120010609020d05070f0c0201080601030e030d0204030c0806150402030613051006031b05040905090a050d02030c060c040b0304061d1e010c09050a031412040b09 78
    0x48410079a510610800100c1444840340b03204101c09000c40c0e0421a070f24401c64155603241e0f000c081102e81d0b100c003c014103540d07044004020b52100d601c051800d4140000103100c42d02a10b0032200d141c50686454400346d60590044070350030002090035050580d6201c1d501c124060800143c25640c0201c0030041e980d034110f061a40310030f01c80e40e11504855000c42c0c200610310f0b40056030580105025503025880380c881030002190005402c400204152a001c104288140f03080188002c641e03050300d04000c065280c280d0089031001025000d408240204002c1182c03400c1584107542c0300c41d0042c15601010803581c0d80ea42807559000c03113030005a00c0815a8021400244042c0e82c000158042c1c02d03291a1408031300c1d03081d40c080144060401a9512003064070742191100c00c015503040d2a0603124103802c0c01420082010880c140d81c2d030a5882d01c5120b4103e00c3c0101885c10a4550041100504034550f40d2810811018090246034034000c1d003281d060b04040713180c09000078281000115031100358100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 938138246 1250 938136996 938137007
    0x90e1203070206062b0f110f010215040302031b030901080c0f070f1707050304030b100e04110a260606040e1c0e1c0201080601170711070513150b0307050d181b06 71
    0x317407548114040351223002c95a800180d00c0042041002e04541070369a6070a05034150b0255480e907084001600c040c040c0e50300c8010009101c410802d0700c0b440d040d0340b1040400c0e0200c3c080c20005e80c00080d03042110001040848501c100014822103000130001d0b140c3e15040000d4110000032181940081014020400621903c5522400704c58203a000c007071412038081050a40500040c0caa02d0b0444289611521501075000c00703000f01010300900c03d0700c40444204413910036101f00202d409006c000c100e140c607050180f00c07c0c40c0c00d540010300800d00e41c80c04000b2066804038103c07041c082141380c1c0c24182c0d02c0702e601390f5103e140d40150f4000c44400c140000f41128400601c028100066414035040715008450003640202051401020804104810038604000c4d6009190320650242040c4ca1111454002003000000074604882d5580e894101c010180429113009000c80c00034020011b412200e41d004050122188055401b18002601c8920141c401b00c43c2c07501e40d030300e80c0c44002d10610780c106 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 938139496 1250 938138246 938138273
    0xd0e0a0c1d09030313290129070c0302013006030b090a030207090b0a03050a0c0f060c030e0f0604091b031503020109141801090e1203070206062b0f 65
    0x3005546140303488846502c44ca0403182c0f004101846400c3c888001003000348629046d4007a180c16030141303584415502a2441c00c1441702000d4100c0075900761041046101602c15403640108088007042c2075600664a01c03650f131514a4164590803030040d050205000380000800c40300320000b6440e800d50500c130307003020320041c08045540c0c01070900c0d00010754001540021500c84038800034070403004400140b002001130740090442e1141c42c00c0ca0040c086400d0141d402c5401e10032040740403036542e0005075000d4400620190214400030580902810001e0f006990407a00401c00c51400d0744074031610044462440079000003001d030042d8181103030b4042c0305040d813244082d04000305940c9036a00082292201d405041010561507954007001d0301d541c4032101d1090690318070b00c41b107503840b201920700604419a45558034496405e65045016514045074041e00540e40a001c05a4940c000d002005c14010080460780102440704412000e110100c0e80c0003602c0f400c002400120141006403c02c51607 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 938140746 1250 938139496 938139511
    0x30409060311180f22060509010b03210c0a1a0405070f05030c01050d1d0d0e010c17070203160b0a0e0303090a1707051503010504150b0d0e0a0c1d 64
    0x91110700b0703d00b003502c00900d507801290040b0341038090340c940c0d001c80c4604c00030510910501c852126403108100c21030b0855446230220000800042081104056a40384108072282510040540e000c1c10050241c4c020141e4081550440d4000001c0da43c402c0f0b81340750a6000000c40003602400d100810409000c180001c0c0101398140942c6800d03c40040d440f41c2c030000c4d81c1814000c0008610302114965000240a4174007081110089440000d94981305c03038161122900003101c058041180d90700450f42001041d4024003a848445141c00e44882d150380030b00404d981c1445005072041c4a413a4074044c1002134000c001140d0f480703083d200d0010302400c1203e11347c180300e81c0092040c91030648420818000712114141c090a014000140140c05c14815400c2250054000c0e082014444000e200440c101c420565040000f42085500e0300030825090041580e42c510030003025501c00700ca90408800080c402003030359001c1d186030340e4040100c10554441c0121038070003c000000c20070071550242c0d10500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 938141996 1250 938140746 938140759
    0x507030b01020c36040507060f020102072d0b070e010906030e0d0c170304050631120918230114010315030b191808030402060a03020c030409060311 65
    0xa000860b0074001c03140507448584e03d00c03051407080c40350b41101d44c1d60441c10104407860707050504207591528030a0042d03202140b441c090540c08203105101315001d407070b00521042c0c00e944040c40c00d40e0140e010100810380078902c010100c1c0c04a110f0fa0101d5018920a840c0d100003000c030b00e0005040640340354002d500f81f51400003c90540d100204003005403008505c0c0910751410740303280644030070309480880b283c00c001c0882004100700c0c0000c0c0e840c0c0984403d07050708c071454408006000100a040c20500840642014180c0020f5005841038100030710904200c040b464451070400c2c1000c40d05000c00c603801e51900c0907030103543d2101542c80140c0080c030417125031a42c109984051042e0740380360454101a0344070000181c09880c0c84405000e15441001300d401420145010a081185000d80004c1989044401d019111000340e03041203440d80000d9441c1566565020000c161b0000d028110515808100103c45050103200030800303010781100000d14141141004641d038a00d00303022501441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 938143246 1250 938141996 938142013
    0x10060804150e15060130021b0a05150f040f110f181f0303050316120603111e10050319180b010b090901050f04061511120315130e0706030507030b0102 66
    0x403296100701d4100c2c6c1180b14007682c2c45491401c403544080000e0100110b6008140000040260101b00c01c45c0d00940d0004000303150300c6046a050001c0003e0750002c100b0100c00e1117480008a0300380316801d0544001340030b8003088185401260700c850f41c0c4005140416040c1d403c006680002c40502642c035050081602e03115415580c0240803440003a1900088000040a0200d42407180d2003d08920700c140c0001e1086c199245030290786a410061014030403c1c2070880110300070780510741d080c40d0440080c0ba60841d110100c109580a0f0b00203070200c07211042e01c5485800540c2c07207020b400c04440144400f584650a681028461100182c2200681e1082001607407915901d20440d41e043d10000c40300041d10061100c0040c0c000d2281d54002c003901140102c04489054205500c8200c8401250680380500c500c1c004400691000700d84807004480c440950340541e082100c0d0310a035680d03091000185030104920054981000303a031102000076141c1c010407040035414001d4205101c4203000800282 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 938144496 1250 938143246 938143307
    0x10e0f06012120091806070e0415030b040b0c090a170109052d0303090d0e03073201020f0a0311031303061410060804150e150601 57
    0x400c01841201c041c4010303524295100c15a1a00e2200b09039484060000007504010072406040c0e1010080c038480c0b282e003400900d54902c1c035480100071400100107012039589400d002c0e42c0d010741891082c0d0704141c0c0d4110907440039501c1c1c01c90310042c50096843c50714078070307140c0b6000b44146002001e003400301c8018000303480b02d900ca000c1c40e0015034440488a8448a0362000c440340104000c020140051013024104075010781030f0101c0c201ca41c1014000000c2c1c0c0101029104c0c1d491109494514441d0302c441e281c1d901041c03060484031001c10009040d196002c0e80d80000484249101c0e01ca01c00200b02d0304038815038a0b020320817981007000280040d188078086c800006881d22080c54024061144420002c2086001442203442104400d1004580c441c1c982c01e0007001414010380c10000c0321641408034031880e03401115002100c5072503803550b4040d980ca40d41e1501c42d00031008078240042c0c0320302248281c40d07424403036000340c0d10311149429040d20380308000503c1e0403450407564440703211816411850 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 938145746 1250 938144496 938144503
    0x60f05070c0b190e06280e03030f04020619090524190509040c050306090912071401060302060d05060f0402030c0a05131e030b0105014d0f010e0f 64
    0x20941801e4114440d50080140b00c026113010090300d02180152010000e084055074a0940100c4181209070500a0f01000e51400c442138542c00300c000b40d00074000034405680350030072143e015201902d6117044c031007609030509260004034061004200c60460a101900b02120003880c801024801307a0250841080308d5006071199400805d20405540c0130402c00601a004880c402600907108020350400d00d80024400e4000380c8a6600c5000c4040114500d040005a07841441001081c000d10300700b80d580d00c50005441e8141004c003d552901e03000809641d84038041d00f60221070500c0480c00b0300d050f00400c00d020410010141c4981c0c410b0060003400c40301c0d4402d60700b260443c0e0030034581e1200c40110100502c100c1d60320072081019a030140c940000216041071040b684a21094201c0b81d0f01c03100103503210240c41050b09103110714414400060f50f0501001d06401e40402c411620032048115602150011011418990340c00068032004d80442442403448208030b000c0a4000300f0f000b00c000a44 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 938146996 1250 938145746 938145751
    0x207030912030315090b03061303080c0a230d0b0414070311090a06020a0c08010b032113140f030703020604050f03100f090b3405070f060f05070c0b 65
    0x2a600754046040406001e50722003800000e2185840041569492001c000362000f4401e05010380034890106001c05401c1801c04801641502c5110142e0b5545154241c036401207108002000760303030081d03242d60501c03c510140ca006004481555607070708620340503003a26044290103008038900107a0f410303c007a140703585039003114241c80d000c58800b082ea1100340c0035008881002c2e0744099030340000165136400003943c00050b0b11034030012022955940305142200c0c600611980c058001c4002c103004c0407a45a034030701004000c400d0450510100900840c103040c110b0300302e0038006460260174207280c50a41180f40039050110000e205260450340403c1c81c40c000c912485001d40c400c8506d0b540180d50a20a000b4140040f100400054414940384005820700540540b05291998003144521013a82082e00c843c010010411180d006025001d600594603182183c0420000340412030001d442c240141c01014003560000c2480f400404c06070301103440203040007091000540c1d8020005490103030866 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 938148246 1250 938146996 938147009
    0x1a18040b0102030d0203090a0b24060a051b160b28020109150b040f0902030a0b10050a0905090c0301060513021c020c060a0b0102060921070206191202070309 69
    0x3020601000103030716501a00380d070700706800d001008100c501c0000143c0c0308981c03402251a482d503912082c49a1500217844c3e81c002903680c10300602081d050078904020011299107240081c030b085480444521070b01d444e810060915004100b100741c07000890b081c49400740102e0b090b068a0519400b90741c0e01200e244844000c0d41944500141c01c9541c001c1d44a2600181c0142c000c80c1e0460040655600414801065900c51842c1c4500038800806038811048110360107002013050114a40700c25190100007001700030303480c05228021032540c440580380350080204460110701350811040b018149452112824041e82c5001c004020681e2004402e21155110500c01603640c80c03102d42a1007101006440309a0040c00090b9a02c8041c00c000790040c0b258004400c10040040104012626600d003541c2c1d6100e10392000303000c07408031542c0e50b0301542c00c2c0d10b803003044902e4445180c0c0480e0190704000400180305880101d50a6017035000f01a1504124400c003003185042c0741541c014100c5031803802243c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 938149496 1250 938148246 938148251
    0x5011d0a020f13150f06020706080414161707090905121305040203040c06030e1b151e0307021e030a03021c060e16180501030c02120d061a1804 63
    0x24240d502c500112881e025806a414400710101d2018142c100074103105d500c0300d005050f04001919480072420380c061700c8080d9203102c09a100c075220f0458000d584c00f4000c0aa006c0d80c0015131042d0100c140c1c5600500a000c00c604c2c02003d04104c2505007411a40310120a074100024640012400315006000f01d0748044e03040e44418078a001780700a8199904910381061000045c4024813950354070303030412200242d40600c80c50f00d504007621b4840ca6441d802c5401d00c49144e03c04502403034919450090000d41d55510341c1001c050681120b98070104000c13580603e000001445001903040c000f1402c2640c14425a0144004000556581c4c0c4120f403001d0303041590201d03035101f076080000d400172902d0701030100030310007a0780703400040d4030440c8281d5100380003901d410350460116010307049062240b0707240500382110514050040d0041c0c02c10f5400f48085010381c1c482c0c40c0c17407403c00e9000380c04d440680b0000081c6180c1060409402684258488601001c05109181214441401440c1c8082055501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 938150746 1250 938149496 938149519
    0x1050103021b0105070c0c0b16030e28150207060206040813050d031218050703060b0f090c04090c0318170f1b161a070804031202010905011d0a02 64
    0x11540c0780900c02c00404029424a0306025070701c1d03448000c04c0d0a5502030400d0040481c0d5941d140c9400e8441c10320380404032411203000a000ca40100c0032284040c00c040c1071200c14034840b9074030907069510215040b0360600b4140301801740350300c614440e01c445000c0b400100754041c10141f01a40c1c603000100003c00c251800030708022031341d801d04c424100501c0c000d40071017030f0f0310f065140c003230402001030703840e21032071850701882c80040c1d5213941d0703010101c4d60090301420200c1d0441c0c4807003003d408010b40c65a00301e007045c0100038281d1202c2c232100d4810340480323101750748850401031b50b0001d54007480c117a0000c01d401d16850301040442155110500360b1310419001e4200f01c501d940300460b00500c08a8032001d080450240040240301c0c800d01956010722060303510950642d03c0c40b0b110060b4501414958144001301d08025000d240c0040c80d1107801001d84030308042c5e82e503840120410310400c0d50801030b51241480d10810100b40500c0c42c0401d40c0c002441d010207200c08045036645104400030303120740085800c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 938151996 1250 938150746 938150767
    0xe011202060f0a0f030e190b090f1e0c0405010b0d02030601020a02040c0c11090c1c0204082a18130f0206070f0b09070303050405010309150f150f0e0105010302 70
    0x2c8464041d48448250303140c6248038405803d5642c12060b10b008030381440d6110f803280c407010a10031010f080300109580001c003a03846500b40904001d09400c0349107e001d108031038041d000c0281010300940100305d065404e4106020f5070810303041c0030000d8040e034280801840700505203010348540c2a000c8400503101d690300c0380100d01d0120111006900300d8600640c16405540c041c00720780c9207900401d050304030059400700f800411030046400300c02d4040140704400c20324440440b2007480164228000d03061035190031100341046070005001060248041c03203003c000031840e031249008602100c0e8903000004c400305026607900000d2465008021080e0002d08200d45210801d41454000d41030703540741d440b0361610403150b40c1c00701001d481d1925540d0000c1c1503903400107031203000d9941c180e0340e85082c5440c1100540c05400180700841e0500700c480d03900e0f2115142c40c814040800c1d0040d20129030322107042d00c0c03103100b920203800160106110031814020391051074800da044400a10300143d0301e449855 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 938153246 1250 938151996 938152009
    0xe0114030102071b1a0304020f01200708060708090109051203100902070803040501061e0e040c05100e01030b010f02190614040b041110080402010807051b03070c0801060e011202 78
    0x2000241400443c03688154405101e42580c010717100f0052007050601d0281c140e054480c0021a0300950101d90242d14a42c1c0c1c5d4030030105580e01e80f650382040824a8540d00b102400c1901603000050780f507100408200c5019404101c0320b411400e00700007000044034035107407070781c440d0071002041b0710316200000400d090710720b5030915070000c5c442000110b442d01d03440d103041d070815407055070141e03103540c20a000852100000e0b40e48180603406482880261854550920000f01004005a4010030500000155902c804c82c4d107914145065582d1601000e0583c009001c07560f83d109014108004021525141600001c24501e00041c070b543c000031100303803442c15401406940202c0c480645100003404100801070781d40c980102d100700e1402d816926504148640400d00700e4a0000142241c00420055402600c01c1500004580b8021f440c0c655850003a40c4420081003540f1b42d140d0000075160180918007036681c0c0501702610003440f00c2450043c1401f9000c2040c05401540c00721250810b0031903640c82c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 938154496 1250 938153246 938153257
    0x10c1a0702190c0806010e1905041104110705060f101a0d020c070e130f0303183c080906030a29120f100f021e03100801060e0114030102 60
    0x240c0748034042c11902d00d000e03030404010b0311601c0502d214a01c004100e80f540b802c00b541c0700341c0c400d0945020b0300501c0400342d00600b1010b4400d03120ba18180c3c0c0c0b010303200e40301ea000b00d010340b500c1601040ea85644502d40185404130042082d6880c2d159a800d100c0341d8000d101ca0700c002c07110305500944940705130078200d0b070f118800c0f408020200c0340b00040d22080040085074040494101003c20b4036580e88400c07a15060380344a0100411902e1900c0c0d0450001340240e001039104c5106075103000001c01c860707580f08038a8412182600000760141e202507d100710640d58400001b0b9420080982d000c2c0359540d04407140500b150440c42104007200040c006c40a540c0b01d00c0c0f04c0c82c90032020010a007542c80c059800f5849030704000340100440004507032024000075001d041c0007076010080c03c081198048000080c101c6d8250317500115001c0082400c01e030307174001c0030650106035070111540d0ba0401801503081030340103038451000d07641400000c10060244507811811144483d02c1c04a00310440000079009202d01d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 938155746 1250 938154496 938154523
    0x62d0f050a09081005010f06020604120f0e090906090c0d0f030e03102a020102090a05010503060402090d080405040e070e0c0a0c14010504020a1406090613050a06031505010c1a0702 79
    0x11a903114a42103130300c0c0c0215040352102c980120751291a588100d0320f0b030400711000b42101461a0f102502181729401c5003a07500f44520f0100303006502c1c03d001038040c0f0425030700b03c2c000368450380a00000210034000342c040c0c403104403038102d4003125030ba90b1150600300c8104040c0512000d40c49486098400703001c802244ea00e1003508211f01d8203510084020b401000020001c0c0300000b02c100c0300001d005200325800090005d099000461904004644550009040540068080c04561496143c100e840940103104000550300c550030f001c01d20084502411100820303621009040140e44664500150001c0e2010120344d03807207846c054152004d5070540002030140d80000402d4020b1101940081c0c040c0d882102d11800803030b51741c0c0c0d000b1003c0c9602100781c1d03408071080007030700d56604e004ea00410400c0d42500402910568500020700421000e5101034086038650a00f4981d83c8503814001000c1c0a00b401c01600007171650b101c02030040120811117903203131642d40220700c05a00170403441c10030920 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 938156996 1250 938155746 938155753
    0x61416080a08010305150106051b19030816081003080f0f07030e0112050106020706080a060911070606090504031b031107061808030315060f090307062d0f050a0908 72
    0x900c0c03034005010303031000d02c0261583c0c011b800f950196420031040c014120382540c3d403518100382102c0d9640035207004c1050070485920a81c0c41310008890b80d0100f008440c0d00031785943c5402e00d0444403004c0d20031140c3d1311480402108030708211b040c03d107108003170094076001711100392211031000e0031a126205484400080c100d000c034900d02007540c402d0b08142c40c02c01c01c0e80e45c0d144800425901c00103443c401c6c054100960000b02081c01418850241e4591010340c00f1070100c3d03950b507204803400464100a00f0114007080006604d820302015000346401055522410051071620391001045114417605800060f0b00d02604002458418000800e0104480381a40c02e1f29982d14809424080c4020010400d40280d020000746403c02000340e0303124230400b80007441c01840d540d042115075440810782c103070222001c0c072094040d40c43c1001080064045a01e074015103d0031810500310413107039400d44142400c200100c04090300d5210300c2d501c1d03c045040c2842e58954903404800e940d181c5040e0010300940c81b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 938158246 1250 938156996 938157007
    0x1a0a1404051306170a02060a0c02010e04060306020901110a020117041406100501020c061e0a02030f13031505090d110307062a020d1b060b19090608030406141608 71
    0x82d0a0780080c00325229488000c01c50030509400903103841d115580a5402030381800b4449465004169211813903105143c00c142e82c03028100020104e41442d00b0503526540c3c04101d07101c455030824500800c081d0300c0b03001008440040d50008114804941359264906928030208040080c0107030549840d5440400342c40341444c0518000219890b98800c842c014400c04007440210306008085071500072500000c449031440251840c001a03000e00108421480200005c025084100001d04640011210942c3d030341403075401c1c0905842980450207001e14903040600201e010002030240c00117669041c08a00c0e2481200794604502038480f010740641d05081001070100b0110800040212100c824a020384e01c800700106d90b80c042d003289000c04541080d0072840622402c622500300700c0d101e0f00000ca041c021510100c0e580e103a021120424504030714006010039140e5001d440e002d0903841e0001c600f4540b822030300600390102c103800c0030b0300d20600080e0840610a07000c81005080d8021304140d039100c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 938159496 1250 938158246 938158279
    0x307051812061504060509130201021203131a091f0f0e0a0c080115030b04050a0204140402010305010602031e0d0e1f06060806060318070e070201151a0a140405 70
    0x14070088890b0043e0b564a185915081c0c6000e00ca4079007941e4000d000100c055032080300c25121402c5405003a415407003103501000c4c2034009640214841c0c07042442d14040b0442c40d02e81029110314108104040c884103d08100400c1d4000518041200b4018000c410314802250410b000341031840a80030b8a604040d880e0400400c0000c03400c007854172440c03442d1401640c1d414194205d52002d80403020300e10109100300301080b044480300d074020b80141c054920107850780e4001800c03101c0c4411044a8901c444c0100001e640e09031140c3e5004084900195203002e11040441c034801c8885110413407d0703040800c20015051555204290303001c20001151000319141c0e0401c1c0c41540ca01e800b09035442c0c10000d012400030300c9440850302544000d00b030756055031200309140001c59043c420070b5104e48a0341d94006107031103200354154020f41d42030f000020500290100701c100280700b90001c0140701c50700540e40d910801d01d801200c2130b1030140c1c5081c804100c010300d0034002902c078940c41142d100054080341e81c2c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 938160746 1250 938159496 938159503
    0x41109010c0f170a08060607050604080d0e010207061a120606060a170a1e02090906090405010e061501090603050108060f04031b030f03050603160e07090b0d06031707080307051812 79
    0x10130100b61559403190340d480c000c1044510078044020415000300001c213001501c000302420425404c1000401c80460a1600d282240c000c11019030b840342c1c44010384a4110803128403080c005130155009038040c040120010350b100c1025041c2e85c0070300c1000414801d542d00c1824130302c44075601040c20001c2401c040c03103140d000d007240c403d0460701044000c6500d01703060010b1080764941200640650740780d80c0e5803402c2000c800340c0248195129501c8030020180490305000c00b1b481a0300d140041d103000b40000340014085002c036040314003814a00070052108640004900b17901581482103030126580300e00d4211200071001070032a80710502140890304040c2c001700d11642e00b0545940c100042e60310380302010760b90140e40b1040d8980444a8000380300c0d40054040080c1d1001d42c13401c1003800e580c0c0d1020f12400342d500c520441d00e0b01c260f641105008102d400b8011041003081440c4060401c111602d800360b085c4406403440b41408030008000c046441c860714420b120000083c003041880144080702030700c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 938161996 1250 938160746 938160757
    0x1e0c07060f0e120d0e09072c031f050603030c070909080c1501150e130b0303091302040305010f140c07061506210203090a110a031b0311041109010c0f17 67
    0x10503803080003248141022100d0a01c01c07109a95006054030184031803880034038100650080040b00210a5548c030f4500304002c00525440e1240a420210108210002c580c0c000d2300d000e21035041040b2071440d10b00005010800c1e91208031001990140a00d490901441041d00c07403070140c02042d1403a980043c44642441c100c0e113000506031f000707460138002141c814080c4607416601062b11411a100001c660f40404803040b00070b812240391108000014401d803400d0048070200d40c1d00044c040c000c010f070a0045070025031441d2000d0101c1260b11107500d404440007005002000d07400319955080c480f0903008080d030042900d40f03030b441c0203444180c002c8c410010401800132003240790326916100c01140c4202c1e803203050b240c0043c22105a44d84d031400d9100705205404c0b50f1043c03800501001169410320311815000740c50048501c002e2851070070080c080300b0402d01034412072802480716042d0351500304551030310400b4608021481d01d54680900740382cac0091750190050100240d030000390440d5000401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 938163246 1250 938161996 938162023
    0xf0306090304090c0305071b15060f05041a01050f0c0106030b010e071b112809020703080c07030e100201020c01050405070f14030a030302090a0b0d021e0c07060f0e12 73
    0x75250184245c041c1c0e03005482450014502420444074000c001d401e814000b032051041d00030104041c0d00c03800503640e0680046500c5604103900f0449031402d803088084c41c20301403100040032200100040d0407401003000c2c0940301000051510348410082d445403003c0c582c000000211540c46040080749400111290001315a000da1042c801c55002001440455804000c0c06c440b107071030b80c0c00e2012200c000708800b103c410030720307241c0c07000901240380ca0409084203040058941c1c0700c90400501c0400040d24112030420304000c0c00300401c0d070061481e503071102c050b211806041c0741a58200e00910a9844100c0c40c4d5103000d06010401601080c990225400d500100032016241e00c913070585040b94620166041c3e01c14902400001d0081e00500308651005108100e50741d510103460f11250711031128082d99a6002881008099510118011802507000d04505014928011650310308a9000c0c0000344a800d020103000c06100300d0b03241140c00c1c80605094240100004655070301d10701c00c42c150 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 938164496 1250 938163246 938163251
    0x702010506011409101812080d05071110151d041b0803070b06031c020609161202010c02040b040f020903010c0c200310090302030a02010e0c060403060b0f030609030409 74
    0x740f000034151400d40d260310000070019030301100242000c3c0c86584a020300780c07581c407000b100c0020705146565028070702c0500407a000e960b40c80100b4001c0301201c000400d040c080c000da0a140c0c0c800b08000040e460000285400e0020b803114110400300c00c03800c0c160b80b06500d500805034003101c0400801c6801800760f8800c58540f0300c8041d031120140c0c070700035150003110010707401844541d010440c030103107103904000064165641c0a00f03030380c0399005409500b00b80001680c012014010480010003400b42e581e1803001d0784a82250070022854020003043d28003034100840003010000b955201d620210412000a00420176131f035a503003400c80a500558081c510a5181802d52208540a44045048d05d540322042c244c40000000701150440c0c1503c0d80703a030705031095540701d02d1032a52500c0340c1610540a6001181c0b503044118009080d00d00c4450854410740041d8807103907142d21600181e0f01640e074061400b207100c4400002040e0300800e107400d200d5161061038280480c812010000b00180c0d02d240606 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 938165746 1250 938164496 938164517
    0xb16230d060803040513110c0f1e010504110118180b0f0901060c02060c07050913020301050921090f0d0b04150204140603040312060e0106090f030510091a070201050601 74
    0x151a00d074041c0307102d4141c20203284071110701c01061b0340c2e01031441c1e494620052800c00050b52441da10300701c1e038400d8005a690211503c07803da030301010007100c0089070100c000d1149241580d00c0041c921200b841d407505210b500c0d22030101f00c18141c2c1c0d83c5000b400044044403511102840072802500c0d480710581e0040900701046c60340e80c03e101101c02c0c140c0d0f01c60b4964030000c4209a090000710703407001e03001d4140d60080500100d0166076400c40c69014243e151003006195029004243c03c680d000742002c1890360240d00381c001003040a0140c80c4106090091440e26140d65101140b46440b050005076444401c04402100300401214114002c0f4000c29094410326900d0283c04228403c1d805034441040700350740f034038425280020055a129104e4038121b005c03104c100120030203890f41504000450180c07031005100e50341c3d2020500000b40356100c038030b01100c1d15503110b2075264112480681e9100f511948524144000c20f0306110700a284102c200f500c600e06004d0080c02010700340c5a03280004d600900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 938166996 1250 938165746 938165759
    0x1e0e03121b030c121e04090621120807030905191e15020304030311031e150f04110c03030a15051e040f0f0915050a090b16230d06 57
    0x755001541e881c0c006101c070444c06001d21074240c1000360800c201c0300141300b8402c081d01080000d0402003100d403001141c59810034100c2a21410119030502006844010140100e10b09481c0840c003900c00d4107007640c158590841c2200600103030280a0700d0f500c140e036075841b400d481c2d205002602d01e0181b01505960101c1070103c0c08801b1003210050800040d5400081c0b8000c42c6500564201d071090500007030450728112355030102d0301b049aa44481d42e0080c07600c8000e100d03c19846644c841c088107030344080249400005964038240f81007250055548041d080506c502c0c11040720011f08c2040100c036102e00c0c1034020417014042e580407605614500382c40000d8503080240b21548000f0282aa00f000004084144030041c50418808541c803900c41201c1c2c0000c400c60305c50702c0807540c0540e01003014045004010002c2c1d0740043c20f80a00b0500c1d0210b000d0115212081840c1c0011050400c481c4200e080c0c40c0c21161504c190045034441070162249615004001d0000c00000085000074007002e035a900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 938168246 1250 938166996 938167003
    0x10c080108101e0e030a020c03010204180f1d0708010608032a011104094d090a1202271512030f03010608090a02011e0e03121b 56
    0x4a6040c05a0003410780b0b51000c000c0d908802e00080303500300e110b04440b40c2c07600d403d41501c40981c1c3d200308a801c0041c68540460f4103020500610405034002e6280c0341c500061044201d0454810201041d60740e166000c0919039504112880c0700f039400b15140300c913486440c0c6a2a0991442500002e40c0781c84000110f404002c021340383c0c24039154030345003c00c42d400303100003902000c8500e40d14199540ca40d8503840d40d0402801900c0600307030028000881c861005540884821811070a000d81c11a80314070080900c0f44e80010841c105c000c0301440243d100f1824203108038040c516801d50f01980c03000c0081510003107610b84000407030080301d02016019000d0981060f254030010802d02c24141100003544000c0f51000ea0040c0c04d4001d0040802070400541140c11a0000c5070703544616500040100510f66000362699089521800a0000082241c2c00641190095801c0b495507601038500c0c007545500170340d602c081e010b9018041d20802031030074502071120340c0805030b01c1000c2030850b1071500d40c40c3c6000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 938169496 1250 938168246 938168249
    0x11010905061e1509070e010c0b04060c0311030c2d07050a0c060309110f0609061b0616020c13110307020a0b1302220905030c0f12180918010c080405010c0801 69
    0xb40401320641c465000c1100c0d0304004010550601c1a4602c1a0b0000b0700945100751065014940c0000c4400180b00c000b019910f04a14454200e4000e0052089080d200c04c101e900410700358041c2c0c4640c20950301d45107503050300c0e4103a09040f00004524201846004200da41020784114071511409032900401d5003112450680a85107903800e035010105410054502c42400031b0090100d801c05c41d0b2500012104c2e80426907403100000b5180d00b203140c0000400901d60080c918103004500719400301c000a50311880300841511541c1010800790b648149940060010464140843d60ba03141c8040702035910030300c6003002c4400071905000958200040c503171954101e0390040442d80b11000c040ca42c600781e4110b81140280c0c4507901e0900e040001d904100910b092940b08020b4601c80c4e1103d10300508043c18030303001c1544c0060030027409191044000c40b00c401800c1c1250012801c0c2c5850b5050760102900307a580d007040c1e40c81c0c094031540742c9400c507802608c07544c0310790020b000c0e50901c80412204c80100b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 938170746 1250 938169496 938169499
    0x503030d0e011523010306170c09060a0303080c03061903030305040302070509010803040b28170c0703080a0c0c170403060e031303080a020f060f2e0611010905061e15 73
    0x400603101460040c4d90140c0f203c4140524000c1040d0340c541c4541402c9202582c9060010b50241d561280142005041c043c2d0211301112013042441c40d5860180c400c00c0d00804441c0d41d40700020000f84180d0701d080d1a59001c9010309001e140c07141e1079150203001060261820b80140c03040c2d15001442e441c008605905a0b140f4070041d40c241858500d400c0b550360040daa048088590768144040049001c03c14402000f0342a92085011401c8899000003044003030a061500002040fa440210703801441a40c2c011044110001e6020103804080300e4500740307000014202000074103170100c5e40080324060030549004031010030813404008040e55a901c62118032003805401480c0400114940501030903410049006444020300c554001c0390078000c0c129800401240b010003030105880b6000c0e103052010740040d040740d48000d05aa0220300113090f6201e03c40c20400358420000724008290060344185600c081207417070a00b0002604c10f02040081c02001c0e00170715620000d070461501c48206c4072030100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 938171996 1250 938170746 938170769
    0xc0d1a07050703023d0207022709063105070b0301230a030f0f170406030e01020a0e060c150a09020111060c040605030a11071529190503030d0e0115 65
    0x140485000c24042c0b03170618070001035420702850016844030a08103440311a105800320300c0c41d8000e55103445140300070f410072030030317500401c204181c1c40360228039200410b54a007001d68880050b0641c02e401c2c10128103000b4018084d41c00002004900740d0003a605860390a0303400715990b16490404402c40b8501c841f603652044889204201041c0d0108a800255015040181001060382c032503030601c1902d4180b095000c0e0002a00b0400c50398144100c4002c40315040003507192408034440202042201300c00306104900000d101400b550040001c0543c0c400b0f54030020940d40f61a424210043c40c0c00001603020071015a007000c506207002c03501c01d20071981e600001c0d060900300071048809810041190209554800308040030b10360a8000d0202e9522820040316950003002d40740301500c00c0c50098501d11417a0b0a21489400c880300307408403d001080c3c40c02848210062020004018681d00242d05030000081d0002c02600c4e64000040882a43c4000d126213402c078060b0780c0d1031428511550b1440074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 938173246 1250 938171996 938172073
    0x5070c08040317160b060f09190b01030b04060f03170a080705131d1806070f050315090106200c060d0b0f030303150a0b07050c0d1a0705070302 63
    0xc0001c40706070070703000c45003070348600b0300410361940342c1c3e10704d60900e060711807444283c00c020452801303e1068031960f20640e20718a142c04d003001c0c102040071040d81c00803109902c4030b040c0038182e44264000300c1c4406000304140b1145540b203a8140d2000c03e00d00007510782c1501c080601c2c0d83e481e501000c807280034400c0d60300c0207241d03901d1240446207508045a0029007240004d000101a9000c52011a8076103001141340c3c00d078105404120700010031410701807080c1d000881042060b5070410010090074100c0e080451352a1344822a0300c000320f520b0102c683d4414600c4002003401507003c0ca05880007403101150524103240300443c150384ea504401c500e90703c0b98040182c01c1c00c104042e08101030340100507000040300070411001070304542044a00003102c1e2180511458030f81b4080e507840d8001c0685182c4189800da4a4407100c5d1150050026180107041c0c00c075500d02008018400c14080c85050a4104c0e8035080c010401411940700284c00e40c0148a00c0302d01000b420740c11803141c1540b41124042c110103c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 938174496 1250 938173246 938173253
    0x1090e0c0408010507050c0607090803030114040605040504030320090f1314070305060a0608010e01120f080a020604111e12010f0f0f050f07080a0906111b0105070c080403 75
    0x1880040000c040090284000a14540c09000350f501600050321059101da144168442c0b44c1800108800700f0040070600400c00030350f0100441c1c0c1502c0d840d0003005060314096003c50003418a55004030703001464003041005056050380130b4080000030311110581d00e00a02c0c05900d090046200c041d9003c070301b1120711807071458038440e00a04040207040104242c4101c42c0c42d40b01c1040111404d001198641c000c0111030303e8079506003005024541008000f9505000000c4040f034414060600002c0b007505204050110340d28403214007642c0b111829075100072014000b910b4810a640466450002e0925025545412503904440707024038406107801040c00c108100074080403002568a039544d45041454030b82450240c1010b04003034100102e4400d81c00008101283c4004225604c694158421700c030503180c0c00102c1e190444d21071a030106101a581c1490390050105194025a920001400b501c0300c10404480c0e0111a0101000b000b40e030740c03400e109864542c200303080201116010001400013 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 938175746 1250 938174496 938174519
    0xa020c010c120c0213090c050a080d050d0507020c0307060903031e0804020118080f0618030a05030705392e1d060c1201080c0f01050a3501050f0109 65
    0x440d0b00003050300c003044d07175130301148000c80b038a901069500b2801002c00b8005800c2c990f85020080c6007040c002c000800c640000205280142075234040d4081d110703804119064400c1185401c040c00c01030030f40381c1d03150340e45202a081448a1104070045804031100c1c2462511150f066a5044215102e05406aa580d80110b1760f80c0c8150710a0600c0c00c9956101045000c0c0801140303203003007100070082140c1c0c1020b460280200c07644039079402c03081c0d2041041c1c0c1d046940c4802a030b81c0056a0f0b0800c00c0c0c0b0740711090a6507018807402028111121040c440781c2a00f0300200514140b69011001a074100c0e900440d181c002e00403000030010703c002c2042d1044020341c50b86074040c0340070820f440404160980422070181c108001a1901d0100c04004200e085042e80c1c02c802e010b0040c407028001b0034004126102246101001e140258188600881c110241c2030050f00032104101c800382c65a098410070000c03d208504030383c410803030200c400d00000300d001d060035400c514a02105031541c0c20910b00c0c00d145503d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 938176996 1250 938175746 938175767
    0xa05010b1c021606060602010903080c070c063009141204120501020910020f0f0f0706201e0c010302030c040e04150203040b01031110170903041a0a020c010c12 70
    0x10f030f85201c29203074404078005120b0f501c0a01402e50000c00c20b00e00318100108243c5014104102a03a0200640030004102c1a00001182c802c3d0810308182030f00c0744000c4205110349481c0c10341071191072a0701c2600f07a200f03030701410029210700445481207220380d4a0581d6182440715071150304004010512008202d6614400100d200350005490900343c0300100700c00415468004c805a4081ea8019443c8042440b40c91400b003802c800601c05900714a030005c3d43c3e54420320a8800380519910000c80880c283d501c40620a001941144c0d0b10b03459044408208030900d080106241c011710b4052220f645c400d0003142d005200c901c40e103e084c04d0030310340d0405013180c024004540803041030000041b03c41490002d948241d028030381c161029891401c003401c04544005026201d0b02440a130f01c0310045d007000703001e4a809034000e200002a41ea814400d85180b1071074200710440348040c5130624002204c070000b4081d81c0026425552164045001903814040004000f060140801900000da42c4580022074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 938178246 1250 938176996 938177017
    0x30215060a09180204140c03070e0103020c0a05061902040f15021f1a0405190c091a130e01060f03050702010f05011707061b1106090402120a05010b1c02 67
    0x361101e035a2410001150001882e610b41d0fa14408840429440d0074030070700c81c10710450f0a000b906841c281118500e40d1000408000900046901e018101d074480d5050300d100c20240000c403100070340c05085c05941e40702c2c21201190180302d03100c404003c0e0319a80c001e64048403a12400c03401054140340c41c2024013004501044210700c10034404020504044a1503d000348014600184860940c216036102010610042c2d01850804c0103105650340c40100304880350003038070b81c0002c040144c40e0041750000029440340c24001d145401120407480c00100402941303c03000705606886545401149100d04248a9440413402408200c021140a40c0100381c0c031500380d20001800481a64481d4101c600071f8000181c850946000d43e40780a6040150701c01a11060502c20360102070120603502519050500030486031f43c400840c0c003180c0b540d01c251008080010700035520b6080c298104400c2c00412600810a81e0810000043d8a0240011a201989680141d60740c2c40c031a140c034413001e5404070b034012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 938179496 1250 938178246 938178259
    0x10912050f060118110403110f2d031b2d04020f0a11150a1503050a0812100b121f0b090301060911030a0b0111030c0c090a0903021506 59
    0x1249201051040b00e000e040080c1c403500c000c12418036030104558000511900c0c1910800082c808600d55285282c00540c0071140c8400101e4000042500c2c0e200c09046108e030021480c800a100c80c3d4050b2900a543c1d1040c2c0803603000c0c00c0b04411508035500180c07aa280c00070b2505444941100201c1211944544002c3d28444007111800103d0107d17806104820045480804c0c0400911750041c1032100c4810b5910081101060485400e0340a000c0686100da01340d9481000441030b4002d0f11111004540003000d4451200d118100304c3d003994000941d8200d881d8195001500d000490301000080c2d41d8025003503400c010030201c0700f002404002d01101500d80b085010300c0d40c8a4141c0c0322030310161007125060f0342c4808040060500390380c800e80103111034504042c5c441d00c2e80c41543d41a40d9000310100d10218005003880010b071703003038410707003d4019150000194681d200c8000182d2551000c000f91008191645e8642c1107100300c4403c0c260090050b0800800d100e240d107032507402da036000200180715 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 938180746 1250 938179496 938179513
    0x5090c13170a030906051206120f011e06060207080a0b060d1407030302010c03021809040f08041401080a020a05030a090309081b0f1804030305131505180c01091205 72
    0x56030000c0c20030090300c40c1d56441030482c0c0b401c06a00c864590010803607400c006003010030810389440d06d00300040210f0301074106002101d0a81c4000c01140030b601503030750020410502c8042031540300040d100ea411a41909200c0d00040981c4001051000c84006a02400700b00c0c6081d6221001f490000d011103034410942c8100f48081017003003d402c03110707480c054020000945940741c00703400d40f0004010f013001d051050200e040510a001d10740042c4a80854503003000c2d80d00d500d40b140f00300c0340610019100b0300d404a004501c409240d050008082c2090305d07640c055a43d02d00b641e0040e03114a12030200000c1d010b00c0841c0c5129925041803000c14441c0c2041903110b612840905c0c40e01e4000d0215155008420080100c0c03800c01c43c3d1760000106068855a4280201c51100f003143e800280c001410980d40d04005016403180e18254807030260300030600360010210400210103804150340b00c04801c01900b4440e0144000041d56058089040c0c441d0f81045181c404111170a56000c2c4080e1501e0165054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 938181996 1250 938180746 938180759
    0x1f030e120a020606180910020d020415020a15050103020a031b051207240f120603150e062a0d24080f010c1e03020705070303080106030e030405090c13 66
    0xe441c0c04031140d8002d0180386011010050f0000e401c0044440340d0221a05005e80b10501040350a203100d9511405652034118003103810092285074421140403003031240402c6403649c04103601448900030325007e805030b140882310904441c400c0c400258004c03400a0100006480313800c039034000d41040c01d20702c00590ba55102107040c003041144008035070340003944188044d0200341c50544840c10780107442c01c0607230780012020305100002c200a0060010101c200e03041640d440d045180515404040840040503044050016081590404955005007400a190046c14056900000016401d180c0101c002d03100c1000955106101312007901d030711806174282c010040d0155503405030b454904820090325005010f41083c1540c4103815259040002c40088950b00503480007a408010b00704941408601c10190028030074200b0040007402041000014940c201400790b048644549003484612210b1000503200e21072401400c1e4080001804102916004809000c1c18040340c1295000c082d00c842 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 938183246 1250 938181996 938182033
    0x304060e01023409090f083001230114030a1808030906010b0a12053706060f0c200a030f030f03020301080618010f02040f05030c1f030e 60
    0x28031001140f6940c2ca50b000090201143d000c01041a210204003003221540c4804c40e140a5500c0a040c0d45008103081d04012940c1000d90060201e41e0991441501491502c2d6210b2009108120400800140b418400ca1203030f400e0002c0c54405950b803540c2c00c0d1700e091001d28150000350818401c1c84e503c1007220b14407000f50141c14162802001025101c0c42c10031000d074030b400c9050700300d080d201a0522501c403407039810405140301c0501011021850b60b40349152225807456840303c007004000c2c00d584000f8044c103407034001820030961400c1405050b4942d101502c2c408183c012180005500190b0000403810394160503031503000903080381c1c0490b00484006094018250015240c0401c440c04201c201500f003130400050401c0ea043c254255850f06100b113445e06802004a44d903900446518130f40e1460030362040c044500304a0301192a291500003031a2110302030701540d40240f0031058203940303510740745007803581e100c0f04981c036942c940c00d880c80c04801404a80051490601c9010700d101c801480343d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 938184496 1250 938183246 938183293
    0x4050c120f1c05161e0b07030b010806010f1808070605220e0f0a0e0d02010c1403090c0607050a05010c0c021e0a0902130e10260304060e0102 62
    0xe00929154881d000c0241c01d00a0380d803031202100d20b800105801c020b80040564901601c40c0c280700c1e881c000c40381400503919680e0107080c035411a2504101007003111102c180fa02401081d6002c004011810f801550207480030359402d80800c0c0c00010480b60140300f084010104000380b0602c01409036a451010301d4620b40340c00413800304102143c0811000210501c011100700c0120100829a1030040004c13101c00c4040c058407020342c0c155000408203030403508040c41100b403507011200035140c0440020300800e02d801034400080e0300700e9411034000c002901528000c99014020f4002240050700300038090340003200441e1580030f06500007001c45c40a00c907110058009880d510000200d510400c0502c0138144205001342407070500040d05a2680e25109064400c041c2c401a034403401e18041c0c90b42410340d94800b403440c001c0c00c400c10a080100b4070442003100c1c29503c0146182040042d00da19003045448200e141d9402070000300301c061311440c0c0d540070100042c01510480d80982010355000c0f4540d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 938185746 1250 938184496 938184529
    0x70507050d0f15021c0f0213080303090d020a08180a15030203010f120b01060810030507171e0a02010806040e030a230a0203120a06210c050f0306070804050c 69
    0x5000c014414044400c1d40ca4403d514100d00031840c01d668071441000c2102e4030700c03144403c6a980c010300030010109a04487d151a000c68002d00820741e1100c82e10f80d280d00c101c2c1c9200242c01801100b0804900020300d10315107940c01720305103092518121101c00ca5104080c0a0303607001c140c1710300020300a900191025402c05042c0d6015a6030340c100340e805113000c050381c0d11003a0420203503222440810744885400303043d070303e641c5081141038a134408001c0c206801c580011f00940103200c030010b42100d4405217694006090420f49140524060a60340d90200b02040ca5000ba006444281c005600c58000164070003401440016000c00c012115881c58110140d82d0010030703803034034400000303090142040c40410400c0b0704003454103803000002501d80c001d42c0040300d108926440440d00c04103440c6c01100103040c0d008096090342001c0217282e1070016014070b050310410118034022400f42400d0112403180d401c007500424681e12a01812142044001e10550351401240d20f110006c0d03494a2011215028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 938186996 1250 938185746 938185763
    0x712030b01140903100f0b041a030c0103020c190201030f0603120225051309080310030311010501030b13020a0510020a03080a020a0f0f050c010c0c1203060b030606070507050d 77
    0x58080024040440d041021400b4180501185103181d900040c01c5001807810000407805154031030803013000d0802c0056180d4858205910b40c003500848182504c65180103c04984802a198005404030701c6842540d98031500314540183c059458010703403080851040c034001581c0c01d05488200121944e42d001200c0d09ca4a1481c3c41d00115410000b410310740d0007501e500702000c4680c141c1d21000300414440e2030700070f201d0b2b0700c0c00c2d9400d000c995100100094001c00700320758a00d0400000a0a280d4500045000c91f070120501281c00005101e10b5060724ad0101d0f07054016202c92000c1e41a840b103982d002c0303038030252011020605032100000101600d807250010410004185009032030108000e208401e02d9105010255889501c2558003d09e40d00c41d06029441c00e100503411035042c4244810390036250b003000303003001345258082680f0030030b94020003520902c0010158120300780d0303000b0300c620075108100348085400f03440e01c0002010340034480c1040f07a2890b5600c0d40421703011017050500361419503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 938188246 1250 938186996 938187011
    0x21c080d050a0b0405090c0409031b030519020102180d062004061b020a060c0f1e1a040201170603030403021302030601020118050304121403070606030201030f110301090f02071203 79
    0x1a243e015069104408450038412413620201099868060010301e5100760703103482c8048207150049440d00c5e00651248201460281381d4240500554490020a110440158004c1660358418420b407814071800040c03080100c0e908204221042e51651002d0381d900d0b5442c640d807100c0d0703681d101034182c5c01110f00c44120380391460710001401a100d0040740030aa1100c0c0305941006a85644003c800c0e00c0b001e08210075080102c0c28881d0f202d001400c8020007240c01c01c9407440c540c5681c107041e034114600c41e425414440001300c050061580c0255002808034004000c2e0701004101c100600d540403102504490400b6070703940000f0200080c03d40500101075001050100c5c55a082c000c507280b0343c0344003202039149020307551242c1d500d2080348103500009001c0390000b408c20080098402c1c80d54100b1040300e44600f60350400c040104690321040340460716220318102c2002d4240181c1ca8100184190203081d03030319000b0700070050498403040c0e01c1410b50801944000828503c06c0319405100d6540000b07165 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 938189496 1250 938188246 938188261
    0xe010506010806040e2a090f1f451415011706030a060e100c1b020d1a010f09050123060c070807120c0b0408030403021c080d05 56
    0x2c08041d2038140a01c2c180b050b4910041400100342101e20407000c807030388000d0030940744e644c074109a440c43d050b400f10028050114011804802e00e005111411658170201040c04030010018003900c190030921031072200000e00c8551800100600d00a000c100028418451040c0006c0d010802400f1042d42e07a505e03c039001805480034a181d01c40c010000b0740010491000c00030300050380d00e540020400c001000020341030344092182c00d01c0558040400d0201c201803003030981e140d1300b2141002d40003500c1c20000128151291501c4136008004000c0c8281c200b0300c80e000d00228008242042c0d44001c001c28408035580705d81240d8500a04411910040c40b03810004144203803401039120506c080c502e00c1c401b4a00d804031240c040c202640841c2c160341d4a405c011400350412146601140c00b501442d1700c00190052000d401e981103030310071840000040d454012000c00381c000d6010704459584148414401404e00d48081c5520494440010004101c1c42e61085450b13405481c0d660b41960b2030307000744001c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 938190746 1250 938189496 938189507
    0x112050108010606081006050f030411031b040c0c0314070c150309051509030a051809040501020d0b0a03050a0b2503020417010207020d12200606010f020609060c09010e040e01050601 80
    0x54101c041c2540b440e26103100180235001d681c41c00e40036044000041001c01001070401e4541c1c0002030b05456028050304840c10300c1c1207200400303d01490401c50010300341c034440d01c0004000c0e54180c039000740b4005651040006074200c6101100c4051400001143c0f440440c89100103038110b694003c6494030361403a0080c14005041012410074070042e0600004a00110a945604507145484e5072190000e001c4010448240049550405072032400d1000340201900240000314a142d42408071606041c28450380b04014403028000e9040410070700002607440d00000e40140e90001d42e04800320591000360161128512018003003907001408202e090604080034504089020086007800142d07000b18045082c0b00100806444122502083d000d000e000c4001101103d280c41c181061070054001d5a02d10342982d0306e50124018440b808600744c800180309100305c5089001c0c0c4115190681e9401d21600030300420f03810300002089620550b125442036242d9260002d001040e18240540050311 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 938191996 1250 938190746 938190751
    0xf0b09070503070e01050f060f070c05150705061603061d0103020a06090810090203192003070b0a0518100c0b010b0307051e0417061e130b06011205010801060608 71
    0x20740083c82c0402040300c2c1202068111442540c402203004924000184c0358824500f14400e55080417502c03405002c0104000701c10746105641180840e04041003050007400355480c010600c3c0d01030000035203005400c80000a20799010305010030f0040d00c0d04190000c0841c0d001800d0008138011004000354541004101c00034401c50801200305814078a141c0c0d12034512000071403107262601200811502d04001c14510b0300c4102003c0022162545800b0001ca055144144100c882c020640411403501149070411515a64120341c60507680000c1581c0340d0304003801c0f10440d003d902940c0515519020001c0c6514407442e511950032821a14008080d1001a000312081d5101402000001c035003000444010500b00c44026142030300f440382045d1188250b0300880707130314040403010000e01d200000307045003e078000c01c07040c0030104d02d0203813100c0d03c880c0112643e0711184050400d5002055410350482d80104042c03424000c40c200040b04841a201d0070780c07150904c4c2c0e55039482044019808120f064 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 938193246 1250 938191996 938191999
    0x130e15070513030201050a1211040513050115080c070b040b1f0b040611120a03020703350a020c01090c05100e060f03060a15050a0306090227030a0f0b090705 69
    0x2e007000100b1501680e80000e0740002410702800003403c02c511401040e406104010300c400070310a182020524038119006445a18022803080790101c80d00b030060700a0354103172100c8010042c4444566001100c480c500540310503401041081840082146201c01510807030240200180c64101110f2034004004908800220382801c45014480741e10440c1c00c42e4100c840d24980020190040c14015040c82c4503030801403a040c10004043c1c120a404d0380180c40440e020703480e00b000c0d00001001c2c848180748421546004402030402d120f50095001d07461941222014000504000656424a0844100010030741c0c3c8041410f10030407c074a00714041402d001c050b0320b00300b00b0400740d43d0080b810901612072405061003010000640c01e07204c1c3c1c10002e00a100380800c0c0c4200030540007000d445e55011080d0343c40000e00b0a640418010202c4c02220310890030b0075a1141d90b40056141c42c8880c040c000e80b00d981c54052030050001140208407084000d074000c40303018640381071180c80749281100d41d40c01075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 938194496 1250 938193246 938193257
    0x108010b0909160302160f031107062a0b07120516020c0f01030b28060806030a0b040c050a0815060108090a030804150f0515032802130e1507 62
    0xc00c00c2e180da403007158101c1024402007070034500c955001c1c0d0281c0600001c0186505001d014003003448402c0d4410305605010362502940c42403030401d03243d00c0707240c0b6000d048040fa0200d02e544020150940c0d441030b03441c1002c840303a105a01207641e22402c0c40010749d038007030000c4c178661442110038000348a0982c0217401418101c9840c0020035029440f020310000c414400e45c003054403440790380d0080d00030340c0915000510780c00704502c40d40250102004220b6402184040c03440000c07402c00c0c018110a401100c000f4000c003100e025075542d000341403034028400c668004206500182545900d040ca5001d4a440d8002c0c01200c43c484100b94250440104031904000302801803003803948010038044140d80d09858030072885e40d183d0502001358100020f0522100d481e00c2c2e207410740d045440c0d02481c018032071400c5170035250790420b04169640c403008100c86004003030003810b10107204214440d045040c3c401742c40d040044182000b03800845010104141c25500074940b0b0754012104c40c0c0040e6880325103070608 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 938195746 1250 938194496 938194507
    0x2010f020a0305180d1d0d020907080403020d08071e0905040e1b032e1119110a080f1c020c010b0a1a030c09030313230103020f1e040918020108010b 65
    0x10809452481d210b89486d000c85003000c0705807914071100f207421b90050400155400c181d40000c0010000702d605400601503a440415118400d07008a80075500c1d55035400415400030200c401e01c11410040746050140c1d0b80400103140e1507601528206001c4003000c0c104404061402030100459030111610940001410a1900f410095002c03034020701e40482c1c00c040702d105180d030740c0101201d1204115454021031300c004809201c420340204201d2075070300d0100402900e161161780d08044c1c0e0005102d05010722205001d006410702400e410308260001814414400151804a03880a02810b000780d448044120490405183c601c006240c0710700885142c4031048000380321804042c0c030302007800344001483d003111381d0100103a0711484040f00c40d54801a640e14038291003508080751560098070302c9045003038603600a1094480b9180c099400501c0c1004108255140410340b040e5120200024000801e03040e000c0d1140003081d5074690554061481580009007110505074458414800b0412a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 938196996 1250 938195746 938195773
    0x30114041103100513030f021f050103140d0804080a020a0c030c06020105090303040309120804031506030203100b06121e0403090e01170a030c03140f121303080f0702010f020a030518 80
    0x110300117401d81500e04031810342207904040303040012080301d489030844910150743c15001d96a10003812170b840307101c0310800b0b80310000c0481e403642041020000410600e00004012a942400800031894607206450804002e50f84208504140d904160b5030442c051105000158091140e2900f004425004504516140e50002e046144034080c020140d0220100c40080110000a0f03d0155920101c6e1001c4004210900740080000e840145d01c079114403521440703480010300c00c9501080016140924041030009440b03100b00029002c2c40510003074602607242ca4032010000360144d0300c00d0703070340114440c5000c20407689450182c0114001810303d014040007002d0000f01030f0482c65050901c4c042d0ba40c800e09060b2034515025440040c002c400264940c00150802d00400120b400b4074500ca10f02d8840d643c006248001000e0000d011802c280040780c004040201826403014040c800801c01400704151041aa042021000042610741c018005c225010a000f100007850302001800114007042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 938198246 1250 938196996 938197021
    0x7080604020603070c06021c020c06010603022a0c150706060f0501090306150b1306080f040c0320030312010e060103110a0c110d0807021906080609060301140411031005 74
    0x501400600034442082030406c03516406a4141d01003020b00380303090542d00b4024201a40c81405400844d028890002c5001402071095803502321a02140d440782c0c40c00441e54920340c114988a00880b0b00c140600600749948902c00d054602c2c40c01d80100343c86803c186084010366100350031036140b0015028090010f070340e1200d20307070341140d40091011a414191809040d1184410740081c000c858002500c1c00300401c40500e4034044402c05d58842c1410f956009a280011100762001490098101000c0010074003d00070130f1f04009001c20008041d00d00c10b030001e0728550120260b44e44500c0d011004000c2d000c09010a203500c9403082c20240f203400084184d82c4d58a101d042e000b070081c00103444544040c424034241203680c0840103410665552a64181004903800000080b48203443d040e0002441b000c40c807a01108680050b21442c8071030f12004100080000001d04c990b80540d82c0d008106104459410800c3c0918025040b05504c5401c15040c10709004010714404d81072030a2005028103d122038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 938199496 1250 938198246 938198251
    0x7172403250608010e241302130e0603030a0e031905100f0902090a15080610051005040305120304030e180106030b0301060302090f07090f09021306030b090a0b041e02030907080604020603 82
    0x2100c0e0b40d50083c070510f0801c0b000b0109003e4140c100701385605450300746005500808a03ca27500d004a00801d0703640d41da2002103c0100d8125426401c24490402e149000c0d40060742d1600004055585241d510320300350504811048066400350b110030b43d07414454541c0d124095a8a030f59007020b210818498011401c1c040f0b02401d0304400c10b583c1d8101c1c0d150465000880c0c00545051404d83d803441c100302c10b03041c00281e00ca02030680705070041c0890203c0d050103036084074100c0f94404050300c2e845081003404030084e000284240c2c140404050f031207201707590303d8087c180661454000440e1a50411000904582c0d000c40c0680c000da141c2042030000d44d55a030a0103030311070100c1e40100420750301e240303007119681c00d9039008540a040300c40b0b0115548455030040c2405000e8000034500c80d9564074002c4060303850481a441c0c10000c4140850445c070f18a410028100c0c4e00504045105510b2004113420040030381070000c0702690100c1445641c2406000801c001d00c40c00000740740608003a0009089031201 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 938200746 1250 938199496 938199511
    0x150516060b043209190f060501050604050d110112060306020c0114131e0b1e2d130c120b010503070302030309060d090f0c0e07172403250608010e 64
    0x580020041c1c2c50801c01c0710340e02410b00321001c00d03040c80b178501346d17444540820044681909080000c41c550500205540c100c804c0144000380035200d03511646030051010791740303d0405c1803404000101c242c95020b91030007940b05a40041c0e4441101105500b11000102e0309603400f0108001c3c480e0740c4e4183c09083c284260081d0350080300d403034410704862804265190003452294034070104141602103c500c420a8002c50300c002e01680d843c801c415000001c1c070003030040202140d4640c1d40b108030b0340b012030b168172140d9266204000396443c0c880048200c1c0e182c2c0310303008a241101581c42002656032046004000c20350040004a04690000c1d44a000e1807140b180150400704030790403200400d40051400c0740d04800012001c00342400c0c4a421a50240111840340c000c0c1c1c80414480c600c200d01105524243c1d000e089403607141c103c0c800c2d5018481d03c140d9001c01210f42d0b44400700c0c0d601803029242040b4105600c8181c0d4510b04c5940c846001141d211030180701c100d90040100190528007264420030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 938201996 1250 938200746 938200841
    0x504050c0f010507060e0303070909020304051911030609100f09020303190c080a02010b0f0321130f080105010306061e12020d120e030f0109030504150516060b04 71
    0x1e820380100c1c0c150040c0c100c00791629050010040440c10080000d5004d40880e54a00920b5529190324405030300c030944008000e9840105005101141840c002b000a0f228940b02d008100403080000d180010507508203803290004d8100805222661248540c415400302c0c0034001000a90002504d9000f0001221320b006100031000c80040d11400340c8245003584101c03001e8442003112030003030081043c2c0c0c4109000315060a08940b56140000750b03c80d00d245901050312610411700035290558015611042d55505540004984102501034a9015203c07102c0001019851400d01c0d10a58010754005104d109040707182c04580500e0f0105001aa1040c40c00301c0c1c295940c0d8404907546551248025180700703845d80000f0b00090780020861164101101200e04c44441017040300c0c200d82190500901040701000100849244014006202d070f505e401c0450915240c4040e50b0f1190b4180c94085600c0c0750b4481d04550a0300c2c01d0701c54141101449004410101d00c3c81e5403082ca07008030f05000055000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 938203246 1250 938201996 938202019
    0xd0501020307030c0801331b060906050112080a1d1003140a02041d06030a0b0405010b0f0303043b0405031c02250c0801020406110708010c0206040803090a0b010b19030504050c 77
    0x41c0626100423944500032004a49071816003004002007910090440c0c46070700f0030000162088906008580107604054860b10f011120300041e14031080362004041c41905031b49620956984500110031400c4c910348000c02e181ca04220740c3d0b1000d403001442c1d0f140f03a174418001800381e2441029200019080c03e0200c0c00759072504000689090000100144906451810001003001c1900724040c4010140c811580501086040549900540c01070031119213440285004510042c4090300009514181c210000780c0e058681004c070940859054070780d0340c400600d0502c0000f001c81405580070381081e085003080c20b044d0301048498095541c1c041d030b03025080d1404017444800d00c0e11800601010000315a5103594580152160400885003406801003400000ba04030042c007030303505020b200b940900620f40e10760703903804295040501031130703007602c694403200c00010038401115000e004aa48065214441b6a203041c03801a000d03403018040504010501c00080c0c4001035420840200300c60400c040d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 938204496 1250 938203246 938203349
    0x31d1504030e2d0102070e07030903030f020c060702160e0103030e13150612051905040c090e03090913050a023705010e0d080f03060d0501020307030c0801 68
    0x104014000662044542800e24201c400300c10306010483c800c3c4030b416100490400041ea183c5100380f0400a69485020000340341c9407207544200c0101740b080c00c0000750710000200400490700b02044a8174660300a006000b499501005410248000c00d20343c4001c5034200104000d24031300610004040c41111500c280d10756495a04e0403144046002c020088030000301c2440c0400d1641c0d01c10580400c800d200e10511000c100c0c040c5d11303c43d4031031a01c000040c142961080c4c0040c24005d0040e0758400700b203c000329540400f4010380d2041c100c18001191600399010030082e070413001030032805140d883c040d2100c0002e6404503070410520b404442100540000d60030300312a40359414441340c0c980f03551208079603030f00348407000c041c09441d0300307a072034a41201003802031091011643c84060300802c02030040040d910841c80c0103603803241c1c010300a02030f00001c0d0380d10b170390a83c0c200740c0701c960202e5143c0300c0c000e2015034042c01c1c06004000d8624000604664024806040145c2083c0340c10784151040c0f01e03c004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 938205746 1250 938204496 938204507
    0x22d010318020603041a07050c0c061e030705030f011706040f020f190e0106022b0201090f030c05210a050c01060e070807171b090109180c031d150403 66
    0x41a40183c081079403072a0514000050217545ca4040000700080d07800706040300e2141c400e84000340c1c000c20040002c52144c0c0b00708601d035000503414a50706803040340080d00707014618000e14046c403030548074036850741024110080403100581102c0c95007403d6020701505483d00007100d9400c160054271900c40440390380003107080580e2135a0342c02e400c9800c071a01007075465881e009400840e00c40c041002d50990725110226151180c0003207101c080d04a03000b410003170302100890150201c007180000100c402c17140d170f5003206101c002c4030190089411084d254052040511000f454008001381ca80010b485a402441e418050459610204000031845001890003503221380041c0082d5100b81441c5e00e0000c00c024003402046440d140051040c1040100240005241c1405143c041f13203101042c2484100d00c400640268440c54100849031400040310b05500501d03100c000d40c210004101d8820084010301924480e182c441e0300d8165082c0b08072a5800d020031003441c0b8820b450481171017a126800c084a2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 938206996 1250 938205746 938205791
    0x13060f0206060d080d020319020f0403051629041809060b01030c12020919030524280b130b0114090d020904021f0905011106090d080a180f022d0103 65
    0x8094400180e8401e6484541c0241c02200c3c03046048400d01e40301c00d4500f00240d61284508004030000e0200d3f4080c0d80c0c8502080f080e07401c603403081182070560300d805138542c10041c0030605c070695650351840380601c400382c011542062020700b401c1c069203601d1000241103c0f070101d00e0192459000c03442d00001d5441207400c51100d2810b0011155a42c0c5a06000d9200c20020703101e14280e4250507890135080e03c41c204654400c05040307050a40600c6050141c4407400004200c404031155181d499400e00e9987d04807408505182050005d074803491000007410f0640d583c204518400030900164226a603204506041580d05491752000c41d2120b1010800701c0d4211294102d520306006c1d0720b045140ea00ca08660f0031210240c0c0c6019040c4c641c1c03c215511400c0c1a92403001a07001842447c41c49400742c0c0c88260050100c4200185c0340310320794828201c00602201c211052044007280e03d05515058056050801d102204401b482d1040c07500c4031038203030625140c10b040c16201c0b00c104406030800500b100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 938208246 1250 938206996 938207041
    0x13090f1e0204210507060c0312092105090a030f080c0d0809060c070201080402010e150406090815161404030c0311011403270313060f0206060d080d0203 67
    0x2055051441640c2019401078041e168090408038000c2400b40b014925038492650050044d0400e40e003000d41c1115a41150502a000e10400b0704860156110f140310381180e40c0c1c01003a028170181c0f0300400e0040140342e2030000341d08002d07090100004998581004c14201d960040c80d04a00e10341c1450311441501654150103046e010381100c2183d2180c00c00f88291140407080c0a865559803548fc01c0c2c0120b000302c14010303000640040004005501500c0320184000b4001c01080c17487c9141d20780050660b2080d00041d000036a00c0f90201b0021f41c0820880d000300f000f141100f1843d2400c0c10080740204a0341000c0020060302c2c8010b40c101c120410100c074095a00540d20b03000550300c038104580100c4840d0719040c00241c161807030000164048054a0080008401214100713040d40c030002000c05519203100b1150200704030f050082c02c1c9509006004080030707103a480704407507000b0002e4142030009219a0240031048810000a9101c404442c0034000701c140050310f80d100d820441c14011401c0b4443d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 938209496 1250 938208246 938208281
    0x80d0c061b020601080c0d03171302280e04261c0e0d03111c02190c03020f070f0e13020a03080d0c0e0a060f2106051513090f 55
    0x50800e03074081660f505071780f0304400700c5210003205070074000f944094260240000d00c400301c840012001c110305c42a000f040c00c038518240d01009800042d03541004080e45401862840388400420b05c03c004004000c001d068281d80349480d1a8482c0c00c01c0302850700b000094607054502034440c101020b002c4c2c500700322654000e034400072100a1194002c101c1510401920311a91f180106098428080c1c000481161000c43d401c104060200d00c040f181100e280040b125024480126540d1008211654400040e9115510301d02c8504010b81031004c0032000748120341008609001784d009484011045840111640c034040e03540c0c900f02c03030800c0e81c810310007580160400380020500603190013070304008403140070400405c507079a5002da5400e82039450298000c18178001c204142c60280148403107601090410403d03020f40d00146a041a0f5040c1c203401c11715940c0c1c5c10501507800c149000048007012041034615140c51400c0c0c8140b80c0002e44118a10640c4501c5640039940154100400180711036001c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 938210746 1250 938209496 938209541
    0x90304030b0c0304061d120a170a1a03060408091c120c0b06010e0a03022404240c1a090f1506042712050910050c0f0304080d0c06 57
    0x2100350350f510644082d075400b030a00409501d5190788130103440603101c1001c010700d0103034101c25070300745c03580c00c80c082d62341c03c3c401c64410511205140007900780c49840031500c00112095401d04500b1203820b03900c1464000d6000318100400104200100c450540c81122048081c4a1030780400c2140c400e10000202103800d08180c3d03002c1c198101143c1c4a20354071071203045980341c0d1030100446104203042d12495011505500030000340c200074541000707117003115503000d007030100301c040340d81490340b0a82c00500340300c24903800c83c030340000c1420030a1380d140c0d4580b81054142040791a818074020700541d503e004103009001040e030340c080801200141c0b803401015580070001240f403c1030b959100f1240c0c02d010320b040407004a0b0382e03441c5414407818003104182e0401c028015031105151071f0080341014040c4a000c0265455a999a01002ea00300340c450f50381c150f84c1d4060883c028140001851040300c01d910a0000b0b0008070f001060305043e890a03868103040009584c00d0050140507036068440c54100440007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 938211996 1250 938210746 938210761
    0x509061b0a03080105190302040f0e0a14010b0901050a0b0307020f301207051c14010503150f1504020904060305061e0408030106030209010c1202011e05011508090304030b 75
    0x2440c600711070007a03d94495603030b61a0240984401901150750504034182d60910041c0341ca40d00000d12140034220016000e00c034000c002d45421005001900c0851240014418081c4240250b50b0400000e80d030844d100d52600f404036100c150280510142c00501000140708039108000424651100d2800c0b50711800c11400c3c0f4042006040354000c80b14011100e540d0f10850081c411240c0c8020070300340702c100982d80c0030800c540700d40106842da00c226040c100301d44114038150084440340c0c0001c1000c0c4043c0d501d041f003007510b065040d40c0601004c0f030340d02e010012030b030018400c3c80340e220903203010507218a550000010024880e40b005542d1080c80c0c00d0010007400070006400b841121019802800220030301c050ba18060360413240241244010001401600c2c400c1d00604450303041810440000f00d59a924040703883c0d205140880140c2d07480358811803141055401071030000c6a4a803c0116504001c8025580421410400306110a07100401e2501004004540c019504404103d00d00e041445 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 938213246 1250 938211996 938212003
    0x4090303090b0106271401050307170702060f06010f0e092d04170f04030623090f010c1b0b040c030206070803010614030105030c0d0c171c090609060509061b 69
    0x800e817a0908810004100710101e100300031000f40e448840b4102c0c001040f601c01180c1c2036000a02900070051000080c42c00c0360054a041402881c0c1d42d000b6049034a803845591600c0b00300100700c1c50403c0000c0035405003080d00b050007246c00980944031010150f803412024446500c200b0450f5103402c00e562404a030703612a44c1c070828060351050480d0906a0054112a0b80744d020f422011070388410104030410000703446034480604903c51150110422500201c0440d11440c111003118850704048110402d134013082c03044a17420320190034007511840700d0a8400d10900c8130154018240d0b98800d004ca024801b00301000301c0210703402010550f45020510304000315420a10641000c5064400c014400b41031043c152416190081c001701221268181005001c1c41a031106480090b50313080040b07003203035402c0d0031110000740c00380003002c005808034403140481ca04014403808010034004140401503100b10100f0486803d803800f151038001000015078588203542d4541450030703031010503466404020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 938214496 1250 938213246 938213267
    0x6020a02090f010317090d120206253018150b0607060902150309210a02150c0f130512010605060a1b020315060a06020d0e04090303090b0106 62
    0x25103954007692030320780b00d552055000f800f0007001d1010a0944241117003540d00640040440180b00d0340e062055070721070710000c0c007601003400300680000007044a186106070240c00201250101030107599801c0b14020103c000d15241e00e48450003a410b607080742c2110a40030703141c001a146080004030802e141d10001103030742020444004200c4400c841480d0044d200c0c00c1d01001002d0301d1549048119502e120080110580403a802811070081d11250703103e003070182d0722505850008041c1c143c4015054503900740403003441c900702403003040745100b00e0740d001c56820b045030915131610b16680c681c10922400c80c05580c00800f0010f001140c0e00600102c0e14004034200c074410389244003202140c0d65205d090340e202c0e004007a00408100a0700400c02e20424000300780322600e059000e900c8000d80d0009040232842a495001c1c0032080d01484280d01d445001c0500800c1940020200c43d44265806040d04691a4030075204540d241c400381c042c540a600000001c5601000c085080d44e100c1d1009004a1200e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 938215746 1250 938214496 938214499
    0x40c032417030c070b071a1603060b13090c1202070b010e0a0c020c150d050c030a0b010f080403080606070615030303180201091802040302031002070b06040c08061e0a06020a02 77
    0x1d59951002440002c001c44a01000c070708054040c0700e0030889002d1280d440200300b01c0e00780c7c440c0301d0702000034448140120700480744141229900003d0203002001d5030465007104a0754601000b20002e80c07002030a04070308444084401080300321800c0c0050760110741407003090a4103030001407220300700461356925a050321030340c000500b00c6031500e00c0b00030700f02c130280960343e0050792200c0b00d0394550f4544055044030300c1440041c0c03c0d103421407018002e41600c0040d074583d0620341d03011003406aa052107000302741807103400307181500c080c05515000408210003c0d00140074002c0403c003185d6540c403144100c5008540103001800148940d086c040c1c0c01c4902c078032003a800a4641000304107080002e99041c04441d40580d914950142001780c9500440c02803c0800320b025400c100010041c1c1b014003600005c0686090b0050300c4041a0804040d4104001d10080c0f00c0c1d46030208118086811291b015086401500d40c41701d040c401d0000038125040c000c070700603401206540d00280142e130004462102910 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 938216996 1250 938215746 938215769
    0x305030307050720060d0515040603030201060302040c170703090f08220b0c1e01060e010807030c2709060b03010e0d1403070207030f081e09030607110c040c0324 71
    0x600004421012001e104e1381e40c4941d080102910444482c0c0016400c90198450440000c010030006404c5415550003240542d4640b4010415886c0c0782c424200703114100d082100c920082120705d06a0b041c0001e2010042c50355402e500d20900000b1074042041c6540451415552403813050140c100b9003842c1c110603c032142c03c2e40089404420b0f81c00344e07825280d5541c01400c0c6121020440700700d00d800140001480c0d9a10200014030802000002d802041395802904440e411420b08a0304250380f81c000c680140041e00301210100702510b0011071182c0240f10014881165242100c05828040152617141d07080080c20030252401190f007501c40398540e141c61607000c06500c604421800210740303180c09a0010801000030410b01d032007903418503208000407841c1c50325016007182c24a400f0465940000c07004103411880381410015607400c80680c1c00c00d030030b402568140c5169100c40301c2d9440c030f01582e144d00c07503a0503081c0203800c007207908071a0f10002409039405858039084540075101d4080d1007032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 938218246 1250 938216996 938217023
    0x305090604030c080c0d081e07050601060302190905060a0c110a061d240309030c060108061006030506090103030318020a0b0702100c030f0c0c170709230f0a0603050303070507 77
    0x3611100613410a1f40c402105800d15942c031110346541c0e0302264180c0482101080312500145051010f00d003e0f0110f5200142ca0380702814402e40c0403150100d20300b0074840720074010b1100d07684040075a289603d00f442d02c03a600c1101e03881c2111010314fd840310769820201d204400318000380c010201030800c05032800101c1c2001020030401c00100c00318000015800e501500c12801178104000941c5d008000900300d80c503180c1c55424032850104240d0100d40c1d5034010b1410700407880c00070841000180507525040c006400d00301c0c00501403501c107200080074140d44502c501c40000d0491070341014642c008103000012542d5105001895110300c1d8203d10424101c07409040360390107058458405900360707803070001e845000001078070080c3c07000406441c640a0702c080041d01408050751030100320818005001c1d003901c0c1007080003c1c1e170b42d1401214265036420a001310a65424004540c0c018180c010003806901c13600010002826150009499800000104080e036a0442c1c01804228401d100b88030410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 938219496 1250 938218246 938218249
    0x21209100209090c0702010c0206181f0203160618030e150a020628090f02031005070509040902040608071d01081b040f1508010e0c030c010c0308040305090604030c080c 74
    0x24032448401c194400c1d5008045200c401220005d000b0f450702c1810420f103440284d80006000f40c00c1140d805242c0172803840380038014241300035041122106103482ea0300154042e40060748078055800c06080190660744030200317000c001d410800032a02080d9045030b502085040082c44403031001040703402050307001009550011002c04076441c00d001a03001e8842912080045814480c2c0c42019a0003200c801d04103a03603055092150440c038500c01c04800c0861609072050506124a80c0f81081500e498035007003040240c0c2102c02c5450a000483d000281c1030741a10014000b0035040c0c12105e15841411800f048c18000c1a5201010010000000399145e0344d5030406c070f40d070701300c00301590228004014600b2510b04140e0045846000620b40204091165020842e080c03034071980002c2444e03440380c22040c501c000c184075458208a098019299240d01c170320000c1d1120132800802410840740000007400d00d4403032025203040d081d000344501c1e591582c9062000302c079040c5015918083c0155007921416 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 938220746 1250 938219496 938219501
    0x120f051210091d01180807020108100801020f0a08090d1b0c090518120f120415110a1704020f09091e0a032a08090d0204020d060905070203030f0103121202120910 71
    0x4a6005035614900041680110ac01042c042c3c001441c400710150301091012082c0050004424580c00746921030700701880c014410140079140000c950031030172800180c40ea000f100e10604c0221a200e40049041c146002c00d40920700c1c4e446140050b240c0b8041c014407d04030000d0910141c00001101d40084480030610502d105064904a0103030782084131054210f0228055680b150149441d000030540c0514004280c81030200389518080d4001440314406030400b41031134809841c100904d2041c50998007250380300405098062160b062034000641690080101c0c10031580480290b2110589214945584a041d800220041407114804c1901d0b820241440d40703c8907602110038517030042c2a29881c001c0d605c5182110b0300012184209005030722140006c0c030050450380c10018209240c0300e0504102c0e1000f411440031900100144a1010214a070860540703800000010800700d032403905075840b02a11031062041c3d400810399906030303480303040ca15214120100940707480d01d01c103003040000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 938221996 1250 938220746 938220791
    0x40f0515010e010608060f0d0506180d2c0d0305030106032901110733021c0e0120150105040c020304030b0a020d0603080403120f051210091d01 63
    0x490b03003644010040036125000480e000700300600190b0039a03030008082042225807150580301c51340030300c00303000403444010b80c2c8000c00c032810006000141c160340401424803821103629242c6104900410039440400f0402849005008081c0350440312940342c00b601c107070405d108640220340703031050740c002c584544000c0020003008031042e041030321002e000554240004565850951150b454003190501d110240b099052602150b606440c080c00d448400882100800341c1d070454020754885907515250341c915800e900700d2414601441c00b50540100e450000703501d480840c0d09400c0e0715405141e040891b0300340c2e02202a4501061983e215014001a11803035644080141d00400040000c0740b21f2002413900900701b1440945420540035081c0e0965a96400507030304130000103020410001e659180d0011841541400018841d4029019045000c0e125410f02c0b20500c0c2e40000740755041128444001d0240c440c0c0400121003072070b02d920f040f0140c1c07103c0b52a03a90302e0651840910380d0f01603400e00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 938223246 1250 938221996 938222009
    0x3082809060e0414180f010513050705183103030b0316081914240a140105040c0e0904060e4b03040e0708130b06040209120303040f051501 61
    0x42c01c0d5200c0d4004901e403949003c0011700c85000b94044000021070031b0242501441900340d01800041d05410128103010b0541d02c4907120720001c58040c5c2c40003c07495059a030116074072807189401d6403460302408548141c0c0587c03011800040d184202051341540c0b00d140d0008003601100e03a44402c540d020b401e21402409000016030045000303060041100d241068400e10442540c0030202d1000190380c40d0403c1e1000d03080480c040c0d1054000c921320342c3c0c618150b007e5440350003400340410000048400074018010107010300e844580300201203018607058107110202901406441c50f140c103041005164000c40004c1c00e014805451100380da08090782d01c50305075500203039203003503e0800c07454543c0001d10070b100032039448a000140c0414000d0000d07100410582404600314900b243c0028401d0000078507200050034005205030100c0c1040d0141c81e400031058070010381e126400c8000460a1400010208640c400001000104044a0302c0c3c0b0703140502c51402c0301c2401080c01d0210024110900440b03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 938224496 1250 938223246 938223281
    0x9080c030f3c0c0a0606030c080d0206010b0403030c0606031a040b01090b01020c0f04060e070c030905090403050d0c2309090604020307080a0b0f040203010b1801031503082809060e04 80
    0x42e4204650700e000b400c500f00c0301c008407206204641e5424041d10b0040d44161107204200e10100282034060141c00b0354016144080c041307560401d080c98207680650b00001e400c10101102d5941002071613032104028640001010940d8441503100c0030116074204d80446149044100000790400c0f14044ca184c2800140c0140244000241c20300c451812846034103640315468a2000890004c20f5254a024030740c2659860180140340c00d000e0f210002070381c0520300810000c400c000c0401c1d402800e03103807214040400412200300c0c2c090120380b0b80d1551050072002c119000c686001002c808001844076440666a0000564801301084100d0108551140209040307000280c0c810701903038800160000014451844045194040303412a0426001148800e9001031000700e940300f9040380607409082481c01b4000d013120700b1081141203c0c81c0c0b0005021400104100c002100c0e40000d401c2035481e00381c0f08030414024241c004203c60101d20400e4041100d40d00c04070001d09150180400303414071180030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 938225746 1250 938224496 938224597
    0x51b0a0624030201141b030c010e07030209040b0702010e190309050a060519051903020307020c0307060f11032203152003061f030507201009080c030f 66
    0x15982e140d46a0103117020001c0410014441c1580c40202d100680c0c407010066466901c070344c50031030840c0d008440c0c0c0c0d1440d82c0425000c100603a610341c40141d0055029072480f5040d01c0301070b8140e016101078602c80e05140104000d64400c0072403108041003141c01385d914895946c3e584c4060202403445406441e000490801c1807220741e200280c12a03a848150380340851610b03904161008806503200329100021350000180045180d040102096801c4214040c2c0b680515143c07000e070034030141600ca20184001521440c40e101d0003401503402101c0100c3c240c0c980c01c044800d2210364032802d80000c5980c250f404420703a200000345c1c0305240f40b55036400d064102c9444490301c0c0083d03a410040c003559110305400005c0071004141c03410700e0048403070391f2004203190611401c058114181c40d2a207400702c10310360814143c541c400244081040e8900380001841c403566040243c8188a1070664688521000688690020341200100130352501141900c02400d1030401c400c4030f40711100c03410241704180c0d008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 938226996 1250 938225746 938225749
    0x91706060411120c04030c080613020f010c1407061803055a19060b1203190f0f0503060915031b13022701051b0a06240302 54
    0x1003003020342042da8142081c50800d0041c0080c2c2d000c4a0504c0c0d032500205041041003202a03a000241c116036000d4202e40c80c100e8482c0030114100a07000c1e00c217000000100c081070b400b51451a44c0190031040d4140401d412445003582d50545100304c4001a1901c18010b00e16100300c6108c10907681d015020f0400650302810b000e600c0d142c02c400700c4241c00b0b01d09409000680041c0480950b1070000d45040d00c0311320460850030f110400189107400590000d5100007506100d02d1980344040364060400907184071603070003180800001015202d49880b0028038089404118000b100c001e4a40381e0310b0201e13021400c40e040b00d40011800e080804a00148041002407802680c2940d0118480203e60106000c0400080c900004190b62800d2040b80007030720107090400c1b0b1907004405079041415442e0a0722200f28550014031440e4020a00c6c1400c1d0480950781e01c180c0454030381240000d10401c040d00d030b5070b01d0340e80c4801060004035a141e01e0300d900982000e16041d005803052032044480320b10649940c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 938228246 1250 938226996 938227001
    0x1519020c010b040e010e01050a0213050d080708070b013b07030b0402180f06120412050903060a1b090f0b0f04030b07051b010b10030b041415010917060604 68
    0x10250102952142c00500003901c40c2d20450000000c0d0000100c1e54080c1864102d00b150400790200f80514010001c9080745d110510210b011100e081ea4184014540c500b0b180180c0d020f0320000400c5850005000380a205a54111302e06a54500348211800300c1c400c40c0f0038812100c90b900307104000d28031100e00c0240032022080203620140d10f040205584007032400180403030313000542007402400100c4009145060140c0403145014056070524076000790f0443d02c1404060080c00100705034000130443d410144204191404102c01078102d4080382070550454000d044960100c4d0380501202040b00c0b84144190781c81c6007115040c3c00742401560412220080f20750010441c072030707520030030040040012151703540c041c403410955031495206c0072001100950b54105101050701c03031303041180590040e80c0d2064510041400d40c200003071700c81082d0780400c0c081c1c180028450803440c0100c04000030107407804030030400d01009a0703850b07074001e44030003904400c0c0035030500e01031556015900180760341c10941d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 938229496 1250 938228246 938228257
    0x4080a0b06040b0901060206010f05011d060c03120903071e0b0402010f051e040e010b0a12020a0e04090b090105060301060e01051c0b090304081603112b06020705151902 74
    0x280c40483e07111582c0001c80c641042c2030b80010016400400100150b01990004001402092070103203040030170810030400b80c0104d035150038441c00c0300151210310724808004950160480000112141c541400c1aa40f01d8200220958520100d1844018001c00e41e0300718080240d8040400300840c1c44036001100c100c03039031102c083c0600000300032004031842d244292150041550001b10703552820140711000380380c4103a1000303060407020b004a600d00340d040410900f00c00201d01c1c00586542e819a011030b20a02e003c2c1d1a2071304140742c41e41100c144911000d056100d404008024405c0d91150701c00d0600b00c6080f817190041500e50303040140181d180120701c00340c650000500d6204400da444d100d054a084007940e0b41d4446910000d400c2084290138058030f8801002d100360788100038a0358584105040303901c4607070b52190880140f00640b40c0402914402e10b8400d00d513400303124428620304240294001d81081d02c0b144030792041070b01c050302a084414407a41039070001c0c030540150440d1280203034020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 938230746 1250 938229496 938229499
    0x30c03130507080a052109220902100f0201060e10050108060d0503030709150302040b0f03100312020a030305091219110604110108370e030a03051b04080a0b06 70
    0x188640080c403c2402c215108180b4051800740001d500d06203c4201d102c142c9090000750030905000c03061455484e9403807940810040700488804d01a140c01d00c9000b0030071311000951045441d041c3d1426954015000800044250020890079488070010741e8080021214001c0c0c20841000074032042d44144019500144090000740540e41c00d07558032415500101c5071000040c009840400c01c4802e0204940000c50090030214605070511098844a1298803005d03c030f88040040410349460b01c2c411b26030000c5400101c1401100c2070071340000e4842080f100c0c241d00217810301012501825001c950404101008000286009506502c0d8590982c020a8010032711803550403c0440c4031082c48054403e9108050302240220b00d82d00150016401404000c441030040341445110110150070701c181100340c0a00300138040ca004000030103485203000d00c0403030340804529410a10b805800c424011415001d45011110003800034031152300484c4102071580d8481304030080825980484207420070030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 938231996 1250 938230746 938230753
    0x40510030609050c030610110304090c020a170309010b0a0f0e070504270c03020702090c09150408010905071e1e05040203191805060f1f0311090705030c031305 70
    0x2661000d090840e202114113041c0700c0c40c0002000202e14040310a0414003a886c100020000e5030811099a640914060480e407507903148140c1344194000c01c50000c401d85d0110b2980d80c880300d01848040240c00a84032540d1660800410510924000c11180b054940700344003105c0c2c00c0c0c5002412010300c0c0000e8414000c0c003a04120114041c4d90b00700340400c81d035003540c03030503981d330700c140022582111034540d0785c8020144140070740f20050351080010b503001107004900c02d403140c018400003410701c1e00f840342c425a8002c0010b40054441419081300c0007581c040d02c1982c0c0c03000c1c0c0e12051700c42c840c00c1204940481c4141000103001405d40b04203d01503100f030b101e07104560785840344080382c2241d00a407040007228a4001303102407994001e002d08516000d61440c01c1008242560300c403556010040c04041c1b0344c0341c2e03c40000f01020907020a448828803040082c112403680d81c24000c0c3d021480d2010b0502840c401d1000400c1180140200c034004c0b4400031810f440c1d03a0711104000707510305c0d88404c200d50f10301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 938233246 1250 938231996 938231999
    0xc0c031706040b1906090e010b12060111150108121c0c030902310c0504091a22060e010608060103090f150e10202503270503030405100306 61
    0x49904d183d22100d102c0244004d20141e00b8008003a041350340a0784000003280040300140300c610f15004c15508010350f04803901034107443c0d400069844681d2541c0c611945d204050301c00000f48444001c05040b1210801516554025055203540c2403007140003a01c020342130441600d411144a501ca1070181016160024421a441d030001d201500200c81c1c4040200b4000605070410304150b00710800000a82410480c07100c01a801230720324000c47c480d0000c001d40d10861021214a003040145054a005200414503c0017488000e034406081c5850106c1618012021a221180e262403038141d17409521583c401303540301401140a0304101c0021209101c60407504000123081c515010684441c0600c0402c8001c0100c0c2034514000034500c1500b01e4504040ca0081e04044000844c80f000c0c0e8152085651000b105ca41452502d0b12810881e5048002c0310404052540c000303424880c3e0254542c24015a04041e01d26640604a6004d0640c1c16081084100681c4c944075107518086081030401080c500e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 938234496 1250 938233246 938233249
    0x903081b07053702090c0d02040909060c08071803080c0f010f0606021b06090d0f0f0302030d0b1905060a0e030a050f010608060c041520010e010c0c031706040b 70
    0x11104107210300340c030200030034030961196521021450f200c0308403164502c10221500080e130450070240150140004c0020120038003210f86d01124040c11161030240191807491a120f001090160005000910b20001141d0107c0c42a800d81450300707010a48070000b80d04540341c0611b254080c500d41075691161000c0b000050500b07010f15030a4511029000400030701d81310010b420a41b52a80071006c0d200002e903030918070307942e49040d00d05480d01510324000041240c6006180d441c8020009081c103491070440800305a400002400403030340441051100444d01d200340003403400c180398a1420408480800e0040b420400058442c4081c035142003104400d09402003410032008020030348544c0c204040681014500740a400c000304680c0b00245418a001c06118409000d5406041c00303c4101ca6100700049210782d14032000c64031004c20700300814080203809402080761a517075180317030350810300042d01c410300a4450004083d003541f170f090408600300011008001c4020459580039544081203d0f06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 938235746 1250 938234496 938234503
    0xb09090a080f190305060901080a030212030703091a0103020f040506090f25090801110901050301092307030e070e0c0702060d1b080703050c0a05180d150c0e040903081b0705 76
    0x350343c0c1c4d0f140003a090030000240400b040058205203095800011104000795001982030344405030f06800e1a02c81d111102c0807000f4044e42d80e809400b0558100c041081c00740381e1035019049038400c80d903101c100c2d001c2c4000d00081d00c4c41219415400b80b002d80c0080d083c0c40c94002401e82c820403040e10820800204c00c62400100407008000c80060890001072060300424420310840f200d00a44c024245550354000820310710050260b0703021203440711040508501070390f0905000c1d01030505c0203002842e052400030010007014441800b01d1198207000201001000344080c0240d1060310028075080cd01e8080c000c89900044001c078102d035603460841c0d02d00c1080c0340c529212220a5031800b001d4140b1030b00050607640040c0c0301900e0300008000d003414040d084812595000840307a0041e103802c100900190103031000140c00303007007111994000091003000d40e000b4251b28285840d20312200041d47e05100446003a603400401180c120000b00c0c000c9101a00f40003402c210007080280390804a82d903640c207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 938236996 1250 938235746 938235787
    0x8030a020f1203090c1918051501030605010f18080a080c24060409030216080c04060e100314072111011e1125090b09090a080f 56
    0x58021a10341c0d0203000302808000c0d0924801d4004505605080c00d045807200551101540704211880e0740e51507411460041d80010545010820341071842511024080c0c4401c4403d50b8080b038400042d00402d6010f031082c50306803103041e95281c0240740c413408156452500da40004000407440803000542d202c081000a00d41446129040d0b1581d000418481c680580740d25076002d8040715a41c01d000881e00c1704034840d84254101d5001c0b820328030310308050f41060200b0800d00c448034070740c1c00d012400301c0002034001d0716200e013a6002c0140b00c1d40c80e00700c0c0041c2d40081e22560b4a030003600c041000422004808944100d0034070003035404640da924203500010b11403004241844603100402000c0c0540c40482a95021085c2820888003100c1e500700d4005e00c40400ca1481407100c040c1c01146061810000044c91007000840030f0403070005034031030411a900901c20551708604001c0c1410003403e00c0d029050027100e2a1009003a580010380d07030521140c1002450342c04151052140ca40c0c5642000c0b01c115 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 938238246 1250 938236996 938237017
    0xb16020306092409061b0d09110a0b040b07021509030304030c0e0a050c0a030c030b1815060405030d0804030302090915010207061e1404030b100e06011b1b0803 70
    0x40e141d070b55155255030900f800030414401d24100c5080100000000c03e566a1000c581c140809410040d08005a414005d90001d40d60b601e190071452820080e1240c40906910b404644038141c0999400c1150080c1c4650f0141e549011428001c00005080048001c50500d1803216014204414074001c0303072440e0010360084d0b0b2201020348003008982a5009181d4000c108980148040e16000310341000c2442452280f07000c1540c1d0341c280c5800907200b5030044160300e00c000e110301400e0703424500340d105080c8255101c012010b81505a041746141140441c0c003200e8014025143c500500d2000780c0e00301c0f0009200f9800c0c90340030045001150f8520701c01501c61070302c0c0e030b4070301d62040081e80009181c05a2500084240203043e0042420307014810f40038150080306240c200c2d003010981400b80d069000315880207005190907402c0c0462509100451400c0da150505181116941c8100445098401108902d23035000c90b1800c48003c12407038001140b10350700d405100d0304100c4c1e664065601d140e00241009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 938239496 1250 938238246 938238253
    0x609101d1914071103120f04051501060e0a05100f110102040e0a1b0c0b0c0a03180b0f0c13030305090301090f1203110702030613030c0501050a05060f01030212010b1602030609 77
    0x883c149800007545492100068021810b100580c0007030071035440040d00130901c0d100100c0001341004400c00100c40c24008c82d90104260356034600010340900e50b0040c20a1064003100000726141c2840318039001c95903010b80c1c1e028020030710f404003030320b40b01a240c0341c132036255400b00404507081c42d1f416039143c055420640000741c08040802e43c03e1104202c0718183e0700708003402c4a02004500108030180e04910604010b5035980c21000042d0b0003001d01c58514190101300052600c00d100400c048107104540035201c1c000341e03640c0d4690680c054400c40d501c00c1d0904039200c40500100c0e1003500a000001d00140001800f8140341d00c0f061401c085401c030803030780c0d1080102500e801c940c1c940100360442c944000d02e0f608000941d40089d40794100104081c4580003120016012f0600c206000c8400c41e40140081005003081e0f4407020103000c088070700500458040c0c0d0381c030f15194881d1003262300102c1410352024440c3d08284c2c1040966101c8011100000010315002c000742e0340c240f04160040d5003500c000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 938240746 1250 938239496 938239501
    0xf04060e1f0f120510031106250501060b07051504030311121501090b09060d11070804050301050106110606010e13060e06031b060708090d17030609101d1914 69
    0x81c4030b098044108900f0318186400c0c000e00d403002040340340680364020820380482c82d43d030000c41c510f8010700803d04a40c050f0012810745841c00180754800041c0650001d002c183e031200300c1018948524500202246d0000701002c8035084450a45900a03209140100d54502c400540d988030f900100003640034030004505001148401d064000003403c42801d04221140c604110000280200980b05001e09030010300c01481104035406038005c1070841c5241c0340c4a01140c10300b2000d940041c0209c5000b98030742800803a030940a046c1c1d2210b101d2443c40104003da44410045402012040c41d840e000210517421095000c034601411000e4248501407803024030b0080301b01440c10621000303100c00302d20207140c28001512a002102c4000390070035405903489650001041e144480100050f0030128800501801100801c00850080034101c518442640310351108103034046142c0703d484e2440031800d01015140010016040e8040203003480c0c0c882942140307001000b1b40f02c07140081c03200c0c191744408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 938241996 1250 938240746 938240777
    0xf0b0903072324190e01020601141c08310b0a050c10110301030b072c0d0b10030b0109050c1602030f0109060203060f060f04060e1f 58
    0x44407005040460740c0c0756400c05441a0b400e5808458040640119050070814510890701c24644014215109545a8950090a02d8415900c0c24140900002c02d003120000c42036100040f0b5a05803000a005240c00c02001c01c10803400000d0104850170b81201a10110041442e02c0040c00ea600c103400150504401907500d1404c1e103d1510b028404184290302041c0407140c45001543c44000e414105566900c0003004918a064005650000000d041c03403d07501820154001941c12288201c01e021040e84a10304151028900b59440c0c03141c1303500c8108019541301c2c1a4118039001c10010b0302c0c2101d01480c945691810681c101d0b80819189400c1e50200100000310740d603030b030041c4140c410400043c20960408030b160701c5040d107030500c103054240f280c40039560180048100140000f00030800c1c0030040c5000030182d08126050382c0300c0c0407140303032802c0d00741402001c031042c20140c44106807509046c610241c4000381c0c601a182c1c0c2041101c8024029459010b61029010245440e0204111201c07031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 938243246 1250 938241996 938242003
    0x60306090e0307082a07120b060301180618020a03080406110d020a060c110105090c01090504061d1e01080a1101030b0d0f060e01060e011e03120e0a0f0b0903 69
    0x704004258001c0102030081160001581d40300c08030000010043c0c007070702c6400009581c032001c1c10b400328001d55a0005611441520510040388100c454407074079511141014221803140c185103140700450103c000015403194841c50300c814a10119010503101600411403040854000315900350300083c041c4a010382210704000d01070f0500d001061001d80d41e910081d1527030179100c0024113103a01e40352198070b480c1c0649034102403092454020421071070314416240d69034111109150100346801804903041c1868024401901c44404441524488183c3d1a681c0000010a041c0e010301c00541301039103640107826554028036119000f8103010446041c0700b481c0d0421140100e0500d894200f21440030340311403109040f031581101784a00b56540030300b4101c2c0940010b2100340d100d5482d046010880150b0603a00505a038824010042d1030007814048036107015141c08090070405540384214035080c4610313212000c0d010f014007480d8281d95514108030105130a03400482c800317a00802c01007220308042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 938244496 1250 938243246 938243261
    0x3210e100612020d08030c090405090109110303090a060e031213080c01031e0905010e0d0c140607020c190909060209040b030d0806040b0f030703080307020f060601080a1a03010606030609 82
    0x1600b030758188007540007440104810300000c1100c030f000300000f840084208281d0328070100141041c0401e21b0140001802450207a030101c1d46011301d0740c014222824000b0035101d00f9940a801c1120013030030030109842e0605144103250b0306100341403042c10b9041104000e02014001ca00b06d4035112401c10800c9820888a0510b0904041c504880c8402401c81842031440c83e607140c400c0022090441d040090251440d40400c07040ba00c261000881c04650050322480d0050003450345114605861f4010390b180c3c8026a04040142d120f030303405c1302c55440c0c6014843c5070000404e880b82c602c650b54280c00c0040d01c21804040da405540412035069a041c1390040c0c900f4000c084001d0301044042c1c00c00500640400382456008965880c03804150340c448080301d220011000781203883d080c0e0f5a1804d1081c80e0310031148540140240085484440d00002e000c50284105848001c1c080d5600386041005041c0382c62240c1c2000c4244250020644003807082c8409001c00750340206107182030060000954150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 938245746 1250 938244496 938244509
    0xd02040e09010e03040320090108100b01020109080d0c0c150c031802150a0e040e030406030e0d0e0d03140d0603020f0f03030d020c0304030503030a1a0109030f03210e1006 75
    0x100071101c3d540c101c001c0b0458003a40da00035128850044103e00c1282070040c100243c039000010300e000031540c00000070300702c0000d46100390140291000d810049007600d0b4520700c001c240c58400c1c4a205030091503034000184604aa10380400b120300d498580d801200040d1078801c1c0703081e41d24040e007a0310b25890700800c80010345072480d91f90f02203595030104001c8070b100716200c205004c0101703a99150a01c60001601c1040f0020400d01000c004c604040e500c0354050711950012a18021202044400114040003440c0d5151188000513015500303009800c40001e104034200040443c400d440006c0d00009400080518000041d800d0700f14810310800815a030095803054035072a4000342d282d81c00004035801960128005600e45841340c4c80d03549107008a0300010140e02002c42080003690300ca80c80f422900f401c01c0001092280c00c0b10044d1351104103800068011403c0d030022101003405000d100d400035000303030046a80303005001400011508110000b8105400c041070380345840680740110310147c100e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 938246996 1250 938245746 938245751
    0x804110916030c140d0b1009031509030c06060e190213140f0409080d050105040c050d0e0f07060c0203160b0301031407090203040f0209070f320d02040e0901 69
    0x514074401c51211401c00300940805486800c802d402078840c90341d0821200070800d020b5241d620207018000902060810b6034015442c200600380890701c01c4459004030394200c6401c41441448103050406488008416000d00090868034000118180700c0e6600030312180d0941c01c0a8100341100d081c90000d02c0c40c0040d00640140040c480c6e82e4100c540c56000c030b075240342c21000f00401e4000858010042052680e922900d00b58a117414400c6400007072100d200f244c0380c20445a81c956042004640500d001080000d03420f010f840321051041d400000c41041080c22101180c408544880c40d09003070f80c01442c0007680030460030f411400c04000b4a1050416600c10b94481414008006000c0c001484040d05050500743c00000d001d000307012590241481400c06d5540345818107010001012840303040740115500d0001601180c46400b500381402c24030744d104030303100c0718040100e03003095040c0d110407070348044085500c0340a2400200402c0306801d040c0015032900d03e8508150b80f00040105074a170240d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 938248246 1250 938246996 938247001
    0x2010b010504061d12010b0102101b051b0111040911032e0807062105040203070608092b0305010806041a10180608010e0318100203090603040308041109 67
    0x81e00101a603080d200710740b03801c040401e2103210900307410001c5290b1035000a511030350710241d0071040d0003202c6000401e030202c40e90648130880c014229100d8040f110303030203001c14852009840c1b241c00200083c003040c6002048408681e08135500311100000c0e14000002d0014041004c10154024848030039400e0168034110310b82441d40010010000e003d8400080e01101c0c0310061100d42c20521000e819010212245551a0040a0104940d94060b0040c0c540d0b42e4401c0c4c403540342c3c00e0080500c0780758040c0c040c0c60075071305d410801d4811350b002816280c031134010740180b0441031484054403003820350040c0601010341c02c01a80941103030300c180c11144094201c40c1c1000042120041105e1103031410036407010060b52042a4016040025000b41c0b01c491440104a142d085c01a0481802e072120000204214401240920707520b104080140081c0591040c001e80e1034074045105144000550040da890300700310717800007145030b070041350124041081d8074280b1040c01860741c8507000c21041612015950f0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 938249496 1250 938248246 938248249
    0x926070b130902090d050706030b090f220312020703030b0f060301210f0c06020a140105011a0c011b260402010503040f0201030b090a06030b091209060c01200a030b0102010b 76
    0x10381e0540180304440da00012411100d850720301d41030448580180a40d94210b8482c1c000a01500d13540840350700c203e8111002c11166106202c00300d002d4180d4502c3e0040181181e4041c4a10a04800f0154140841405800300d0a602c0740010700c001c910030fa5000600c0108602002080513407142e07014000e205c28001032102d246101040c4e104101d680d0400f045141080c600340940414486000304101c0d4100000591507030001002d42e2014490882d1040c07171007503d42054203c1704248560507180e4104040810021605401841c2c005035500010441c08801c41075000d42c00340c002d10080000d0041e090403201040030b000b1001442d03004041103002070038140c00007001c80c00054005440103a15070340002c116030003071b031100c001c40c000a44a08138515081c220900109640e1000751403150b1500000742d104803010659150581e8024881030500d1024011b0002541011017210050742d42c520032020101d5690090f0300d85500c1502c03100c0d950300e40307100006041d60b106442d00b80c15681040c0d0b20211b203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 938250746 1250 938249496 938249527
    0xe0a14010f080c0c0a0b0403030f091112010204081506010f051801140909040303320a02071505090c010f030c081b0f031302090907080a0b070926070b 66
    0x340049403420503415212809881114131a96050b482c417849050624800c110007004c00328801c0c3d000751005c00002014140b1b8605403244004010100a20344911004515220b00070728000c01103000010306258607548c54a1420300201503190f8203020140070040590b0b4002c00320301e105c0100389800d07400e10360318000122518111040076410310048400720790784998a203050307030380342031009200c1d0102c0e0810307041c0600140440000c503114416000d0450002c1d190306245411181d40a6403c800a42d59440305c0740025040490111901d080c480b4465015030724a014035406609544050010f68410390700141100e904000303000d0600d4100450441816040100d2a9022030001e468406104502180a015225200b244460000c021081c030104007811462250308510a070b0b03002641c0e49640d00f0040d560000d0303114580c19540108a07000000d212070641e135820074107a040124885480e04d80c076401c4c0401c5444165150460300340d01091020301008060024410103956030304c0e01c2c2500e80040d88 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 938251996 1250 938250746 938250767
    0x105060f03150d06021c0e07080703020409020d021005030603100e0a15020d0207080415141b16030f0303060506180409020625060b190303030b0a08030a0e0a1401 71
    0x1c10400101c14546162102081c5485055100d24110b5132900c0b94241005610300381c03444030300002d1600c01c0d0b0703451a010000c0d00a0a44070310f60b0081004ad440d43d07082002900944400300c0e0043d80d002d1011005881d000a03400844a440c0c6034113860345814014146403004600010b030865040107445a0108000b00f100c00319990002e40c0000c080a42c0c9070004083e02c81c0c0008140528400a1500c091141d890050000d4909446500c00340c24460001200c01030050200c501c1c01c10820000003004100218000703503604110320a4174004980c11030880c44055481c0c1c800d890203406519024101603061103490003401c42102e01608041c00d0115480311020010312243c0281e546583c1102036503103010550348003040c18a03142c3e0010800d0042c01460401e8240b040702d0040c2040b01c2030305540b07400c80d00b41040c0150048007007801403950710202d000d021740c40e0015030400040c0d800851600014030041903040c0007a104c0c5080c000d070140034059104001d40c0840720f15000c070300e00380c01d40342c0c2d00409081 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 938253246 1250 938251996 938252011
    0x102060f04020108060a0b0a2601082a210609011505060a0212161a0103021e04140a0615090305060a1e0204141e03100c03091a040b0105060f03 63
    0x304640daa80006c07035148046504030440102000c110101096844030164404402c080001d801c0d00352480b0703d05c03030101000c1c0201c4110750440c0740c4111821100d42128440c41981c1d100000c1049882004203140c1d03004981c55017554502d1200f032079a204810000c19030094031201c000c008844601d103004c5802d031480d010741881468000740b0700845520802c003000c0c5100c1034495095072059003a5050030f000b034590074110303030b412800200240005035803081c190490f50040c16540b5003000104440700204060100780e42d0141d5110160300380e16900800440c861300b06c0c4980040c00030b09109081340e980c61074a00303410030080c0308001880040d4000c902c244e04842950b80129401c280d500300200c801882c0c1007034100b5140702040001d4101c0c0440700c1d0001162081d0b03644100400c11003016103e088084900a03015804140308004102890f030080c59005030520700014064a59500c0c034a00104412080b030150359404c05100c203101007820014014081281e10f039190a02d0310340b0a9096000c0101800c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 938254496 1250 938253246 938253257
    0x10e03030c0d110c0a080d03060e070909023103020f0d08090607020312070606030b0105120a320a150509190503090a060f030b0609030a02061303050105180c0102060f040201 76
    0x1003e0001c0100030f03000e25104018043c4145984618219598094200101002904000000603040c0641090f14010050b076510b0031089802c01480d00080d5003d04158414010034000180011400384408007140c1401003480d03c50a245004000b0001c2d00162294132601d60a82114002481ca10889481d5041591465196000c5000103820540b001d610003807400c000180d024100f025550040707043d24403400c0c075200240d0302e440c140b107516200711100c0880c9520000c4043c0210b0100e02110100d00744820003031000d070a09810601c0015445540710000350710103a5a5400c11520f002c0d000c03035010010808000d00c0c602501d00300d954003c9815000408142e240e5600184413050044612150000e0003c042e00d83d07980400503c0b41401064590000b4900020070281e80b40602c04c0b60700c800d800500408515005800b0000d940d032290007108201c0c40d082000000248003805050310400342290b5410340c403e41d00301501e050007440c5a1003811034020350704120881820781513035a040b54083c80c02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 938255746 1250 938254496 938254517
    0xe120c0f0f0409052d011404020415081207030e090c0301151e05072303030c0f0d0f0204080d08090a080306040b0d1b0e1506070f0b0a0902010e03030c0d 67
    0x890010204a02c01410785d000d40340305190042d00d070b0b2050150740d4808509040e4152041c042e41400c9980e10004032160030644000301d405460260000c514001e0482440c078001a81c500105240c0324045400b1100a9008034400042c59001101da802c504030580e07031009a80b4000c041d2075114441409090b1030b07100304443c11100130b8400d41070703120300800c8100d01d0f41c0100e42c0c1d040040d040b600071203000c5442915205400c040c2c0da180c02c0801c0c0030003058000450450b01c0300b4034042041c0c0c00062444106d2354080c00f031102e070441540102d00749001d0315480140c0e038034141940d682c1040c048100a9090014081c14401546800038150031050b4012030485e450b80c582c3c0d00010003800c0c1da500000d0b40311070007190000a0200307140c00c1c1c0000c50a0488914400b6546100005800408850b8886a00da80520041c40c07410044010a440b034880d080ba08030051407655104011316064070650030b00780d6540002d81c21540c00c040c0c01ca103000801c8005504210321419482d55031220700766014100540c8512 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 938256996 1250 938255746 938255749
    0x12010b0a0225050907020a03120f09020d062a02100b0607080c0609010c0e1e0307030c060206070f110a230a03020a12080402011e090e070e120c0f0f 65
    0x50000c42404910442c007101035007002c00d252581076020b8603100340104400700d540180001011402c0c1541501d60952541c0a1002c550080060560f070a9103d622400a480103940340210603000030701c24903001800800240420312426030443c034060005402d0400c0c14020360300020351044140e607501000c00d00c1c0992002141d070500800e14024002100854039083c0b030311001c141a40b162a0300e400070044060358080850769082c0c480c41a0f900f021203086100011811070070200e100c02e001504a842c4c880c0d4956a80c40328810316407102e40103820000c1800101c0350700c111a00f082c40501d00d0001c100c92000040c0540354102ca51009005c161405000358a1690a03520b2115107103010058035902511414080c0d00e481908a08032030840351300e10703088940d602808886008640681d20a20310024440280700c1c035420400551003481520300000451040120070184030b0f084d83d6a074079018090a4003400100118500840007540044030700074200d8650745043c00070403074200c842c217040601c080c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 938258246 1250 938256996 938257003
    0x30c0105070647060406050d050a0209150705160e150409021002071d040c0303050706020f07030c030e150a142503110a0203030906030408090d0308070207090212010b0a02 75
    0x20100e000c180028105070700365941c000761141003a160340fa0401000015010041184164003500e00451002d01052810b9520b550100c2e0303102112000040c0b50800d8000008c00001d01442544403694002400604000091016404107140e252091b0b01d114281204103c07180070040241c442100506400c6a49a40b16004444219005410082c0300312642d00029100c01041c012500c000f042640f60011801310030307210a100c2d0713421407299155142556011107142c0c1c05214140e8103a9006d101e040c0c6034035903280041c0905842901c0c0c100300e5081031b103806004040d0390501c440c882c041030404245169071174004c0380c901c5101854003a00e104011040018075000c1d1624007201900302c0e510b03400754040718608e45103185010380c80380ca921042201c01d6070790315562081d000790036030414806003495080407006944c020b4802c024075070802503584003150301c3c0c0140e10390a5001400d03810900c1684bd4042c00900050b041c0f1107020340c43c020b400e08018166207410301c41c4104080c00002d082c8229403090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 938259496 1250 938258246 938258291
    0x240f1c0c0e2a0a050703140c011d0a050604062c0d02121606091103100914010e0703110a0b03100504060b0a080f0a0204080a061a030c01050706 63
    0x2600d101500c54584015002841048940704814071506490440300d800c00b408000001c0890540240741c903202990440700c642107582c1c110301b88103241c403a110b02d01d08910701401c194686d40d000081c4181c00b1800301203003401d40c02000c2025400c01c004020100c1c4002c5000756215812941c041110714205c64124455002d02404442c2d0381806080964845804114a001e00b5015400c640b001c0c85141e01c101d815100350480b44a400c1800c00300700c00040c80c2508a0000180105109036003400311101003810a41540391820000d59211034401c100150390003508103070207054008202012605a540d41ea8011600000c0e00c4461a0025008160f8520340180094068032504640720300b494010071044281a00483d403280d81040000300b1503621660503100c26041654a00549449040c14900c9408000c0c1824070110303002c000104540404201d1000418420580015165840c000814440044440851007504184060b81e600e0381d000b001c0d03800b140e80001c8000b40b548902c8410681307a2110 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 938260746 1250 938259496 938259503
    0x1206042c031605101a060406110a140109121d01030b1216030c05150412051213050a140a0506031003050106060c060f050709120201090914240f1c 64
    0x4406591040010101300000c61100a01042c012102203a040c40c88440c0712491658000209010411450344140511101d480600080e65003c07807103034031000300c8410840d0b07001c1c04581d113445400307040004180c914800384180e8903110500351926120f95840c04014124141050740300e0a04080759503030b0341c0c9050800034607201280c40e101400030241015400c0c0c1d01c4107a481102041000965003850704610b0801d4114071041740c905420320041d1a07a0a080f00c02c1a11184240480240e22407000070041000e243c0e0312400d22181483c000410070380e40740ca034100244180355410400d4603520b46803e80b1081d203008454843d22030b982d501000c2413070360613a8806080d0350700b440d030001021504042c0001300e450007900107220749040120b0f0310b41507840948850300018013800701000700100540c00c1c210401e10525143c41420307540c150480c1580c80f0000801c021103104010300805000e43ea01606585040e00f821803200d82c001c40000f80042074605440e4094100300051149035500e201c20703110340961 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 938261996 1250 938260746 938260777
    0x20a0b07060c0f1d0405091603060203010f0f08070605030c130905010515130302061b0304080303071e0c060207080d020a0c050d020a0c0512030903070b1206042c03 72
    0x8081c140000a001c1948101c00030840c43d031901403140744520483c800f0200e1503110700c006070f460b080920004107402810b1491a028514584840640700c032108401107018010160b242c1d4181981c1c804058855480380e5070035045024204441280400e407281201d0690400c0c46d2283c1d5100000e12040c4600707941c0c1c0c00301401001020419002951003a41a103d05407802516103051444555051054040001c1c2c0742038601c80400040c03a04d00c0003407105000102e89051020fa502da6244d103150880c0e080011143c1003c420026a140c0c410300c40c00403142c01461401c0c211810303c40291611402441c043e20760754001540c1414040707843d080351062000b6500444d503c02050344020904802d08504844a0084452200070b007440002c0400c1502d801582203022140703070000f003010b41510303501c0c0000280400d2200c0c00700c81c0e5050017038500908011100d980d485032101c00d142d09445008100d1842079142c01c8641c0c02c51601108400302c00707110b444000c2803040b0140140c5281d80140e030b040120319030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 938263246 1250 938261996 938262007
    0x306020f041505030a060504090b13060f06230103052a071502071a011809020a0918142b09030b07030b240a08101509170105060319020a0b 61
    0x583c000d00840c030400e120314040001a4480c0c4c200800d89039007181c098665200400840c5040c00401082e095441c82507600180403208001c007001681c2c901c1d40403642e0008504400303000780d03070080a5100030000918040110349000014030728294817120b0040e0b80c40303140444a0100358482d104440c943c640040b403940504004914101c003952180d00103c403150315090b20002e002100c001554186d500d03080700740e452142c681660000134024843e080c1d9100c00c41c008001140c00c50380c4109044840100300c900ca000040b401c0c24100d061403030075240c4541c2e010621528540300c5ca00d00d5500288040c03c0341e00611003040384110b03080b11403900040d02810300c03071050001c01c2c0c0c1c00d40d0082140c100d0a86a50240355455220388038410003221300070300f84d101d00700865a12a44a008000e81c030072200c00ca5803c00759166546a045844c007058407a0101c1d050f01c0d030030b0040426400180683c1e042c10310003845a07203400e801103900d45100c044000038003104442c01c2821036403010101009400e00c07801d00358640 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 938264496 1250 938263246 938263289
    0x2070503010f020a031a10030b041806050402010f020d020c101e09080d030e0303010b13090227090702101a04020f120906010f030206090a030b0f0402280306020f04 72
    0x30b601c40c016203c0403074548443e21503210a4035010341a1b181004080720351a0190883c2500681899a440c0d40d1082e5070b03080c0c510008051940141551b4028030000603585098070024100d082041c96940640d4001c8031606480d56001031403000e842c03400d031660012401807010a6800300390b42004038a09120300003403192100d500c00c0100c4201c030b40d1201141e148001d121030980848442c80d01d00c1541d42c20400045c0320700890031005000000d01100916125640c4130402002c036040520030301c00f040072030100180b50003100444110310f40c00440703014049051880019545400c10303c101c90360280ca0b620500c0303200748081c1c001403003030710094025959400c44459000c2e1641c06400702220000c4240c011400840d4001185416500740c044140521401c5070208800c0d80c102e135900d568003009081010001039020b41c5800e00951180441d224941098410030807502240c3d038008101644c001039080081600304044012203401490050b0384000c0c0300c0b0350702c0c81c1c1d1090f900030224200d0210718020b000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 938265746 1250 938264496 938264501
    0xf090210020109151e0515090403030618140f060f180a050a06060507060e010609141501020d0f0c0f02060408060a0e0a0818130f0f0b06131502070503010f 68
    0x580c0301e035180c11340a041001c204800c030b90400d032801c0c041d01c1c8250030b400041e10283d0300c5907800c820322019091080303808600061001a08850413400240c0300e070b90400415480340c0c41804180e1041d00d0a2020600c0d990a100ca004001400f100340c00060380701080c442d480ba600038400c4424081c012201000340e00d00c110154581c20780f90303150260f21b4200042c004100e00d01c140029140c0341d585280c07070100c003503d44101030a2003440d1003c0f01d558940c00014244800d200301148501e00f1465007006140800c2d03030540464242030300d241503410020301030005a41c4180c0c090400c15450500b512000101d080200181500c030030b00942000c0c00103008200840c00107000ca00c90300300302c00140f00e050301a030007407910b1f14444100104401c505101102c00700361500e224103c2807a000d088003508801d180081000c1d1240041c0c03841c045030f95904031360b03400c1205000305214401c041c0c43c0d080c6045e007002c9a2008010716446034102428100380d6180c4e14038820302c0750700e000f0200103009000048885166800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 938266996 1250 938265746 938265761
    0x30901080a0b09042a060906111b040e0307020d05030c16080d03020304151a1212030109020703120c021b010f0f03051305031314060c030d0f0902100201 67
    0x454268000180e40000358041e0103002d00003d807a04000340c070340303070749072003000104403d09283d51400c011144a006002d44041004154907520754540070720f0303c000a032008105001940441c0c100e40c030201c0d521074040d56420641c42d030664000418041d1080c01908502030000b00070b500c01001c5d449007050280c008041d010312008101501c2d010303c0c04000c0c03104280204c0c803030094190001050f07181442d0003030380507552181c000c40ca0400c44000d0000f000d0115002140d40d8030b510305d5008100c28032410100400e00b152508640201204031800c0d0810b0301d58003052103072031205500081c8400806100c1c044807c400c0e50811400e00c030300c0070303a4140030791076000580129004000b10612810301d50310480010a5000e00d0b500c840d5072045018a0031070152100600d010340d9120081d12900000d0005c1005000340c1d03440c44c2c03c0b108902c0c00d180002e0f44540c000303007240b44904003d0005440800d400710881c0c103000c0c601c500019035280b41c401200003030b00704c91101035444080700741c1000030982c041d0400e84 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 938268246 1250 938266996 938266999
    0x31b0d060f0816090504020f10020f1002090105030105060903160f0513060612270b150406050315074b0c030c0206130305030a080c0403330c020309 65
    0x28000d074842944075034030031485440600e2000f464204000c1c041180d8010f82d0000e00140130109403c40036400306510300e5038540804010381c804200726007040c60a003c80071181006050951400202c98002401c0d804180140f42c403e01000400c08044da4081010461120880359001c1180fa80d414005000c611140f003000d0140017080344035901340e00240700714001d90780a03856888540203058404070052054000ca04040c00c92031001542c000a81240d60303100307034420078010139145041640105848410b4205074002d90510009001d203584c049280c507155a43c10510a040360342c1c45d80304540c1c0241803042503a40305004080b43e032a050b554140500d07640d42e03080d0601e0510000c0c48900c0c8208100742d24110002c0c0310484008002407040601c1800d0740d00051980e41004044441800b848041d0b91044401e41c2c00020b9000085030408645940110910801070605145440da25880810132010b1a4070300d41c00d040542c07102d032456094031101c2c0010350b001c21135071202007006540e903400b0f407a481e03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 938269496 1250 938268246 938268269
    0x8130b0f1005030c101d0301020f090a0e0f0403050c01240501030e1204210b0c040f060c08040323010e0c011805030c061c0c080f011d0705031b0d06 65
    0xb20b55810300103007240d01880040c01509504010142c01c5407150032941d142c009240e90814a12242e60313090000d0a03086440c2c1c640580d03941010010056903040c190b001381d40c5151503000700b00c01d01c604003850b10b074410f42500f8655a903d240c40c0c556401482d0704401c0049281800302405100c003001121142612801c0e02c0030405200c4c503544150b035509415481c01c0c00040f04200a01450000e01070f8810134481c00c01d01c0c0c100803409035507848441d400031900711806481c0400c0400c07840f142c403441d410081c0128141640346950341d40740c840d01841a404082d10505401c1c48841c0010543c0e01c2c0411008004402001400701700f00c034140c1c031200d0342410a8002207815406141c1141c800411030300f261001001000e0701c2441d0028481c0030380020b9000035032010300d024466003001d900d001e452080c1c00c0543d01c0710903900c1e1103444061110410b800c01103244085142e100c039501d00c1d000c1c980741c20aa890070324903200d5031152004036070007190202c94402d1000104403d04040d02d142c019105440720010f81 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 938270746 1250 938269496 938269499
    0x5130e070203040911120411030f0a0602030a0612082505060a050711031315202107050a060b03070504022706130909030309140307120302030601020c0108130b0f10 72
    0x150320060042c640c00c032006c0019103002c9000076035800489840040050207640c1c5101114860a00700410400c060317664940000820500701258031411303021301f41c4105000c1d084601034132080754074002ca50001141e0709000d0080c0124140026440200d99072000c22100305140c88040840a41810f0b6030380e0b000b041e0403100c05940700c03d022050b1440301141900f1007082c14601110300e00494031410084041c414a15000c0301c03402c06145101c00582d24070380c02066079581000004007603452902e180b082401c401c1c01141b00140780032034600d00c40c03034010380301040070210322000900301041644055407003440010140031040f04186900e14039022081c05504000c642c80501c48684190300001c240c4090f403800600610131030741c1c40700400341d0007440d00254050060395410b1881e5202d041e260b100e540085032040030001c200c3c400c0d0308146042d18056046040c510300103513a94401c207420310b040c0070024000400d030119120b1b003a1051600800b4150342420448001020741009440300620101080070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 938271996 1250 938270746 938270771
    0xa0b09040f052e051f1508060306131113150501030e060601080415020403020a0303080411010c0b2802070303050f0108160501141b370305130e0702030409 68
    0x400e40102040c580005540c41840000d5401414010310301034a108150305600c070500c104c488500041c0c03030b07844000d41c2d1120350940087d2801900600151003980a8070400107004000c10016841030f50110720721a501d014840019100403140d82c05202d183d1511350808241145070400313070101c900a0b00d040042c881d40243c0380740c03a4202101e01e507001c40c180e800820002181d03a202a42942414040103090030784a90000e03441d001d55600035000171f074180341031105004101700581c0408001b420504820601da645140700c48030001c11105811810030b411182650100340d01c084007540d0418115924051464060300070901a07602c091200c1c0301c01e0000c123070b040e4000303141e94034403002d41894010b51b8a048011110303032055020007505814140400e0702d4017080380420600e059840c101503d40760103103070b24201030301103651312001a4402c40d048004840030f01c002080310041d014500b0a5a41901c0c5031400c00c60a12035206a20040c120740400582650100c040c02c152013200500b4010b500c403003030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 938273246 1250 938271996 938272033
    0x13020f061207051c091109071407030302040314011a12030f0f0d0b01080921071a0610031512060908032406070201021e10020c010204090608070612050a0b09040f05 72
    0x30401010149401c2c0034880c0381c83d103a040310b1f40c0003072315281c481000703140c044120007550070a00b0708501094010800384100a043c3c0390050340c40480340d000b00b00f003006031104498104d403010b41c0d65000344000d00b40001030032400d20450f0b00c0c043c0405506903a03201030003042011503001d039500403031142c90000214030035842604e605005000d840005d2002c2c1e04a109102500c4000c480d80e241690400c11a0500107908100c0340395403061280c815511502d0000c090203501d0b012081d0340000c151618540740b0610340c0c01e48505003510b40b48203140051855524014000340803c1d0006401c148000c806c00294846011521000d0700761142ca005079080b05130184140350256403c020b001d41c01000c680404e14240300d400c02100c0c001c0600302e51641c1182d5200d002280e0011840b01c8059400081c00c4c403038130500d4040e220081041720300505c50035103803070801072a400165462100f4035484d0360100d03100480c1c0b074010f00440c0c50020011022402c0528100c4041e0561341400c480038003078100301001da0301600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 938274496 1250 938273246 938273261
    0x1a1e19030b100f090e011e0f0e1c18030f050d020d0918050a0b100f090509090303010501081906060c0b1003110613030b0f0601110613020f061207051c 66
    0x42c1081034910f0500c181080980000c2d110030440c6d42d079a142d0284a080b0082e8461429426003a0008034900740400d00810758140304d2074484540d205243c03540c0da8000d09100701c02400300c58074091200780c12042405400c02056403010340b0b10300407511751400f804408a01d01581c40ca1a800b1a0440f1810310016241d1540c940b00300c070900e003882c02c60030540c1861038000d280c0c40301031441c0008480c0b805100040000380c0385041600050000400500f80b5a001918034024150841d6800141d1900d045003640c0d81c80140200350400c0409400301c0c2c8200e2014a092a500c440c0380018401641c0b03500b80103050703181c1c143c1c0030f56034007c01c1c40c0400c81c1c1c1c280c0c81084005494020800d501840c01010600215901880d1100480403040342d00001184c0242da06074000c864a18103590541070100004141022201e04128560070410522882c160783c50360b4000d5850f816101c00b5a0101c072100041c1540c0211030130841c04c41100c404100700e40341d000c802410b615103e6421444801504002c0340b0031100381 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 938275746 1250 938274496 938274509
    0xb18100f06020601030c03150b0a1502011404261c0203151903082208010204062a0f0c090e0606030d0e0d2d030c0b0a1a1e19030b10 58
    0x32008188003196000305200a50231680f0400305075034640b803000c00d41c0302c0c8080d0703c0f910741c52012190305200a50f081c0511421070b0712141c0c0314015410a9100c902d603140f0b4180780e10708401210609204206004130949000c0391180302c0141008601200301c1c4d020750300449031051000981c04484029192005440e11102d004210005095046580e4500c19a05c20180d4902c1911280c0012005842512080380648042d40000d42c0fa5440c104c4080c21611840d41c5100d40000d840c0b81d44065103d05d00b01e14289560048440001c003805401d0058016045410801942d804c00380e507000b00e2100042d955002e0b510940403111500c80b40030044503014000036140d984101c0c524103500c042101da04400b125400d8250350b10903c0c20789000503000b0400701f22021000b05004841c11414084600c14555100c0c5500c6000e104094041c890142c640209040c1030784541400203001b01454103460035481d4040000c1d001e0029810f82c0d50f614603640216110448484400f0000540342c0c6036030b446090200d800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 938276996 1250 938275746 938275763
    0x61809100b0a110709060b070506010f0b120a09020402070b180601140906030f030301030c06090b09010807080907050a12151503021309080307030509060a0608030d0b18100f0602060103 81
    0x9002d40101d030260030804007240c0d02c1c4940c40000c00c00d00302c10b1041c4d40040000c0b450f110366941452400d5070410313805a2004940c1c00070940100b1080075900100c03107425200c414803010a07586c40711000007d05501c280039401070701c0864540704200302160101d029403401e401d0b2628881c10010303210f80d510f10034004d10307070354a944144403410b6080c2503450300c0e002400241030701c0300c2c180c3d100405480c64000342d2090b80c03424401d10b000c110958022250b1005050b400500900d002070a000203460001c024103c4000c101d581800581c45800900812016020045c05090100d03668014488092400a030a403188203552424083c940190b00c1054404a0100c1444030658955000c1004e90500c28040303c007519141c0c0c280a00080d0180001c51003940c068900095600380b9030022490038400920440e460b1b4980300c1d0a000361031000040c0c42011312040c40c080384d000540f0003c2118000f407030f04c0c008019501e0000341f0400c0c1c03254101c0c0708160307107004c50130340703401940d40500300c0e0742d49400c0c84043c14080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 938278246 1250 938276996 938277007
    0x9121706100c08070807031e0311030f2203091d010503060f0711010501060305151c02040213170604020f090f012c0709030b06240315061809100b 64
    0x81c0141090402c040c0140002820600c0760b4a80400075801180120001074000064a06003640b0001001480400b0f02d0b003040b12581c4113414022504c8090705c2e98545542a800103000190900b6070390303d526460000d024850b2103a0310b0060712001c1c041c0a400d90346a1500e0407449a07605100d101c1d0f0490703038000d00034280742d01c90305003090302b06002602c03070b800b0826841c0202e2080502402954001d07c02990b0000e841e1911140d0505107150034401d4521450211100308012000d004641007220380407170707005a455104d10180c15000100341c2c091b83c401d001c081c4000c04449004502d0ba48228000e07945400d40c035440900b0481c016008542c3c5000448190005109600310020300b400c0c0040c928220051060500d5016013101c01d08035500000a100704800340104415030400710313040002603c107a44114009600041d103500041101081c4a40c00310028521440c01040340540f40c401034101991012013040c5104001d4280c0b28090044480501140c08011107802510894040040240c00c28 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 938279496 1250 938278246 938278279
    0x31209150a140a090509060607120f110a082113060b01052704060602120915120f0a110a080604020c0c091306060812040512010f09121706 61
    0x180c008654007420040c0d0b070200c00c07070485a10301c02481414600e490340c04001d0f20f00400c00813959401080c0c1401128180407010006021000141040c049414101c04801e1180c40844486c2d400c003d00750214807891540d1b40034003c0e06d40c010507030300c00c44042d14a03c51603000b00381c1010324401c0c0c600d071b030303505640e40390000c003041c92036200902d4190b05140c407518151a42e0302c1d001d83c0340440420f03610f206590142901040c5410700c42d000050180340058a050000050000013074000d20310154010404d4082d00105029540b00321035100000d485e40b20100e062120407010b00b508215020141ca0745001641390074114044255000f0600b00c3c0c3e12002550740f00c0042c400a504140840748036849084203208290f5182d600722403049031030114508401c0342a04125040c2d9646e40c2c0541800e402180c0c0d00d14440100d0001c403425500203036080003034400c40742c0b016070040cc0c0340710306004c5442c540003a800403c00164020440c0c004180c5c0c2d241e600340040c6414003c544000e4903003584c0071201c401380c0c0c11300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 938280746 1250 938279496 938279539
    0x80a0210050a053f090c060c030c07080a0311030723010e01050c0904060614090111151f0519170f06040c030201090b0c28150b031209 59
    0x48405850504d081c5035085030b18420f441007890000c210b6241d000741800104000e00009889094802c411405906003884c1c51500c42c6902501c0034041d840000e401311100f5020801c03035078030890503021100f400b940c40707160741d8070b0b2030079000100c001445203202c88070007080000588201c5c0342c11400000f594040a8035951a082400308661215500e54440d214010300c203206091041d035013161050341e2081c0b80400c0000310388040e0020310500030900000c0d8029032099042c0c518100f400e0030030401d03d00710310300307481d141100101c0040c02011106041101c03640c440c02c04400700031310080703040c0401500c62040083d450b214a511301c4003400c02160800c030a0785503102c2d20340ca10864400fa90110003401c0724080c00c1c9002182d09440c8411266400c0085580c0700c149407004000421013241030002210700c00c1d880d480d0b20040c080c1030103083c1c2090795000d03184500b04c0294070361241c40348604d44150608032002e040d810085500c80d000f0b4001d0f8207002c4103008100c43c042e0400520241c6400c009005200e41c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 938281996 1250 938280746 938280757
    0x4240b031315241409061518010e040c1b020609031f23071202040f0b090a0828020103060f080d030b0405010621091707050d02011b080915180106080a021005 69
    0x11f1014030b451091010084a10003001002141c030000d90031200a400050001181c624800d4000c1d45403003640800603030300010800400742000282d41c021105030001586501941c6501507043c003038080044940c2142a051241e100301501043c4465074821403aa0000044081441c0c0d600c20208001001207201b00815001105498801410183c550040c2c0144040c150016003101000290b222850b02c0e02c06004401071210750011f01080200e60070b1040c20702c440d621001860f01180403220110380c003a40000c40549600d4524849013503a44a242c0d81e00c4034652072403000710346021080c1c2014201401164103030ba10076240c414591108595956003990700b450b0748241d040c0d4801034140003403a400c558580410904e00c90540b01d100c1810000d0900c40c0410b01c0c1002c0d0380c5040000d0019118010380300d174000049060280301d9540795840e5905008016424400340da40c04820400212220740c10300c540780d01440d008214003916244040d03a83d0007068408ae510075405546000007600c0380c0003c00303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 938283246 1250 938281996 938281999
    0x91504170c1f020d060f030203030f071103010207080d1b0e010f030e0f0123040b010b07020301090212030c010b0d0c0b0f0c0d03090204240b03131524140906 69
    0x165440d102003402c00c0218280b11940c424641c0004500c090341c05940500c0000e410195101e242640c599400aa9a0b00c110010007402c9180440c4400034480c00d443c2104248401070001d540d1004c552800c2c610390340c091201400c00900c7c0031003080c41013000d03846030703030400c072141e11080f40364180440150745140c00c884c403000405440f0022094010424031401030000c04100004c074082550301030303e40552038134030f0000e00031302c00175030402c004030b8060080d80e13044800400d901c0f551075016001080c007400b0152000303500035101204070301d02c1030320000040074207107030400080002e503004101304180074040910240456481030414001860078000420380c0703814042c8414038001c0e4101c0c80b2800c1c40140c00b518000720ba6211010b0066082a01901001d04000442c50042c0c400241852000300000c1c0543c90060001100252074074558554480c00c160b04401c004c200781030415000c2c2c0c0a03040403580d000f0186503524054504800080c15a01074a0116034032681034183c900070b02844180c000c103050f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 938284496 1250 938283246 938283253
    0xa09020c10060b03072c010e0406050303121023060d06080609010614040c020d08071b050703020f0d02031504151e240306090206040e0f091504170c 65
    0x101074180346032040b04001c05a036101d09032a880c0c03d0301c4c040c0140e515000501d00c040e12150007404005001e1005400c585800d003007aa50310404580414000c241c075420290301480005811207690a280104078418103924103030780440e03515400b04d1480c01d6140c0a040d5030f5030b50070340b4056070945407110261001241d003038000692640d0321400d00f0f1610344251044c001c01e0350b442105201c103503a07002d002c00c881c680039030341031043c40f81ea0f2000030b565900b07001c90070081001c0c82d00450b00c1a40f25030600b006a520480ba00c50f00c52000f41071080d00c405175407008034854a1302d010544042e0912051503894282c008001c0c0c00e00700492004410402c074010811601014141e010000e0303100070341304c2c1440780c1920031382c000c110b60104180d113001c8806d07441da404446800410440c00b2416080300400a595101102141702d03043c920100310740307018942040304410210300030011074140150200b8403684007c411168151100301007820403080684001e445443c4c004018642001d20000405062041804a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 938285746 1250 938284496 938284513
    0x9010504120812011820030612070b030901020406120504110904060b03030307080f07080621010b06041e060c17091c0b5403030108010606120b0a09020c 67
    0x85441c001d809070003804500381045c03803559168006200e29240f030442c4030340203031100c0c0c20750000c0b9000d40070042c143c80c0300e201810030850788030000740030006c02042580062622424584c000901039041405010001010500c0340074084c55540503603400307260440b820411318840d0302c051103c079560040041d25103c0c0ca600b04035840351010401544111415624041c050400e1041c21108240140400c0e0810200005002c0c0a6440820240d40f031a0140650010201c5074030f03806d0302401c00c680d8083d50185000c24000342c1c1c003020146007842d043e000e66801c42000d031201c0f0255081c10121101400303050820070b8400202c240ca00003804400801041c611b402c1e0010131445a09031802e40e41183c82075041010b1080e04401700100ca800c0c10030546035078207103c0203010280e0030850b000220f0a40c1000d034032040030000150501e681c0d0b8499400041d0b956940c3c4900c4103502070685840b4043c0014020344140e80c500c0164801c203007546000400712034580d4989034080c0302a410215003202c580c001c0c5450f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 938286996 1250 938285746 938285767
    0x8070c080a030e0a05030102030403020c0112110f0403050d0810060c080f0304060905060c0a1d010c0203060c13050609060d0903121a460918020411090105041208 71
    0x60440c0c041e02c00d0340c414500c054104148403a10880390300090091380144140b00c002900400c0488c0158428070b170038815030306104410400303041895480303600ca110010340c1680118a010041c400d0742c1c000d501300c5584900c001805c4420350300464031410a01803506c414494a8811911a48514001c181082c20042580c02c07d11140e40705035812a40740740c1d9001304008209052001940c403206418016040401d0004060840c1443c415031420310780601000c4903143e03002e00f5640b141540c014088640c2840d0865142101e03520605140a98500c092400202d52408070105c0b800c070034026000504010210a0071000b81100120880600c944045890688509072007070400c1c040107800034051090b540c00a020700c41c241c031044a60190035a05c100392001e4040600700c0c2d400d65084291100b80125114006031038151a005480d0480c00c0561829594038100b0320f50250900858041041025140031030405200d0503c00501240003032100b0000103a06144c004606805491440e240400744030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 938288246 1250 938286996 938287003
    0x7120606030b0406090501050612090a12090f05100c081b120702040b0901050306010b16020a0f18051909020102010603020907090e0c03010308030a020f161101020f120708070c08 78
    0x300680e00003aa9022070010750702d000d019910060500500070025541400046101841351020144070b41b01d1b44c1000c101461010490601c0d81608030500300e0720096229402031940d05240308005200303843c84004180751404202d0340301c0c10719003a00e900300b6010003030b600d4210f5034000c0c021070748003040c405011080155041c0082c00412084010f01036483c4034130701c1000304881d002c0c420320303005480d400018003140d100000c0140c1541c0020310460340368100d40391000749600b84450025000001140000307803841c20440c0e554180c4da0b280601e500d06c000b00c1320f13a9a0441e4412130b81c01402154100110f003e0801d5a4401c2016500620010401d40e0f2203070045081c0280c1a1402000548409000c01441e04442c0365181c001c10104112455075140d83c0f02c000e4a8000038001030304c4035600080340ca0898011000300e034100200c030444002440283d0510010704034226140710302600540d64520642500881c40a0580b1505000b10381040000e0300d9a26543e0041203007101da121410502140c51001003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 938289496 1250 938288246 938288249
    0x70306020301060f050301030c090b030a060f0516111506151b07060f090302130b030d020601090507090807170106031b151e230a080a060f0815071206 66
    0x620000d652545480741c01040c04005190103010041c007400144005184403044900311020207201103400c1d0f0750100024100614890014262450030454616085050300214859103409422402020104409842d0100c04030718041c02c87c0c011050162080da11000c28680221014080328000d00705894450461303803010341244900b450803481c100321460104035407809131000345040101c41c01103100140266030741d400000e21450f6140318201c001001d0303a21418042c000201111820264280c3c0a0f46900382030140326105800c2400040c0d541d402080305000720380702c02e4001c0280750310380004184400462026807100395200d520010219004140c107844a00c001d1203200e4000340b6001d100409003902021040c1445000c4850500020080442d24246292402c0803800400e80034a90142651007840602d000540400c0e880a940c0d881a045807160f8800d5070300308621600e850821310280e01c684244101640800340310031440d0700c008a903603000720350b500b42a0f0440d424087d40c0d4042c0d901d107 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 938290746 1250 938289496 938289503
    0x13081504110d14420403052506050709091b0c1e03080f0a0603110d170c1b0a1202120a02030d050c01051513110705012a02061e180703 59
    0x28000701882083c920042035020020804252400b495944e0034200351000c0180080e0522601003a10000421001d4201428041000004108148070701d015002020250f404a0028240c110081781c2100a445642042248190304c95006201c0010032103007041c100200322901442181c141040c1c0c0c80302204515014400e403128040c516001d114581d10070001003082c0074090900701c082011a000016001d100d0109031007014004400d41059503604458020700081642d0001d554040c0c10300201d0b170701c400029160640340f03c4920031800c00011101f24000c500700319010780803040041c580314070b03000c1c01101200240c80318684503400080c01c081002407c68089040001c070881210003e11845510141d0000586402095000851404411052a400303001c4d44c903048250840225416901150360000081c44205464140c29039000000000b2030743c03c20203007105080b41130003c1003892192285800201c081d01c007061048a491401800c1c59486450380d60890301281410300549019500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 938291996 1250 938290746 938290783
    0x10050f010e06030f07080703090f020f0111120301050a05060f2d040b041d040314160516050103200a1409060c0d1e0801090e03090613081504110d14 65
    0x45c80c0d84007400c1c10a0007041e11042503d0503050741d00140c0f00b200d0b41c610b2290150703030b08680310450b0382c010780340c21030045c0351004148210f03494100c2c5001d40e83c000b11f060341c4041e1000c0800c0b581d00c005019040c010740a00d401c0c406401e1201d60301104d4141140f0344031005248440c3d00311500310010707211603403103a0007060301800005028000d200c6c150102c0520156101c1000100d89030036200201800358000703c0c050f00b980000b4150001480c8840e80c140400d03040800c0c3c4140100c0740c0c0842c0300c040031902c20030b404642481d2604030007a6410340409c0d081809404101c0c5003007031100d0119012844c200c00c0300c0d00c08000b407008002c42d84403c8064119012000014a040c440b92a80035104c10700301c101c0d10001805000c8c1e0803841c981e02c400e0b96411185201c4c4085184c1d124048030b541180185040e5030b801c090041843d50340c0c80c000d80182c0b01280d00000c10fa6100080100b0b94071504441254040c194401500706010281865500380707500c40d002e992100c1c40d40d0090080b8a0030a51a5840c1200502 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 938293246 1250 938291996 938292001
    0xc0904110c011a0108042022200a0f180f12060f11120901020403120918061202100201090803071718061f0803030103030801091410050f010e06030f 65
    0x68209021603e40b02403c04550a10f020703031f218005820a83e09060aa100c00a0b40843d248c0300c13454080040b40b1611074003e02c071000820450010544200310281150550144808440a400032540d080c1195907071130783d0170b0000303400c15030380070b0410408500f11a10b00840001d4420020351510094000c842c1d5a00f209005418450290790a10050300c840c0b031701c0d0900d0350001912280444a400001801e08040b543d00d1240203070080c003c030307840070300b040111400c1c41b04007a502103030610a4909070301c50405129040903900045803c940101d804400c0701e84003640140c50b11501035000c0200c94030002c200d007245983d4070b80c80c03900150b0314100407910101c49098209602980a40c1c40b6089401d0080b44a2031180c540703644178005030440f01031341d001c0800e03402d0690680301280040d10301001160380c4c0703507035074a40181000380034410f60044510b4070443d150b0041711120058024000700e0420f650440c00d00040280920106003814180001480401c100303849000156115440215042c403092 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 938294496 1250 938293246 938293271
    0x204020711030c030724032702030f0705010c030c0203011517070501051e0903070905150f030d0906030c0e04090f14060708010b0a030b0d050705040b0303120c0904110c01 75
    0x10f01c10107158460380000d00c00f0303c01c0100070325130708028295488100c0c00312040b1050a400511141800290015140180c000c044504158002000f48260111854107110380f04994440c402c0307004150000f01107180a03c0400d1080d0400712844d0b0008000090f84415403007011030b0440c403507100006004503c0c1c4100c04044041c40794000509080c01e10f58078104401400d001c40d04440451444e440380c000c2591030380c540b01040014081c050042d4200308a042414203c850a0750080005105036041151600c260401154a141800454540459440c1841c805034090107d4807124002c00802c0e0340c0d60403084c0e58500400032818010780c01403040d6461030801400100241c1d0450070303644c0c442410f00c03078a981e00c0769620f41140c4041e44600d0315880400030840180103000b0903035038020001c04c1c03540c0030f010703011030750074111481184d003003044c03404420a1507140c0c058607503116100c2c2405000184d10615480c02040d43c500002c2000132400200e02c008500d0340c001d007402c40d40682d9200038890b400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 938295746 1250 938294496 938294503
    0xe0a0903030e0d0f142b0615030203060a0f030b13021314011701020f0a0c05210c06060301201803070b03040b1b160606170f1c0509010f0c020402071103 67
    0xe0310301d10708803854001640c44200030b40a0502400b02001c0e1102e5508068804a50202001d0042801c8c501881c9901800043c080e400a948051150b58455000591141e4126442088035800703195108203580d40c011071203034051a0181070b0b8104440b403e48240007810740c03180341da60400c110203031034595040c114481b62070348010745c0319285a803040040070b420024a41c02d03280490098600240700c00c110703262680c101380305030422007e01c4003d601080d480c6070010b00945019072803a0129010b55907103804041c00e844041e60700c80d0380e080031007024200c036201000081902c11214142d80e04098160404646403c4041d030241190030700101c14081001040d082541d000f0090541c4020b032184100388100191083c035511003c0e5140c20303401c803c104481ea400c2203000b0040c401480b0004410110341c15115622844090f0042c018840290302044103004910f17180074142c0c0d80c0341d041c64100307001074070f00d408411094418820f13507500100041c0c1d50341c00107007541e5100340491400903ca4a05040c503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 938296996 1250 938295746 938295767
    0x110301090603030e06210901020c15061002160b1b0d0c140705010e130f090309080d0914041e020325081b0306010908160503160e0a0903030e0d0f 64
    0x100300800c100c001c0103c1d9030140b44040d010303241d41206d296034441c02805802417140e40c000da1740c140140e1565500a41c5c1030114144600000d9540d0392910100a01c03c0361250145014810003c0f0601006d01c10170034054081c1002d1488141c400d010720050032285480d000e480d855100001c1c07007003c8070104010081c08982003526a100c0100f90080c1000000380207003025880d9103004552102d444803003e81d03580c000040c24482400300b000100d8407424001c1c240c911034010045107110f0312600050319889219100100d451404003040f102a00804101c0a000e0721810b01c0c103e0b00f04400301d5103040400744003c60003100c00c8034120f0340032100140710108142100307560a0601c81007030208151000d06c0c0400041523004904100e640790303913141c010f80c2c4038030594000c4141c40c45003e44007000064405200320580d1400c400316011600003d0582c402003c560203960b80c000c02d0036003c0340483d0065041001d100d8481c1c14013240c032200c401100762a0840340b010380c40c0010900c0741c94119443d084064440c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 938298246 1250 938296996 938296999
    0x5060115180e010306150509160f02030408030715060807090b040f0c1d01033c0203130303020f16110906040506030c0111030415090e10031106030a110301090603030e 73
    0x500703031490495804494141484050003803512229801c0c04480d90301018009400c1c010100c0009080c120f0130340d9000303d001081503011407410004134040500010958080b10016001149000c030740c0d41c2c030b606400201c849507000b0710f52103070f602084000702070044001421040f040000c6200014003000180c070607980c2c07201c846910323191340100040d900c81212144003403d041d0001c031507410b00c0012401000d4490041300944001045885c50100a40c2480b0000d01c0044d00c440581800880e0041203100c241c911240b0311000d0320074400000d0080d000b8202a00d4602541e03418150b40d0b03140456009442c0d00200e48240003240958802d00c1c00c0c03000c19400120541e410841031034204086907a4400e038000ca40d040c04421040b81440c0342c1c0420444000c3c24080b04c2d01c440c071000c2c011014213303072141d0090001d40c00000002800004202d2a03060451b60802241402c0e03020800601040703901c080c0c00411000e841b8a14481003410102c0158020b10700800d000408600c0c0d0300740200107410f0b409109 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 938299496 1250 938298246 938298287
    0xd0608060a06140f061e0316030f0507081305070e16021603020a0b07150207060506031207020307061b20030d081303081f090b010e01030c02120a050705060115 70
    0x600442d25404130740c1c000000f01381c801541d00c114559000d8030720154040d894400301000000c0255145080d03010002540168605100082c01d0758102e1054070800c8811200103402d42001400c43c14030f50144c000d03014014000d45000036100c4003989141c01003111541003802c0300742d140700850380d8100400c01110591000e02862141158002143e9000a100e5403012070030100c0c280003030002a8010401c440c520403800c651ba4107403468107001400c001c482d414800c0c0a04540810181c440c0412a079150b80d0041c0030384003050804005551500215500280c50b80d200b943d040f002075442400f504100c0c1464a00f10340200071403040600d82150750141c00b007045030200900004200416500c0300040e4035050004040d40d8800585d41c07030b10b81042d1149815049070000140d0092142e01144030f080080c1c0c1c0d00307192031400b41c00540030fa031040000c10005031320040b912038107403c44c1030141a003007c031403418500d498030645445103049802e821031084010101d42110405400c00f00700b04205455000310f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 938300746 1250 938299496 938299529
    0x1d250203040e010b0a0f11030d02070b06090609040f0b0a110c01050115050720030a1b060f1103030f2e0f0504110301060513030807030e190503210d0608060a06 70
    0x403c1414540554000e00c14203001440d241c12040c13051b0f40b1884a009c10031521a1901e0410b40343c5103800340c5a01740100c1440b00460381e203080504189208a8000905250022441d9192544084024804400c0941c3c0c0d00c402d80e02c075117200c0014100e84000c0400809d0035410404081d103000c044201e01c00500a04000c1da00000744910090110310114844000030801c2060200e403c000159500610010b00920f014800f00c014000359801c3e030b20540d0b280b60b503d015030801602c1d00f5111000c50703461507005100080803000004040c5521240ba030649107005091804106646414049242480e954464051100050340440c1000400c1c0485060103c1c4040c20058850b40c4018000c4d0030030414002400300d0707944d02190032403009641c0092b1050f510304032030500078450081002034500c51107100d02c1c08003170b12051b15011404d440000b400b07041e4004907284403003905101c0d1003c402828209000c0d001700310304944110340c001c1130300b000609100d20300b440b01001291215000340d88840050710a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 938301996 1250 938300746 938300767
    0x1090308071d2106090703030206060a0506070605070e030d030614030606090403050310120c180506090a020918090a020109060329061303120e06041d250203040e010b 73
    0x801900205036000c3d128803040c44001040621405140003542c4590000d000740c900b80084d211007128041d6007034038055103809040084130b8071a44506980b00c0000c1c040840401c10641c0709940081160500c0100c074080c52000c28145a40c44a40c040030035074401d0208110000f40301c4690b00d905044000d88020310745107001032002c81c0040c0002e0108a80400054203148555000c0d0000c2c01502e113501a21010502c1c01980300e20040c040c2015004901506414221090044074051803004011a0f0a03680e07440c030720f000940042c03170070307035404000c0c100039142801c1e442ea4098080c0211501411002c401800050400e658592141d0100b40c41c0c08404110316000036140300b90283c0d04002c4006000401c4e00041c0c1c3d0740901c440c418031654500381c0c004104207040c4040d00b80c9103220307281d150a90380080d04000c1c8a00840c440c3c2c07000e08844882072a242030403945416031020340400d12500000000c0300440d80c4820040008001d0780c00080c1c10310840440c04501030062500741c02c1e40780790040584 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 938303246 1250 938301996 938302037
    0x31b0f0308182d12031f120302071707090e031e07110f0d080a021c021f020703031118030c06180919180c05010306060f080a14090109030807 62
    0x440184214a4000b07281411002c0c07124181e181303181c1c41c05588a00345040b00448402d582c058604000b41c00040001c0c2c0c0d20b01d5401454000380e0140c0107002050703e0158004501040542d0069260042e004041184a404c0c40394a1120b07245034000c40d01e40d4100c00000070901213401d40c0c1c0585403014090000050401d92090f40501400d0b40c1c40491000407001042800c02c00e01401442d4000100b02200341c2c03680011400102003416100740e07100c004005040c0d031642010350352100040d0324180891007084290b001805000c0c82803900140c1c2494a06100049403c541c0340d00c42c4000c559003080501789020031940c080c44204941151900e0300b9000c08503018005441d01c0c078000d201800018034a01e440302c807021100b100e0b00f8802c3c44002e1181289960750300c80980704607480c020301c0da000f150a52080c0309100581d2010b403280381d018841190241c03000c4000804ca45001c5441d00b0f400c807052808441c005000b0b03514035001051202040c903000d0710340c0c14010015010000400d400d061080b280c01d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 938304496 1250 938303246 938303293
    0x1b0115050a090b030102090d0506040c0b0903120318010c1d0a05060301030b060d120e010210020408030405220603080301061106060105160813080601050306090705010903031b0f030818 81
    0xb090b0005040c8440800310340039020b0b51a480f54480c0341c803504002880f2011070800d201c0c84c0701e250b50111581c0c4038000415103000d4660001d81550200407805051245c10009540012144440c0d52480c1c000300c8a007800d450120500d100040c14040c420b40d0320102e1550020b8414500301d8400710603604010100d01c850205210150002c0b583c0d0b800700d0016200e45104400403074001240e5003035012030010140445194191090040c420b8014042002c03989200341c50503915000065864140307803404101c14900c1c3c15412204070b04840240c0f2010819a104881c01103203d2002e40ea101e42c5070440203069140c01c22040c17005a0070001c01c00509a0384141212400c0da030f034964806c0242041d04124007140140c8050b103c07680611745008c508040c000440e5412644220200c40c900c0c1d4131030860548070840d13849668085404030b001480040e004525010b070f8241d41c1c6207400d0307040c6c480fa100c0750581480c01c3ea0680c041000c5505100c2004140c0e2000d0288502c10720003080c0c1c14090f0340b00e150041240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 938305746 1250 938304496 938304509
    0x3110303130b0c1b0102090a051503060d05030408060f01090c030b0904122606100915211505101103040e0c0903060f06090a0c020a0314040b1b0115050a 67
    0x12200241c40d01d00a501034501021080308804c580d110502072441c000d5106814452003a00c1d0710100180703c0c50b0201507050628100001103003076485540c20701180c2d80d040b11046800d0300080c800419400710400485104034401c1d08052010352400045000311540000c02030101820800f04401039211120096080340d4840d244145a404d07070340b402c580080422404010100d41d03210f0000c0360003c0c03100d155018440480c3c1000003c005100207548010152140030410f550301d0816a00c207a02611280c003030008a014200c0031101c04881d11012280109144000500d1803482400300f0b051034020320701310992070308003881d4a98070020007070355900440c8281c0600000100014010b44040c00c00d03076001c0113002c0c04840e045d0400019280141504448450050001c440050038548403401040e40e42400d64021b4400a8902e4170210703a41c0149005035080c200082100003115545103000300020302007070724401d1118507540e0300341d402c4d680e089040c0085d1030a07150080c00a40d40d0180c00b40c04030303043e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 938306996 1250 938305746 938305763
    0x405060712020120040806060f03060403140f0c010e0d030501060215100801020301082b0e010e040912180e0f060d0614040605180a0b191b05070311030313 68
    0x800d00740c124050080711202120550428286090050803100a04150f6032403c0540701c1565413901404078841744c007007200b6031540c42640840c0109004114a102420024881900c0d2807101c03c11131039247e1017211142c1c59603550340b1030810100800d0004000140d640e00c0e090016502d0044c0c02582c03161070840e01c5205000403004201c120019654500c0280207641c0255102e41e529030304140c0300e0204103501018000c0081e15036120b000c0c2100e0031300240c2c9070740d150030100d0f8082c0740044074041010326825411650300c0490101060b100c094001030148244c0d203001c00244001e0b18200924000d5100c0d0240810080c18051030311fa011381026404007055a10000b10b800700c0c24400e02400c0d4096207502c058801000340414408150805d600c17400c840715450341a030f411071a074555181100240a007040b81c090000c954212650051241e950700b140b440031405104103800d20b070714116124110404075000003407000800d504100a40c4480e51349d480614110f1508800700d00700c82101010041c903016 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 938308246 1250 938306996 938307023
    0x303020606010f2a05070303050306010906030605151b06090705010216080a0b06130203070503010f05061c050604091a090d09180519050a090204150b07080f0f0703020102180604050607 81
    0x280c0c2040500c01d131504202184d200c941d40341030150880d841540c005002440a9901140b080e010340211012960040d210f0f88114510104040d500c0c3c00c54458083c46540580b039042d00718108200041c02031183c00060440d0781c0c940340c000b80c80d0a8043da40104591410142004840d00106915070603a42044403101c0541e40c010004040261b6020b26a10480c404002e20040b603034010b010b54107940000080d001029110010030103140601d4640101c144046c1d444080b40c042d00d90485078214001901c045008102c40c2d0700c94409005565551005804090400689120800c1810520360840c1040300101d41000d10700e45071821103280340e00501c4d4483c00400d04a00e0405c0c00c40e41d20340b084083c10015400c204002801901892205030720a41c180441440401c1c0d00800c0300c0c00300c0316440304040c13a100469031044100c1d0454500102149001c1c00b40103000c211241c002c01089109a0005039124141407031503840d01c040c030807514044e00c0103000500564848000316480320340c0000f0b9009006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 938309352 1106 938308246 938308307
    0x41505120924150d080c0312040c0e0f54120702010e060c010c0c05010606030513020103020c0a1410050c0f040b0703020a08130303020606010f 63
    0xf0079500c1c0842c45600c4c1c43c9200c19101445080800c1c05c0030f501c018520f00f1078021075041030300c0101c0c00341017000f08840b00c1c210304d028102c16844501681418421400c6540d030003480644c03550343c101c483d0301c01c91140c00340200c2c119440300c2c1042c0e10b201c0146a030341008002c41075072010700f50711600e80e8451100c011030140e190184a400c01c504003072103500112030407080e4112154203e003003046001e100c5d41e000e0181303046411198071940303581110707441e0482c00c6500c107610507000c041c074100c181f100b1440080c2c1805100c0340c0920700035880c2c175540b403241030509000940003003034240003100d007060380d91020840701c842101c20001044159204141120701e4403030840000800310081000f4030a40c010503014003070440c043d20481e0380602c09035442503400e40c48128040d6015180100c01c0082550400200d6440390702840c1c580c83c81c0101e66400303088081175102c1a040d035014000b454055 = true := by decide +kernel

theorem cover : BRFrame.Cov 938129496 938309352 := by
  have h0 := BRFrame.cov_init 938129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 938129496 ≤ n) (h2 : n < 938309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
