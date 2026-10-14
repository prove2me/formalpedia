-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2957
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:14:54.56977+00:00
-- url     : https://prove2.me/submissions/d181e94e-8a62-4c6d-b9da-81c82681bc94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 531654676 ≤ n < 531834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 531655926 1250 531654676 531654689
    0x180d08070b06190611031201081f050601020c040b0d0605010303030f0606051c05071403011202120c0a030816060f090611130b0706180b100f0b1b1e010c020106 70
    0x114441da40300c10f24690408621400d0708201d010540c400324481e043c070440310080c04640e00c0c0011035131207000c65501d50030410503189400c4000e0100e206081007901496100e10016009010303000502c000f03010140114048480e84000e903900780300c00140c0d840c0706141c007031402540c00254058540e1030b42e00850b100354202005121043c00310600c3d480c850113030380820300002c090100386903c8200c02a130348100342e0080d194205501000102d075040d021081e0520302c500850301d8151a0700c03509101034955004c1084540c11a0035064140082600302c2c0003412810001e08600050a0003a01d0f410220b6130341890340004241c6901204040c452140030781905403000c0c0038050318200c80012603169181c5584030f00c80800d800440c141050040e140d01c50188d1030030300c500c0f2406d481d05a01c0d01c00c05d40c1a0031111030714407107000f90000c20300c12441040c0006480703a06144d113241c00a06071422946106220590300ca40c420300b005a84850507120700754000c110748500102e10f400c04080040d01b5500940c0205 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 531657176 1250 531655926 531655939
    0x3110d0303020c060a14150a03060b0a05060a031e1404110f03030d230f13050c0a1508010e060f04020f1e04030c151e020a02100e0f0d0f0206180d08070b06 68
    0x4407d541d0700d42401208480e4003085c001400c0140340c002c40c2d000720f0164800c0b40c0c40000030428a1500f6090f41240104440420728130104644c0d58160384103c03245c1d00d00c10205004039100140c006460215040164a4001d0031041c100510400003450340d80030045540300d030b80d00e0350348075680240c65030404841c0c042c110642c01d1940c0707030468940100300700040044601c0b00c1441804014003030248807140c448180178140c0ca28083d180c117444c0ba000f00c00d03105400d000401140c000900f5841e102c80c2103000d46402007000b010010303280c0401c00039404c001e004070040300003002804088440140c24001a5580c0341441d51243d20790b0a040030660842e03448800001c44c40170400c0c1102d54880c2810408190211542c00e4820501000f03d10f001e40f5080029004100d1a50501940e03801200e0201c000f04200c4050b8645070108003032110f10780021500411003030b008000c0c90010715106001d0485209128100d00040641d1400909050010030095032505d02c00034100301032060345128903a01000c1540c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 531658426 1250 531657176 531657211
    0x303040807030f1206060e240313021201060806160c020108010509131a0a0e030702100c02030a050303011202010906030c09051002010605092e03110d0303020c060a14 73
    0x304030311482910300040c00c110b0000c52602e10203016043c0c1504041c41c491080102d030340c8610020b004e194402461910a02c14007403103c5858044d02461503808000112490a546070092404419925080200c4c0c1c00010307030010b4401e0203c00d101d0034009110b09801080745042c191780b0070b80c5060403142843e082006010f00719000d43d070013071040c504444096034a24015a1030400c02075041d8407102000300001c00496440c0140c40703040702030a011700c403c00c108008010700040c00341d03901c0c8200c50b4029003004c0b030315010245c0e06000f440d040f1240b40c006011745902440565900d03095030b109802500c0c4c03520100f55a80195603010343c00901410309400c041092442007840940326080341d214146c0710342805010141c6140c400c0d00a0303030050030040d100c1582e03420b013480811490000e04c00081c418402c2041d1055040a408198500300d03034000707190244c1d442058061203c858820b2501b501419003c2120300c1c03822104202413442401941c500060000c5490703070922940c1d0010344140e040d50311103082c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 531659676 1250 531658426 531658433
    0x42301050405100b07080f0c15090601080708060612070806010f1406031311130e07030b0703020a080106050c030403121d03012003060f03030408031206010503040f150f051f08030304 80
    0x112485a41c011050707e450306060b1b102e0801d14400c07140b50312824007504103681001903c00318000c1c0502450815160140c0e22140d174142e03261114800e00c80744c2c0d4002c8001c01d4041c24a40030340740c1d0340e042c00c1d401e5900341501c0d031070290703e0b00740300381d000d8440100b80c000100180800740c503070706e8445403040321054694104203085112924641c600501204200104103490780e58002a80b002100d000105028a04803d1003043d00c0f00d2480c403041e0303808100c1c50001801c4500c64801c80f41d041d01c42c0e40b02c00c0d005900700b040484a40d08900009401803000304000300205015950a443e92020340e0354010800b600040640c1c2d441001440180c000e132b06080f440ba064210801d600810848c1782d1520075141e0380d030f003c0025103550b81c542c0400d0f058040051702149040010005000300d100b84005032401c0e4440000455052008a402808040c80200310034009842d601007142248281100481c1e0752041204c0c5404480d000c2d240c1c0d14911140002103203090031540b611400a005020145003103160a88 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 531660926 1250 531659676 531659699
    0x30201080402010e0d050610090b0405160f1716020f01050c0d0905070b0c060402030d0e0627041104080f06040c12030917010b1e01120b04230105040510 67
    0x1840241800304030b0354500c413151941d028600c1c14907041800c4518034145400540d141014501501c50340504040030041c40e401c19019a41c012155420124003140011a044600020042c07024040041e8038001c0720095014110240c06038600300100c0082100800c4040e01e085116072002e40140d0402c0104032501d4002d006492404480c01808500b54034603140c13680c10700304950010369a0800210f4003110782070002071828400c61080e802c403503403601400d005591111034215100c2e4010010008500c213036030300301000418100d00041e64100c03411248001802c0c2c03011300341d0740f4042003008101009400d0041004110913210000542024107043c4c841112041345801086210940c1842034005c16204814030070091030007074047c0d00c1703482540b80124064180c210101c2c2c895103c901c407000710144048001c540300101615400701e0026140c000d400070300205041c0f9644917076a001191100c0c0e01004200f0000b44040311301e88410760414081008568000d0401d54125075482014080403540c803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 531662176 1250 531660926 531660931
    0x1806090e18100e0c0603010b1b060f0402010507031e080402150c0307391401051c052203080f09030915070c03080d021306031e1a0402040b0a02011503020108 69
    0xc0e40100d0000c0034400d10311302e041d01e40c01006030820380c004000524441d081d000740807004025a18043c0d83c096400210f03a80320419a14072240c05442800300340103601400040170042d01c00d007020001040b001324a103102040c60303015540030900110410003180303440e0900c2c10b9403649100c4441d0800001c1810242d403401454402042900f04280102808110707022101e0514880413000101c280c1c0c0c148a0f03410745e0482c0c410325890f64480072503000d296000c0d00a45000b5200c5203002401c2c00500703044080a4280a0107202c00c0459452190080007441c3e84003074034441c000d803a84159400d02d04966000c03810000e00d00e0400b50403e1006c021541d84400c0e101e40c2a1a42c803803116103518190611710011850707544001c0202c040050761a10024894029200700529150124240707562441b06074190b030440080a10500080f005075202124990b2003080005c0389040f45400240074a030104080364031039000340180301c0021900e4104540c2c2401480414180e102482c01c5291859001811b1440301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 531663426 1250 531662176 531662203
    0x60f1b14130612240602010f050112030302090409021e03101512080d06030f02030f0111030604090f02060d0501050a1d01090b01030f0c03020a09060e100305071806090e18 75
    0x64003540c0440c0c0913030400b02c0325245030041818950039451040d908030a50780320340030141d4248a45c188c250aa030303200d150304880d444041d40707284c00010fa80880003540000302407640556034002040150311100616600041c4c004850300100c2c40314810103107000d000005c80040541004240c002561070f02752190100c50b001c2e02d1400e0304032014604880380380561041109203e207000d400000b404480c1490112060003601501c810310407040c401400d030b03941c0014a03c4800c9003080803452500b8194003000c0058068034040c0f050b4140c0e03600003065a8440c980050455840d0001442545810b000000003060034003c6218511880e031301c40c0740d60400522484480c1537940180780d8441c1d000c1d8100b6280c00ea02d20200304641c401f00d03107024000390003a41440d0002a0191707000310345540945030740d245181c40100702d90888004a80120060040102180208000b0450080c0e4006400c0c0700c85001e040145ca40922a60401840b011110401000318403415905061545690008656000711426 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 531664676 1250 531663426 531663437
    0xf050105070804080d05030f1e04030f09050405190506090103200114030403031b0212070b0c093613170906040e1602070302060412060f1b141306 64
    0x2450601c1a01c90043d68040c61150080010010015a0220040d48600c900520b50091078440303c09440c0c00141014000341c10300f90440c00704000c00c1c020010302041900c24a824203205440c0da0200341036801c103851841e9a15071010442400780d58074003c035640814180c3d12040030790700d186c8032414000d150160200d0040904156200c450348514552100480702c88209644ca06043ca0001c00a0495041441c040c490009142000714404104222903c1e080901c260500c912511482c91101e0b02912510701540104840405130f02c0343d02007184100c032360880902d0710581d855007514103d031781c020541c1400403103c1c0800c0100b19042c1c2c0d459005941180071030120343c0c0c40c4001c05e102d81c8a0704883d95880382002c80d00194181002c1d1240d0321586104112000c41845d6110a0740d848240e80802540404144024045c8145204260203001e0040d43e010420f0b0861880d110101c4104003e2060054500c1d4030100e4487d4100f001440d00450703c8a85501c1c0c1544003004007080021070048a04011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 531665926 1250 531664676 531664687
    0x40f090504150b1f36030201030f020903011112070f05040b090a0302120a1103030307050f0d063308040804050d050307080a0f12110315060c010603050c1503010f050105 74
    0x11140107411007103003015030391528195505000a0a1410b40c40280010051415580610b100765401702d0500c0c21001c5608849035401c60f8010740140c00210100300d02a90700b030007042050350b400d0140c0c004403d0310800013603507607140160581c99080c00505540500c215282039115850380f002c1118219544290700907202ca15050000c2c00803145503001039030050000c00b080b1912a004034140b9440d40c8100440d0421840b4041495101d000442e4404045182840112888055040101740310031074020000340c480d0311025454003001c034185204414806944014030b6442100e02c4240d01e00003242040185803400b03030354040b490710072402500c0c041e80118848004000c8200240d03180c0d01d40c000a0329440320400c2c040205011581035800c400107801030301030404104684a000180b8054880c01d915607915080080009520719070740340d400c007004100e009400142803041d60060b511410181044070061001c00846c1442e001e0b1341c1102c1d0901f000100600c00c40188800c007110404c0c200a6242e0703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 531667176 1250 531665926 531665929
    0xf02010b0d030504090621060e120324030c1516060608011a0612040605220b090c120a0f290108060a0b010c2301020c0102040f090504150b 61
    0x4014042180740c000560706600c00401d90444058400c2d11054401002020342c0c031150b1200001c19044000d041204461107030340403590542003003280600328000c6a070900d01810015400340e2017100d45008070382e140a072411408452040800c0d140d18100e00500c2f000f01c0b040006100040c0c01d00d401c0380007000002c1d0342a004102403880d815100d1b08070008000c03413541c1f490401d0103021a409008440c0700341522010542c5040402c0d034100c041755401a1442d035966035210002052f01801c180e00f40001200003150400007803c02901031485038062050504210300301614120f03400c04000c0c81040c210345a4440700760b0003c6c0141c00107400294500c4109000d045c66040c4281981c418503400c0080300c081100c9030700315503031607040707440c1e031000c40d04035945d202d0306841101c0120985030700045444800c880410b180c040c24070001c00b45200894401581545e03068220f038480d41440c180d59402040030400254260303411001008050702c284131a203800e580b060049030340001e6511826994608001a5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 531668426 1250 531667176 531667181
    0x5040b0907122702100207030f0f03020c0418030f02070605070b1308070305120c03011206051b130602060906090303010605070303060f0e01090e150106050703111506010215070f0f0201 81
    0x1507200040c0070051000b480609180700303540040c3c00380d00a003040400c018006100041d0003084980042600c0c83d424070710340d10448a040008401da046106c0d0200c0544c041c0c2d03139486003190380a503654910001091528000e401d004984804406641007410304025454018044070302c09584803000460300d0351485103c529041100001070300150022801b50101074101d001060023001ca62603100c095500c1c01d4403485d45101c00d0095902d007a0b070307254998000503c070b60481500103003043c10a55114420ba04282115001040300c1000d1078100c100030454240c0500003507411504101c081e09070f40c9080c005076175481c0700c1071007a01c0401100003a6081418482d81c42840030f48085030020030625507400c207e0300006000e0151070501c500d030234030650410000040039517003401c0507003040a05030b2070548203641c50341214100342c1c2071288200d44c041c0084401c3c0002444130b003020034405110f00b00321000a150a261410000c06480c509052080346904030b0800c4421030040d1920782c002407603c03a0304a01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 531669676 1250 531668426 531668441
    0xe010c14131a041e03120c110405040b100e0609160203040f030302011b03090f240e010f0506010c050601030b0612010c0f0e030c06120421080403080105040b090712 72
    0x701250303070766902140c10b903810780204100c0b000d00c01c4940c0c00d0790305120841034440091000800015038a0741058040e401205500403042c0292408641d40304404003140c151142114200c0307240203000100840c488c40e0a107054060300308501064003528155010400601019000c5020f00c03809501c1d05000301d2007001100d020349641e48108030340a50300e2a010380608809145d103000c1520119103002014800c4c4112003146404c240c05140c0700e601034448000c0203114901c02c0b6004818103a14512503007250180c044070510a4000040c0e00d10791710146000c551000d048141002918501e00d008544009a01c5040d40d4201088442540301c8500190300215503040e07024465081104074249507805c20260420a4040d850b4190f03101342510426841301c0707401182c82d9215205102809420100003145540144030b41412030b803201520b4003010b40000e14540d60700c001115841000201548920886d00420056805110b21903200c030000e845103200900c4501000201c07031011401900300e0308442c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 531670926 1250 531669676 531669689
    0x70803010e04080712050702031506030a1205090a030b01080c1903032d0f1e091202031227030105040f08130510090501021e0a0201180f090509010e010c1413 69
    0x1182030203070b0314046e103960421034081c2e10901070101078610310022a03d41620611008015107805843c9076100349150014a14071420080140003215940d2034007103040340034502481c0000325541c9045180c61a24891400d503501454403001c65101a40003451500b0135290302d0306045006c0010030010f03d44500100b03488504181c440600001d00310341040065458040d6540c6055040714165043d0200c419003409920014880d40c0041048801040d40c81090303902c01001d840901e18981c0400c81203812200c0d0030030101041c041030703c0c02d261600103c805007150941c0248014507040c2c071003408030500501c01900401d000165001d40c1c1540181e004064440240224442c030560a001070a11580b0b0080c0b80c0944100e210048200d00800c0c52485846106002040c0001c415801140c52a0380381c3c1d03410660100002e004604107124104460141214100000c0c8a207024007055082d10b285400d030300540d034500f00d40710341d0256000300950450103104018076603500120713005c00e0a501c074690041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 531672176 1250 531670926 531670943
    0x903090d0b0105130e061f080303040b0121020d0320010c02103b07031a07090b120103030503090f060a0b040c18060c030915020705010f0302070803010e040807 70
    0x860800003201c15003816142e0a03035038240310b00c0c0c10054000481e80c000c0c03003500c49030780842e00142422660710070341c0154404201d16480b9013551420003500e903406c256030885185150100510003a44a1072815003010107c01c0c2407092030105801007114080044000713810800945c04801941900410312500d0705035040080003d0380c10004001e4581c82c08502e4021500d0620401c190411500300b002c80c1c81c0030700005082c1d5014500d500004000310352540e08102400f481c2000008900541420512101800e038400290f01c4d000c4c90052407820030ba0072415aaa105000721800c04046840032070640341c0c18107042d9629102c0c16131052a00d29010a400440d00c103220421012400350b805c01181e80405603002d01164040084c00d0301c00008603100310040c18407400041040328491020601a02c1c00783c10292441515401a00103100c01d50344a0300c056844250200000d5900407100144508985000c50904000741d8a14a051206200b8114008000804142840658411514040c2d80407200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 531673426 1250 531672176 531672199
    0x20d030c02131509050601110d17010510021f1506032408030a030c0e2e14370c110105070812071e05130f031208090309 53
    0x14014840d101040303000e581210030ba541c109085001c0d5102d0300d180d1054280d44241885064001080003c2400e81040517221904241180c144098034503088c069817100c4201648240c1c0c5904104103070b00442c010103402d0a9801601d07030115209031065400600a0070b64007442d4102800b4201400042c040b848119500007100758150340180c180d07860107a9000d00d40c400b56400035040700c4480c82004584d8001f049847c840324440d40c03044d29040221305000000c00c6101c004940d200010760107640c1c103c210484d4040840d60f038160131400c08013442c54401c403018003103c1250454050904a6800e20340103641c1e404c0384e000f94804000705103104000320103454034030120040c02c0c010010015940080f00481c3c0140b25481601219206600000d140f4507200904550f4450cd9100500d00010015402d0820015070310340708002000c507152b43d451030b89031084000900e038000310f558040b2807011f003200700c0dc10001d103905440e110300404c40d0800d070b002c1e0f80e502c80d0054218441d4651081d03204c881c4101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 531674676 1250 531673426 531673433
    0x60a09090f050f0d020708010209090f0406090b0703050702060f06100e01090905070201050105011e02071a130938041d0304080d0f08040c0b1308010908041410080a0f09020d 76
    0x107000c210013005600300c030f400c0703070f642d0001a080388108141540c00048000008000d0380e014841160424442e16000800f803c841c0c945002900d4140d0301100001d499200340501a5810406950030810300400440309003072103c0020345440c3c0203050001444284005603205a00a410750001030030803940c28406072500040081c02404240201e5000c903000e0f18142c6003a0980031000301440702d2980007442e10a05051400015040700744690502c0c0e40100701143c941d50303100560100420482e5404034492042036844d030f0300c0c420a114807220420744145a81503000030150003082201c02501c0020b00150300da51030011044a61070700640511000800040c03c200005890000520a079a1200740c4001090201d4049005542c0070f8908030310110180241c1c0b00500040c804445019000804030b0b80c0c840c001825161020300a5542110104040040c13140280e00103d02e010100c981c484011201c00c0082c006d914007520f002c8089070f0303c0e1803940d007041842e404180a1500206078142000c0342e8039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 531675926 1250 531674676 531674683
    0xf02070c0f0b0c0d14070f03020c090c070b040b0a0902120607140c1c031b0825171e040813060302030903040302150f03040c0305070b03060a09090f050f 67
    0x800c880c030501c0e20355000980e050784142550440b0b403441c00a01500651030728100c5101940d00c0c0c4140f2040c408108290020300c0c5c1c1c0014080341c52007174029200100b40700041128401c001848a4501d0b141003145000140b00700300203542c010303803010700700502d6203da00e0a54010184807800175001006084400152070000034501c0c4035401c1c564840c04c1c80f9017041050070f1b40740182c49214403150f01204140e0f0901041e174180e6280b5180754500010101c11f03a51147e00c0c13101507001c811300031502c1c9a040c03129034081442002640f0b80200c00e590481c10041750300070140001001c002c024596400f021a2032080c4528941c0e008501c1d000202d600c0781054149a40030354001a000c07000c6240c00d20000a10030700034001d40c0e20a030460009141400d2558091000d070103442d8010039055030041010b10311400d882d00c083d60080e8001c0e03581030309140c1149013051411200e0f400080e03100740c0c10700c100038456441803000c0b41a18024031001c11040e031107140244203a01c41e01402030281c080c0d203001d0404a030000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 531677176 1250 531675926 531675929
    0x1809010b0c1006030201080f060d06020a0509030106080102161401021c0209010e090402010f050d0b06030117060c0715090212010c0e03010c0816050c1e061506130312030f02070c 78
    0x11041d180d0030510035241804883c80c40c4002808505004001148003985450f030320ba0054025000340c1d000f491030340d203020403a8000440607002c124080b88400150900b4401c801c05000d5520003189094000c00340d01c1d5981c1c8554000412400c191a10144507076029010b0310050341c000400c1c811101c40d00d03144040a0b40109034030500180f5051201040e034540542018041e98042c0c482404600c007144085503690b10406400340006c2d2103500120140d00c0c1e01c001140240740071424144000d0207803c00c1404d001010b4400c4040340d9040c4005000b1402c4d1304220102c5e281c0340480004d000385544086500c40e0b03048101240c15510b804845442c00381c000c940c104090200f240200034120021405135100c030000e079440107114038441088111640184001c2140780400808c0b5403c01ca0300c0c054000000724000074040140e04890b00703201000b141d11500004a9500300c0785075080a1030381c0c1e0030500000b25032001170301c1c800203282100301c218041d620403c2c40005401080d96254050f003004000c242e420f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 531678426 1250 531677176 531677197
    0x18030c0e2203031406030d08040605061c050a0201090e0c0d09021305070c020913080d021e04080708120415030f0b0a03050c0a050312161506090b090108011b051809010b 74
    0x5001908610300403507da0302104003921056020345075600c2c0c2c41c000303110003000250004686c040c40e0f01e540b82162201c41195114a00070000a10b80b0710006000440ca42c0c0a41d0130f5805d51424060191070710015500241d0109a0020710b0303025500015841041c0000f14002d02480c1c101400503041c0d01c03c4e00480d150780290f03a4050349803103000642c2080f030b0201002800114041c07017084200307001e03500103101d2980208440ca20504244001490991195000000661100c5810410f041c02803005801c40900d0302c1e249820203242c42c0041ca900d403c0140c2080805139900540105030401354400c1222200180480b5003154403407501550303c2ca140350307641380304020060740000c8030700c0c0000708520308003282010326090000118030b000050703a1001c42210300010425103894501203e2103240003c001c110310101d0b02003000818002c01c2d00040e003004280341d0410b01540001ca020300c000c0c042c1e00e0028641079030b642a50740d070348015035428420350307d0f44003d03e200009542c00c0e180010b8400c1644 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 531679676 1250 531678426 531678461
    0x90312020d11160b0904090204021611090105150c011401080705040b0901060507080c10140103060506011707050901030f11130902070b0a050c2818030c0e220303 71
    0x7103240b070940c0ea00c030410610141a180041c0503c10201140050700040c400a400469140d42a600007402d9809c20942d1b1781c00c10b4030400a10742440050141c06c2140d02081d1204030030395061402217031910030600d148034151800051070082520f4250b0201e098590305000d1140303203503101c04215480d400c9510416100c0e50901c0303020b40b0079140201ca524121072440d144d4a10303164181c0c3d16440d190700300d81d0816896014101c8000d4040025000d440c4c80700e0803088502000d9811460300e2012102e0142086040203000503699a0440380317418469004001401c0c15501d8040c1c090048001d010010449017566040640b40011114080090003690003900c0321580703400c0c0ca401c4108102c0c081c901015141c4074501010901882c02a40050740001545070000d1800c8218981044407000d0400c0c400d1140c0a400e030820f14040c0d026001d490303e2008500d031040400d15640b2044644000c5004645091220f4008141000c41155103690090b0080800c840486210b0a0141c000e00041c1c2d0710001020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 531680926 1250 531679676 531679697
    0x901051803010603031211030f0105120a0b0f01090c17041b05060c010501170a0c1a121006020607030e03300708151219170706020c010c03050601140a090312020d 71
    0x41c01f40240c07072080003a03080c3d1103210f07841c0c40700304101000644a500c00358002c15044070b0201e40c0d1340c0099072103500c001c1806441d951400400d0800c9a01c80b0046c507041103c0c2000a94020441c01c0290f90850f82042041500640c1000c80781641441a44903d83c803c4000030014101d2506400050485c0c0902307041d0722040c03110b01c50680d107034061440e00808070300801d44240404103800c17040f00c02c1140e005007814240741c030541d080900c2c01c0c41526425001d5a00c00300800c10030740d040212660194440c031f024062690300014840d030720701540e20360300c00030040b241c844c406c500c8280201d000120510f07603148109051075030001c1e1180b101910358002104d01c2c12241011403c040e0824090095044000d110140e80f0b02c02449101d154094220303460129950b6843c1801c40001c045d10405001e840e0040c0e460191240311800c580c25110114149410070f01000020b80e00407602c000c5000d840c0f0101f0707a4442403000c08449010f01508010406190083d01070401036001079114070310300050312282c1c1c2e01c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 531682176 1250 531680926 531680951
    0x9060e0105060307090903020c0a030f0c14181b03070c0b070503190c030f0615031505060f0a02030c010906091e0b0610020a050601090c121109010518030106030312 72
    0x1d80080354000d426500c0b40c9030030000b00255501c0340d5461802441641c03940810040040c00410310366109486900002401c102032041d800c0d82080181481030500c0d42006030b0030007013885e9620b1909200c091809400c002007924036134074901d040e0849141c180c00d03a01c0c039002c80b02070700c02004100c05807140c0010b032000522650080b4102d03401019038601c40c032580070a001916020300a076030b00300d0040680342c0000440e44802800f8490240070101d036400110300704c0380001400c4540c01c2c101c540c02001001c0e001c004a0b11440308945049080a85e00c940d40c0c01900301c1a481c520401d405001207629116142090125660002c0070a5129201c020042006000010044080410301038040c030f6451011407400d103005400a44411401e005480d500245500d600d03080000992103112000d4880c003803515455444a8004081e0558503020410107241c103182c00460f008074080b1606214000500d50f94a4100061040c0c21600040007804040d44034070300102050415103110f410342c3c0c104000814171 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 531683426 1250 531682176 531682181
    0x3060f0e130b04051507020d0e030c0a03020409230705040c08060307152c030c030f03070809060702030f011d0304120f03090f0f151b03110316050109060e01 69
    0x10340c0d01200d1048079080380e4451140c6810003500444041c443d00e0f41e00600c0241d071940c098443c0302e07183c001d0200c000d009040030709140c0c10b0484640c460b40012880741d090380e40301440d9030140d03a019a00002c0b049013074544001e403842d51481c80d18120704a40b44400580c600040d040041d24401c1d602800119138900c801c0d11400400d44015515030005a010302080000c18800001940c00e0b1800c400001000b0081d072004609011144114041042c0c4000c1d4500303080002288840c02500101024030701c0b40034180d220300400800400c400c4c40040d40100654503036041d00c0d81150002c00f910041d0035426903890003002c102c0310318010044941c880c41c0c008070002c4107441c11600c0c440f0300704040e05142e980300d10140c01c040724101c00b40315010001180c0d0035010b1002d500a0028050380105042c100030900c00326004210720a0208401c82c00d00c222414036681d03211180940c181041568240d0b41c1030541e08500490340c1040c4c1c0e406000348428103011054103c600814002c1e2010001c48510461050a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 531684676 1250 531683426 531683431
    0x31b0312050c09180603060708040c0608190608032a0309040504021c0c0e090703080406210e01021c0b03030702131503030e0916090902090a051003060f0e 68
    0x1152500040314189000358100907030005075940107520b01040c0744002400402c5484486885034640820031510742410485036402030071030f041c0040607151596a8540d610100d01a580400c00044c01003050041c0807001000c2070482a1000d02c0000e07240c600c825526008025918280c02c41003c40c100d5807150000c0d05c0c501a404d035009145040411001d000107040c02400881e00510b1185c03216015491a07820b01e14004c1c454510a0000d07860040122419500a00402c1c50b030f4116031010000115903004031011141c0c5410070342400d52101c81c41c45260090600340c2c80c81e803420f054646000c404194020440200d074109038103402550410708000300d80955800e00d415602c2003156001625103200309400d403214614011131007139003c507942c9060945950017200428070ba01d12510705d5141036503d5545c0044120f072034905404400100409440c3d0030301c03c0c042481d60010300c00b400c0e07482e015401000390001800c900d114404000b401802840c1d00d01c52140303150307004030300480c42c042a81a0b190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 531685926 1250 531684676 531684683
    0xb0604270b030d1805130203040317100614073002210906130e06040b0405240d0b0c04030c0512030906030604020c100c0f02070509040f0314031003031b 67
    0x1030a4041d500342c0e603a552404645002204d130400001d495941ca08111460b04241c90000da02da007450300e0041c190f0042c0200b1020384c185140100400c0c989204002c20480b001d40c0b030400b02008191240807014070a0740c0e006440202c1c43d450314103a02c604004038030100300c214451840c584281d034900303d88543d180c580c200b48500c030b801c400c0c4c042c00e4540e1000d41907000f07004040c90718000202c1421590f03000e250348080804420281004401d18003442200d030025400e580510962421030042854241483d141140782950242d201c21103403540081101c0703540d44000c11075524104a2011005030b0854401103903196058080420789003815038800100781d1a1400440c00c1c100c03007104001c50760300014a82c039045503090008549240c810414000368040075540011906c6101c00010580c10080407100199031100004000c513440b285e49071903000d60814940005144a442c04582000c40c0034961000e1980201c1405410141400146d0807240300e519058086100760200000400c26614050f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 531687176 1250 531685926 531685933
    0x70501090803030a0c090b07060501051003020f070b1b0406020604050f070602030f070204110d05070314010623040905040318060801050d1115040b07060e01020306100507060b0604270b03 82
    0x103003070b13903202e0700905032090480c100400802e88514016019070804a001c2e6881500c400041001e81880602c031615280103183c25071070b003001e10441c0d826901c0340d01801072854008400040001c094414902628403000e1052995540c0e1003500a650315819201a6028041d0fa50003100c0100d00040e8030303084034944d401440c1010b00c036018010355600020000c1c3d81007a05c0d00c030700300c204e100c40308000c0c42c0c904050b42c00000c85040c41c04005040b9a80c01d644082800c2c00b100040c4611500300b0740e01c400354809801c03609400181e40c0900003940c0280d5020080701401c100c1030004050300540f610105403040c1100706e00d0140d07200340446101c0020b2188541016980c3e8104000c0798021800307003420304002c1c1c02da0440d00ca80c1072320720310f0b990300070782c040745406002203002020003085000c0c80d01004900c600079811410a1800542109800c81d0501d0500c180010b0034820414241c0160008541c0113042d5600d40d0303680c030300d84c0035001c2000d003140601c43c440c0003c45508032100e204d062000900940103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 531688426 1250 531687176 531687181
    0xd02090103020907120c050c101a04020906090d1202160f0311010c0c0906080c01020f070e2502010c08131113060b0d0e06090a0f08090109030501020c010e07050109080303 75
    0x28042a684007a002c0710800025039140c01e0174410324052070038656107a9880e16650b07142c40400c50b0506014403517880200341070812650850600140d1001e2000303007240c1c0140d07100740400000e06284500d519144d049100f000d6a10203112001d481071000102071303020744034840d03c0801d00c40c944440030301842e9040000d40e8014004140340c000c4041600305c0c1070514501c3d811030f60f150040645400d901081609850340c00502c1101010720180458800c28001084050401420151140d00d01c0c001d180040f000c0c10001103028003440c0d070340c80303128106529105d41c0c0c040840000303000e002c0440922011456400201d011803601014050b81c003904aa0035251040240b000c20003900428601d02900300d496283c0402d40b40404030042080d50301c1c0f01c4000130b01c081101320b524248040240380590541200d040500880d0180000e031500b140e01044042d03840c4480c5005071110351054201030f017158030200c0c0fa2000c1c5401503004090b0034034001c04a4401c1d42c0d8420044036806e40314041c0310003a400a101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 531689676 1250 531688426 531688429
    0x5031b01170921071a190c0203040e070207150215060d0f140c1002070e0703050705071b0e04060b03010501050f011704022b03090b091011010b1e010206060d0209010302 74
    0x450f9140d55034021646140c45200d07100c000680101c4040c51082010320381c10710903442410307002c4c91082203840209011440b416800a5140e00030345c420034480408000002e40200d03c01d100c1100640011200c8100034088c500000b0340c4c03455440d055040040038040030071024988074421840056001500c1c0c1514000d994071a00c69890810040300640b10340e9682c174510f551030300c0e4544401e50b1654001c10070a480c01c03518244480000e081c0005052078a0b0038400c00c0c683c0300d4101c8410719000b50107241c0d5101a850502d4812000c2d902c080000d05007030050100300a034540004421140403002032205907211803c01246030101c0c8c0d0241d0200394820700e03010038001c5074580c095015000a0003c2505d40c4951a068950741a0106038621040300c0b80800c8200354119031001d02603c03110500e00e0401c540440842c80005000b0a201c00380050545400d031841c1707003500302507104c2001411900a8161401e1980f8580403204440390150048000180c5141042c900c015041c0742c008010114603440c540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 531690926 1250 531689676 531689713
    0x15080c1f0c0201170106120f0b0109050913055b090c09020306130932010f06080f120919091104030605091504060b010905031b011709 59
    0x2904a0620024142c4140c15551204c2c08900a24481c2c40e125604154a43c050084880a04a486429192a07603140c01079034818288004c0d031b0000d031030300000c6840740e11440041c41802d1800a00a2294652020711086202d60340a1900c881c031003103907203140f4041b003e403030a80e0007400e660383c0179040500400c0d4860100d00c5d1302c001c41c10000500240840b00b40d00c4a0036003c0d82c5400c030503511600001406024200824220024150f01608202c43c1e161035503501e407102004428a40202c0c1e50654100d40c4601881410301c60449000081003154001c81140010740018400c210315806140c014110000300403480340303900c032140c00640b49407480c035500f0007031090030340542000307140785814001c42d540d0001d1281c4091a4403010310306031164070790725246e07060b240c008001c0c1c862034201e41d42111100e6152020280c01903800100031400e90303004401221545481c8d800b1560505c2025803000c421000515008448032003a41c48060aa546c045c024161490907201081c0320ba00c444000d02200f01c245 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 531692176 1250 531690926 531690947
    0xa0c0c08011e02180d060b0108100609060e06160506010f08032b02070804030f1b031a07180b0717090607030503040f02090a020a020c10020c0f1315080c1f 68
    0x5070041136100000c40049050318086031402c4482603554080d03501290b800010b1039a02ca09a21504810740e420214024170b40c40c4203201c3d0780180100a80d040c8100d039141425038824500480c03426201a10070309013281e58450a02c00e0711076403110404007140c4200080200c0e11546140c80402c3c0700030441e04890340b0482d4224003940001030b0f082c0148400240140000c0c80118000c1000225a50050030240711030b5007020140e07140c02060440410010744010184940e4014020701c51000c0d94451006403000e0203a4812000320540c03000000c641802220090400e10b405444454410701141000004038407821541c154407000c10b01c20100042c0c490030056900c64800c9504280b60801e950101c1c001d5081070707a00e10042500800c0601a80d5410803103030b070003440200d030103084402030b0322000394507405103101c1d45000f01000d240035a0b103911000221440a48c58010420078041e0708900208011024000c1c500d2601540380c40d0b910350b01d01041030302c060342c0c0381d00c0340e009a44400403400c0e115091030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 531693426 1250 531692176 531692197
    0x70e042a050a1407150e1b011713022b0516030206030424050c0406030b09060906120f06100317030c0f03070c020d0b061c080a050714030a0c0c08011e02 67
    0x800014190105c440d000d880191038844000308070351400d030454510038803030120501c0e04004003541d09900300740703490040ca0382144000c516203088040c1d900100303034103103144400c100b1303248201705100341c016081403ca14111030003001030f40c00f811480d0303088801128242c4406503000304207002003008501075542081d0006c08524500c0001c2110600d5101981c40c12610002c561101080401250b9058010a0540c040c216185001f6240c200c000408001d4090000703801910b60240080108c04c04000707982d01c0015210840b03415242103104c26401c0039550000312900401e054045444c0d420b1b01041d41d004982c410555402c3c6920080201d24540000b007040c0200858000050050389844882548283c0106080b140d0352802d0401d1001c0e5010600416214006404d0703030703802040901c800c0c0c440504c0c103407500710b0b941e940c00d08010301941c03840c0c503250b101070000040410360103410400c00700e0428411100c94007072130340c0c0c0c051007422606102c1006040b03154443c600f0110008550040170824603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 531694676 1250 531693426 531693443
    0xa02030c0409090317010608090a060c030b031b100f02100203060f090a05100f1a0c01060f080604050d0c020603040b07050c07060203090a0b0703021005070e042a050a1407 75
    0x60b14249031003500c1002c0000e80103d007403d54464411040031010901600f0203040214450804074a06590b071241c1c0c0740050940c40c4e0301c0e0881c040c1d2a02c2a0401050190300504607906110314880b18000d105a0300c040520640342141e800d0001800341d645041e1040440c0c0107031109910171070701007019601c028490f0341d00a8285105408994940c46030034050141000c00041a141503a0301c2201c3c211a5085803909002d046400c100300103110b07004120100c0319a0704e00b500d40c84070240642c05851140c1044030070040d0b802d000710b291203000507464829070140045944155903c1c00c10f6508815002001e9000701d81000001c0c04102001c0c15250025840d103081d900e04044403078841d0404c0c601d46c07c0500180c20006540f43c4528206c8444000340282c00d0b4090314041c4142d030069070701c601074000d40c8281c2d0b403100d0003d00180c0c01003000c51080314000d0004e10407009032088108a00354010155136034040480140903215103e10140c2d0554421a00c440a06030300107040c1010580041e0b204403074040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 531695926 1250 531694676 531694679
    0x12182b1407030218060f0118090f020c030406120c0507031b1a130c14060714010902030a0c030201030c090f0605090f03010f051b0a02061b070b01030c0501090b120a02030c04 76
    0x8495a0608080500380c413542400303801c20408026080040c0e10302141000b004022101c09060180d107824200c030a01030f4006801c5e840e042d40c507006801003036500b1416000c00301c0c0006009400a4500118411800041019080307003203003039a02c0c3c020070b00e018000651440c00c8075000040c5060700c04145000f901420180400441946800c44007115010031a130030380540801041102c2501d140940f603503c0b03094100c1800b62010508c907024503500506543c16840340c05c0d4011000f9441100303140c2d000381c290780139098141040a1203c044e441700301d000916060304000380718810342d28181581c0c0303090880ca048518001007200e2a800021041d03511403114180c0a01d1070b5002d110341a030307120761104080b0b020701d442d104c8c1c5544c124840702411070000040084460540c2c7c04280e045d8003007403081ca01c6500d035480c0315003804540217030440241182d045c40000700901005008480450f0001d1f07a8540710517480c1c2c2e80c002240c2c0240241582c0192a000104503540c41030380181d80e1000e41010720342c4c00c16 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 531697176 1250 531695926 531695929
    0x50a050c010c09180e0d1b05060a020a110d090312020312130b1608010501080c0c060a051909050318060c100903030f14041412182b14070302 62
    0x11205600c0840109141d41420054600074103031050303075413280c18070400001c4150014503032150024a00c0d1010803010310600e00091040100c1860016040740458445180c1444007070002c3d400b402c04c56010540004031210000000503041484210301c0d6980201e541c0b8540d50003d191a52440e20700560205012130310910002c4045184100320509400000518074144888551720250600740d03516142c514441d8100d17003060884d0304644081c41e1148180e60f4180c816015401001c568111900405040c00012061500601d004002c440c104120841c68015181c007202c5040000a201d904280b08403404021400f0405550310740191546180c240070400e40d0781064086545c0045040d604d05004c42419810310407020310102c018030401800c800740000880c81400100b000300785948920503a402820140f01a11a40042c5810f2648900307142840c0f8081403101c44106020380c00b08038400400b00c07440074108a00f100b10381001c81107000c0503101c00d0b18500642d90311210a1040a0000006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 531698426 1250 531697176 531697181
    0xd15020910050702041808040b0915030f04200102071a0408070f0f05090c03150111010e0d020f01051006120605030304030b0a0b15040b1606050403081b1207050a050c01 74
    0x748845580c4281d50348840344100000c0321404202944038224207410900050000811601650f10075801e00c0e44846400000421192064896000406010090280c88480034030500d000314030418000d0100c41c210168000078031005100c003401a4040703901044180000005c1c40440101640014500b9481300e50041c0b4225031540000b00c640c40142d000c102c42e1000c0f182c0310740941012182002d2504003400026841e00019000780002d8041c541d071074045070b0003104206446007603080240600400b00030703026201c1c45003011820142c064071145411909040c400c8620941c440b00b5034514290500100300c515400100701608103554500002c034071a6010005070004500c81c1d24000f05520301a0510f000343c071015201a07016040c03030390140030005062803e0b54161001100c0c0f003512212400e03100c09000112000250030300d890a03040c00141940084d00754403030304000725200c04100700f454464030540308461400e40034200c440301007129240309000803e5941503614000c1d00303001401c40005c0c02c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 531699676 1250 531698426 531698449
    0x1c020708030403030f120b010e010e03030702041b020706022409030d0609020a031109010c1212020d1a061206130914060910020c0a080c0f1b1c020d150209 68
    0x2241c8440071106105501c45179140e90016468401c0c0030b11045100062716024000c900340e4184548400c200300d050320104140c0f00c0c0310781c0003082884403008121811580b110030a45000050152200200d0941d00000301071200054410b449145840450205140d0000180c00118203000c101710040fa101c0e81801150702801c8040070050b60703019602d0001e02124420003407003404500510080700d1341e07a0481d000e480059084400740c091140340c6181250441103c1d024080d0681c40403900c011010075a5005804080c05071104c0110001d040e01003100600400200317144049032200012140d09007450604541c074134008020030b08000a544e0654441c82c8a85920100d900407402c01400150400a554a001104004500c0c0550000642d601e1300b0400c90003400c04200041e205680d18020040700110744451019102842c7c1851035000c007460802d5001481848510b007080442100c90420401c40c80d40100003004107400380e9504802001003409125050394244a000c8036611000303584203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 531700926 1250 531699676 531699683
    0x906040e060403031a0a050105030711010b1207150503160f05120906061003020f0f070c0e010e0403170c030f070e100c030215011203050c0a0602040323010e1c020708030403 76
    0x1804000c80c03018400d0342d041c04170126100300c070905010072043c2d03000402c60b0b4029541d403402c8400c3d0207031704a08902600000c40d0780c6400500d034040d800340240b070200303101e01540c00782e41c1e00342c200d029039210407569404203417640c1910340c50112044030010f000c0c200b03440351000241804c900b0407942c405040086481210f20207060f8020504224551500300e5009040e0301d581d040440c2424030009011000703000e0146030704c880210000f00c68080c00341208a0a0007010810705200c1d01d9a1070f0400d1f14800c0b07100b9a001c802003141c1c039010304200310007848140d2040e00c40902c41b5046039034403070100c004030380050000c80511945014020403529041c103500084109625202d1025501c1d26000b441c02042c50b20040284a0000040c4542100d1802544030390b40c05107002515100304100d464107141044000801552002600000b00040a001c0c0120301d084811080700000e20480c1003420794184042da0941600214084900c103d40300858400c3e00489204a0745ca07252175203c1c652860b449a042074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 531702176 1250 531700926 531700931
    0xc0606060a1b0c051f11060c03062215050306250e18040605220c0608040c08010e0109061803120f09050601170609070e06101b030f080c13050906040e06040303 70
    0x1176849680082c1c00b2074844007907800400c070790300e415100b8035200e001c05030075144a803400406640218042d1a07040d0940480b070203082041d03002c1c142c21a9425101032207054024010000098080c035004000710f1011902c00380214504143c010040b1346155502070400e40c02080c0b410440c0b10403ca0a0171203110b14400e900c000b616080489000003801c1e08240000d000501003003013280080c4440c2080d0007151581e040c482d502c1d40b59481e1074220640b090b04490200c0d8600542c144110720150064a4400c0c003076401001940140b0380f205001000e00e80004d00441c00c0e41103210325112095101d03243c14602c0440c0001d010100350744041c1080800ea200c5940310604010801e041e001c107202d00c03030b00700550030020055140f404040e0180d50354020840ca20920f28031014491260069490030210b8070030381c0d030a038a65880307072401400c4030140e85002c0000030210300c002014000e550088072030807072f00781c402510a80e241c80704110b080741c3c005203005d0300140c40340268400c3c00d208000c0540181e200e40c402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 531703426 1250 531702176 531702229
    0x5060607061b0e1207030b090102092e080c1206010e100302030406111309090201120c020d14090d060b0301090623150d0212011e020c0606060a1b0c05 66
    0x404105503a07075003c4c4070b00446030018025101c001288011250300c008075004542c0e6030004e59009008021000e0b8014a0040110701016100c1c608114152442c0744161144410b4503000c44080c00200c8080c02c03807a104201005280d1220300100398020014982001580440b20200d440741c0034424103040403035004800d120030402d0600480d18110380812040341818080a216802408140308101030b8550ba809028196481905080b0034030088402c00d02c6015001c8030004d50750b18006007103400081444281d4031801c070a800444851050060100c855400740d03888002c02056020340c00d035851b650721100040007403141d005007003048049622100c00d2180d40c1080010458004001021204011101c0301c45540c82e014102c01194043e16801280e50142103203030b00424142150120800c404090213000700c9850300240341076100081918801d480351014400c090140c0300780c41e00800d4041503150f1a036901c04d89200c0d01d00d4069002840d115940e800400c6400021041000c54540080b12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 531704676 1250 531703426 531703481
    0xc010213090902030303040b04030903020607152406050c03040f1e060e0603130204091730041407181b02030901300e0c01030c05130303030506060706 66
    0xd518010200e5840500c07502916070300003034491000a00041a030306c4004003250a2612981e0b9110196902409a40d03607038080d41050f0408440d8000c020600382d0034400c0890072440000303c40d44040800000b80085982447c1007610b50780c00c010080704440c4400d102c0004c0d2466071010300e81c0140300034000c40c810081c007544002d4508100e0340044043c803001c1281e100054031980b0481ea0b02410100d010f4503601142c1c070002d00a001c840d00040e00c01760344100480200301081d4018558140420710b6150001c801d034452052901d01c002c090350b4841019800600440c140c5030317807038408111640950b00c0040e121090782001603021100c14881599440354515111441d00c1000e07044550b50000f18100800c00700028454844400c00001c0414483c1c20641e01028582004121313000940080c0141186a00301c240d4446002a070503000030300380881c040300d160044007207a05040d200d208607012070f42140c401750003821b005000c003034206908000213008201d041c850700c4a2207110100080880a0346030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 531705926 1250 531704676 531704707
    0xf060d151d0603030c07050d030c0f060518011503020402070501140114100905102a03053c0702010c0b130c090203090a0f15060f090e030f040303081305030c0102 71
    0x3440b1602070340c03082000307402c00680055410201d4000300c0300c49100354018a0101c0d061a00c01e44014286507408103260200450354014511803100002c6c0c403d104075003000e80509a954048a03071280c64032030b5a050015041c20b400414045000d5400400c1511101e07100d0340000740240e100680724517010301c2b900c086203040520305000070070300c2c0740c4980d50505120000b01c081d40f02e51603a6040c803070004080c245460411505001d50300503000007a220030134031305000d08140e10009249a003c5001c5543c0e95a0070040300c00169103480626099000040142400d0303040d500640040c1c0c18480402244000070f01141101c601c9180b01d400c00c4090781919280c4060b1900031030f0081e484241c0140708014074003000050148042c1e03045441d402d0200c455062880071980c1d1404141c14440c2040c0010410180080c1c0a00807248040030403c241001e00ea400c507164040d141c400d00500b1010801000031034812608660002d131540c080c05582c4100759a41c0345507500010355094103035004150900d2500341d06 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 531707176 1250 531705926 531705931
    0x602010b01021c080a060317071109090a03050309010905071403010e06040b0a09030302090312040518060a0308180301051006110f2e0603080d06050f0f060d151d 71
    0xb0300050250303084070341a0484441c2c1d05911070041100d5803001401043d4160005401550000c03403400c0718500c0340d42890b88981c03140100f6070b00c00020f0201204642000d0249501c078500313900103045042840c0c1d6044a50740d00c041c2c00b41582d992a0b0a2000200d0020b001c194018220705209080c52801003080c142990f0b01d08401c09a40d030000410030020448040b404c0e544004400c3c0c1c000346501080c54140e000b401036400d5a500361168030001e0124400c0e450003031080c0c4004580c0c01080b11070505c00040480c8044034110b42040301102c00304002519040501501d210002040f9401000100032a0031079030219070f80710101a40300400c2220540216201c0740b686c1e41200608440240b02406a0341c9819950640644c18a4000c1100a0740286101904810f050340c0003070064a0792400c2c00c5040345c2000e9505240c45140000c009914680401220445c2c04043c00104403540b24a0030003c40750840503e038803c2c2d684904120402000700d18046028258081a522036109078101d90002540c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 531708426 1250 531707176 531707179
    0xc0c031c0c140c0a02060a09031703060a0e07020a24092607210e03030307120b010305041128090f05090a2006070b0703020a02010506031603030c020d0209070503010602010b 76
    0x4202000c180f403804142580000c0d01517440c140e890716a50000c03148407182d940081d020114192003c000c80003184000c600844045032119040e039111040580640000d484290150307122142846c0054285a503840540b05482c08485c0c0c0a80b50a81e2a810740d108041e04866803010f04c21580c0e0b6651042150150f5004421031560900045960f0200101c8401e0a00005080341c10b20482d0300074811000b8500000001e0140c079120f0510820203441c0f40c1e0745032a84090b0a00f031200340d84035544644549449250482c8134201c04c0e1a18000b80303c40b400071900344060880c00101c40000c0e024400300100300030401502c00286840358a4110800c03a50042c0065910380c010354003400110700c2c2d08170500b400d214000540b407480815200001e01c03504c03d03080d0080c52051420201329134640c0641c068400914690003e114580c0c6500400d902d91401c003121505424011509101080c412030490ba42c040c400783c5550803081360382d000a041c26000311800d0001841c00030041c003a4541c20300503050007100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 531709676 1250 531708426 531708467
    0x1206141e01050414061612020f160b0c0721020108100b07150207021008040b070f08010614040b07050d022401050f190806010510090e0c0c031c0c 64
    0x10800001c1083c8103500c90310700400c2552014110355a0744108640410f040180c10a0029006184c1814200802032440300540030321400d05425010104a8200355251111982445800c01c5001003150b000300c000700300e10b4071501c840450089804504241c041d69044220700005005100040a046008100490205524000b040b811503040c0641c1c64050b17000241c00c0d24041c04606400c001d0090760400b0390b0011402c0e081c03c95407030f00408a6401140290314080c2039503a074134400d0b20001014540400083c06003401000f041d80b0401c00c1200d414a0f040456243c9031b903615180800390030035407003950f10f85c001c9501021001c2d0100209040421110701c030300516070b0304100646803c8414842c2030300600c1600701d20b50b15940e8101048104281e0003100581d880e07103d007902a65100c0034050240100c1c00a045800002e00610002080301c020300000c04059541c9410701505400107464001d007031005000020329043e104a820b07010541d43c041c00610381c2090b0307400501a0031442030400d110340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 531710926 1250 531709676 531709729
    0x1c02250b092103070f06050106021b060901030902031c0929090a0b27060708030a0903050405180907090b0d060915060e090c060a1707120614 62
    0x481030161110300d00c0880b1420050301d41001c0c000402038040e4000c005038040051008208280a0002d9100354050901080391740e80b070300d400b41e940d8801c24800360000c422506403000fa601c0c2401c02088800410714000c0741c8000c20381d001ca40b40110901c0f0341c82484da4105c0c14032038482d80c03142000c0010300f458400115800d01d010001d01c90102c2c20304032003c040c000066440c155444801a0030000c10740a003410359a075844d00320705078802100b0000c1d2901c81000d800b515a841c58820103590880b60005c9016107140c981212400040031000021014000b06020000721590f40e0760340a000d41010070129103c905c1c000c0016030511901d6000b0a40b0580740c03441580007620303050715030080780342d100c20000342c01c01450402e49110b800300c40c0b050045600f05100803034200d0000310440c2c01200002c00300d800c028400380030803050b8001c1c461200c00041100a181c01404040400e0542214050920001031440c08204070207591964002406646505508404034100070340c038180810100780d00b0703c45c01e2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 531712176 1250 531710926 531710939
    0x306040b180a02070305040b0c0c010206010603050c040b03040611030f0405060106050f180d1b060e120303131406270a030203030c070812150a090203010510111c0225 73
    0x42406061010700c2d42e400f041c6181094020f204807000391203c0b07001c2a481d09182c00c0302036941c9464441150041c000e013000001c220307000c0c4c002d540c080d41040c4d15260805051100410080c0c00082045c0c60305500c3e140c800080c08001ca004500903035034204014880d2805080152800340113074000d4007000030401003d81da001c034250648a0a007440c10004000101180004032082007205001e0100b64007800004400240c10a40104840c03003911442c10450400d0304000714102c2c2c0f107030304100c40d400c10000030311218a0144508840d500c00c00c04005020b141000c42407030120200c43c010b200d41c0030444000c031142000f49800c919424a80014143e1410310741e030007900c1e400003901c400a120b00c0818803500b001481b205560420300d40a4111485103859108016510b83c46040d181c01440a60740200b0703032000c0e90085034141da01c00740a40482c40100700c0110b070104204a00102c1900851685c011095108100c241c44196994010400040c40321050306e00544018034002031110040c10070080c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 531713426 1250 531712176 531712219
    0x405240412021e0f0108070e03060f0a180c0e060105041706070809061303110c03100605120f030a0c0f060e1e1506090709030c0611070509010e04020d0204020d060b0306040b 76
    0x7284c080c40c0c40071081d00d500d003055503a081d0482d08a81d160040c1000c03c00031292194140d03204103114031003803181990a451154181d4001400035000e28100c00050146100304c8868030b40007241072404900d0329070b5504458406103840e40e11140c02e50000401d1004050303100c034115800111100103400c0e00e0800750b1250141d00711441c0000e05002e00302d144449aa00144005a40400040c0036100c0d80380d45c03c20550020041409010b00c02d005024149a403080006070040c401c6a82e00021440e00d515480141e682540e901411910711000c0c0c0c0390705000030f0160003180103411030b01006043c002000502e00b0500e1070074030754100303056200032080b0a41e0030003004000e0700800241d400368015214160300315250040703900f004c2c00043c0109000550340c2d07401400b542c03100c00381c08140e440d0b80f505c5004020b106da2080c0310b2200b1700001d501c0860050b24052041080d181d1000744010715001400302d650041d00c00d180d0052040d0000882081100d0031f05000302c1030840302c121f65501c03290f40e070650070b00301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 531714676 1250 531713426 531713449
    0xf0f060708043c230102010f0f020d06120506070806060405041b02010f0509100504050f030309150609010b0a0f0314071805060c0a08070305120c04180c050405240412021e 75
    0x4644c83c0205103031280c0d000b90b01c0919000b030b1000d0103015100040c00100041c2d400700b20348428842c50000c0000701388d03100d41c010f007040030340c000d01415403500d80c0181114808006000203510820800001401c2d9030b5502c0f4100b030001c01c4100b00d5248203001c05010b800c5800c2401c1c82c542080c1044200300d40d03448089001410002d400100003201d0f180c5003049440d2100602c0c454895100010074400c0a03c0005141e10361601d00c10b98403c100d07070f1180c003409100c010038801c101202c1e1081c840314039401d014552074480c4949031f10b07002840000c42840c600f03004806071840d401007030008141881c105c1e1200094406044203072017281c50014100c0443d0390314444c050015109410100703400042610580455200340c00d210b480c604141002001405154083e20452010140120642101d140035004802c6c000d4401d4542d54206482d180a111241c2c0c05401e01803d09450048070300009400d007006440a88480110790410b45a1071041c0081c5082c0d100b101e50b12a100000c568009554450710b129 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 531715926 1250 531714676 531714719
    0x150e010312230705070306060b03040b010b090d11010203090405101502010e06010510090b04030302100507020a0b0432011506141c180515060f0f060708043c 69
    0xa0342c03580f003401c0c03e0303080042507040101458186800001c4189247c00994010b40c00780080858990342c601c1064020f114162803580c0006801c0c8140d404584048203010015074103005a900d0a5500000602241c904850031141580789080074000301400e1042080b408526000030820003410340f406e16604d001c14425a840303865103a04001481d8811100c8200404142d5079841d165a2a464041c1d10b5001006038001003a15000000e40c5103840011020300e09034000c244241151500d885109501800c81517803c2c0401031174103003121144101c5400c60300c0207100000003d641c1e1a03000282c443c01c245074415010000308100310500555003400b140e0740c0d44650320886178072250090081c005411320500800044462141c2c14080c810301041c0c0442d080c0c1420301c0c28000760780d50b90800511412174002180c0000e01244a040b1031b0a00e900140707000c84c00740894609043d51140c0a220444c2074203c3c0c0044640111218a1240700c0c00f089000c45d250310740ca00340307021800c1100c1c05407100700508089 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 531717176 1250 531715926 531715997
    0xb0f0d080a0912030305070216140909190f050f06071d010e0a03050a0614270717030409050703110a0e13051302120f0a080a03150e010312 61
    0xc00000c2c00b8858000050032544000e8607402c4042c20701a0007400b084407000054010b05d41e00b03140340300a50300d105090b1270142401e0022080045c041c0130f0385075070040100c44140f02d40604440340e250f49200400c00d1511032489465200c600e841c007181041e501000e82142640070009001e401d6401c006070b101e0400d01400c82d400111240c10048a13010f0b4064002c07900900b008070302105010010900e0014203004034001d01040300040350742202c00304111140e1a08106070703564104100514401c0c0501191140c085508030f0341c80e01c2604d480010721030001080c640c00080c0810180035075004032030b8002c1c06401d0400042d8054103084000e80b040755107043c1004018407000405640300301c01c195030690104420401490240303404600808a090140d02c2103103600e0008030b41c180006016546100e40c0000f51401180030354444840b604400c403040c1c203051300c41c0b001e042d05405409240000f0140d81240d480d00d5450b40c1080103818420395015801c200440000c1c2449001000503e1083c4060a020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 531718426 1250 531717176 531717187
    0x5031e0d1d0d1505100506041e05030f0618060412122a1b17030402150a020d0929130506160311030a1b020d0b0a0c02010b0f0d08 57
    0x14a501c400c45400707a03076002c50000341100c00c1c0402643c150968508088041050b503e40780b051520a18075481102d85c4641e04002c280301ca1913405482444000d030030424034a03100d07121030000e4203040001a440030030b0340c000800c02000d0700300100300e101d0000d442170250855040c00c1d200c510b40049003020700c2c000c0c00204031001800886592184041c0d403000d06405184030007200b0400c1002c0201d00c0170000207005240c020410324426056800e8075036100c88020018941003d00251a400007402030340e22200c90304800900d0301c2040010410191103134080c110891450f28050813001c01e036040180c4d00c80a00b8140c8004c2c4014042d46400b184403400c1850301c038520794403142c1c0100c010f50000394004001054110400b0f40d00f45203014414402e40b03030400041c059861b4150340b0700505001000003810201c1a80300c20311304031140806203001030b080702c144a0641e03c0d164158a401d484900c0c910355102c0d40440e03000d90a114019140ca0200c17109580000b5560015a01d504003a0340130b407a10100240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 531719676 1250 531718426 531718457
    0xe0a060b0d12050f0f0a0906080a110d0c0c0b040602031024140c010c0e03120a050307180509040308150f0315220c0807080303040201050f180a080705031e0d 69
    0x20358070b440d1724401a6a644d071001c25402411108584690b00100b05100b000c02c40030115405102441d00a0580d640d0a1402d01d4962401400c0701004080a0148002c12400400c01c00c42c5030b107100c1ca008000150f9241041001490b41c00e50704c0c0d00c1030b83c1802d90b0328030560102440000500d0001c10f10300d0107125011750060342100074810452615001e6180011080d030007a00700344c0307000081c8402c40c15684075000102c04488203105200141c00022030070000102c5850054244210a0119006179603240d40c82e0b00c040369805805a80c00d401003050350081054000040a420314000d10940305405ca1600460220b42d94151007224410400c0d4240001080c0c21100e8a220f0010500c0d001200c44002e1035080c80c04404486028081403800740101c0481c5000f00041200c0c0100c1e81030751543e00d0040f0461922003181c0251200c103500f00c0041c03c003c2c2450343c800e098440034100c98006001d83d03a107000205031400182583c51400c0d0421419400310b90700c008940070a243c0f00a0a120500c41d01c1c000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 531720926 1250 531719676 531719707
    0x3090902031b0d0e1203012414040b07060b240c19060209010908060402091602010b2d0307030f060207080712020c0f09042f040e0a060b0d1205 63
    0x1001d01c140000c03c04403c80111904400311036408142a5030304101c0008a4800c2d6200074090014262086030040c14800d2400e50040f01c03890386490411b0680588140e03c00c035940c05540820b040301e20110b03401c024001940300d54100004220b4100b094448840011f11002030790464920f000000861082c0c0400c40070712a4500b0490308038041750400c4201d00d041c1e0020b42040f000540069048080401e0f11000054220b0259400911310703205503a0b40180322a002190440c0441103540ba403440390882d8458111000341c042c0202c0c0e150109032450b5032001102d5002c584603d100e41d014810070404100e40c0502e0200780c640108c405030303030303a01903080041c480c2c441e10700c000309025502010000328a0b404034408102d1481151a100482044801c010345401d05880207801c50b01409624048080e0034400403800c000c1c211000581d000c080300c0050111440d840c241c442e03a4209040c2c141c204052803042650300e04040301c41d40041031340c90f260001c0c400c611424510900c900021200310000700304 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 531722176 1250 531720926 531720961
    0xa06020a05280203010e1b030a0f060f06080a0b0105100315030f060e0706120c0503040201080609090708030c061504060b0a0305040305041701020901080106020606010c06050c04030c030302060708090102070309090203 95
    0x613000744603203106d0171102c0d0768415a080c84500644554911030b42030b89004910308000c1c940004941d41c0210481e01e4035001040c9040c9120356196481000140d00c86060020800d0b1070b02071075013401d00350f16010038410b0f1030658450000405181081500138184540711900c00e072600300b140e0401e08585031030f04100400003030031072200504c0388180000c0c1c029030240c07483c6100310326144148040461810292018042524024046040840080d0345410006a0541d028a1070310848400d1a605c00b86642585d00207140800f058024130304103d1210510005249010415203080020038503050010784540650320190f400c2644450110303042c944544140c03009081510b08022520125150041c000d5220040ca01d0207e0038100000601754000706001d0312036007060b1218000c2034010f54440000b86001858a007040b0400e10010000c190f55490103c041c5100b60010805401c04000103421030b080280b2014103030707004010220000c0d42c072904980c100c800f02d1401580701c0d111594142c0701003040c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 531723426 1250 531722176 531722179
    0xa2c0703080408061005011b0b100f0620070501050a18050405070c02030105060d0809040b06070b070203040e090f120325030c12020c060f04080d09110a06020a052802 73
    0x4280400d00b90f2001c02e005005e0f0702d002c050300201c5646d0750019070f14030b000d0a40c08008051075101c0040401c001c4032006601503900036541c07100e252150018000004140c10140000c0c074801200201d0034250107200d44075080c00c8005085086c036250008109210b88011902000740305815041c0050714602071402500006005014520300490010100707100880140e220350b0805020841a0900c20072803102c0f42d40180b40245850001010b100160200c103244c0c0d90015810004040421015200c803801a071460780a581d0340e5192400c0d800031040043e00900658002810307440360704c8400603500780308242c09a442070726a62071000481041860f001d44080881441f603902200c59410303032204000c003a1035290f08444510a0107518100d0045100c0c81c2140d60180c008130b60b01440d580186d40d0b0140c404c40c2003514000c951042d50b016030741c5000040740d010b1449424854645803400344000a089240f0040c10000c0e00c603114a6920400d01c09010640943d203a11000b0b005006240248500d40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 531724676 1250 531723426 531723443
    0x60c050a051b0414070903021512010f050405060909030901081005100909051614070609020a0e041e1101080702030d020408030d0b0418080a0504050d0b0a050a2c0703 73
    0x41860840d515100080b400e51042d494010030451140c8850760b030f0345c01118960384060031113003140d0a006400e6180b198084014a042c0300120400103141303005406400c45903030b9410b00e01c0c40c1c002400161400a0700c00b5100d80486020000c800e00700000740c506c40c030004d1900c02000d485442281003802c0460b0070040d004040d13140152226604824640100c0e05940800c1000ea83c80a010340e807042810000c00e00040c940801c0351140c0541c2e107001e0003502d40207503000110647d043e8000f0341100003640c450703079540822000300414401d04c03000c07402d20741802014203251050b29954060154160143d058140320b0a08041203000f81300300709981c42030307001f41c030115aa41d4072110040e136603400101c03031400080d0801200180030700341340c040d5102d512100d601503200151140d50307400c6070341c000852030800c000040c0000110341d9103090210f5072090050030003080500f801009a400d80700010001d0401c60b01307000c041c0c0508050388003504820500340301c120502d030903201c24041c00c045503540050032a01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 531725926 1250 531724676 531724693
    0xf0301110304110a1706100608090c010815030102030106110d030209090a0c0309021302040f1401091a0d0c0305090c1909110702040c090521030301091a10180519060c050a05 76
    0x85c0014a1400703a00f84d82c0c2ca16001e1642c40b0422200382c1d4048890500640004480c031486500840304c154001c40381001e5982c03865000000b19089030000da00c020001440b0303c01140750000280711145078819a45829850814201c001c100002c501903d64990103075a1181902624800c0d03000c000c1c0158010700d110f031a50b84041175031020b904140034641c2d1101b8801c0f0000380c54910b501008400c0380040e1946941180303080040744051a08004001752194100700114410710140f2800a08030310544001405040088002c4d1901e0707008020b482c0100751019580135000e4854034140220b8092441c0828201014103808030746004403040290810300b13100118a900742c001c80f0b21030a4032001d852411101200081c43c00c2c5000fa4401440f510760800c00041c40717080d0450304803500d08240b010010a0124105010038030303010b4054a0000024001e050881c000f402c2006140c00400048904140c180d50b2181c040d40204070f180708040500c01612954400c0040c01e00c096800c0325000015501c090 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 531727176 1250 531725926 531725969
    0x150d030e0d140d021b040504170706090308070c030e0f1315080c100903020d110303071103121305040902010c05060c0d0c09060f080709180b0f0301110304110a 70
    0x861089002032880d0080d001020003d07440003424685a658003911200642c20362001d12004250103801504d03220ba21001c54000e80300020300410741c40e8803d14000401040c2401c0c01080010050402c9081101991500022030741c0800310003896541141c80280205002c0001500c072400d5a0241a08500b0702243c4030145d05091558012120900d040d40d85c250204001c1010402c40000050081109083c06101604107556100141c0307104244150301c20082da000203145401c4030004032030f022040d40d02900c0070b041c1802407244240d201000c00c2e09001082a0350781e8903031000c3c00303094091130341d9030b40034800c1d6032060507608110fa0300082614602c0c1825203810103558002e184081c0e000b0300304521954202e2103040b410089410540e101c0903400d8180c1d1046500041c081c01110411000c030b100410004200b403102c00250b03000b0300c030000d051708107501407014980b131800315103210f64902682420201402001c032070f4000d9004d03140d551118024800600507074ac103600520b4a191100b40c949a54 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 531728426 1250 531727176 531727193
    0x925020c0a061d01080f180109080c010b100e130f02040302180106090e15131407090e0603072601020c030304030e040b0d03050a0c03030f0e03070317150d030e0d 71
    0xd65039142c1d9031010051210006650b01300c415250806040c1c4100002008560040641f00c11814501e0001ca40c40c810f41d22003003000e800080c011040c41c0d560b10000e559524101401c4003000407242800349503807200b40001001c2d2494185101c0905480341611401107006504a070081c650041c510802c4982c181c40b0255001002d010361b2000c2100100e01107521190704404603c036000f101c0c100a401c0d6034400503c1035a400010301c102d03080392260f480714880b02003100178a10800e1107699a8080307a00c2c040030759a480f2409040180030b074000c3c0c08c051002000030321044003002101c0824280e40582c0b0501c9a00a2003103280090680c00b000c0140f200705a482800c5981d00c1c0c004603428004002e081040211010030b030600280455070801035903040390302a042054080c1d020f402c0005502d10f200c642c01064540c01e600c006116000000c2203010160080c02c00002c80c8040e0340034802d1403401c00306402000008140143c4036048115a1404042c894200302c030004e074010300411a80c000ca440c00004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 531729676 1250 531728426 531728447
    0xe123f070f05030c040504090303021c0510140303040e1e1513020a1d01090801092d17070c080d020d030f020903190602121f050925020c0a06 62
    0x5060020301c2039000b40b040c01501c1c09049a40009460a032420040100030b00b5055811000d2540901190404144007404455171944810300840c2b40d00c5c02c0d031481e05400c040342c4c00c5001c1002c0f00f90812059501d00005071010b8412002e400c0c3c01940b10440742000d483d18505003030710074020b90f404014848105410000c61440c09540c001200c09404010b08164003c18007044005101301800302c6405551403400401c2410604046021580300d108082c20f40d01190340503246074401c030403100f0100c2d13030f0001255000140f11001ca1202d940541d14900441c00071040c89801150220341d90302030001e009031140c0200f001c1d5040795550210807034060f44400c554110840030a1800308582d4400045000712007186100501402144101d417032400c1c4801e1842c3d20984d5095824403840907411680100e8900903903824030b00c07031064503000c02d48209a1000d038005034000c95803d03041c41401551004500f502213164510341c40d280326000c8040b840e002d144501258441d62074080001d441c3d410411014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 531730926 1250 531729676 531729691
    0x110102011b0906090e010305030703031508011406190302060318010b0402071a070306180f060f0f0311030a0830070c1b050303040510050f1c0e123f 65
    0x1074204c3c2d540d0100010740c0d4800d01c030252180c1c0041285500003480fa82c0507041409200310540480342d00c1d004c00304d08541c186501508180400018044180743c50009005d1641542d005a8031050071503010501b21300000e0440c1d0040e41540d10000b564050a410032810350304060411500c1d0821070a055100000c5450b03000280c0d148030012841452003030091a040e92040d04045d82d1400078004c1a00003002c0d0459245011303541c13900301050320b903071650109006100300184454101c2c01c0d820410301d080b24031410306200f42d014240c0040000d2804099441030300310814078501e90701c0f0080ca030380312500011415207201c4400c1d1042041140c2c1020500402d28060744a4040301050301c40c60704141540c0740501503043e8003d1104010b00d1a001da1000312071222480d0440c1061000544010660859a0460004120704069903405041c9104100e0507003a00002849244100e211144192223a15a20311100790300b031340c034040818026810120185929000c01c12100d51a000c0020590025074840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 531732176 1250 531730926 531730937
    0x20a0b0a0504110306090d0c0f12030b03070816060f03090c0602011a060702180903040905070801170604023003030a0c171006032a0905030c040c0804110102011b0906 73
    0x840f010304001078807034414044940244000301c0d416074182c45222307043e8030441c0c1c3c0b000c800d013001c00041c1001d1202101c4c548561001314254401008040c184550f50b000710b01c0b20f521511403a421268010404400c0714074074108030541e12045d5804601a02c042840074102d00d4011200103107035a0705505c4000c0410308500c0002c030b285005030400c002c43c400c142000c3d41c060045061031446210007481c40780c1052901c0122407429139200c0012040e24000c541d0301d0042004900100000d40084003442c40e1551980e02030551480d155000031590101070060050a51441100000e2808504000203001c8542001c40c0c0c3c0300e2421304c00140c05007404d281c0e05c0c4000b8002c07070320300309c100c0840c0c1c4000d41c02400c0fa10802600c20707040002c110020102c01c501a1038a1803c401d41e0064146010304014050380141e6a01c0d0840f800c00091518185c02e494031107000e245005c070401c80065210303078043c1e0040d0f8005280d1100380d0035030004074094040c00c907261a00041e25100410780940002c0600101c03010b545a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 531733426 1250 531732176 531732203
    0x12110a0605070b0612010b0901080c0102070546030503030615090a0b0d2721021b0f2701080105061309050a150906050123010c03020a0b0a0504 63
    0x311207030700036040c009081c10000b5011404a180c802c51051288101c0c100010300d02d10030b84000740ba144001e80c0b1102240c0c00442c1010b1103541d0600050001e0300d82901d4003480c03080082c005c00d40890020122400b41e895825644550504a44460300500c1401c00b505050684134244a904d0358416203200d407282003040001d0ba0444810400c0e510704000c0201202d00c7d081c0703002043c07100c641c49000c110b001950740701c24208402d04140d019a040c10720090503003111f80f240d131800e900384020601814299445218000710080e500241b070f100f802d20003400b9503103400f6640e400b242d400311400c4d030090760025481c60704400310440c2250980038000c8043c001d140990ba5101c0441c00c80718291441303501708001800c000c1c0c03902035580144502030721900c2180c3c078000e4a9140c0c00c08000110300312440d1540c031000e04c2d1003405494012039026011240310106420844150385545030a51049a07050040c1e46403280d0a2500a10440720306a0700407c00c04498030345418940010942220212441c0c3d010080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 531734676 1250 531733426 531733439
    0x5010b0d2405090c07020613061101050907060e01090f090b010f03050603070902030c070c080c030c040b030a1407090903020a0c08010504020a090b0f0d0803041205070f15020412110a 80
    0x404036600300c0c81078008205051000384025400001d0110000c45420881080140c882500074500030310340080c004c60150404200130b010070382c40c03182c25002da818401071041000c400b00d001411180e080c104083c0318003240c0010f841e05a4654061040140540400551040365400c070303d810040990300d81900d40e1021200742c044038800d40ea9284c00d0741c0f001005200c1800341c1c0d8015070b008513a6107030081c10042c0f180c1d514449104c464224131541e4100202401480c141000464500c1e802240d0500c0314014010106e42c1e1500c0c1548042c00f4682e4040802101c880284081ca020785542d40e424802c01206003000703913403281d41d40421038040b60881c0f0000380c41201841814019a0300825040600c6e1802482001800480000945c04000b0400c0c00103540e6801d43c000d0409841112191307241c2c80e0031305140710007001000d0500b060080401020b000105410810025a5032003000161900d410060150007800707190080c05c41d800701e040130442440f50041c9945240c0004484201045490740c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 531735926 1250 531734676 531734711
    0x20c07030b0601111b0d050327060c1c0504030f03090e0f011809170d050a1d0307080d1512051b060d050603010b061303120e010e01031e05010b0d 64
    0x40c1e4130402a004803070040d101c1d1400a25004c0c0d134401c01001e6603045045c40c3c540d1070031a4071042089554954015101d072041200c030400c03a0210100300c581306d0030508031600e0b1548a50005540d600004000028482d03950b0059041c0c5002d513030040300701c0007000054038010b001100103004003460701d403d0000103003910001c81c071010b058400840080401e05c801460348005010701440c2201c441240e20000c0c103407228a00094541c10a0b11000881d990828484030b60807203000140c2000648039103540080045800003c0351000ca0f4040342041d5141460050040281300240d40301441004424000540010400c0b1410513a40200b080c0c0b10710300c4c1f0074000c030001222900c8015401c8074040c085a444081c003644400c0d803058024001141c008660400524554407840019030700c09031a04090003070004100c075950310110181000240c2d0030007100083c1058051802c400d0401d51035181007591140341c1d201c80714134030074004c00500c095619030b402c0078841d4000040b10401c0c5460000c194500d0007a06 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 531737176 1250 531735926 531735947
    0x5040804090e10111602010c02010306080f0304050a08070303050301030b1009091a06030a1e0618050a17030f0604020c15150f0604031703060604081504060515130b03010b04020c07030b0601 83
    0x1c21728469004081c0d801590080001e6005070306140e13a445001034000300c2480022a8050490042e644c0c49003450100481d80110b500181c0055025000c140006900b00040301c2c1543d07002040c000c4603640f1040d61440d0086250001c102c1181400368050801000803c25002203c4200b44460a642d0b05402d240c0e03650614180500060351a100030a0b503e1000c5c001039807007901481000c141c4417034810030404c2c0611006400c40b030302e0740600882e805001c00740206e0340c10151508021803550503d03460038500c1d1480a002240301c0d0343c2c0024200501c020400801c0801800800c2c89040b83c134000c1c81d032000280e0305118840c01211600707895400c3c1e1418074110303010307641e006002c040c1840810718800c1503500010190b41e008070701000301182d56a02080b18404601c031042c480c895500d000c2c58400280c3d400075103081c4d130290b02051041c109a0318001c030b034030300d0300700c22744000540460903c00640900304558006400c50302c0043c108a20f01408143c07041928062900c889940d11801c0045403c241d02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 531738426 1250 531737176 531737197
    0x9090105061801080c0927010803041206110d0c0819090302030f09190312021c1b0206091908070602030903030a03052a130f08030a0305040804090e1011 67
    0x1404002c40315600070120136030400e0410144c541018141030110749072040000d044070b9118100e03062400c130440c410f0502ca000d0600d0300c02943c01c05181100c00c0310980c01035100189200d490340c443d50040c1e04440269141040d030220107000c2140c6802014080007025120765168942001440c0c07103440040c019200b81951682c000c514100d40281340b5a45a08a81d0f00140d04c030300358514038402c410700c84200801550140100041200340d010010b407403c3d25011000307911f002e00c401006e20043e0040c4117014840081d5400388190469480062514844c143c1140e038421160b0310802d0417024100032110541e0207101c1214900b036144c00050742c0d40e009007191170380e140d8410440d104481e44240c20039500200100540c1c001c000c41081c40d81c420115800806c082c1043c04543c7d11090007144031803800900001e0a0079400c01c0c1071481e072300c3d10313842150005014542c45601090030403180c3c4044400134809800100400c00c0c48480d400c0c1c4800601d210b055602d8109900d1014541328035040319902e208 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 531739676 1250 531738426 531738457
    0x406080606012010020a02062d0406090c15020120041a07170711040c0e0a14011e0201050106020706140d050718030b0702070e0c0909091606050909010506 68
    0x240400f00100b0702c10074140c4011800745480e05842c07105030f130021740320b003101caa00544072502d0294180b8201244180001c544c043e050400101035030703800c0600d2900190030460200301c0800751f0803c1d49040070260b1203914200040810021050303411741c8024000070071102402c040109a1204050714040c40c012241c0c65050b80840d4140040e80100030840944102c00c0ca01c07181515003076241858100d02c07001c2d208a1002c44a058152905114a0038850b1150404030703006907019010628452090081005000301c001ca182190780c05400c440c003442c140442907002d040c1468034000d000c3c0c003080c400c0c40e0252145040c08a0407c1c00390003503d003e118400d0182e428008a007009101078070000c0d161030148014007540c3c800b0b025880703580001450061040300c030302d03081500c4001e150034041c0e804460346030041003e215032403a00800f111000001201c504440351116240a4108410301000300540340702480001113441c0c016002c2e060840c3c04070780550046ea43d07602444000e11442400d05035180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 531740926 1250 531739676 531739697
    0x306010f020c210a08030a060311010824030a0b25140a05070623090c0402180411280f030e190303022101080f0d020a1401021314040608060601 63
    0x80c0d03d0380340c1d5401c2c0c0615400c0750100c400f10380350342080b42c0c01514030100c050b860303000c1031060120303a0a4140c600d45080c40c10100d2031411510050840a07032817003920306000c44c0c001c2e00030255001c028090800350802d644020340d044c0148208a000748170441804010b0001d071040040038096800081d000302250740a41c6481d08000044515a00040d0121080b543c2e8004040091080d1442007441510354800d216842c205140c49030f160688600040d13100e640104451580047e005550002400050383c0101e00030614640050550245265036504025100e0704a0801c20528107007041d011103a480e0b4035001000703400c080701a0361b540651031655900c95498000d585c0d0f80d1411694440b4040e14005051401498039801400021451404840c10910050100c150244100c44020071340c2c03001032521400c00d440180d2902c111174009007200301702ca4000d5440f103000f034049480e0036003543c4070050003a40f1508101c8032202c4601c001030003141ba00d036003c11540300000c0c2040c0500d10585401c0081d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 531742176 1250 531740926 531740959
    0x7120c0c0b0a02070f0305030d05010b0301180e0322030b0105060a050f0a0908010e0706020105010b0301140d150f050702190305041208041212080a090305040323070b0306010f020c 79
    0x5030b21284421003107215894002a5100c110030003200a144a4006141c2c0c0e800d0303008510301a55411381155010820400041000b03120b144290710780d100c00800c01040321940c2e0005035045001703054403a07001c00c0398031208140307511042c14004203480c4140c0d0110781e141d0329441400583c3c014001058040f0340d04000702c1481c40b4241e00508035901c003034540203409031f41324050f26003510340003603040440e54440c007400d110294080c02130a01420001590505643c074181d42183c010a442d04464096106080100140810002180d08050314805c2c14044003aa5800c0d5400500701180c412005015280184040c04000e4420f400c0440d0140e440c1802c10b410714200352886040e251044400b84010480000c0401d4120201002140545400c0a55602c02000a084402c004083d03a508510302101c50b00065003140075035003a00d42205c09035030440d00034a40c801c82481045150092441105000180d44000c00c000f10300c500e600780c1c0c58400c8290040d1050740c1c0c40c045075020642c000f80303030305010604 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 531743426 1250 531742176 531742199
    0x140f22080309010b0a090f0e03070213180813090c03020c0604141005090106050405061203070b04061d0a02010f09050d0f241527050a0b040f0207120c0c 67
    0x2c80000000020348861040c0040e103c0c8545a21148089483e055038450015180c45584040440031014516010740307a400511032144805106001c2c0c3d03034030400c04251030500030908140b16030094005644010464a01d1945051403203840e40c2c850a00240c601c081d48a070080d2401c250702c500091826480e1548c8001d8808000361041111b4424007626200c07950703440c081c0c0c500545e40b400c00012010f05013403c0c00b040d120001c0c101d9001e0344003003c00300d031180000000c589100750024003c035010348551034803c1c050854001c4002514581035a0500070b45004070740f205050303100f620703204405480c2c1d940640e80078003d0f114032580006444d01d4040401c020550584ca403074400d030019043c82d0383da075120000b01c90b0000000c54103540d8401850342e6042c075484c246400341502a6166099815515801d1040f81c0c10074400c1400588400100714400150340103012411001003080c0309011015410034001d4205000503501003400c0b00a4000090142e6084903520f42c104008010301f90500c01000385 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 531744676 1250 531743426 531743431
    0x140a050601140706090b060108070207090203070c0c17010b0a08030a05070f081b0f06040b060d111c031707090b030c040f1403011409250504140f220803 67
    0x500c0500c1c0815144880c20000038101c0e14030513400020090707103504000002001c02403002c1d0520841009210b155900022600100e41143e040980e41e035031b8101c01250010000103005000e04082540824540350a00901243c00300c068006c0090b001514200818111144106680f50700200110658240700350300810403503004040000c51454a81c1c0d520800c0d5000e148600503002c0701c218035030891341c0c090004100101801d0014030f158103040d100c856000348090a00c031311450801c0300d4400cc0202616a42075045001020070b401400120340030f040300d0b00c00c800200c1c0022107210951081c0d90580b08018040c8107075a4900280e00d003845601940350340050580e1006d01c2051100103418101c0044d1140640b8a1440d507000c40c032008418107080d2441144010a0301c00001d04209079250002500c2c00340300a000d042d4170706a0160950170403414030302d400490f00281800000003034070306a040c070b180c000d94141c10b43c1d44442e80c1c2c1c00f0f041301da40c01485a844a034100b10814410200d04803030069034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 531745926 1250 531744676 531744679
    0x110a0e0405150c3c03040201090e240111010608030c0d093b011d2410050417060624070303270f120f091701180501090c0504140a0506 59
    0x70741c003a404c0c0081444501840ba4045003540008100f00455070310802d40d4000b130100116107003440c1804603580c030b410300e03c44004038182d030407442d0206001e81c8181465440b600b0041c000700600c0e610707103d00e262a40c0c81401184180d00c102d41112041602c58a507200803221000706204000141030414550202080880c8100340e24032542e0141c07038655810914000c0c500c400c9924000d84082c2d40d90b0f0203041004000b2110304400744113000c1406500c0c0310244a8250448141450414452003070301c10b8065904003504c030000c90b8004005c0400c000031018083c0c3c10403603803209509140100d01e05180b076580040d40c484481400324100180c042d4010340c52404000b0034044c40d40e00b103480f420340c803a690b92009850440540c0588420710245601088200507985044241000c00d6140036008600728401d090382c0003850142c601107a5400c2d441107013070391340945a00034044141d0038824003030070700c002040e80d07840c03c07070240000c10f407400e07104210030f81c80c00c14110003483d030f40d4000401c0101001040d85 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 531747176 1250 531745926 531745987
    0x17030901090206040602030301050103060b04080a02040b130e0c150a0f0e0109150203130806060f0f04060815011505040e0c0901121d060105040b010516110a0e0405150c 74
    0x100c010303035510f00640058411680110348a40c03601000400360741056209002c200020082030103c1c000109490801c1501940c0100d21040d81d800860009031055080c885001d1405038041020100400d405184a00440c0e0701c5003100090404400540b20764803002c404140c0d80000341c120140182d0307440c0582c1c4014100421800d94480c1410b88502d4041080c00042c2c1001810040d09402802c881014061200041540345400d10200d400791401e400300510914011a0b41d401590301c54101501800c01c01d402c0e500401c511032581041d21400f8010800c201d4198244d1164840c860f200342c6040310b4940e1182600c40c0c5400c59400c80d04c0c1d00052002e07040051a1142e011100070074000d107100007400700ca600a0400600c44001d01f0000180c01c2540f2803401c19810040b146ea0040a443c445000d080780301d040410945484e0352450841c124541c0c02c110441c10005500d4449082d080c07059000728151805c40403002641c540c021070032182d491028000707004118400c00300701072903001c155600181 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 531748426 1250 531747176 531747191
    0x304260c12160b1215150f0705070f05010206090a0b06060304030507061e0f060b030414071d0604051f03080d0e2d0303010605040b0708070b131202070317030901 71
    0xd011403140740c2c1007600c40560024111104258030740c076003a80101310000c07010503170b60008001103c105401c1c411100000c0003042074038401051000b11540564020100c83e6450b40c2c81ca0704250b400010b10406003d4058400095201c000106c2c040003081d80c80346501405545000401020350005401138040000501010f80010158030501c500110022085091303204d1500315141038560044210b012070341000350401401e540c10007603d820950200f040d00e180c103003c10503945440201d902401c810b140b03003031030541e00c02c80b0b04550b0350203038009446c24000340da034400c1c030412056024428281100f100b00da041010a015002911084194030300c0440c00c40032092032146881004550b0841c2c4101403180c542c6043e21026a100c10446200003543c01c1d90b140400140c01d500803403207013583c04100050403d08109a83e4100c0f80c0b02588120040042c3c1842d418031500043d04020403142d000d00c203a2012807090001907103d003120341c4a41041b10b01180203030508800e0300b026100812542d2182c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 531749676 1250 531748426 531748453
    0x507050c030a0806240409090204090503030c04052e0e01230c070630090209010905040b0a0203060d020616080403080a0f051603030e1e0304260c12 65
    0xd00b40756100e036941d1a4641801410040c45003036407858020002501800420710002003c25a8200c0b074200354005011900d1380080b07005083d5608005015000010401101000d00c41c050003e940b820b1b1003076402035846250a80c00c012620061b5441c0541915070f040303040340300344240145208189040d444505995560701080a40311002c059140c8000c58003212151007009800000c207520302d095400d0b04010824000d0414a00705540143c14000a09200c0c0000c150080e10119902600074001580d441c0528001400282c500f1103045e40d03413a006c01d51520140c020359000c0c000050101d41c3d071614690130464030703500104602c11412101031030080814202800741c40190b001c2ca01d916610211580010940145c10900c0b81c03c5c01820704c42d180c0145481103040314995454100014a00c0f02c0c101060701e0a1450080c0400c8580440c00b10106507401001810440b20020510485460f40100826410420442c2c824441d0b12000f900b1901d031501203000044103107280b003500d05286c0c125a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 531750926 1250 531749676 531749683
    0xb04060302060c01060503100605010f1b0803070809011503050c0d231606090807060302220f0f060329130213030201090806090d050f0405030106090902030601050105030c04090507050c 81
    0x55442000c4e55104003c101a003401d003c040382d5003c0c0c00e20b00300005410880040c20000e05000d01400700248001041c440c031030031601c1c050b241c98012020f9900c0780340c400380090014a044a00070310075400c013907403001a074520040044c160790f07100000c0e041002038981408800d8412420980d1703050b100032800c11005000f1494503c81c00e40304005005d503036941140700700081c10140c0c404030800009c4482080a60408100c507015280d152070701595072075403d030307208002a4001c4040d4411041078440059034040d40440c04048400d0104155460b035503d0f80c050b4104c6441c40010040c1d40d03c0d03071142060607040e829900b41e4400000304126010355500d80031800326003040c0b09a60034018a15414403d640e00109030030000e100c03810082c0468035145003001c0d21051070f03001c81028090b001c80d0400b00400d4600a803005404050020041190b507008003c01401c06844144e00074000c01300041819440f07241124450303c00528080d00d4603240200282c000c01c4000c19881c03c00005120754045485e050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 531752176 1250 531750926 531750937
    0x70e15040f0204030b1e0402040b1815030d1d15070807030c020a091a0f030f0f0a1b21030909021b1e0a030e150c16050f0a090b0406030206 61
    0x401e001610380c0e08620b081581c00350084e214800d40c0803060040344803800001211039010345d059501107a4800c0010111724141341d8459801c201c030324401d04102c0c61043c0b00074118208070f411000c8078014540310718151145015103d28142014490b11011001c0c10714001c01c1130308403a810001850140c554440218a170416102103000039014000c24040d0b00c1d02105c840007901d2072120800c100c04466180610102c0315001103401069902d140700030b039aa09200480d0f211568a0684241031845542d194071644000c80827212092101c1c00401e42c01c0310904071106461011000c0d0000a210903158032803d60402411401c000c0100030104a00c107950000e840005a100080c03041c5140c001c03070150501200403608103041c20404a690301118001820500d480e0b01401e0852612696034041241401d800b100400100000904100c0301200082c0940c07840b40c002056500e4140c1301c3d0200a940840862195800b12111400f8080020741c0da01486c52070700c00401c0094441e03030b40c0d8041032254010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 531753426 1250 531752176 531752201
    0x216080a0b19150305010b010e0604061214161101090f0209041707140c03120f070816030f11030307121a040e03030a2409111b060403120e070e1504 65
    0x20183e0030005c10000b40100400241c0908200c010f40340c840f0080fa400e0b004901c2600e0030401c0304049a851014035038030040d04030001921040640c41c1810f103641400045001520000f031018034100503400061248140300c80d48a07030341e100c4400c001e800f08000e0b402c0c090410381c0c14aa09081e822074098048004103816031203038455803d040070a4092a003000d800c0340f5680e021b500001407480c0a0880107041760b42081d100d800e004d444445504280c29140503a600d40340d060400080007005154021119005064803130380c0d95061400414100340d203d01017a5400700220320b0f120050380c2d5a0440d604602e64074244180d0300c1c900c00e04004005019100c4204154809130000001d0101002143c00703018501185011f000781000d81504000c00c214a081c81445115561420660803a074102d4044964010100304404102d105001c6c031152112002d0320b08401190f840e0701780d88800c01c80350040010795240e0710003800781b05151591303800a80300010843c2250a40c1c4c400f0704030803a5180c3c403075074401211 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 531754676 1250 531753426 531753461
    0x6010e04030909050906061009090906021b241518160e01021002161506180b06160201020f0d03051006051c1808120402010216080a0b19 60
    0x14203080151902c20507030880da00f01c80c100410410a0000020040e030050390031f5030000505410108110343c00a20f642007454080c0c1800d18101c01d201240d00600b140c8858281c0030b01e042250314615558804003040c54040d9110900015840340161400c41c6520062078036240108081c080002a58250042c0c1e0f88251039030701c1414441c9950b038402c03103004010030a003400d010078100100040e5031891102c54040d085031700003801800300c00702d2a21a0014640c07021041408a4940c02100e0240007540903d1024241482001585141902400c07040f810050005407034080300251072242054410404d0307065129142d415101540104030302c007484501c0799000100c50a051629040d04070b1280d10180030040c0a211101441003007a10404400140f02000200016500500c095000d1010800b512050000c03c0110b00e210001d0b003180d101e01e01c00da0a0341e01080c1c1e00890001d01031141d0080000310f0380030780c0011000807050502c15400c14013010703008559109640c5414151413139540c0001d007508 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 531755926 1250 531754676 531754681
    0xf0605030a05010e150607110d03170c031e0a1407020f06090c0303040e09010f020a0804050d0810060e010513091e0c0e0603040f0204090507050114040e042306010e 72
    0x84480c03281034050500c005001040e8217004003420903904100004074851240000c1034420854074002c044001c03030002c0d002e000d01e50102d0401408502008551800f003440f11400180d92000103c1240d105d2506286404c030411341d28191104100c50041c655000745039101c10700d443d070400240000d845928036500420000b544010720a0030088080e040e5035455120640d1100240d60100588041c2c0b8640030300020a641d40600e410301416a00329424134151001520501c041e900c8a2298070070fa00a01c11101540c640b5903088903000f1048030040c080c2280000140002c038071a141c080d03ca410145400d1341004030822161005040c15030152940c03503624204c2d150121650310a560349500c00e0007041050148140c0e0107003080700901401c03445078000100040c10020000c24004410350046c1040042c0d030306610b0440d43c0c07600103000d014041500c0300c8501d0304409035102110261011882c01030225111a0b541c0d82c2c0440c0781b23001e0018144c4107001e001c0007030081007000d5402040040c030100c0060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 531757176 1250 531755926 531755941
    0x121020c010606020a08190225031a0702072102090114100f050306010e150a090905010504110405090411060c071a09100e01050f040f091503020108041b0f060503 71
    0x124543da1224056410602c00000440d146c0001e84500e405204020809080f180790200d0501c000081022003800002c480c81d0b8010441410480035240320703901036800300c0c102641a0107400c0c9c0c01c41d218001030b8000e140034084010362840e481001a00b803160500c07600901e5000604440b426080a41c005408000312401e910740085d400b0392180541c00c02030075054150f44000d03d035110081c100360621082c2c011140d0f0b151180b0f062001c46c1508111400d46541c04885d006018040c103108103450b09042c200081054a42441030107140001510703030030300e410719040600000c00e10040007030341c4081c85890307490401d40390840203104801c00f1001a054850400010314580c607610180380010342010720403622141c440101207407078000c660610410329a1080012511441000107580d0a04c8002c0b50001d240751544c84608d0a0f03d44002c01032004103603004840f181d02e5224440a4001505c1c0000b0401140c603c1c0101a154504941910242603d51801505807880b583c0141c0010f4400420406403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 531758426 1250 531757176 531757181
    0x50c07080c19050a2306030403050a0915020a0b060604030515040302100515040911030318150a020c09071404030f02120111030105011d1207060807020705011d0121020c01 75
    0xc8401c000008880c9504003c003090609646008014000400b00d1081035030003503960b5a10400d000042100b030b500d141c5460005c2403034200012513808101103004c08a0440034407a29401609050303401804403032502e4580c450362003800b41281da00310a0400c404800300e0740511440250141c10791400c901e0341131524000380f134850500702107101549450103000c41600703954020340f5219022580415096003034284088441c0c2d0581c0119810322002802c10480355910b03041003040c400448040181103090b040305015485141100f01c01a000407441c400c0d60f248c11302c181030b04120180380c1801710045441814000358445e41050300c1510a203c0040c04518040f40001a50000c0a00a01105032801c1441c1d50340d00040c02040c2c180001c0743e140040d20168000d140d00320840c020311007400710380c0b00d203c20380d1620018007520f8002108000007440703203400084d602c0119501a900c0182c2c40307a10410380310144d03100c00c42c42410441d01e01d0300011100200455030950301c1002c40e0060741d0b100401011400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 531759676 1250 531758426 531758449
    0x6080405161d06010e0d12030c14040515040807090f1d0601030809130203010e180f120d09060c08070f0c0203030d02160f030c05100605090412050c07080c 68
    0x1c100c4003604248040610700c8850499000d03018001c80180c1c403a007005807400440c2e03000c0d0581203202d00c601c410030302040e00188045e241164400304015189a01d0441e4001c060b6015102440010002040300341004d50759116a108081540b40c1000c1c0c44224441c24450203a2110b0320160700d4400d80c40307507264984202c92520750040a9011407450000006441d0b01051002600d00200032441c40c00e02c0d211401c13045c2c281c4210708000c558940c1c583d40d92200302c1d0810f981a0701c15920b51072009010310701c0000d011026000040082100d030400308507000e4039a10801c0c0d100e03c9540c0ba24013220000d06180559203040080d40c680003403924100b40000d0141c01c10712620b03410081031462210250310301204841c207400d1011302c09640d58445a0f00010400e6140c1c1004008407500e584003014140d0040300844164856030503108144034940550301524180d00526a01c910801c0203c1c00180d1014580c85501c03400f820018240020200310318108891640215a1600034150805030340c60842094103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 531760926 1250 531759676 531759703
    0xc02060c07050a060f020c0f03042c0f070e040204080a030806030d1b0503040509190501240509010924030e010606020a142d010b0901060e100c05060106080405 70
    0x1400e06941d620380c296a50341c4550f01410240d0744e06541d108802c2150101d500d1106000110380c0c500d40609500c035900c0d8010f01c030380184034039440711955488100070700400b00d4104142c0b000c040c94a40d42c0c00002c0c0c02e2000350444082c07188000780181562944c1c00900024022031002c5d0114440c03500b0301911001004100e24032070740009001e2401d240d00704407011200c50b1742c81082900031390f1500e011451031007150403e40d400821001000f03c2041c207014100320744044407600f48502d9a03902040c3d000584201d00c2001089a08545840c140c0e11134400b42050200514050a200703968143d00c0c0041501c1c0d8100442503050100501c2c400e41c2c041c0201c0c5181480003000b0040140790080007034940c06400300c028045c0c1c07940d10482c8000c84040103004141700c044e2002590041071100100b02004c51404c61110950030214120303460701c1c000d00c805040340c2083d1940c0818111940401680f002200c040c0020300580105110200340c04111240c0600200c0d2202c0d0280d007030505125151041c001d6100c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 531762176 1250 531760926 531760951
    0x901120b0f07080a0b012c0310020c03191206030b06031212010308031e07050d060e0405120d02070618110d03050a0302130909240b0904020d020a0314010c0206 70
    0x82012507020400301c0d44049413a40024007000f10a00484012030103541000000c0c038100b01c041900c11720602802c40c400000c60444c3c51510200a200d016801403c030480080e400620120301d403001d078003c3c50070070341c8a145130195a5003003010410044540a410944600e4220401c210103420100031890000d80b414000508109a142940f00c000805000092100d10040042120540c26110381000d9941c0060071501a26206000905079000003902c10905414440b002614050b118403a90103950008043c080421000320829039540c4808006001c19030b00300000408502a44254080c00c064003041c1c25101800781402c06040c1d202c545401e00caa80700c5e88a110000b50010100e40000b4600d080141e00c0e108000750030440410264081e0300c132181400941c40800031001020700405da82c200903552400f440c103c420781154080d20707078180c101640401042c050700c0c04e000c1e6540e00a20040003440640d40361391301d480d00041c41d82c1c0100c0c4070760746580d8140c01382c0303805001c001e92005000c0e428 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 531763426 1250 531762176 531762181
    0x20c010902031207150207021207060f090e010e1f0b0412060e0106060813030c020d050a06110906070201030209190314010e03160b1803040816090b0307030305030c090901120b0f 78
    0x19200d01c00d4480c40100da80139400030b503003400c540300d0a80000711048500c00f072b116403075a9000c000c4c000401a507580400200000703008100565402c811070f041c0c652041400c0d000350790b800604060f00250001e40040d0300e031618000512000c01700b008001074070b0142003820320320700e55103011410782d030341e00208202690400070140070440d4403403e4260320542d2456150f0b00031115043c15510503c00760b2003e500a200c1c1034040045c07010000c1d006d401c840c4559410007000044035000560303405000e00088d4040d03003c1022102640c880d4019000902c8020032146001e10003041c0c0d101d002d0002c0e0700448583c50028016203900d4401c0c8150060791460030051071030300341e01041c1103001c000c000034000c0011030240d002c10010b10700f50203005807c0c0d1081c41243d5407651201c40c2103a8480d05a00c0c40292100c55400224411302c1d24000e8040000d8050002c018240c11030b58107680e150001418904803000501000304580d4501345114020030000782150244200303030420300780c841c800030020141c44806d4400d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 531764676 1250 531763426 531763433
    0x14070203280501060b030115092d180519060b040303080a14010602011b0314040f031403280504030c140709090c0807050d0c0603020a12020c010902031207 68
    0x103240003028101e81c01c0000341c0741ca000c003030740d01000201e0000d450341d80f80150200e0243c00140042d03050b42c800d4091016040c1200604071340a0801d030041e800340719010030244485454000c1d448803c500d1205c4580001602c5499151581d2010030601c00303c20781354001e01a9128400841d04001c1071048028072485003001d0400d0307424492440000c080190071070008010800710f0340000c00000103001040c0040d69a550000c0c042c00070340c2011004500390b0700000803154003a00c0342d2645080e8114004209640750b403204500e18075a00c0040c1c043c044219004a58004c0703080c002c501c03401002115251085291108240c10540b02602600302841d02d07080c000401d81000c28400c0301d81d4010f030348444280c0c0010049040490980c04110103a003441450400c00c0b02c42110300068427524003c484c0f02d16903600402544208c1100045c1c007140b108001800041e104e60014407007014103040c601020070344030341c1d510700702c1c0e003d4003a001041c0d66a510410071850240080c0c2c8039481e104c1503d50030014540c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 531765926 1250 531764676 531764683
    0xf01081c0c08120907030611070c03060203100f0303170a05090c120c0a180c030b06180f101101153002060c0303010f060c0803040201110f03031614070203 68
    0x203500001d1009041c004020071446104503950401da4185502c154240340040640e90f03510760000301c84c03480c2003c1481048040348010b4030f0743c003600120041c0701c0c4d500d507468540084d880034102040c0034a0040021607098681100030f40114466540d4a005008110000f464a400a00f0618150b8141030520680007400100d481003890212051f1401c000641403541c80c0c40510302580b6003007001901d0000340c1c690f0080002d51a0b003a00442844600c003480003c504441500e403003240d01c9141400040c1c900424044031030343c440740180107280031a0041d00003c0151044e07080401c0060082081090441c00038002c1120511003034014403055400e000b14149040102d00280140e60b0505410181ca501d120310740c0b0315100d0700540b00390390700e10a403107a0584070f600034010509030303203100c20000480034030840d60700400b05e802c85401805c549031580111105041d0700c40380b045900c50031615092020702880107500924246261150915807844013500b4402914070201406130207221280c0580c4021 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 531767176 1250 531765926 531765973
    0x1b0611010c181e0f090f0b0a052b0206030a0c030b0d1101051c020c03090307061701090b010c02120c01110604020a270f090c0b091e030f03120f0108 65
    0x10f20541c0d0540307001c1c0340200d00040e4103078440d0200002c074071000124030001d68841071842008010a0215407814820301500d01c0543c45190340000c00c0400c611044500107a85045401110102c4123040381d0300e40014880782c00503108139880c290b50f650701261040d014070411240030003c0e035009070b803e2000e885090094403070644440c144100001e603031610198042e4224180f50f402501192504000080d41d9569004800154041d2144110100d02039020f0100c8090082d840a0b041440f6802c18200307030041c0814401050500200403a1680107940d0300d8049001c0c040c4600090141e244410001860200640080581b64000405210258807169078180903648041c10030700c0c81410405201c58400100c4120178078580c40e11480904078181170b0452501640540c4449403001e4444414101e9071080c01210f40d03100f00000c00841e102007802000c003140b5032000307042d03a090105900d1518110760019181c0c40c4074402c3d00b010003600311100c40c44180588500c034018010107143c21400a00500075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 531768426 1250 531767176 531767189
    0x2033001050409020f1c05070312090605030f0403050d060e130606090e0a0227040f110402042607180f0c050c032d0705010b010e1f0503041b0611010c18 67
    0x1043c80d194031b910380c042078160f00c5035008085456031943c9052a408d10b00c3d82e22440030010b4181840080c2c00d901c281c06481c000c2460362040c03140ea894640d02a2110313407000840382003076038840034002812658022481c0c422854801c42c0420030034035141040898405801c0b800025140c0002e0300441140054092101e6605480004110300200c007250050010787e10541d4181ca00f0748200010000c0061002c148a481a00402c20108441c002c01099006502800207071050a800b8100700300031400402c081040d4690a0b2100240c4688400c03508054840c81c10443d80d450701e9501d2a031150b1841140c800d40a20b181060078550624440c40e01d81c4100b210040402c80c06410198103584440c003d98208807800050a0742d0f5582031906601829140340310700e011501c06c1c0a0302a42d41004c4091400608610f251150200726040055a003500040c0003a00e81c1c034070005040100751000018080605069183d40860310304140b1080c1c255580c542c650b0081040c05500c0324041840d11454000b0b5404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 531769676 1250 531768426 531768439
    0xa1505120c070b0c0a0801090603030806240f04180c0905060a020f010c03051e1018060b07050a0c0f0b0301031509060c11150108030306040c02033001050409020f 71
    0x1c40e01441841030154410180820346081c007030060550420b0020302d56503007140c075081c4103aaa2055681c0403204284809004070b545940060803034a00141ca6480146030b0300d40c01640114085c003440703000c0d0482c030380d03040d001180010144182d0740b041070384000c915002502030114218180c4001c01108181c0300d86400345401003038003c544c0b4000c1c0554030314060800000c000180e424171005010308400d0302c0c12811441c9105d0004040d500700e0100521610002062260a600e026103044061424103242d01d2040d81d1050007041d50081d143c01041111700400081040c0510f0342008101c3d92a00d9100c20032405030384400304202d204c041e090302d0469800c14070300a0a10381030030156025052042008014500d850991558a80c12038030440c54206904225a4040c0d5441540d0000110038011101540d009100040d8039280076003054550130641e20503681403005464004031441c1d140c40710010105041c039219440440444d0101d80105005c84080c000700046030041220b91054002d075501415 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 531770926 1250 531769676 531769681
    0x907030f0f062d0e0c121e03030709210209150d050607090503011a0f0d080d050a0f110d110c070608150d05062a0a050304020a150512 59
    0x7079a00312421416030046401c1c000000821800361000c40c0d00c081d0401c02d4100e00c000045004141d100c0c01251800b80d00041c035103502c80c0c0081210200100522100c0c40c4a2540502c07441d0a00701c0c04110807407110401580c4030300f0001c0001e4900820740e041981c10001405408884003580764140703030302640580f0343c6101500c582c0c11400c070520403100c1301500004c040702c41c03208020300081c0b1170f031240102ea03464808035a2100c08042c2a2030300018880d100d4044031740e000303801d0b01c0c180c0074101642000405907040304000c0e507140c9000e60000340900d82c0650341d40007044003405e140c0c01441c024480c554001c01c01c9407500421041140203410f001084103030340300031041035882071000325480014840100caa20903605ca1004104850458400d00c900882d2540d482e081d04008200d080115400b10290555a90381c0d05059010342c45283d01000760283c2000654900300548020309130140a80d0301e440d581e190170f0041c05007824280e803101d940d1103044185100720700c2c0d100d4180e801c1c02e44850706488054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 531772176 1250 531770926 531770933
    0xc0209010e0a14090d02060f01180e031b0303011401090303051804090602040909380c070f06050708060d08040b09040603020a0b0417030309030f031806040c06170907030f 75
    0x3400c5458205083d00304440a000c05001e000070108041a596402c0b02c00d140c2e5a4512044058000c1c41488240801d01040d510515880c0d0805403584c1402c03404c50b420204001c6c202c3d0007424074035454841c5c81c0c000100500c01000d0010454030907110a00303152100703910b980da004041d1312400c02c0720442e499100e00d01c1c04440c1d495821080081790418400e54450f40c80c0c0031a0720041c035518201b180c900131048101300540e0107050310b484948402d17080000110132020110300d841d40c801045101008400c206c0140092001da119200e480d000d130740001403c0c034040d240070300480c2d0050403003072180700c4100704080010070749000c88080c0c2e0b4010038000e0300d8043c0ea50104001d4800c5c0e410003940311420750000301d01d04441d10702820444008584862203200072020071500c1c0e200c282c030300030301c150810420701a0660f21000115004200c1c4c0030759000a01544888908041c3e060750125604000b562041061640c0448c3d00030280c18030000f242d0060500c04849565071081e40310080c41e0000758201041403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 531773426 1250 531772176 531772181
    0x302030406180b0a0e0f0c1002070f0b07020a060e0a05010f0e120303060906060a08070503060d0b07020d2c0f010212030c090a0e0910050c131202040c0c0209010e0a 72
    0x442c01c0c2880441d25010140f0f01210b490300111200b2000c540342201c3c98260074000200004500d5884028203100f91168082c4041404030a19a4065101d214000142c80741401c0041c4002e0888240d2241c56400320701c108074000c00300354031010411540910328490f5035160010301c03044500274240444082000340055038012202030380355501c04c010741440c1c02520404001540b1444040361501200d03a60181000300c2d034054001103600190345100058041d901400c000c54100e0401072113400c00321510781d516421000110b4082d17006820a090710040d15400240d50900e54020160089820500d070407000d405e66040e00003d44966102030a1400ea40d0003445003280f503d2509072125540d2400320028420b590241803854081c0038004d80010b0201a214015409222488003610b10300450a001c9009400c010b40902840c0e041004034804140405041c440240b8003015050140d826500400045585040989090200b00910080103a8510075198190b41003095802a16154103074600300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 531774676 1250 531773426 531773441
    0x5060f0d0b0a1d090d020a05031c15090b0a0e06030c0127030f0b010509041a1b0a0903060b0f100f0926010c170601031d0a08030108120301030308070302030406 70
    0x1c9001840c240f070a0040d001c0c0b44903510420592084840b0000032003022a5500a00000580290402d0140301e242551900345507803812141d880c04107214480004241c01340300c017540545001d50340e5040f2014103041000421000f085103042401c002e180400200351104107500b0613504101c528100b10950601f144518180001c12601071203585407249403038003070f1040d01102503d80303004080001034946442600346102e00d9101c013803118080c02d4a4111600094050401074210244002080c20300c00c000f005031241500340d5943c606041d00d54200502100d003500b0754070740105003d158008240c1c0791040301004081c0ca5140001c10710b6000c1c482244c1032071084d000741c8007800305a0440c80b1490100000e421401401f0002001203000c15030b415101d448103603101103040081c410000f040b641c02940700b080c4108075070032114604800078102c00e0610784003c9040b6035203240440144882c800800c201c4104501440081c1d28550440d1409004414003c00c90350030035400100003810000940c00854 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 531775926 1250 531774676 531774689
    0x81608040306090501060f3003020307050a0803010f08070b09010e01110f0604110102060601080103110103270606081b1e0303030403120b0f0a0e1e04150605060f0d0b0a 74
    0x1040c3c031501c1c41c0a0b0b0281c070b00c0e8460320b20001c0e40c503880030481c4442030080c240107080100d891060910481b09400700c3c0003c220b000e40075408140545400304400b07100075148103100c0c100c65540e17581000060700800c00c507904800300c194070801d0180400b541600440300e25003000d00b84002c07070008600048a200c0807020824045019061200070a021300082c03d03401a071180a41190110502004aa0342c48044600c1d500080428004001143c1c000418442d920010f14012031b80014541c06100d0a24070451040b00000c1000020b006020491040368082d12009002c3e10303405500315806183c861001d0b4440d4480c5074080814410300520300062444800041d0a680d12850a428060000100310f104908500c2c1803190170703007075498980f08030705003920000c04007540d440c14510000f1081100821074101001000032100c040c0b40d00c0000c040c45180306100301c08100c0212184c460688620740d200382d004040078003204040041c401c0544000c200200000100c003407808000501c00c10b42030340841c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 531777176 1250 531775926 531775931
    0x8150613080102090f010503041e05100606090f05010201060609090209031c0518150403030305180609100606080f0138041a0909060d030e090a14070804081608040306 73
    0x80a41c019006040b85030002ca03941d6070042c010390700548107403200701c50041400c81a003225a0719a9403c2446e103402501a100726203c03505904018011101941c00900104051440030025035200c4400f0001a1000707100078000a8681030002c2c1105c0141d000c2c100c605074000c0784820f8103403020000500e000444100340d0031241c01d54032001d0610340c4620007824001c101e04070402d140d8202f0341c0040090145514020340b5003460f5480c102c004007009841d0340103800d22000807042401c400c00100e4041c02c040b07000380c000c0c0000240242c0444d401035000009002810b001c00031350100e40406641158644d900e000240380341c4003800311603101c141c11036a0619000042b2491003540d004040e0068a2110251581c030360b500c2c400c164441d01a0b101c1190b408a4254000f58450500d0f204050850303100342024104055510300040c000581154030030440c81d034171a10555000d8090b01c0880c1c201d8410b04007101c8508094503041e0943c452440c85503100e201006102c0100002201100c00958005104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 531778426 1250 531777176 531777179
    0xc150915130b12060a0e1302040e0a0605011d070c12120c09230d02061308030304050c10210c2007030b090613170906070606050301110a08150613 64
    0x4800154102c40b000c508810307003000c0000c1c2c0e81d017845c07802d42003914500c0c02244443c0c0d81d0751030300340030580d5440002c9800c662940238506007540104202402a4800c580c0410698146500e0318440c15102d102c00c00900700440510801d5600664030500ca03d40148904424030b4803404180e40708869034444001c02468035560950351360b0b00070458000e441c2d00c900079100300300d41e0010000f00303a0881d03501a80c3c0003100d000858010718200c8003c02c000180081501821542c810329241036030005c0f141a5482d4001c0e0340032406078039190184540000b000e080c01d040303086d591040d154a40550b0481c8805842da601801c118030f5018040214200440c074883d4407003107010440305520b81050707200407510702c507046011851a44012509a1003160501d450902034946034480400303608044a11070122001001004910340301c21005107515801180301181d0b1a160400b8142140c552100c0380c103060200b401840c4d5160380c1704000541240004004091440000002902500c03401948030030110140e8030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 531779676 1250 531778426 531778439
    0x1030206090117040b1b0f040b0d0b06040305060a0b09010e0609101e0806090c0d03030c0c08120411100c06020705011b02150c0406050910141602030c15091513 70
    0x1d0584200d400011b41740103105000034400050040c041d0305040008140414004c20610034060514288a01c1000c0307082140300001c1070403580b0a401c207071041c0d007000081150300c140740e005001260005856012007076152582d04d640425010f042d140c801e805100104800c6069151040c1c0600920921180321a8403202540703141012840f130b42d146c50080c0b400241e01701c100440c144038003100113800540c8000160760f00310001e220300a421803e04c4607002981001c1007201014041494062914814500b000e0070241d0b0911110440d8034401c20354005e030080256480403110954a511007400f50301d82c9914501140980b42d80c50025803405500c002c10000c0395030000345000b07152070307903201d8640307031f0311495824041441940600b10100340100152112428403c2c08070380d1210140c0b5048280c0506e00e6040300503a031080c2d00000010b158105141d0079454148010ba1035030300d00b00c9180400d00240207071503486000e100c04141c81584071391050a54400b00710101c07074120388070000106050391030f0030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 531780926 1250 531779676 531779693
    0x1180c0e190f090209091902010c24091a06060d09150207050a12031a10050c06091b09040f02040213081501030605130308042a080309090f0f0103020609011704 70
    0xf02640704802c0c100102d01c81a0000c00c80e0044015908196071103080190019598503141100c211001e0040712050344a0103265030041d0f00c500610740300030030340d00c4140c18007061403201c1803450140d0340596004d004042e03031110700300e6a0340c01e220307480030a68041c1e5050010324240f02c0c90300009003500000f0340100700400451003828140c4101c003880c030500340d81c0f0821011200a0000c0a018029180000803030b4030b480107100e0b880c0d00c018944a071506034024003142c1005c03400d64020681c0e6024900010300401d0981c024070a6040a60300022545800d44504001e1850a4030183c021580000d40352658440500860080c100380e0301102c1c0844034a00c02907907014424413040e00c01c10b181401051920800d2490030040c19050354a1180e10b450b29110300c1c0741e4140d860040b200180e86101016010801c170702000d4004c00c0000055a1121400e00034441c44003002020710b9500424001008691042000c500d41902c3e0161050b6840c0c01001300142c0346009456811024142228100f000300070061 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 531782176 1250 531780926 531780941
    0xb010903051b1203030103051506060d0e07030507140d15020c070f080607050304150c030b1008090d030606050a0c08090d050105150619080910110c01180c0e190f 71
    0x2034410488a128a12419413240001c1c04020440e400150b804050300c00181d41c4d041c2c014400410b07071440d141c0030340846070440d0800486200142c100120800500005210880c0202032032012011000140d00000d050301c0c09801c002003000001d00c1c45500d80b105180e050325080e400440854903450744402d01c85048103124403e070140c1d84259800100c0251050050741d01596100e01c1c880002a04000c1030400f0385040c1c580f52040540d5020203052640c0e07a441113014444140e2100c818908101120300e0908402c00080420306091500801c180d9070f02102705e0721448064035140300409180d1030119901c0c416028400d51040181c4401000d12006510060060f40c1c41c0551000e00d400c0d100c2441020f01400c02800c120503401041ca402040c011401c0c0b41c2d00100013019144c1140d958010300c000c881008102c0400c02c2408154441013880911603547c250140c1c0381c600c240100e890b0b481440e4503020740034402c0c40b072003184003003420201406000c3c0e40107800004107008c0003140031421402001f54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 531783426 1250 531782176 531782179
    0x308130906080718060501080106050c0a0203120c0c10051c020c0303070302092d0d0c03020d0803040c06050f03041e210e04020903030409021606020408150105061c0b010903051b 78
    0x415984d019000003038807958040b180180c40b801d0701c0f0307860a074080c5c3c0c041d0130003121160340d4000e00581d140141e40c03d1102074018800f540502d80c6a1101c100414605514000018020908100c05480041d008419600c40820502c6c1302c02040c80d810346820041d00400c10614040c0c0f10200a02000b275402d5005482c0e4140142c0e0402c0c240d11041d81a410a040361108404034984507a80c40c1030642002846c840c50705011740f8580030754544d00d601180d0184034810060b41c0d240c4001c0300380402c111034803240d900245001c0c5015401c0a0010342041114480580000e1681046003410419101d10305003007140079400044001002c040028080021170502d44090f0001c1c1138180c0d4100c1500d4184252010040003a0042d4141803c1c0b6602c03000a42c007001411035070251100325400042c403580000d1024140020140410108007001c00010980c10782226100d21011b1003440106080d1100c0110b2005c00980e0110382c42c0324000060313400c640035800160041c0100728140c103024000c4000960748039070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 531784676 1250 531783426 531783449
    0x1090302030904050a140114060708042d080309091003120207090c03060b070b041a010b0403060c0e010f080723030906100e0712020417150f010f03081309060807 71
    0x20394810b03c0d400c48406c0c01d03d505160750b02000520142031108007900349500040c110510b000074070b858001650b00135500c03280d1100e804048000341c50504e001c08000348251500c1c240c1602d030428140c141c803806001d0799a0f000c3e841207000148185545031900c801103030040071408080c6002c0000a4071039080b80100c07001c1030f0410312078500040c480d00c00c3c0300468404000160800c0e2107035031400300041001d80295010803415000e69108803864440340d000b0455090381d282d60754a1850aa01503d040c850180180b00c5a50154011030742c2007841420a01c640d071514012a039190001a100440410409410032070908220a0500800002540190101008c072107040da1020000340841c2002d014a000c804003a001143c0d000b0300500e101c44902060383c901508140d241c03a24894a05018412045c096018040369400e4040384040307190802c900254500896060041840e801c05a134440103011000011304220007008803c0000007501d000601031040d2a61030010707580d1010503008607041044c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 531785926 1250 531784676 531784681
    0x5040c08150f0f0d1a1303030c020114060f1807030606090e01050a1a070213050105010806010e0a150c020d060c0f091404090515090d090f03050a060209120109030203090405 76
    0x20341005a034800c42c0005001c215500c1c01801404030310031000d6001ca41d0b2004406046000c841c50b00c0400e17100d00d02c07800f40f21b01e0004007410000d09840b5040c81d0103065902d400340888100f0080203d1942c8400300303498500703800203240c2c0400d40c8024000c01130302d140ca142806018906600d500000100c61066840f0317131003135889079041c2c0b41946003031141c0c40c1d004010060802440030b600c0c041260000200e0403c0e03040c0703401500401d511410a828419800b40e8800c0148055030300066030541204084c640803821400c20008a1040011401542001d0200606880d041c0b03100781108403000f035025114820b881818540f11000e40000d1607060b001c035000360b10b050000c41c851107403481101c6000c45960052101c180603c801000e04100070740352801581c0c0502d202c104200c0030076001d902820010284480881e8008090301a1a0000d824443d0b80304402c00100c4c4000560b04800d5422031030040ea1894081d0014038140d0081543d03081c0b650030607003000240760b000320251201c108180c1c3c051000e076 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 531787176 1250 531785926 531785929
    0x6160e09161829161b0b0d02030118020c0c091302061804060e04032307140c0301060602120306100e0307030308070206070c050d080a0e100501031103030408030d02090a05040c0815 79
    0x2402540c06a00003010900007400100e14607240301c44900714010b021018003901e991001000e0790062111f1032540340c000004110040441c1052020f114140804505205e040c5013020340b64045820030740d01c5041d449011a20344800c50b5040100307268010b02c0031341c2c4c80010103041c10255003190b070142d00c03491608034000f58260510503010b229036070598504001115803110000d400400c40142c8000304c20600481000802c090000c01030003200b400103050340c0d00070000301401c0d903074680c0100e411504006080b150303d0303080a05a1b0380200007161f00c6650b0b0200c0040454403a61440d01e155414824403d001007451740081c0081d000d903400d079083d2201031b81e50780c0060701c58141d1000000c000d5800401c50300d1905224800c04c079001254100d002c95100c001c08403031858100030380b00040d005691003004004004000c00c0e2104980003e40145040600d00301c802901c0c1d000300e00340550341ba84c0010f581d2030503644100482c0003402000380100301c410b9085800400c0031008940307100408045e20140b0040c0e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 531788426 1250 531787176 531787259
    0x11040f030c14150304060b12060612031303030e0d05030f0408060105012109030c0204050901061d100501050d1103040c21050304090f0e0f06160e091618 67
    0x30003029012201c52124403c07240090343c402402030340c0c140e81e60700400280d41d591040b0f803445400c00e10000c00c0c40d42400810040e134040126a4064154000c10507002d516407060041400c494041c01c0550010360720402142031a400e00500610034040020400e061a00b214003400c283c602040444419030b0302c802c0151940c03d440e403548034203d8083e100a20881540f60020300f00f0074880e00e490468100d03194081400d441060322202c20a07511010b09018001c0821624035141154800c894100e050074080f0b4548810b11b0b02440c2e0421600280001a104141d040680c0071406600d00d99520701c2e09040088125400b80a20303400c500444405440e404580340902ca24140c101014603d0186008091001271840040b2446203d80300c00704448401800c0c0402000103007100050400c80c50003045400d207070180160f000050100c001d1450810303440390020164407101100404880c0101c81c0029211024455480003068203401d401141703082c882c1110740214401000070145c04504200350081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 531789676 1250 531788426 531788459
    0x902070302032b0608030301080d1806032c0303070f03090b31050c18070801030b04141b1f0c020415080604080c06070903030c1511040f030c 62
    0x582c800c0c04940400001242010580034140c5440c90301c000c501c2241c2415101c49034001c4016820100c010231200005120200c844051171800e00034038584c07101034542c1100320703019140070142e0307481c005020b00c5088108035038004c80c8003041c00410000d61500c260f40c0c2d4001c035207540018505288054010b070103170041d02426079200d454880103a4a4a00c8964051030b403860030305a41010075000441e0034052044c0c01c60150282024000c000800d100380401c040c00308c800a08520303200007c03c0840355001c120603040d00e0380084200b030182c960303003046140b15031076908108503401882e8182e58204801a800420100e0589413010a4214859100041401030030002c0200d44000c00480040c90540e200401850400c014900010b40320200f903460308a007113a00700c498840000c0c2100d0501720400c4211740c01011443d003044010300303540d001040580c1d10103000b01079a13140050246d00304050b4101c0c22000b400024902d49070380c0e07955000c020441e030b03e20003500c84040100000c140c40010144106 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 531790926 1250 531789676 531789683
    0x2070c0510120e121206190302030a030e01020312070f020d0503280f1e06140d0b072a1b0609061b05030301060801080c0a0e07030b01090528090207 65
    0x2652102c8905a030040d001408403503010740241e1004085100700c00f0080d09a1010242c141030141c80c02c0380030f00005503000514000500240c0c87c00300010380e4009607601d1626414913100101c1c048030703401030740b07507024041c81044010700030b004010401d54441e0392038204402c69400c6881100c030150094035644010b8889982403400c0e80755242d40c4074030500b030800540054080002d500c18840005d182212070760603168444200e18072080d20f100045000324400340580810700c10080c044280040d1100d9113450000740040d6030080095100c030b00940d0b01c60740f03041810207140c1068120032144003e030f90310f020080342c0b852107940c0d08a0444000c6210344082e41c00b10b84a298090b03081c40d00650302845600844800455213810300800500140055402419940c880c1c50865052107145801c0105200d509401038555000070001c000125000c660824540d0030300060142a032001220348004540241d6040303680c92803408070890020410b00f09400750000982907040d200c0181ea0160b22442e14090f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 531792176 1250 531790926 531790937
    0xb040912030e0c0301050f181b0f04090b0c1b0613080304020d0606080c0a0603150e0603030904052523210a06090608030702010c1101200102070c0510 66
    0x40c0000d800781d4444002c85210a003103c0b070f090070003400682135640860320507074404c100710b0501c120000c04440d0404852041d102070a109010714400b00f9406101030002c0d4483e174500685010291600da200c48502500725a2941e40e92070007a40051081c1e00c103002e449094254171445405192002c20f4a900072000070f144d0741c00303121103a00d8004480d0009082644d011001d4030035100083d150b8440c08004040100c050310350302030f28500b00324012203650320040925041c411421031301c0810080303000030360b1903e410401c000d0f19030070003180c0707140103607036149412a01d0031040c85151165194240ea00f200007421546485d08108400c55100881010b008640102d07580030700001a008409841340303103100d00700d4603481d02c1c04d0003201355000420380c2d280074416030b00d160501803500340740500d90282110b04010352401806a00080031a100c001029101502095108070642e100740e1100102410a2a04206100441c0c0089000398001075088503075160100f00000d503420403540d000c20301c80705078488 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 531793426 1250 531792176 531792203
    0x11100c02030a0809010e06030a1b212c01021309060e070c260a02060f06130f09080f040f050102011b030902041d01061403011104061206180c030b0409 66
    0x4a4500d5004001301038148000041c9810482d00d070000a98801d004a510100301c00480d200d0401c4c1c2841042c60240030000e0000900c804155681546072000c1b102210029200d82522420000f08181620b40f11881401e884681942c0300150040c0003d144038190150200b0b0361825900d04540300381c845c007015130481c400091021401004c21001180c013500c403010b40641d04c5603d02d1444010700c48200c1707404101242202407a40d0401c42150f002c85a413160030000e003800030004103c004032442aa5140e51180300c031202a00c80e03034001228055200c203d050f1076280d1405802c80030342250040c80030040e401e0200182079813050058020403d441032812290302500b01c0e04070054030342040c0a0f07070000d80380c401c40c1035255140b4206511840040000051550030404111400030b514007080f48a60304140c01c002c0d61b03828480072070f000c0740c58a00f03020480411107140000900000d82c0000791000d45410840409006904601c03142c0d445031307400304034132030b00320003048121010918050300b02040c0994 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 531794676 1250 531793426 531793433
    0x408070612020c070e0f0a2a020321090d030501060c0b0c0c0607051309090c0e040302070f1404060b071713081b040e030307021c091211100c02030a 65
    0x111031030581c0000c803015103040c0c0c10706034943c070784041940048120394010003001201c15401c5092a0040b606c07040900944445500001c0c4000150401017528048100c4004916000300b0498003c1c010180050408203200d100318540400200c40c081c4140c05140300c0010900d20900c84d86040c2d9080f9180c140030140a07490304641c511b0002c0449c00210300412490000341402c004040c450715481e0341e52562a0101141c013040b074100c9500095071981809241c0d8009561404102c080c1c440032544807000382e0700ca0804034601000f60b4440190300c0380c0403c0c04111941030360700604c0c0c00c100aa074144020759882010346444d00c1001809021595004440007001e40b440c4003c04440100c7c1000d039046179200c1100c0b504100b49102c004070362401c8003a9200c46800c080c002c89411040f998040d5045241401c006901d802c2c01d00d4240700340c0c400c5800d911300000d0080d0b00400240c848a0320158014405142100604610424251145c2038045925980900c0303840f01c0000c09030b0140243c55604640c0e034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 531795926 1250 531794676 531794687
    0xc050904032309180105041b050f0c01021303080904050f0114040e16090b090a0b010507060216080a08150a060f05032d1b09100e0f0402191404080706 66
    0x140044140386003003058152130380d81d0000c0354008a00090302c06809500d440100000c03500b042070500c103468101c00740200c03400e030080c05603600c1d80800481c159456502c940d4180c02803090040740010b0040b22f14012040c000850302600b41c101082d2010003040c1c071481000d219a0b0400d10030100c083c82101c2d010002800d0a801c01c50360b1080b071790120b600030344c6005003a816800803900403000b207a607a042408424940224a00e07009211541c0422298076407000081042c81423120143c0115000542500800a410840003002e074001e440c0c030703464061500c001026058140c85200714201d000c81c140c0514540300403c0011101640c4981d000c684480c6400d6669401c0144454242801c0c0485400f42e00d03448007907524030b054864007250542c641880350303241da201128502005200e01740490002a00c0d41c8001c182c8041090400c5491820280006507102d076544840540181c00401c0072504010402c10342c40c0046401d40b5148030081e108041450580214465007100d0350241c88100152070098 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 531797176 1250 531795926 531795977
    0x60e0a26090f19080105090a060605060a081b0f03010909030e0901080327100c0b092a2809060803120703020f0f0705030d110c1b031e0a0c05090403 65
    0x403118640f20b0b07682c481040c2150b00840e251152034100202076020401180308600240500302d070300d5800c00d112980e0003491450010b01200c282000d88144034151742e41082600c0403428180e144a9503907854604d260302800c207940c1c00300c0c0402c000c1312040502c3e03d802c0303503490706958044c0011410800415611245028a00c035800513290300700300f44040d43d88031804100344028840d02d070390b010702000f4038000c2d529183c000d00306a426005180908200e5100604483d2000c008816584600c80440009070500c0e100308481000d9215480e0204040b00f030301d4850408840c0c0400d0f040007040e0b41c680d0072503242d10542414820080744000003d10041c0640c0c0645514040256101c0c00d2080c00c020080e0b02c2c0c2c3c860402a030b0150300c04600009039618500030f0380380400414031018240600c1d5002d040d84e486c40c0d0f41e1404000f050f81040101142c034100100c3c1c03585881c41c4050a908164418490340312001d2880076284005090004070301400c2172404c42d4011641503070380a08101d00c40151040c0e25903072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 531798426 1250 531797176 531797209
    0x618040803100f141f0c0312060801020d0e0c010201090203030d0e07030203100e070b040602100e100212060307060e011710090203040b10060e0d02060304060e0a26090f 74
    0x34480003043d80c9202c0481c00015144032956100202c02c05410401d42820b1aa40f903000461810803500308503030701c80c2c12110700715410b050104000c0f100041e048050040c50300080541d41c8040f0f0f243e01c6c1c51000b6007040d4980083d1205a0301d070058031a0049090f1074041d580690180c2c802c0151405d1100d45a0014886c0307551038003911252a2240d00090a0202c0d1451035050103450711a16070410105011000c010807007214002c0c901460b080b0081c0d258480f208106480541d40d400003007030090b081c0124a600b031407171103045640325454020508101c9050311180d010f0b00c2046030200d4043c4c043c10040703945800586909680c00c03407030020520040d1000f4140c1c11292450800004c2828090001c2e50190307126031703d4807865207480140c4001c0d1003220740c400c00c100081c0f6000030000c0d4403a00e103100c0000d070b0142c44403966543da80c02c0000103441d0b10706980c581803056445480501c00c0c400d40301d80401c044a1403003241c2c20086c06003e0f21030b00a00c0c00c141e1f484503040031170f45502c2c94500d002807050081e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 531799676 1250 531798426 531798451
    0xa0207170705060c06090706020109020a0902131503141f15030209030a0317070c120f020115090606022a133801140a0c0311010912080618040803 64
    0x84a0000c90350f150070000c0e00030f80c3c5501540611400402c00d1008001030300081c07000300710203042500003402d080f995114600256600103210030301c103c401c4038980080c040b0744122810ba1210800010001d0049090001000c0c0c03908012440d0b001c600b0810003440c1e080c400c4007c15190600540c40200b5900d54081401c2c1039080004030030071f0720240312505a85000b0340f110401c0d2401144451000c49004200008124440300b64000042c034611f41442d0041c114a8020754135881d42a00740e0060001c00f04040040406000000303c03041c242e004a42030700c00b19400d95140c000e04802c8404801c0313140410307444440c841646110141882501c0154500c52044003040c00c0d900c1c1c2202d8401c21440d01c040020b102540c00285400705040140180112420311b0400d10111812030140742c10700915004100b0880e0001c001c8003851300c40d0619120ba03109500c002c2010421a180407591503001c42140004200a40000740b62468401d640241c025040c00b60502642e8590b901d8155980c0f00800c04c429048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 531800926 1250 531799676 531799679
    0x6040b090d1203051e06030d0809070506040b211e0a0209060c060f07020f1c02030403230709020403080a030504080c19020316031a09030f03190c03020a02071707 71
    0x8100300b501407018801e68a0000380c60801044104024200c02c80e50300580165000b8080141c0b0000381621540300603103064035164075548185418071006034801b903448000402c0215090340329270010212503640104483d0000071862814410680c200c2d1281c100500a40e402c50f1610386641089500c414140d0f001480c00e100200000d216401408041c00a5070140c010807a80400c100442d98202c6141d00003461b01d4801483d0003a0744480c1c904813903100c0820001114034982c020000d58000d594811441c0b80d065007454100402c1c45d610703c5071812070f84501e41c3e0020b1b490350f162003141c060700c0d0811f462500e0981494419000f814001c0d10440e2202c1c0b040025245200342441108100c00c02050880306012a40c01014074021100b650f0340d468aa50402c2000042d50354000c0c4c0381100145a2180341950310000300c076042d4010b102101c0c040b01ca0000c00c0051104403203043c4c0040304c10b40f140400c440c3c6256141242207000d507842a102513404050180b01504c200701542040440c50000c0b1b4646a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 531802176 1250 531800926 531800933
    0xf040c020a0803190903030c02060916170705121501050d170c16091401330302070501060311101d040906020403050109080310090213050d0f0f03080604140606040b090d 74
    0x50720745c448150006607a80d40000400da03410702c54032740c0240400c8010180c00410050148046851340f0500c0c020040d29024000403d4080c480c034401050020501480359041503142901c0c3d07a061500b03402c2c0c480480c8004102c0307152200700040c181c0d0300803141044108054207020011b9114050300e41081c0b085035101d8003040405000000a050b150b08045411155200d495000d0001a0440081805006908007a02c0c3c0300800382c0000c41000008054000121003081c0d000b44034007100588a54204507010045c00a03404131078a0030413040e2100d1012003582d480485013400302880d40070b5945074038050055a864540c01c1034a10070f0049600520b050b03540d07661070f0b00f142c4910710119084100881001041d6030880c2005008000100c0d06519060300c142d05600c0400c0b090203018400c100c0c9001010a00800c00c40703d101e00b540c071440503400962942000741c580901200d0b41486103080422400901d9040128503000302c901400740d60500d0308101a082442e0070100c0d180b600140c41e9060b03800807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 531803426 1250 531802176 531802181
    0xa090f030207090b0301020306031002030709031a150102150105040c09090501030b060a06020d09060528080114010c050c060904150e0615041d0405010b03030a0203090f040c020a080319 81
    0xa4425001000b5261600c501c10040c0d601109030144203910610810001c0d80b400710f0524692000080010781c0caa40b4400262084c0650303400c042c140d0201e03035281100c0010008002c9016400e0103000c5040d03001d03400012a500c103030803441e210440304450700402490920360080c0e40c207000c050910700c1180e034880c4110400c840e002d910658401c0d04a0050001c1e6041148144000d485584041c3ca10000440710141c8180f1440c400c0e42d0070080d00007041f01c89130340d070400c40301c08188507138500003034003914100300510440c000e0007400b40c03e403000c101d856560740c0101c1101e40815882000340c080c10b544c0008000c503a8001c3c0e0669a0400d480d1501140d01c1c580140c00d000c090107400100d0f040c01d082840a0044440d80e80e0030b54080b00908020a020205951014145100e40f9433881c1c0380e03960762031801c24050171002800503014030010405207031954001c030160207203500039a008022a500007040000744e03220000d0440241c0c102061030404102d11340c00139039105083c41c0050750000e0261015804 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 531804676 1250 531803426 531803453
    0x209040c1a0d05060108010e0f0c190302030402040f05190e031315080603011406091005030f100f0c050322020907080711011a010e0103060e04080304050f070810050a09 74
    0x150400005a80010302c000c074490a034102d003080c60480381d01d6041c021003c0001c200600312420001d4044001941c25191b03e04841070918106e40c2806001000940500a504280c600300d2086061a4500710b0710842441018481e282c1c0050107136050a2040c018030003455418080481c82c0000c002c00b4024402e01c0600500810301c003443d01d4803410301414003d180b660040c10790b0f882a410448411030000c0c3c43d4090355003041c402c4a4082c0b00e51114001e24040b14081d0b80103503094001c1c1056541440f10101e00e11216040f0f4480600ca114004400c840c01c640d54020303000b010400502c0843c50300400244882160b50340b0203244107144420340c00042d406201181c5610000300c801042000f1241e10450121007410520002c1c08076883d0340e20b903194541c03005491039040182900001040780c0c0719400c00c2d401003100f02050400e5051500380f8003500d0380112420748140c4a2012081d208042c001900001ca0b034040000e0401c0b0ba00e130044080180a01030100c2d40780f603450314038440114484086041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 531805926 1250 531804676 531804719
    0xf0f0c21021c051e0a0209010905040c03021e0a08010c0e01020115030602090a0f030f021e0f12010207141c090e130c03150b042306102106061d0d0209040c 68
    0x5c810405441040440c01c8143c101030841802c02060000040c5402240001d8a03412941a804000c021801c18022440b801000d80d1207210032000292209041d030103011691031170703aa50309015002c10011b9081ea04c200d90007100c884070150040011030044d60290103118070003080b8184440c1d580c0b00140564216800598003028000c02460861518030140c0001c02001700140a2944520340012011000c10401c58007131901e190705100d001c58217504940c0d80307541c81030400015070b4204204540c0c0e1000c1111207121808144a9813000c1c0c1d000380c0c652000c0311481200c418441e034901034082419008010112070300314800c0d0001c00000c007503d406400311010008001039548114003000142c8000c1030007072200d0311100105120a0200c0b03005076a0002c820344006001d0350507220101e80d8644007101c3d8094008900400310720300c007501c2d081141211183d40d5035115035103900c65400c61048200940962203003824100c0320050a00c100010b0b4494000c0b28840d5005942c0c1812a0003441011900b6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 531807176 1250 531805926 531805933
    0x8070b07030501060e06090d020f0a0305011d030f0a030221040605040b0a05070509120a0f210203040b04090b040b06042c04030c0305070f0f0c21021c051e 68
    0x40c015414442e840c0100041e14003242e841ca01c1e480170411030300c02e05808a001326456031601056481c0c501841e8080c0b82d014043c0012250340741012802041d400030022010344a01c035071424480c80c00001c1c0c420340010464800c0c83c02455031420780080d804031520640800300f20003454000c0701d103107410b41d1245001e08030206403841c19140903041200000e101e0b1090340e1820090005150703018064400001d000c0d0703103500100356a490305078074002d09091700070403134103411100c94204101d00e450740d20180074a41c0c8170740c220110018181d03168040e502070101c0d000c40130f200030072076a0010f410894031000701400000d102a200000f00d240340d8030540000340024015403182005810350560359100403151654654241003958005044110446010b42048800f08980d4140019000130703e91540d808a2481c07150781203454041d800c241644100408100d103406090a05044507129440729a4010001064454940c800034074550548005941e284545800d10141d00c203c1005000c0503c280ba005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 531808426 1250 531807176 531807181
    0x252304110405091b25171b010902150706020c060906060f030a080a030203042d14061608070e061606051605090630180307030909050601090308070b 65
    0x34001511800740104015024034052500d10340d0380d24040e20701060464000c280c1030020741050703070340a020300080581b080034412005480081800d005100d01d50a00160303601d01c1184031685e03070884102c0395020350400c0e41f104c483d000c001c007002d000f0560584543c100608004805107a40d140c180308455100c01684200e00b440841c0c58074100f51041036404400625000300d543d80c0e48822030207240201400d25401002140070840900c4071550001e4900707100780400d10301081814001c60080c02d05841c541007410000382c0d2098003040307045c4108058481ca0102051889003103c0d0070500030040c6042183c000f10400c56560f841c40105401000ca00c83c0540c0001141001000c842e4054140303c0444c507240c2150304910740180940311910310884402d904c070391180d10b500b80444040f1000410f1900440440c400c014451140329015000001c81e400750301d10081540c61b41c1b03202d45000580403c5d40d102c020030040d269034018552000041c075010310050b03130382d9407440307207c6d0004c040803207000c84136004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 531809676 1250 531808426 531808429
    0x14070b0103111504150c12090e0a051311030f19140313140301060e0a0f0f2c0f0303040305031504050408121b0f0c252304110405 57
    0x9031908041c401c4400d0b0003094107960f03292450384224841c00d07010420050200304445c1c0509103100801d5000a0740c044904101e0800811004d1a400f840700c5006e01003011640d500c03050b2181c1d074810024072100c004800c2007502c4140311034400d01c0d0200e40c10301ca01e028242c3d0050050010700c400500709402c25211783d50340c2c60300900c083e18002d040150382e4414040f44450b003840000d600110382c502014512142d1090021a002d8110340c0c114807440c6000700144403007801503074862088503d2850041040494010900f02500c244004407000b01c4d0010313441d9060100c2900c12001c10b8060482201c042c0d072007043d4000d045800071101900840c0011040090060802c0c0c030f1300c5240c0703400f154200190710789652505101d00548103881c410040d4540040d1106483c0500300c0c049030711320301000340c440c031509508500c2c95103c41031071440b030300580b403040101c0f106400740010f451004101c0c0100e03030b500301107034601240f0281d038981ba171600c01b5941380400e0740c0b280d10070103507102901c1d402c0c25507c0e800e060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 531810926 1250 531809676 531809693
    0x30b04090203011d100203060d0b071115240f0103150e0103081c060f0e07030213080d0215060d1b03061803030c020d0c080c0f030c0c0f0612010b070314070b0103 71
    0x51405d18200d0041040120b02d994200640417490b50116802d00390362500841180c885110f00200c0d000e6100e40c0001c0d520030328070b8901c510b10a14900130300740c00542c81182c49081842d210b40c402504600400380c8815990b0194000402c0b03d0040308071640900e030780e0f1808001484080e481030b40d203000c0000d15408400802070703a1444c1020100421301c0924a8620045031000452007513040860004022641451082d011200714540a1a80030071040d203030401e0070f8035041038900410151040e07403140c12407043c608103014843d200092181010f0f41303c1d5103403241305186101230380c0742444c81e150003c00050072303a11a04d5031104891400d1081c1e11094600502210b61714040d581c213551100d0314920307180746d1014801e030702c40f98040c03502074451201076061894034151241640c521301001c02c010b0800040090368008000c0c04448200d500c0c0340400a22015101d00300c00d50f00c0d004042d9005004141c0d9510082080900c00e1804824212070b0340c640900b41c1d005030808440c030f82c50382c03001001400400c2c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 531812176 1250 531810926 531810943
    0xa02030709050a230106140d051501031d03180102010605210709090803040f11030a030305040c0e010f15021006082d030a0804050c0405010b030a0614010f030b04090203011d 76
    0x440070348844031304000c4070825804144124010400e070070010f01c01c20001841954036804008070b003072141d4240450240c84001c81c140d026400286800b054000000c410615010300b07111080156240902064120f10484901c82e44681559207072070380002d450f100e07200740c260303490f0004101032840141c40f8155400c1410b5544406074580c206208140030407444400c40341c2081d03000243e0b940c1d021844c600348052401c110384041d0305000d00c01c1a02c0034135406410070f43c4502d205852114109441b0005103929070750030f000383d000b2009100400d000c010a1010613565450990044035182040c40003071409a5000f178124006c6038010a8a9200c0340b015481a000c3d02140500000c01c1039070080d50641e40c03406030051038420400f0800110f02808020300400c60f2201003d4418441980c42d040303c1c0720315038410307180070106a1a0080002d1b407000066001d8290711016510410070448005045029040d10408030398030580d501592001603400340308001c000e00c000103001498041c280142d80c101800f1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 531813426 1250 531812176 531812201
    0x70c0e012405120c0c0a0b090d03061212050a0207052205060d2a090c031415060a030e0102090d0606151403010515070803090a0c08160501030203090a02030709050a 72
    0xa000b074200c01c9003c41c06076507001d5026003100c3c0d224200d03504824134050701e000b00a08203006240510200c40b0010030306000184698909000250740d508494003422351a04000d00f4100e9a2000c5414092042c0010305c0b86100601c101c1e04030a445170002a900710b81560b020700200d0281c864000404e090303014071a404a0100d0342d0045004132034649030002403c078070f250340c0e0071080d001440000c0450603000b4070150003074103010090f04410305070180c001c040c031100d91045c144519000171000401401c1d24014100c0160955080c015040750907409042c07130a40840d1075540038080c240b030b41e4640d00280404d41c0c0c0206030229444d4641000c4009418241c400c2008004140300700180329240c0d24102c0e0b045810a984c58050301c1161102c201417400391200081424400100703000000304000f500c50400d030b009904009680f0f5803203500304d640b0080343c80340000c646101c00082099602070b80c091903001030000700351424401d0035400641015850380040d81c020f959403040c018051014454003466468 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 531814676 1250 531813426 531813437
    0x170903031b0c061501020f01110d0506030303070e2e09060806190e0405030f070f0b0c030601020a0308090309180a051b030a0c120612021320070c0e0124 67
    0x11580901d480d0f07000101048206050a03890f2142a40b00b041021601075910740201b1481c031f402c40c4802d10344e60142103003003c05414100802d0f00d51030040104c038003412031034945440d002d1004050005d120748150b2000d0480c0710348400880c2030a42024525081e14955a0341c81142d81003071b8001c1c00408001d02081c0c002c10302e9043c1002c0e044012491329003034582c1e200a8910381c0d0340b28030b0054030358424a819010a228007103010300401000081048103903101e0b001419855440c80390b0701519001c101c0300c050042c0c0c0a00710311000b0a000d071241e03a8100320042c041c2c0b4078100d011400b10b20091889062024132030b000c0c10410102c409103103d0b2507005000d04086c001d0b119044840a1181e000140100c204141d61307046000b4807901681c140928100400b10900400c1e41e207900e400000d404400d000c0c0c0c001c9000b099043d9000d0700c0e42c07048540545000a44041c0c1c480c036481403d1060704103003c00c550109491a0101740581180031541c024a50f001ca0802c125080c0c0803007140d1500051240c905014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 531815926 1250 531814676 531814687
    0x1b030b031515120f0c060d06050d1505060d0f0b0702012c15010305150a0e150a1a15090d020a030f050d05030705040603050c091f0e12120307170903031b 67
    0x1400410b800117003082c215042034440c030161250600a080303651050354030521000c02041009412101e4142c0ca002d800030420440d031300c400c14458810481130380181214084a2a0b00014400c0c50806e90800d0491000041c0040c0075002c010a40400a0107031040690580c0c0613241e000b0100400203618140042040c19949547d90f025910500c1600c0080710031542c1002420034001c507440784a44030320840444100800030700762400d0300c650030341d401c0c01b595040c0f4003e20785a20410280e0103101c0740250032010f0a100380000142550813008030305a01065042c4800f0150b914201d420002d140074030302511904480345005460210000446814000107001300704040e41c000d0191021a8640d040214103580c8007581c01c54188240460544c0c03041281440006040445840c00f4800c100d94071514031102d82102001041c003004e8411281d40d5020031200040480d0040103150020941c0c00c0c10061003190321a0503001481c21a41c00741154008020014091a40589001140c9280c0265880d29 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 531817176 1250 531815926 531815953
    0x60e0a0605220903170a0c1b030e06030703020d0f020c210304110a0504090c080c0307290c0a0614060d0f170f0a020109050708011b030b03151512 64
    0x40b107901041c9104540d58003120018140038110f0340154903505454030280f494880040402407a140342e194000403040b03d5403801c030001c88070310125243d030076841c0d00100400d101c04004160380010820320426030203100040d5580801c0c00703041d0300b0350b00808015840c1c412034100780340340010644411500c000070902240c00040140112504150400d00031002d0178056004604901c04aa00464000707103040c107620184001800500103542d604010f88042a041e007003010703075903c280d0184070600f200f0b10644c00300c2001c4020110146441000781181081046101d01d42004100541078a0050b21366098842e05a911445160301c030f04101c54851170200113032a40d2400d800074a00060002d615980c3c003076582d10344a815142c5800d03030820b6003680c844003140000d0103170010602c2101d0610910381c0110351094180280030101d0b842028640490a180200714007500c0d145080035058059080410500d41c503920002d842600400e24800c0d071f00f442041070087e0061044101100360300400446043c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 531818426 1250 531817176 531817219
    0x105040605030c070303061205100e06060312090301060b0f0a021501030f060902031c0309050601081203060105070303140a09140c0901060f03141f0b0309072304060e0a0605 76
    0x70745043d081e407114058038003a0000c261039084100040301c4420200200f1400082e00301013945000420b01c0f00b415101c50a03955503005840701b41c0d1507040310142d06031781441d54001d0610508000c00200c0c01c80d542d116900d0ba25440001c040c240c02200003003419140d6010098910300724641e0721414200e61540c0c484010340c030030015004010306e03220a1960150740c0c003008094440707021031040103035401000c100940100b88041007150303103015500000610b4100414034207104055410000d02d10341d554001140c1d142d011010031014141d4400f00c210811402c042c14500c2803654250020b645202400e00c0861041400480705080e0f2190184108a03141c2540150446059040c144003445103000e06401030444000083c4000601500f0051204200c411244045c003035a610359240f00d8860140c15580c0c4400c03240e0b502c542d03002d4101001892040105440420302c0004564031040724079002405544290f807100305011400400e100b0410002e100d07031001084201c1b85c082000c4501c0d40510003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 531819676 1250 531818426 531818431
    0x5070302070501050a020a17091c0203070501180e0405060118020c070612020409090507060f020a0b010b030a0914010b0f0402090d020f220c020d0c020105090d0528020906010504060503 81
    0x1003084c003003103060b5041e000700a0080d0701a4892108a0103501d401c140c010329400c9007003510312480d400c2c60450040f02c146032107849200c0d0041c000e0b16086060034019600001c1a1303105d014200d0b21100000780d150361101e0070314000c5210754051300c10395240265040b40c603007582c144d00020310700c1000300381d411400c0050303010200c900303030b0400c1013640349444403c9000b4043c43c2e100303c5030b050825032540e0400c540880c89800f0794003d503c030110f90a50045080340e0f180341f644001021150b05030014014200d8040c09564440103081c00880c082c1d56030381d06d008243d1703100e2240403c26034440b000302a2628146000c1c1c210b405095070211f042600320000030781c0680c0490341c080e0107000c0000b02c4201f540c80b620031340100108400c0c41d261546055440c1000246076401070400180500d00004101600c02e6a100e9041e07034050351000d0030140100c0c1000903006a403078049403244140600111a40c48000d0282c1811b800c100c6541f012100500511025200027008141008403c01062224682140540b034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 531820926 1250 531819676 531819679
    0x90f0a0c090801060b04051003110414060d090f11010503070207050f1302030408040f0801060e0606030a090c0605041701050c1b0705040612060b010306150509041e09050607050703020705 82
    0x1811159440d4180d03070205854011241d15400c088001c9144241200148203d03002640c009000300b0745120214126605018410841d1100b04030800000d00500c04400c14800010901c528240c0000a403500300c51900400300d58540d0300003201800d02500212129141c4020300300240b851800c00c0b4025110070f0309000d414403822403c4148a655112500202016403000800f19500e06290510703007651b4205118521040001c0c1c01d000c01d052506002d01c0b03044400d00302d100142512550b0404c50203400042a540c0225030364400500440c1c3c4082000c00141501d484107551607052900611440f01801816819030381400140200500d0090445080034440068000c1072810154040d043c0201a880960f0040c20801c1c04038080c1545000ea041c103034402c1c0c2040003c1c0301500015410b03944544925400140d200e90840c2003540200e000b17103280740f001000081d0360030f402c8001d00001d600c401c2c581c100302ca582e00364541c1040000c012040d017086040c1801400e20169a400942d190300768050f0781d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 531822176 1250 531820926 531820931
    0x30601050114040504050711120a020d210501090209010311090a0b0a110114010f120c1406040515090a060c05120d0212040f030201060f0b2a0a060b040506090f0a 71
    0xb030b0b1042d008034250b4001d028010814052400c160324000c3c010400500c60068500480782d07e120146102c07011108030707440d150042c00c86940d420300c0940328903100b0300c5085503503007c8a488401843d580d109440c0a4a01d0040060711141580d000408445101001c904040000c10008103107641d1060004100c5040481c3e8a58514081800f00d1360850002c00c49041ca42c2402000e5580c03c0c25002100d0582d140b0039110918580d6844040d00e16103007031704000d071065002c43c03020702c232110711545101c2001901601140c5080e90f00d02c00320701202d541000d4110201030100d40c24029140020004005101e2403802d43c054050a0315103645401c85078228a0a15200045040704150142c06880c20b10828455070725803498541002c103100e54100004130015403034148082000404520240151000722094904020411074020f4a041e8401060b1200240c000d4016074515400c00014183c140703e010049840c044902c140400c1d0b0750003502c114481c0503840100403400310840e64181d40200844000b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 531823426 1250 531822176 531822197
    0x1051317091801080601060e15030604051f09062d150c020907022b02100b04060521060f0105011725020f1509070b0a0527100e0306010501 61
    0x34110119101d212101c0d00d0701e507000213001c40c000302e112030403103200d41c80d88401f00d15a4400c0068440355612000000141030021448070b04041d0b01042d400a20fa131011110741a402814054101c1c56902803c45162684010b102c100c560329001c00c410115035003582c1c603420b0380040c03541c0088283d006440c000b40014240000c40c51181004054040c3c0207013000b00b050814050082d111421005007498038104010100184180c1c0000d11000c1080d0780e02031b211041020360b60101a044010480d030740300d03844104c042501c1d603a10442590b8024900d0801501c54120b01880b800c00740b0003401001e40960700e800402140c0d8015a11803e200c01481303091409980d000010080380403044419112600301c08140f482130380c0c0000d44003000c0041801101c040b040031841e28030f4a100c003150008a0768001c1c0e0000c11112001c032001e0700c0c1c02226400c01c2c40c1003041c0d12019001080700e000d004140480131262107000360820905043c42d0f0082c03441c0c99020304902d000800c0c0d4500c81841554100201c6240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 531824676 1250 531823426 531823429
    0xc0210181518230a030f0c0201180f0f08010606020703030809030c070308030601020705120a032f10050609042f040f020301060801060c030c12110f0f0105131709 71
    0x501d10b21800b07401c4428082d203050400107908a0f20303049203040302200282020405500051050595525903603030300107200098002c94055213088800ca050001c0710740c2c00c2601c0c40701180414040d050704819030b40c0b02440d110000500c0341090b030180c20243d141040038496581c0c007207401030a8981509105690f44c03a0602c91600d184134200b1031041a0003141404030030014401c00450141109a00700c03400380e1317140c00800c10380038035a107110409a4000141803001900503a00c03000700071700e00c9920600d54141143c84418807030b045c61502d20250483c00702078400c95164894980c2050081c0c038000300ca403a250351643c0c00b11256a01076045000d421000e801660003182690351817000142080c002c0054920002d4003a420078055200403489080010034080d00c03c18400c18910b03015520809054590303200c24049840686410003040f45074030039400784600030000d00001962060080440219000c601402c44001501e50410401040818004500c0d42c921039100030100900c0155180440030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 531825926 1250 531824676 531824681
    0x6010905040c03050a0308070905180112140714180919141504120e1c03090308041707050102010b0604050f030c04110307090605030412030518030408010c02101815 72
    0x10f100910511030101601d0801d94824801c5001e105c0f90340303a6292035900e64040044c440f00c43c444640c0113030386650042106810031102c00301d006015900900c00304031848601410014141c01c160412003100b013040c0d5040c00c000300840f202a251019814050820025190326a40340d000d04542c2c40b04c003003a01c1d41c10b000030b0980101980b00090201d07655144800c1015511000403502601e03002110103403002c015002d800480c03c1840c0c001d0405048040365004815011000708050f01044884500800014450700c000c201a0560a81342184400940c0e00c80345880d8554001d070b4116418601040c2041d00c0718001d4070700340c4101300c9003194070001c01800319103420a240c80e03143d80541401c0707440760b10044c005c00840c01032045a449002c0070303844082c20386d4503100548004040709100c22403840d45034072030b601507600407008110b040000b404d4101c1461440e04160485070290350f5610380e801300c140c1c04006c6510a060b80703100c00d2064010300a950003244040703e402520035140e448d5400302070780340396 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 531827176 1250 531825926 531825929
    0x3120e0109150f0e060a050702060c100212060f0406080303070f1106330a0306050402011e020c04060f0b030a0c051b1501060302070b18120d0504050d09060206010905040c 75
    0x201c1550010000b03000005090062126000300807516440f600492414400200d5540d0021612802d02e400080c2e4240240c9512540d850407c81c01180e5005d2661030341400180318000e50220503084a090140401080da8004010240b084d860018100710608011040d00d50004407803d003042c80340d103190030940b031000d108802201180214001c100c1000d20081c4401c402c0440c0241e54901c904080083c0c510018200180c9544102035001c1000020b40319001180d10501c10b03d0040405001403c80740c0c4100c440e000a40701581010341e50f03000900300b41c032440700140580c00350100e400741391048a64461201a00580304c4540350320121010321b0240e01114201d02c0944481510495040c600a0701da42070343c442082480614400021010f00c2030003505d00d02c603044402d0b04215211900403030310001035040b0004140c01005508150f071544000a894031106418001c039080c506890700905110b83c0099003000e11030807610a011103580003079038606455a02a00107155215400d2442030030469 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 531828426 1250 531827176 531827189
    0x30221090a03080a140c220b040b070816030e03060a14041b1e060e090433020408030702030c18040b0c0d090311010506102f0712120903120e0109 64
    0x18081030003140c2150100424441c0c0c140221130313443ca10180e140c7c84514119114045d0301c49411300040c444174a9607070041207810f214100c69407078141088441d50b000001c0036425004141541c00d0410a820309100c4207503c08180d840801c00c03000000030507200a20301034405401c8030140d00c20642c0c0f03510017004140282501c00004d00100c5031540040d0100d03030643c05040006041d80c07240c0111401d00c8901e0703c2c02194490182041a21500303240300e00701081960070440004032002281100c100b0788000d0000d40040409180d03540320a0050500e09200c40100a009040c401101c4441c80d103081501d0380c002d94003e10603100b49d21001241d0015000f0b0401d035400303185c60813065500301900024983c031000c0162300244004c0e5101d01c2040812220903620b800420002142d2901c03002c00e040c2011a103948540008201d070014240305c43c54054244c100c3c441c42c1103460081400e00105254a4480036018908141e1030340c00d660746e95240712070030000f401c02d100903a161400a680640c0040015000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 531829676 1250 531828426 531828461
    0x11060301030803040c06080c071203060f0f1a03040b06120c0402030c0c160b0318070306090b0f010b03100b0a0c0614010614030f0711120a030221090a03080a 69
    0x841e0b04010145074800e4030111522a82660001103c42c0500c03a030610031100307400500d01b46940307a1681809103151030162001c1503a2140d001c1450084840b200c0c02815030028011030150500480220390b1a40c800541c62006052003040006407217281c61b00d03030082017580e0000480351040c0d45d4514201008504560150000c01082440400c3c000906201c00c0a40c00b12a9000980d88101700c1880c03090042400e601d80800009a40542680984030548002d000f1a00b446680e5250407003100c5140c4001c507032800d000300c20301400340340300581103025001c11000f241c51800c00c0c0158002e0b65a440c4980307100200d020400110040c0682c40d00c01407580c010700140310b803107141d841020118500340200008203003840700c4113111006003000c2da4840c019010941001d501c806c00300f03543c481400c0ba81200c1c1441950740800195050002406200025480240c2c03030310b07160240021844000f101c0d041013400c4150411003090400190a52000d4150030120070360b845030503114024195191280901c243c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 531830926 1250 531829676 531829679
    0x40c0203070c0e061011100c0207080609061b160b04060f0e0604020310020901080a0b12031315030c0e150408031314100206070e031c030507031a030a0f11060301 71
    0x42c40100361403140108840512080035910300584101c40e00c00c240c00a035510000c05420504030230b910000743d03c0581e00454400c507a80b285a1450304808036a611000c4d0010001c2c407048040100d5030a100440c200341c90313410b1624800d0000312110345c0a034003402006803480428140a03140c0e0100d40017000f464400d00c1a60413081c00295642020340d4124040d12803410000d0f00400340b031080d2820a00c0c165074001140e1134000015000d8030980c0e0003107500c0800e25016144146003040104403c040c465050f4401038540704880c2100301e003041209040c11300b00044003200d0b40e800088101e60440880b0405001076040244522a000707541100100c1e120001d030426003200e100344d1020441c0c807450240b40200c004030080c0086400031906140140c0c0c85000403a4180380201000741110801508462049100314071305154400d0f0944c190b0003003595442408145035260203080240100d86220321b1444c0168000b02e5070b149503048000d400c110904106000708480b0381e045c13421071480104041d4695 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 531832176 1250 531830926 531830939
    0x70804061d010b0a08070b0d110c1903020f0c150c0a120210050a090c0608090307060203041103100603031e03060e0a0507110705130f020c0105010611010608030f0306040c0203070c 79
    0x2802504083c611580180000098281d00010b0980956210714186414088a165030a003d007020001003160950140100003100c101000040d202444100d0000b13503608650078003074140002050721f4070107038001c0394040c0030640746e0f1030f03103118800a2141d0065079600e02031010350a00c1d100c9480100070000180091816030390018441940144140040000792900e84a51042740d0800740d00a00c402c81e4103200f044030b01d000d41c1c0c4140e800004081660b01c3c0c20066903801d0102d0b44110340486201824096161942c1002c000da0040700d4590441003201a007142c0b40600328210030440d605259032103c107290b40c058882d8000d0b0f40145045e440d00074840c113100b8034074406400e040ba0400001881080d07a250954000101d0702c2c01c9480c0500722188603007600c10750030007401d45140b528034001e4003045050200c01d024456240204a02c2d034807002c282d01041d0a903402c8d1075156101c80340960081c030001d5841015901140d070040c1040758002040b9000200c16030450013010030103800c0c01103040300002e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 531833426 1250 531832176 531832181
    0x30305030a0c08060a030305030735010602030a17070c210e03030f040b0a09050618010e01111b1908030d180302031b030c0d0201150603050f070804061d01 68
    0x14401881d0248501c01e42028101c829a10442d185544841d0300310701000440e01880086400014074a007207945045480302202e01c5c80c0888400d03204101c100c08007200351415040382c280c003420861004c0c5282040003440140451046012100d951a405002c9200540140383c000c48844d4041d0859045075106c0700c92001c140c00100150b4045132181c01c0215440c6008030440c1c0c441112520b01ca1f08190500d40020843d030405818042404220701000c10903580b030750098910034a4510503031010380d00714000105007012800103113043c8000e17034202c015001008a506a81e1030390507070400c1c07100511900040c03a00300b6410000c0090025468002c030303031a400480100760001042405100d07024521090780380100f41503030b02800681040c00896084000001c0c1346038807101c03c504036418103950620031400c245d100108000541c0d23643d1002143c052104000300e0041605040800c030301d15080c00e0310b0411480041404d001c0101c1c050004042060a60080000707680340d405204a5085028a80e0b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 531834532 1106 531833426 531833431
    0x403080711190807050111031e060d0606030b01060f08010608060f0a03060f060e011409161e08010302030f0106050109090b241e0702060a0c061503030503 68
    0x9801c0c0c0740c81c0d40c48840c6008403c0300f5664078862901c61b08541920244c4041c0e05018002c00c094481401c89007002c0500c1c4040c0043d559440d10300051aa4030004401003401e46840c4001c018005103007040d41c1651401e459042c00c1540038a42500c0c00786c024401c0000180c807840025600e801c10041c00c00312404c0103000300c1c500c0f41d22541d9442c25502a04014840c0d5075550a00b00309521500d50454018802c0480c030b2941400f550000c100d9090009044904034404c01d03241105403849a1a007200018207503500c1c20a8074010180200f0a88081c441a4400d1182c036010300c0c0c0740c81e01032091104660050310754286c46441c00620384081d00d0344099941d440035100e543c3e00c28502c2100c14100010120000c015a2808081c1c402a040040c104e2080901d031814480900140c55207402c40b0450f032410306121900c0c0d216480d02d180130b051201c0d01c81c0c2880c81580400403c26802c000650b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 531654676 531834532 := by
  have h0 := BRFrame.cov_init 531654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 531654676 ≤ n) (h2 : n < 531834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
