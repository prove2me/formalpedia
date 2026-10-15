-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4968
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:19:08.132189+00:00
-- url     : https://prove2.me/submissions/99adb597-7129-4a84-bd7b-07ee696091bf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 893345323 ≤ n < 893525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 893346573 1250 893345323 893345333
    0x11a040510090302040c2d030227090916050d0f02030703030e0424030f0201050d06080312070807021f0603240b090c030c0a27030510020a0509041107 66
    0x101d6009031000411181c0300700210304150190b03454039441c90810210160103a246000c101191030f8800032070f9044540510103d03800b0390304450905070b80b04880c140d13900e00c401c18402d2106d00c0b000c1650042c0d26050000e04144c0d0b0108102c00e9040f4842e00d0349001c41c0c03805013005101d83c0010425101007001c2081600140d808120400046120f03450f50318400c0084420070003151842c1c9030301c41c580d03a0106201d850700c134040e4190710192544803000050514190004840c01d000365a103524036146848004110114004045c0105055400100038259a00602207480c01c0303050f50326201513445440c10342608a50030b9124010f460701014000f8003250749842d4500ea03101d608040341c0b501446105407c41001c01c3d801260130300001901c0b8207116003806415007400703100c000c04007641c12501203a10050035101c0c42030044403407990001e0100040358420000d840400a2008a90301e10810080f45250f076124001e860714001a511464244001d0105110140c0600c80c40b04a00c95810409140011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 893347823 1250 893346573 893346589
    0xc03071d030318091806060607080f0412170a0c030f110709270309140d0606150206010f060509011202090d030c060f11040335090102060f0906011a0405 67
    0x2c0d820343c21038010400b103409000382000094000d00400c40d1034010711412010010f0040d030080303800d6401551380c51007400d01c004a400303003288801c40210300050000b080a0030002406180780036424414100b0720302d0403042c40c0c034400d261604020580c000020004240205140d011203440340c28400da0900706094080c0c1454115004110f9850f6145c07040d01240c100c0e542500380c10114400e1180540c0c009440c0907100d42142d20521901e015884840525602c03a00c54602c51950300640c18000a42c4500072601e0000f0701b81074280040c883d840c000031742d2040102c030040840713080e912840d1625000c24011240403084406090420750200308108880e150101c010364480d000340c0c2e404810030280d1a10710143d41c100054032403060704000d0759075804407030417044500f01c07944901603d15009820481100c0381400403c1c004805102c51056040d0082c82d4004000300b000c00d9003915020f56400c075842c426607a0980d11281241e01c0f01e80140310030340d00114100a00303007040955138101a40d40000440d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 893349073 1250 893347823 893347837
    0x605070309080c0f0708061b0304060e030414192102010306050d0c180515040906150b13080a081b1222050616020f06070c120201090605030c03071d0303 67
    0x16134442c1d10103658200080c002c0c900501001005424181003500b00c0f41d04070108640e840c4014003002020408004881e0301c095481d910510640340ca440c0c0e10b010602c0c11010042c4414002c41212110356803c290040b4142c041e19840002c1c0c412101403a0312086107010b43d154201d05169480310081141e0303032401d0458462510450b0a521160704000c0015541c642d00304400e18024203003400e00c2004042c180c0640c45517030042d50001801c41c4181000d401514221a650301c000909140c04a9455080c00040c00a00c1e2a4203459000f691b80c0c540c020394481040802030301203007003400750301c00f80c9800350700c00910710300c000088840c0200c0190310040d4a074001035400011406d0200d01c400700c0c1801a802d0b10088c1000c8a9990602c0008828522800c031021402441151100810321081ea14241507c0d0b00380c0e000204a082691200380f20311000c1c0c3c11403c164049444a030001a5842c424411a81f0400e2409002e1f03046403110a0190f528580e2070320b98207000d2103840d5801000e614100046c00f48 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 893350323 1250 893349073 893349097
    0x3081302040e1b03070806040323190f05130b030603120301060c0510050603032209092004290f0603150a0e01050a060503130206270d0b04060507030908 67
    0x68441143c880112000c00998070f01030303040800200502031000c94416405a01418506010300312240681c038000b42080041d65000c1000c29032820391814054140c0d643c8042d0b44035942c0000032120141c80345d001d420b110030a15401e00400340212808200915000040913040320181d441c800714081d0140c00c03d811000c0002d41c00c29003501804010003d10346500404d203c10000c0d410b0490109444e441456861481e1043e1400035040c50800140000002c010704e0208002e806064a0a03c039404001c18900c0c010b000c1c00c00f80c0c15501d1600703124440f00c0b5500307003046280818002c91001b0050024200b65507115140c1845c0806176201d11000350b11503000700301c00a04100410040011480541c0c01c826040c035200401804151140c070509001e54040d414080d0300c83c0d0783d80c03460148681c1c030054000c1d0008030200d0000c06603411101c03041c1c070440c10340642404000f004410300268415070000036001d803003414045804503000f41d01c1f2036008081e52074041082741d106c0c0c8490318940d001001d0811 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 893351573 1250 893350323 893350333
    0x33a0e030a091e141f171e160203090406090e061014012703080304050d0e0f040b010c020a0b0310081204092703020309040509030c0a03081302040e 65
    0x4400ba030050082001e801d10b6003007000c02c0c2c0c0121a401903d11503a00035800c00c81c0300a24028190350b81d5603040070102c0444560440751882450000300351044484400d01107501d10004901c40e4402c2c50210560300300d29a001850607075070050081e9890900d610071300d065020801200d481c83d296801180c01510003e0b501241d2072081c4000181340a00c010712489251102c03903010b01403a0360210b01c01d8291282440c0045034040d84d0405921100d030780e402d0325410007012100020070840700034065803149010b08159421480d2071f010603110107180c0004a5441910040100c00c58074041d40720f89155007040c9003034003065801c0d0b80410b25018aa402841c00004084200035561481042104c090000ca0019200340c2045c1e0711100014060b034080c1803500c6845054130303a00040e1a01c00e8410841d45002c0174111a150360401940b02da0203e20614011414540090403119000044600e258031040c0203140908864500b1507252601504204a0003440c0406102590303490048403a0418900041d02c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 893352823 1250 893351573 893351587
    0x10e010510050f0109050f150c0607020c31020c0f0703120c03080a09030302071b050108010f030b04172116030e0a120e060d090201020609033a0e03 65
    0x1441d1044a640200c0c410b5180d40140003203641c2c40340aa108441084e544040c0ca18001000030b00c8008103820343c140022004900340340008c1c800100c0380e010320f1142d020741e9404806c04003444510590030510b140c84d81441d50010f518008084c9000441c040c50b110014286010014914100740c00e40900f8005540214010303c14480c09100000c230591039401d00c3c131266403090b41c02802d461801040c100401d6998940740d003d140c02134044645099110b4010b442b034001c600130407a03031809613010f40c0c0d0019848e00000300d60807010710318050a50b6000b2000e01155980c5503540ca401c0129100c0f02034218030107010751072031400d220700b80c80e0b4080074444207020706207800080040c09000900c000d0303040604021401d150700d000454803d43d0907410081282c100340e81340400352100c2207544020340c2c02000008104d9602c0d81242e020044042c803d900352161030710381c1c48000347c3d280249a60008100300b0440a13418850800401d102502c151141c440c107540c12030880001140c2c6400c00307410103900f00142c2d40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 893354073 1250 893352823 893352841
    0x504210c0806040302070605130314070305120301080105090604020d11150a020a030212040b041502010204030816021e0f1c05010905060105030607030e030304060c0309150219020a0f1b08010e0105 86
    0x186c040c104901d0f120f8200390600c1c203489200d000501c0b0103400f028004040b007003c02c00620595001d1a00581119803601355603071540d44586c800d00c1440502e5203014086441c0c000041980b07400b0b260004c00941d51003130140c07581e10030004de80c0c1c4001c1c1d001032484011403502d0b46902c041c24401c21160050800e070051400c0c0030703040200e00364a2a4019100700700c28001c0072440b50548042d5400c0380108038115101c0c110582c02442550809041e903200456901c6880d1808004a9400c910a480c60f42c0070300031880240b03611140824805a210313000c0d1001c81e42c241848081c040c680100c49094a5550480e0f0720783c5421203400c0f54085d10150000340041c81607085c1000880c0d004a080c0c50100000850f0041485c2c032804080e100900c660b032920007496a40b0f04c290040f205454003d807404031140d003564a03440c001d40c04440e41d10300c040100c0400c04006400400d6100e810f83d0003001030001e0b440c80380d031036002800e442541031040005116000c10321801c00d00c01c909c40495402d000040034107040610b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 893355323 1250 893354073 893354083
    0x31b0b09061e060904030521090d0f0509010915020327010311030c0a05130302100c020108220b09190309080601051f080612010c02030d110a0504210c0806040302 71
    0x92110916460900019413141500c50350b04c950145061502c030310450f45504140303684070b08100741d64000803040c049424804201d110111041e0345402c000410400c2e016103582c0101e5020601080018034100130302080e0020605803c01c051050301e1810f0038915038003511074030310480c1e040072031109441d41d103c0e56014030401406440908440e82589403e400d8807002d0b11803000d5070340800c5401b1501d10801481043d001d80610b0307000304680c50b114110301000308414014401239000032024004101c441404039190060200801070010b002c1c1d980da120030b400c8c01c80c0030b440c0d004544074041001000000b60340c1018011071003699810602e87c0b6042c4900e18021068000038842c1c130754054103d51082801c0b016031008940d508120960380e07501000940c0c5e130084900b0b082e4103542800a00008554048010000d0394400c107410401c2c02c04428074004c403030107482401404248200000e01c001e45003000600201c0075412580300c8006400d607107080781541d03158482c044503070040003844205901400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 893356573 1250 893355323 893355361
    0xc060e0709020d0b150f250803190c0305011d0c04090213060905030d1b03120507050d0e120f031009090609030816080c0708130b04030c1202030703031b0b0906 70
    0x202c0c8500305041c6000c1b031180c502c919818000b000c17503248041c0301d4400080407440c0c1c5403a0031000e107948a15140005500c1c015854044c464614035009104c202d00340a441154140c41000c0c00b004c0b8034050120001110b141c000d8030801003420107000025201c001030000300608081c0103071070582c0500d042005030030490680c200901c130390080c0d4009441ea0b64445405001d042105a0b9190405440c3c00e00f039500310015882ca03041e60f81400c00304a081a085030051100c5400302900b0440446d070b01018a441c0e40d030f0030f81e81c80481b000030048401000d124402641e0843c07561000c240b292640c0301507440846078604812103881d170b101c14103102803540001c0d201c0d500c6003100100300d03550440407000910004004082c0003100c00f002c0b50301340c02d004200301510400318070084400c14840c0c880c0b28440041c0c000388408c891010840401044021181d074000d08042d5014000309141410340c0d4082c1e0305400302400358101401c0c0a460800802c842808045c0200c2002014201500303010540b0003004600203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 893357823 1250 893356573 893356609
    0x3010803121b09100e0d120e06070b04030e0a1503050610050739032a060e090705161208130f02040c0207050a08030d0c0f0c060e0709020d0b 62
    0x15201140000411085904090302100d10560500780d9110035220603170300c03038000342d042181144070b9010481441c82c54141500e194541f90314452107841005031900c15103000034a98030886000c500040c2c001c00301c49107200c01c010030789482c1039140c2040c10313190210450740c0000252500c02707001d010700b4805507401c0b04040750301d805031810b03c6a441c0c0b03028090300b072030345404a5039146010a6200100c581010510b1aa01585880c0c03144d8a0030b0025140d1a14001080c1c59202c107002d50f2081000021202c1c2102c155803034428000b024501000b40c0404002c04e014107001041049201030800040000030452041e5100c500c54404910020030f2140014801103103000b1301d42804003c16441d00304c1c000d039907504940c041420100807008a040c0b14182d44a10380140008001041d00ca0b07021014001d0030480321400c000100701000201d0700c03255890712080210300c0344070350f00f80071171000e802880200c1880c204440b5126a15000c5600302d070304c241040d208144d40d0b41c1c01a105450b00b200d842000070800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 893359073 1250 893357823 893357851
    0x3030908220b09030d1421040203010507022d0a02060a1106010902090a2904170d02010b0d0f170301290304030906081b0403030809010b010c0b190b04020301080312 72
    0x3103c0400d59601e480f800790780c00c1c491a402c425040111603402c44141003140c50100b071802007485108105444155801c074402d500784400100700600c00503440c444a410303441d100201082242030004010b411920083c4540505481c19002d42c490301c006012807000c0780c3d03c401c1e03c0c1080c551114141401a0002d820082c010400d110b95952641084c0f0103807400c08072040d80030340090380c03044551880c44884030f440c0d14010400050302c00300040382c82034048502e0f090300c0d84034005503c12822507641100750b551203e40c50206d00c000c50006801c2041c444e10580041c02c031200306030090728458000340d020080c00c08244029401a210030b421340408485210050360540c1000c1d80c000d40502e00c1401408100159a000500c403951640c14601031840640e600681e5581caa04004001c01e404940b020010345c02c0c00c010417590752156520481c0300c0c0d00442c81118a490b240480c804080b10025281c01c42c2d40c85a8403258280e440744001d40c020040c0340c005507030326520100c0e61001000c0041403140c0030070036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 893360323 1250 893359073 893359087
    0x270a020f030f0423031911070e07200607111005041407060804170306370806070206180f070b0c010c05031b07060906230a0c050702060703030908220b 66
    0x4008146d840400801c0301860105010920880d02c2d021458a905510f1041e04000160452340d641c4946c05110150786102c3c00001009101d42c80e42508200c420580d84410300240c843ca10451035403040c44106815540401a40c0040c2c07801d41d601070314280c800c064201d007044a02041004098020510360410380c103149090344500c0014a06a00212007030741001000848036942c110440700c0b83c1c18044248040c004015a2413240342d4407458213401c0b196200d00c4049102d100006200c8c0c4204003943c0108016036801c01c540034401112210f50a4511403070b441141e40c404280100c202034107003284815100d0001c0c02c03840342034a00c401d241c031052007010011300001550b0300461140792031018200c650380300d0080c07604800414259a000c5d0802c0c0c03401030b420011790325082d200100120610f051321610f80319081250110b8540a0100c0b010802c10081c48005003450806400c4c0c0f6030003820002030baa40c25854148540c1d200f01410f8005205410b181c1c80b021006003103107005010900040c905081c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 893361573 1250 893360323 893360393
    0x14040c0504061e0e06030c060706060504290f0a0b0a0201050402030c04020a1e022b03110c0d0e04020d050c0a030f18030818010c051305270a020f030f04 67
    0x10f524010a8064074803440024800c0d00d00304199803010402074401950340002d401c0410050041d03000c0c2600c5641048103001030b8801800644058580c0d5001c0d01456502080400600da0712400d40380ea0040b401d00000509000d00b40003410a07502240c0000c1400d18180c0304060500ca001e901c545c0c030030391040c0a0000700070ba00c440302480c100303512040c404600c550f80b841a850304000124080d4421113984a401d0403000301030070402101c80702c0c0c90520254001c1c5a020a140c0a0681408016030040c3e00915200344240c00701021000c0260005140040e42410241074860494a0a07002c100000d02c8815065040c410202c4d0005001c00c01c2001940506058070440340f214006010414800c012032010103400c6641210009003130005c11044c1c9203014060000e1b0000c80f29007813408003c090004003400c141c2504000300903644441441308803c0079010140000107444060391179070034400c4408105c024001180900c4014009540070f241c00c0ca03020341c404103101782124260a86224141e03080d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 893362823 1250 893361573 893361629
    0x70218040c03081806031003051504050c010e0a0302030f0a0c0f0e07030506040b03070f0f090212071b1203091104020702210a020306010b0403030905010c0816020414040c050406 78
    0x190348210441d541c0d00c414001c54001d1807442c00e4a03175000301c2c0041031003454002d0030342210880b0320901c02e0301c0505080010200c1c101d501101d020705180c008040e079200b5584038034440705290000034551844c4640720740101c4d1030702c90030075000403c551202000905102c484042c001c000c191a900c414241c50401d414984424030180c40718060507100c40c003260303169945411019003020044c00710b603516542e5401e03580d429a13140c800c0401c0090b240b0f50125015102c0e000325001110340700104640b644803044120740c0244540c409581e2503003290105400501800d00345240c110107640c01040d8680c041c202922110115011584224410040d400041e2074100e400d2000102440120303102c0105083c40700c0c1012601900254180944000882c483c5050000f030000c0c1c80c0655940d185a43d12400103640c0c440c801080540040380a0004180c81e0b9000350141942c0d0748090b00125041641d84189107044c1d009840c21030b1070f20384081091244d418103115010040882c101d20305003a400c0520b05076108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 893364073 1250 893362823 893362829
    0xd060e0133080a0603080a0e19030f08070515010b0409150e06191d090d0f09030b0a140901020d0c030213121a09100501050105040e0f072003070218040c 67
    0x102c4001c000141c000c164540c4080005e54100a405982c2c049100340282000603103140144621180b0081d05001c80190b521601501d512902031506100e950320b8440072034020003802c0303c15105801d01481035140d40e405003402000c41d243c3c0140c82d02e0030940c500f000c1e42e054240711b01d07000d6241042008400100c1c031038a500b00c07405507840b00c103d800380001d00501041c550040d404100e204603051404000801560748900c1c24002034034840d050f036810440344039000810000004648100034400729854504540c1c100c0440800054900c02d40264100e02a000315081140c1e6507010410210714101070003940401c0f600340c0307011443c1c820625403100d6142040d000325184c0035216000f250400c0240c000c1408001070701d0302c40844e01d02d0031884440da1380460381c0c41c2540403400c000000509502940c240d9003611102c5c1480c0c40070741d89100c1c81c3c51031140c2c01403203c001c00000c000703440e060002410500b49070000c0070003d1503841d041f600500103004070010103600113241100800000c02c40c1c2c00f41220079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 893365323 1250 893364073 893364077
    0x3030417100c1d03120c10051006080601120207051212310305040807090501051813061a0907021c050c070605031317090901060e010915050d060e0133 66
    0x83c0012400401e1a1488958400341d12440019030725000c1440000c0c45030300b042d2840d0090180d69280d0031200c030f80100500c141d078040b400881c00b2800079070144144524648990800501b840115190103280c9100c042c03200c2c0c08950300040040604a8281c2e10b03552010610801c26140b90b82c54605501c2581c3e40c6644010501c81c040942e800c040c0309600300c50081000c0c0341100c1c540c03038842d0b41c080001c09080c41840e00c965440306905c580e080905540c64401c1011b44841c0032001e2554907488040c2002a03017940510040340ba8500541e036881005502900c4107034020144043d2060380300203a030420541280a01109201a404910000812009403071052404507202c3d00c90042c0740180c0c0140200040c50707082c1415a5100306a070280160060f21002c0f41e00e5822a680e540b4203462a0301141c0c800c0d40040d00a0b40244000800359240341689944d40c03074001d2400b655848110125902900405c00304401d0310010003179140012840d1220b8040c21403130400c50b400b100c0e4000700400c510500c584c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 893366573 1250 893365323 893365367
    0x803041230020409020f0a0e0a03050307020d02040b10210902030a060e030408030a0c020312030411040504020a15050409050709080d080603071d091015061101090203030417100c 78
    0x4070709655601a60010903e8010035511407851026501c0d8541000328074600181c0350f042c0a1000303144c110345890403280c108001d0b519000380d035028881c014031050f0059070800c6d02c0c0c0942d25400c3c0c0700c01c680c0220051140d9101f04074598500c1c819405860381000c0010309a04204100016960101d1507443e11035024000250b800c08070500c0c0360540c01981d00c00d5140b8080810f03d0000160401c0ea8180386910071010342d04e00fa0b421034204085070205980280403411102403400d12801c0c164065030308103000a1110740200d5a40d01c40300b02c0c0824001e041c100090000c24100403041c824094250010050300303000c001c2c0c41c20100740550b41c4e1011160352080008040125155483c00d00901000d461004032600390400084850b2100b0407054820384c01c01c4c801c010005203031929a01c078240c1841d541d50751259140e8501201100c2045400b45c80341c80a5503584081d01c0143d07400c100501c000e00384050380d900d500d885009054148a00c0c1480f24680342c0c01d004c081c00311300d54024610000c03001c0b010310f401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 893367823 1250 893366573 893366657
    0x50901060302071103123007021510061409040e01050123060c030a18031727030304140301060e090607080106020a050601051c120809010b01020a0c050120070308030412 74
    0x14810130082078019407c800c100c24042c2190b804180322440c5003100c850304581c0d481c0c1c0080b808a01c9010700c01c110008018001d44211002c0c2c140042c14141c00042c40030030013070282d03503030682140d03403e9200401c042034405680c0307a0420748001748100720b64201c485505007181d0216054803403095645110030006011a10350088000460354400345801901d41200c1c0e0103900c507101000d0307000404d80e64032903100031540a1100d115034024003880c04080c01460038a842c21000307903000a46d003140150715540b55040400c3c04810308240900c6080740100500f541c1c1406100035003903140c103030802001c40d001402940b0106800280c000e0458005030fa0301a2581010261a01c0802c6407034030052082d007d4003023100d8080e034400001030040042c2002040710030300f10b4005a82c0c0e02c5141c4c10007001c2c6a81d12030f0030400c641c001c1801d540188840d1a2a411240c00040414102001070700122114407000c010301c0240250001403c142c405107040080d009540256001d142c264030304801081059290301d0f42c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 893369073 1250 893367823 893367877
    0xb0102030c280804090203040c1e060503070905030102070503070c0b0307090e070311310f0e06041112040c0b040308030402040c11010903170a0615031505090106030207110312 77
    0x480e40b8035040051280c40f6900c600545c40650b0051710151401008244080350302d925904107030010300420341c28071000c5032800a041e0380c181c1005081c5801e024404200203001e880a0000307104e82482000556641d903580c3c64040394980349030704403c5918000b4001c0000081c3c02000400c20740b5049081c1145035614a0b101b140a0000311008202e50f01020481e031b84080c48081c0003035a042026081050038000065468070a170310148a005400e07070700b0717007020040c0c802403880194001001400204583c5400f4000036500c0e8444040d801845000e0000c1106101d2035206403400f0f0720b01100032074a071505d075489096180c0000b070006449141d80d401c4424010740a113004030560102000284030111650030046c104500c0180740920b0b90ba40940005d00112052107000159801800d01c00c81c0c070040303408200c1c001c0400c1410320ba001000401c003c1071545c1c0d8a04101c1c001c0070f8640c0c0150b5520701c03034a4842083c0d600d0302c0c0880d01030781c4400d00c0d5410010101c01a20202c0303004e448400341d00080c00d80d90b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 893370323 1250 893369073 893369143
    0x110309190f0204180b01050114090118030b091f1b1805090901140603060f07141204060204320f01120f02071208011a0a1e020609010b0102030c 63
    0x1c2d07015103004400b8051550703401c1c0c2c4c0000e0902a8180c00c2550780c0e90301c0107581c0c403001c01c5ca44400010007044908641c0d8095943e140d0406000c410814a1076143c3d526110700c40c40c2592107000d541e0000321005203601070020082040d0000d008140402e48401141c0b90013803c2010309001800003e4410784103104a40f11004001c2c00028045901c0d42000100240204031034500d5117001903881001a941c4d00b000a80d00d80506100b4a1009440c0e468090481c2c4d1a0040654002e20000c200041a101d11020944a0246004020040c0e5071881d08040c1d80391302c0c02054103071402c1900340c90740f818008aa155080791003041500c202c40302041480c0100c6007501e5020300c1690040c5412010650703680c050b800340011920903e16040c10040000c02512446802d100f400112410711050541e02c8100c44007508010111b800c2a800c0e00346d03020b04018201460652280040e44090108907240c8000d0064000b840001c0c0051450304c5922090a83c032612404c03107100d03e03049911058600000c0b810380d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 893371573 1250 893370323 893370353
    0x40906020d05040c050f270c0408160510021906021e07060509070f0803041211030109120f050a2c0307152a020415050406061211030919 60
    0x20030800b0b80340c079180250b820045801950f015841c0c005410440e41051400c030b19010310303000c00c030b482c4caa1611030700004407441c01000c244105805100018a00804000515002043c0341402261905100038841c000c4600d0303512000315800580100c4502c4413413070401c5011600b042c40940d44a0005410034a0000c49102d40d0fa0390401c0014032005100c40c5d5400705001c0e20540c401e032249181d48401c072071000706081c001c045194104200401102c10034807280301901d13100e01c043c1103161000c040060308540f45680107594844400001c0000c40b40d02041032020b40d40c41e410401c0c241443c0d5000101040c0004041900c0d0b0b030010341321504030381c0f80c03100e40302d44900340282150700321a1200c2514040300040c00e014808502110300c01602914540011300b1035004040020100d002c02d5020400500100401c03190301071701680002c5065282e40c0104d101815003520345201d0500784119540803160b504101c201ca048060050008081c8042111001062000c9480c0e189179580c0c1000c200400d1100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 893372823 1250 893371573 893371597
    0x120915110d091809170c0601150206060a091e09060203100603110d05040212030c25060e1c0507060f020f0c011e090b1305030d080702061b09040c02010b130e0c04090602 74
    0x4100340d5800b51000402e54140c40000c108409c14003e00c44040c0c0c0e43d0701040c1d4166a02468a00050142020603401141d14259140403403101c0c041c80035080d4111400404150b50340c035000010041c01a001d4803440008040360301d0304001c61440d4200c42d4800c0e0003186d01a40c2015284c0c0089415562a851403649003100c12003603a40d100b001c080029912000d1080848203444510180c0020008804501048400f00c2e143c2c144150040c0d41041800416900c034015440300008545010860420604c00588280c0d01c0d04510b2840036200646829840c1c0300350f40140d0710103105c202da00d036170289610071000000300340c8000c0d0318940c1a003640d828800d5005030b41da10102148070700030754000200000071240150281d0703000f807001560442e04040210346440141e4402004030b40c1c070b9900621340e1450a80004052030a14400744001010303500c2c0356441d000140c0d101d45c0010a607141441c0d0040029041150821040c1541a4903d84506031604ca40b480b0b169500c61581c10b00442e5012038084200380 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 893374073 1250 893372823 893372827
    0x6090506130810062105030307030203130615093207020a0b0405070e01090e121b10090c05192303061806091603120915110d09180917 59
    0x101140200900541c03194108800c402c0c1c0000c1c0100c80002d01040302c45d5000f03400fa41c51940d8190040d0040d505c00b800c0803203080010000717100880c01a04c2a03001e0345103a811901c0c0310b1460050550300307482044041e40c5410358901007100a01007042e8603052480c41c1c0307044080556030b40c001d0a0307080084c03145014040ba038000c01044100304011130700f4400d076a400c0110502e0350342c80b211000e0855900000200e025441694001100c509030b201514581d1040710b0b0a1b803842c440ca00105080c80350b99200080c0103512000c0c00c50400c606542c40b9005058182c900701e250049000b10f4011525143c030030410240f40700101486036a019001e8105038910160403035407103050034403680711280610104544c4a02480010845040d4007040d40e42000124400c0a0340960454861041e041072903081c4805104178040006141005d1260402c0d20f041551103400d2444455114603041c0004400303120208100004280310140010f1072054200066090002d4100c1061400303d0080c01d051110b40d20307076000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 893375323 1250 893374073 893374093
    0x8090a030b0402041b020c120304050a080106081921030f1b0e0306071d131401031110050a0e0406080708030a020709050c07020d060f06150315060905061308 69
    0x60001d950085100b51800c002c00300c0ba01281c4011020104d9021005030400180c46080f071034100f400302c0000340002c0c1540d1030f00365280001002d1410381d9100603640d945941c01000440820b000300c2080500710300446960ba43c00d9511030307110611124510011044552840b00207a1196002d0b10301000304c0071301004200c01112030380c0510303c0484410000250b1403001c464143c00d001c5210b0740200110388900c1140d410b820304240403c4c103111401a00901c3c1c4003c0004060301c18000c47c4002c4050300944482941103090240300201c030703d030306c5a01a240440c000701e1500c0e408002c80b0020800307441c1a4028030011400600640500e90041c0328a1107140d8011074031040100052070b101c601c2d60200c401d580d942c1c3d01c502081e58022280c0f0190f64105210110150919956010f08244151400200c6900154856080711901d821a418519803c01c02c0b810343c6415204200103440c01d0154003480782c2ca0001c00a02c1c1343c0460094a00560010580c8106248600b20340000303815164161001042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 893376573 1250 893375323 893375333
    0x6051810170612030301060e011403180f010203070909020306030f1b0a4b0e0f0127230c031b040b030a021e1c05010b0f0405040908090a03 61
    0x1400508500301c12100c1c00420140d2400f001004003c1c101d00e009507007982e190000a586030760044100905021800396000f0240241d100114072440340c10f03203030101074440c0282c403070302c1c0c5080301c0401c6000742e00c104248800203800c06080301c100d85200c45c0141e40c903a02c20012a09109024a0303907290340c481c124844840006044e90b81042440a0300c81520341c9075507041418440d1448403402c0c820305c03516144148c8041582e614900c40c4ae1a440c2070ba07a50303003034a041c00c64180a81b43e0140c0340705130f88441400300c250807401906006100302400c0d50300c041024075120082c0540b20100b880300555540806101480e091091031010300b8000301c40c981da180100445016600c221640c2210008940c0e2900e0340100b280141d4058034041d81441d42165a020705a0700250320080c4015481455000b00c2030810280c00000c0c000e8000d50340c400e030340c0f52001c02d101d40141e4506810600c1c003070205011802c90843c0020503101107490403600840c08450508000c0c50340e2203003520440d0800034075000802400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 893377823 1250 893376573 893376587
    0x8030d05060405341403040b01140d11010c1b06020a0c050a031203020c010609020c0d030f051915050325120c05270709061701050a06051810 62
    0x10040c1c4051041d039036580d140c2e049100c10114004500004800c40e20210500c10345001c0c884c424604041c0412800e200d5401919002140c084a10301030714801031190b1080f6101141c820301c010b4900840300b160568a4580052200b002c043c10061070701c3e005402d00100608041d003181059840d001034035121100291240300038181541e22084030440081c1c00e0401184020449030042c0200701004075003002100658000780305600b16640740d440c00319003a031540c801007030f12110f00c07070041440010410015050703e02030540c0b03050030b82c40d10040080c5810140802c4142c43d00c509000a6079882d110780038030179081140c00554040c426801c4000c004202c9550244003100174102c5185442e035920b080c00d4080b0785902d401496100c5845041180d400c000001d64401700140700007400d9801410100010701c507013100c401d40045c617100800c003c200e4100c0b88003031a42078124000700c402d40c1080c0200c0c3d0302c1c0d003603403054404106002802015401000d0b044401c0103200074000c1030191050300004200d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 893379073 1250 893377823 893377831
    0x10c080c07050324060d050c040c0503040b0609150f030a0b090606010908030a0c020628091806030b060907021203040605160509150a140f2d071b08030d05 68
    0x91080c3c100d1352485000901110104400d00381144a0301d503950320a0001c0d10480400032291449a110101c1c00c1e40d9850040d48240441c0c6c0d0744550f12440c1500f0102c064140180206004005600074000c2c04213100701b01155460f41030b140e1a00a2352030501007480e20108810250814404c002446200f50b400318034907005040903a54803001e552100040740e200e214200d001400314140c4614031005080000103040d805070402040c0400003041d00d080c660742d04500804030001220f0a005001c1401021848079841c0c80c108000c00120381140d0320340e1b8158101419540c41106c58100085009208000300c1c0d140d04d1005038915107e040602c0e062018000560f9106d05490b42c035101c5209851090081d00c103003802c010000f61000300441c500c1151603111b81d131500c0c20403607003d071400701c0050014004e221040c00010001d81d9406d01c241e0802c102c2c101070110050f1a6602c466001c0020758141c240c85d012030700f064103400115904040c064941400d80e10601035400081001c012803130483d4412846 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 893380323 1250 893379073 893379079
    0x901032405190e2a010c21030c02010b0a030b040606030503040e060a12020102060406091506030c14091014030c18060117190b21060403120b0a030b06010c080c0705 72
    0x201006164205450f000e1004980e02800019903c0c507981020101e003800b1413140604101034606440d4035202402c402103040840c0100861402d02c0f080d41d850f200d001611a020f10080010140002c00070721000c0952101402c08120003005c6402d001c502d5001c1c030025640107045a6031681d0f680000010a1011540c240c800c2111203000507000e040010364039001c41d0b05034090150382ea69a40d840300144500b8000745c4e070148080d41c0043d10901c0074815230b809140038006100c8110320341031071505423009a07101a4000c06000080c0002d001d02005210306031042c031300b01440100c075502c02080c034149241c680298000701100c10150a42034100000707008000030303078401c03031510300124402c00754000555070502500b80d0000c074003103280c00310f81c4149034111380100341c207481542038407488508940804c4807183e15008a024041003642000015070328403c0940709002100da00000100000d1444c4005002a086c4000184583c8c7c412074105030010350200040e80c440742084101940c03860a4014a40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 893381573 1250 893380323 893380331
    0x9010806070909020f0f030a0b0319060e01020a091a09030a0f0213140c0c120703090608090a03050a0804081210050406060311030412020f01050a0219030b090103240519 74
    0x5190740f003c0c003c50368401c03509803001c1e141c56008141e480081d800142404003081d40c0340d030140034969061150b1000b060035802003400240c01410103600722031400300e00c052140c0c41040702007a1240c1040d400350445964010340c040b01d48040a002805104040c400b5078140150300031f1004200c5440c2d01c1c2141e0300d00a0741c500c0d800741c0e42c244980d812680f1041985420746049070004001c0e104440c018004681d62a0076522b43d06000091140c0e141c201d04000c030042a030368078007441085d0b40024901d601080703240080c03118604c40e0700c01400f01e20900d03920364104140b12000406101d0a9400c075240c0700c1065004000341e11785245100c0b00c0300424040c5901c51810030000140052090007004011041c8101440c915111070350b84200611000c0c004406600403c0202c0450020a100d4948101429200569910254020340a000c03c00082d0202030510305104124180c94410056040d2030f0b00030140010801e143c000c0342d040c50394441c680482182410108140c4240080e0b01f1081508072220a04c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 893382823 1250 893381573 893381579
    0x6071221020313170403050a08120f1006050f0405100f02010f0b06030604051b12070e0a03030c150e1905060105040506091303030b060a0c021f0e0d050705090108060709 74
    0x50305070312080d43c60410502040080d0000304140c944081d05100f0401c02d50b51a007980c81d5221f5042074a250b0742a507041c1408981041e00e95282d026241e8041e5200c0384610030381c0741008001124500c0b40c01114204a80400c400b05a4000403085a01420b40107041100103a01c0d584003d01c0e0380c1c100b600c010015403e0090f15003403043c40b8060001d140c5002000e040c02c60356040d0611000f01401403610340300d060390b0384d10421001402801000034240041401c0601c3c0f9000b01c01900c1501303503400342c9008100c2028104003003640040f0501c00c2c10341c040e0640d0b0400150380e2200c0081d02030128501c100f8080ea06a0059048589110040b8184184146e508507a40d400c00c000c1143c0f4100c45198014400c10001152943c1e5102e000c000903100c0c0c03e00094840050000c0307069038010514620100320f070800e17070101354070b0441c241d01c841105182824400321440743c00242510000c000b4940628000c03c4140108142030015001804010700403165969454040310b80e19241a146080810302d80503000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 893384073 1250 893382823 893382887
    0x17010608010e1b0f04112512080414101401050906150a0224011419060c08040905040303050f10051503180a06020309010c0e1c02060712 60
    0x184802c504031001600c1c80c3c440054001909800c59503100c0c0e4842c0070700d61441040d9941c2c3c45a558a04401c400e0292030b03050807241100382e00804088aa4849202d01c3c005001884085242c00c1ea9a41440c011007280c4a41c035010344402208a1176007018050f08040d8400700c0040c0e8054500e80761a44c18480c003c7c2d907200280440c0600c165601ca400c80142030480003607005070310040c000500c0500c1211158026604c690720b140741e56184a1340d024641000410481882c4c8051100c00601110140481c03426007201c0d205041540c882d403014000303680e840500f40980c6805641c01006112001e000a1425103001401040c0868409803810a5403000c40c4411006030700701c0068075001381940100480740300e5041615000104003400781c5000d0800d0a00c008401e00800c10300d144200800340e01d0342800e4540500b51050124840100100b801e005031182d500c861115080c00c0039a03601d0300c0e0140050000c00c83c0ca115540c4d01421000001c52401038550340b001c690261100038403648400384d1000d01b02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 893385323 1250 893384073 893384081
    0xe060a05040902060927190507051318061205061815010306020f0c0f0d0e060909190902120c010801090606020c0114041d0609010f05030a110105131701060801 70
    0x61341080f0305010b0701210341005603103d01c032000440c2004101c19140c1304643c80814040f14054140111000a040301c40110b01881e5045402d03403c19038148030920700c9114020505104021961405d00b03a80c10340c170222640004090020707090280207040709030519640d02c103400c3d01c61580d11421010000b201140100b00c90b01c1d015061414400d40342d02c0c1d610349002a40000320030400340300041150903a920b0041124610750300c544405801d030070700e80c2c900140601404120b66170141000704030fa8081940d4140c0515071241d5002d060300a120701c0300803250028256440004c0d0001c02400794900f401e84001101700400c04242e84490b403d0703889002203c180c40092061002503800020100a02e6006803140034920040310031041c2040d684009500001e241903c081241804050500046050089500d805031494403c8441c50500e81800720707940e002d64080141c0404140d1803004002d07071180040340d03a550041401080300301d8443c44074180a10b50030003001ca4a6103010700010301241c042c0a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 893386573 1250 893385323 893385341
    0xf050f06090f0f04170a03151505070b130212071809030c120e090703060509100506120c1224030a020102060705090103060b1602030d021504110303090301060e060a0504 74
    0x7490b216a00c81000754050020040c4c0219861010080b10811180d12100601320001ea1a81e0105203400f011580c0341546000c0e401c50251180405a04800607401c402203485903944040a101d0301e5070368450b000f988000100f002503100c0c80546081d0080c1800148440c00d44440c00c0211101d500288400c0d0203e07004a407005011802d50800400070503882030003072030049c100d402c2c520f690a031210001504090215a00000300b41d840c0d0091001d4203083c401150b001840442c0401c505082a00003500e07030155401844541d0114400030314149807010940b4124400c000044406051000041c428680c4820500410605c00181401d85140001e50b0704109030701a001781901d915040800c5a4517070203501d840b418503807280400294000d0302001001c0401418541c02d0090b40302c3e1041500b40f140c00c419500455004017100180040448056504546d10410008042c107810700400e0840c0034616040f0343c154a0031900154010415a01034480d11003103a100d0b016580f80c40400048602501e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 893387823 1250 893386573 893386591
    0x30a02121f090b010203090909071a030402030a060b130903030c1202030f07080a0e07030c051906050a0503131505060a1706060613030506011805010905071b150f050f0609 75
    0x1801009944410f511410a100040c41030301d10b09450540401d010000541d2111f0069026038002c00070080041f11000c0c0d034001354444145582819000a98dc802d884640035040c15551400481e169070b500e901216851840781040c800740c0014140500207041103522000814032600041100c1e42051080307a100b03081c0e00c440c07070140c0c1e01e0302001110241d031b00030244005c855845406070702007201008403038002c62180c3da805984034100303000c0c03001142e000520b16981482c024000d0181c1070b0000240d9170b04041078680b0540301e650b60316154a05000c41940544844026211180b080501d60000ca110701c10036190904015520700110b068944080e480c6c2c0c41940040b0701259451804c9801000319507090201c488000f901da8440d6803e10f8030070307400900c881c141c500c281c1460510754064a40100700007141048603250022001e082290001811085280381090903010007040c01d80003400714021400810420402e07010800043c041612140d8031122908000b514500d0503040540c4220303044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 893389073 1250 893387823 893387881
    0xc1f09050c0f0d111903060e071e15020c0a0602061614090607020d020301020f0304060f02040e0606092e1403060f130f02181305060f190803030a0212 66
    0x55144d4802e82e039000b601c0c0c194004000e2401003151381e42c4084440186000d0707600014070340b010320030b40361501c01c05910000b45060690039010102660303000020455a50401180084910030001c07404d20640d1080d40b40d0010701a075010800340d5000503803610900707409015903904245400203a0304000070b04e0001c7d200880411298030303103060001c00351070308a10191000c03503d82c04507800242a41c00a00e2038000070b0101104100600646000d103104040c0785400031458107040031000c00c50303081c0045c101409103c0000c1d888100d900c51043c0110104c8480800c0c03803c103498000410810141d090241c0c3c0041c5141500a544901c058210f0b0700403040105130460360030005c2c09200029800b01d0000c81d0b920f50740d0325000444009400280046403000c190031081c000e0400420820040c011802c101061810042000300d07294201d130316000b14800c403020001c1e400d95030729413820344000b50098809408044244280030321140c01070f0130000d645242c0c1038540e44e0f480841480c0c0d500d001203085045400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 893390323 1250 893389073 893389099
    0xb01020a082d040305160b13090c0203070c060818070f0e04081315030609090302120906041208121609180b04020315030f070303050f0c1f09050c0f 65
    0x840b10404440610700081981d00c0c0d921104140000d81290f4001d0314550000c411148400d40c61005900141c0304a8451a084c22107032242c1071b801c1c4d12203014070510385a8074408000000e0080050300c4916500c4190301c2c03409900c0e05001080c41600342c4502605460703e48004000100103e02c08098851000030074861510b003801201c003d07800034100760750002c0c0400c0002c011176554021003024020744820450702c0030181c1c400604807a100c0e4844403000e4907014030100043e6011407d061408009403c040d1101030f960001280d41c1b040d44d0008108858030310341d0b00108034920024140c0c030b0850b00c0d071106c59075440c1c0321a040f03003200a60b00d502c0041c3c1966024004030f44100120f1803040c0d4101000204a60300d4404035049900030341d40420030007030220b00c669151408100b40d0f201e01401c5006405410700c0c554001e002409620f450340314039480414111980f41041001c503190041c43c800ca80c00d040a4890aa07000782143d92003a81c00380981e0743e240d0320b6820461402030001d4000f503c40041e40c3e070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 893391573 1250 893390323 893390347
    0x607021309020a170c0913080a1d12100507020708070e0a0618020d1d03090418050601030317010527040c080f0d0e030109081e0c120a030b01020a08 65
    0x240c1600303e901c083c14080100e461069003035030300c0315010381100070060030b00940d04002c4282001820103503940c507150500e4000800510035104101c0c1c0504246003440050b03d02446009000d07030742c41703401805011407640d46000005420b0282c905034481040f10f501c030345100320b0f1202564001c540495104050030054698103440d415404102024009103260325880c600950488400050000d15000704559907038070107034812600d90b2021010341c0892003044e60b442680324010000c40c140300e907685074034494444451a0b4211152940102580d180350f840b0f1034040d28042c0b0343c1c810400010202e5001051604260b0340100d5a002d40301807001041264034000100d030640140200d4003049111800100078000f0011910110f08038005802502c1d00c00704c00804402d040e028461007a814030501e400862284002c4038681c1d009481c10580700000d4640e001050710640440307183c94400c2e003840112540140f8044c0c29040841d83d0140305918601c2c004990712445500003400c0b6800c100200c440203e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 893392823 1250 893391573 893391581
    0x2310b0f0a170f090d02070807090c0e10092306090f030a051c030e030906370503180c031f060807151407052509150302040b06070213 59
    0x624601e48604103011005988081d2502911803e02d0780342c08109100544400f0b02118192082d82c1c4020503603140b9001016554110030311540c099a80d54142c940d0120b40308000003081014090520076106000c040c00a01d26102031281d4041c1220344204e1012039800303c0c40305a03440c00010010380c2400c01000030014902c00a0310200c2e0700d1300c80d03190403400050040c0700070350072100440307020144400035450260569410811011080d0020000c90340b00d95100c20540b15080000c6044c030304901c420046802101041900083e151500362025401240d0f0000c0110b219003034240502c080102920807076641c4468412105031305400076094150800300810100d4040c0c210302d100812500d45d144041b505001c99a004a14091070030710543d4412a001109a1440043c82c2c8420341b80c800c076034441c00d032100e18140030100150b1107484001042040b459001f009041002d000b08258491240c1100c070201c0d440c40100e02490400071603206624040050b515103c0d006050180c50125001e85c0d00e00034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 893394073 1250 893392823 893392837
    0x22080a0b060915130603030f020106261203090102040602011508060402010c06021603020a020307120f080a0306091a0307051c020415170a05060606041206051902310b0f 74
    0x100c003d5000300d420701e41d200c0c0c1110100100000c400150f00d8210700b0000c0215540c81e1644003968100401000400e07907110510f040000c0b2010440c90500d9581d09440c1070403440070500e10460070110502501c0352040d4021710495110780c00800804e12481a0940341800710700c500f101c66000a4001030155009145250110348180801803805924040c240005096030905400580c81468402c0c1107080410420010302086d41d000300c000d04455885c803014901c000d20007010344c50041580c820035070003600034101400c1100d03014840c270541509201c1800f6000c1d01d45903c030b841002c2c40017801d8200382443d41c0740e04507080074140b400c1540750240000381940c1da0a80320481c00780340380010790400d0b00443d03191080301403003d40103d94481c10590300e0300ca40034007440d1152008000400c094500030703071010051135100001007200d59036951043c0d04510710400f0030580c5400040c002c41c1c40281301d11590804070382c42441c3c41c000c8011a1381d4038800d078900e005031148144200510005442c0d21005802c00d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 893395323 1250 893394073 893394091
    0x105010302031302060f1c0e0a02010f0e041a040f0614120a0501230a02030c07030807030b131b05030606070602031003080408100b0319060b06070822080a0b0609 71
    0x85a111640401c1d40d46d444103840c19203520f40031400740c4584001244c0d4020010a03810240074100c1400006510b420480740000d0604c5503c2d5107020140d03009110550752104000c004020b100d20748965685044124000680f040d0316110038801d0010346440b800054482c040d110f01194810320707080c41881d0301710f190201440e20840140d01e00041007401004800b03803580910388100303e00c00903d03c98404000d0000c030740250061007008016100c8600f5162203640601c4d043c0c90941302d42c0c1d0250000c000841390240c200c2c02142002d0141c40071900300c01e00c00d00110008200600d0541d40031a00c50205a50707003540004c3c01c01c003242c00704203c4c1c3c0185410104c5003091040c0c4c16500d0b6541200b9900607403050215822585880030804200e03c80c02131151011780241c80300d000134582c0076000c4c01d03d49800030181c07565004488010f80b44d01d001d4440c21340e070003400703507569908504140b5640224909580760b2011a04004140b003040400d155040541c051600c05450302c480c010011011030050201031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 893396573 1250 893395323 893395351
    0x2304060501090b060c0c0130020d0606090303080c0d02120906090601090b030c040903020309060d0e060f0402211f0f0c09030201080f1f150315050d1112072403090308010501030203 79
    0x19100050b0308235100e4001c00600040c1d440c40729086590580e441944104103000c020f0008102181d08082802d5000a9255019543d804180f051038000d002d02d0340081c40010450042100c9984002039082c090700869044a43d6a81d03100c01400c1500d01c48846070350035400c6440b008041d82020b800600d01c0901c43e00680b4244000c034004108290400d0400b4860701d40c032040e010102401c2800091b03000010716a0741c0840b450b09401140307403c42400d003c010500602c1d111b040307030714005012402160980b09401003807004614101d6016117400c80000272424a801c004580c054094081b04085980c103840703608841d80c8001601c80c1c000c400034401080015828000401700400020030b501814100c2c2c00089500040d1740000e04541805049220303200e084402409203981c0d003242c1d60b442640c0015200450328207040400c03500c00a4180c600c0c072620070b02c0c20201e0018512282043c0300c00c1000b02100491070030390780c1102501c5d036036140940803455400050081c1c4d482900150b6100003c404510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 893397823 1250 893396573 893396627
    0x240d02070f0b330607021c06051003020301060e011a07030e09070503012321010b0405040530120408070f05030c01061d07032304060501090b060c0c01 66
    0x70040305000c6500360040e031001003e10300c8800c40400d08100380361030995440400440b001c0480c41c1c41c820500080d00c1003282482c0b0801c6001503020520856074810030074007040c206080a079221264500040b8425400c01c10003141100c90540124102e0b0f41082c41681c0107054030200440650200006808010044603455a103458000c41c55000e04402d40c1c401d5601d6140c0000e60250400c480702500d1406244100841d5907a41d08034807892052020902e07000c44080c40da0850f0040404c2c1c00466082405d20040005014012840c00c514503c86c13003100920707102c08070041701482810800c6c440d8220013800341e08943c0d58526002ca512922901d16503140c080e140e141c1c2c040c1e0200348031003146c40380d000042039580310f80c007801400000d103404004520440d01400b40c00364500703002040e6004140d0354011032882c411800248128888401c0842c140c2c6042c142060700180c0360074003034500642d0900c03050319020b0910008442c0b40032164805809056080001101d520340210011014440304800c0e030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 893399073 1250 893397823 893397833
    0x5070918060e0303040210020109030e010302030702010e061503010506010507031e11011821090b0d021b0a0b0112050d080703020910031d03071e0303110a020309240d02070f 76
    0x502c552540500550312441d062041280c4091074901031070859042c9600c43c3c000a411224401d0018024200561030356203800f0100d0041c04402a0040b1500c20ba0f8107100d6100920301c00303680c41401c150000e02c059a100001501c0902c01c851000b400224034005001d120014203007804812815450010030140b0401e1085081d00c0305086160300510783c03203003944100442d05010b5460cc1ca1408000c00840414041c054080b01700d0b44160092504000f40ca092300b0705a03503040ba00c40100c920083d00982642d03001c280c2e40c520b908201111980b80c200d002240c0240c0000401042c03503030000c0213100d00c4000c10300840d40220043d012805143d000c0c0441c08070f40d80c40c0d440c0c40c1120141950001108000e41c4d0644c40b00040d284c3d00515160020090000880c080d0102020404a50100c205102c0417920b0100c000b000c801015001d0000040703040a501d80d4040002c0c0900d55045810b05a03070300f030303441d9042d480e9000d05035403101d0503c00300118892600c454003c0c19420b802080500e000713440c2c649403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 893400323 1250 893399073 893399081
    0x7022e0c080f0a0522050c1207080d051602040f062408010e04081e0c07060503150f0a05010e01120204030c05090f2202041b050c0106120507091806 65
    0xc508080703407109007000503503602e544480d82c0c01a0318640610182c2468656004403101a012a950040d90940660b043c010104072400702d5a50203400080045840c0003119282c005c00d0243e40410301808202c2444148903c043e18801c581c00b4060120b840550f80c2004014080001d620299030384402c2c0000340e2032064151502303540002c5c2ca41c4400441c1240c401040b2490580003034040c58001c1d41400089201031055a0054211900e0941203850201c00b0b0b0410b8014001c0440d01ca1142960100c1c0e12070340000a54080c00c510010b02400024002c2080340401281030b02d55002980850200250340c07052650103419003042c1410f4020448141e2160241d80c010f4000703603481c59140d10b0401250420b84200c5a200702c0f9154220b80a081402d05a030b208100b29410380ca8407040d202138201507684541c0540904004524000050050140041d00d9908002040c990319440c2000c00600741c0d0710a00302040c8654417034007500c2100d0400d40c1050041101107540300860b81c0035401178000650b0762003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 893401573 1250 893400323 893400341
    0x61201090b280c0201021e12010b0702120a05011a1c03030c030b06270105040f0302010302090f03161e0e011205030c03030a05190b10030e0f15010312050307022e 71
    0x1001603550503162031b1880c107c11b4442c41003051070200300b1014545190101b1004e05484501540c0e03035444c403840c00040c3c440d00c5c5418929025000d03002c01e0904000d4158820002801d0300408010982034071002c0282d510a824032020b100200b0340c132030400003442540611510011b03801c002540c14502ca02244144d08000503528403083e90800301c00c1d0134031202e094060a03405c241707007103440d041c2030609004681c402d41c40004e06040d004144840383e562000300304080c406024040302c400113001564034992550612880d829080241d202482944144030b807142500c000e11180c0700c599182c20342c03e00701450440416030366400705110904031a101400114001c24809601080e070341440c84282c1122600b0703035000c0080c42d180030f032103034244c0d00d80b4000713119680700c50304001600c59284400c81d824400c286490a070f29010350b000c6c580107008400b891030705a90003561020240300400070160f66611040c3d510300c0142c0c1c080c29600038035001100b040391019000481952082030150442420354460719 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 893402823 1250 893401573 893401577
    0x30610051206090a200d0b030105010302130207031202070b1503010507051213080415020601080102040510080a0905070b0417010204050d02151306120b01020c0f010320030708061201090b280c 84
    0x6840b41d41b00300700b40074034040300a049000b00710b15451980012100e410065900d03032034030703000700303017030040c540503c0c0020300305200031070300b956149410314088850940455891280d104000300742005814144181e51040d9035a8944030310704070f142254100711540040404001d8050098100002330303843c0050300050080131440c2c400d020540b04060b003031800580020410f0303807050008000e1f03640c0306024005e0442c40f0b424690a036403075003511040a41144540030700184180d00300055120302c09401402260031800c0542c2d82c0510144c1d899084c2e2040d84212030380702a82058840c007500c0c200c907a403c5000301742c0100034500803000c0c02d20705030515141c0c4254041351000e041d00751074814038014400c846409101a000d03501c3c541c40000c0040d900104c1040c101651802400c100e5141d16003030700e100e07051050001d9241d20702107000a252040440b0724500480b060700c0a0205804140616001d01d9405010848169105503aa80b0084044c032070502a044c14000c0b8035407150181d22401c004031901d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 893404073 1250 893402823 893402827
    0xe10050124120e03070f21030e062d0703140619060e15030411120a08030a090f0204090c030c062d0c0803010902030610051206090a20 59
    0x402180c180030010030201c50040940d400041a50561203410303102d041031199000148954200101450f50244400081002c0c0c00c0c200c250050007000c082c1020100c038030700c1c0846003400030303090201d00f036452111440c0310950080000c2032030840e0950101c40100484514895940550000b0807421041500c840004c60b903101000076803270585c3c6000c15848141a01c01c1c800e505003c40c0d044040003014400c0c50108445811154601d9980005200c0c581200b081c20303e44a040030b00b04100400c01107040d1500c2200e8003040a6144180030945411f07064220030a141182d0f21410303020080c0a60035012a00c010390030349560016901da1140d541610300560007042000d06500d800ca00c6640d140d04200203001d50310080c52540e11038800d00b854040400051000040222031060b40c5a41400350001c1510101200100e07040840390b01440c410700c01100c0000309220b84040c151840c1c0b05507850301c008410b00000160107400c01c400c034907800c003038942c500289805030786040342c01030001000850a0f071100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 893405323 1250 893404073 893404079
    0x9190515040f1502132301031a0a170d0f0909050c040314060703051f1a07051e0d0305060a060c020a0503010e0109050105160e01121103011403010e071a0d0e100501 72
    0x351145c1d0780078150031030f942c80200c40c24000310081c0280c0d030101c15040507115602a601002c040070075000403d00500000c40094a034a13040c0100000b10034084070300c1c40303904428040700e881140d580c0142c188644603c8405401e1213140c1000c0c040040c410304110804000000001d001c160100360101000d030003601c40307030500103801421350320064041e00f108201c9580103010b007000700240004440010a041087c1140445122143e000d2044050280d00074114141d11081d11403030010300d0303a100601958001103034203100340c0c200c8034152030b101e42001c0c0140c02400b903903024201810042c1e00003410742a40ea51f8403c0024252402181034800b01d0b51510040c40411900340211500206044040400827402c2c82c0e0040c200542841010304000044c1445040d080d07164bc45243c0c0c1c0640001210740e2036031102c0c0e191141c504041c80890181d886c200900707031070142c00314100088c0c40350029080042014101000e42c103030880d007000d03180c01740d43c0c10041e4851041004080301c00c0b51031b4107011903250700d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 893406573 1250 893405323 893405347
    0x50106020d08150607020d0506130308090d09050d021f030b0109141c0c0812190e030604231506090108070311310509190515040f1502 59
    0x40200303080024440d02d0b5080c03100f0008812640140510705464464442c030040c00011101200b511014165000c0c0c02c040c440501010700020140c0d03402602d50300e00c00e8482d400c3c080d03038031417114036580300103500a0424072007444c106045030161800200540c00a28007101c10103e8150401e92030350201c0e5450342e0051640d41c0050307282000700146120b520300801284c010482c49103480d9280624200f41041c201b081007803c030b542c20003800180c8101c0e00310b207800e40d4000071154483c103042c0b04505650911880c001d4030030007201135080700103000349c401601e407541c510300380c2c2401041c2030505828981ca0400f4031007082202c2c22215480c48148561801c00c5001e0011036001a04580309980241c131040c000b007261114034000384c0c13500b50303203990418001c8969100c1c5d400f1380d00c2141951007003000d030301c42c2d000360290007040c0a01d106405a4103100e01110104030b0b07c4200f018010700a4101c01a22100b0300c03d80c8204581c42401400b04402c4800310350760301f00d6101e09201d2103e880c80e0b80410240c1100d9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 893407823 1250 893406573 893406583
    0x1009020111030d0b010311120f0c07080705060708570702040e0309100c08070f050c090108010c0c060f0e030415081303080105040b04060305060a09170a0c03050a05040503070905010602 81
    0x80f041f941c61442d00c3d4408803c00542800180b44901283d62040417072203201d000030854141c0740c0c100c4500d82c3c9a242d2450859105d00040e1046400142c04402027841015800d00d040103e1814071054418445207803540c0d03502c0140842c0c40346614a124030300d076007217040e1200b061b0011100b040d001e5565520310300c1008110340d000c4041d0300e02e5510501220b0707440e0b02c960f00301e5122412181000421414170303142c20302c2c0314800c0100080402485041402c108000004c82d10444c4c00111017903652030ba04e4103505802c03034190000c004009540001c400002c603840b40d00c5106003401e290710100d5004001e010750b40c074540c072070344c08500560102240080e0b001e9006d100302c0e0b040380b100081d846101546440003851044103004841c0300e550782d2844400d85540b03592004008550041c1501c55901e0081210f01c02001e6424003a0b0344034900b408660500086c050854004100319103840c40348408503102140d198000002c0a801d100080101207a140e42c20041d01004019000022030b00c2d6060090080c141 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 893409073 1250 893407823 893407841
    0x1710020d0e0f01090c0e0c091c062d020a0e03070308040501110601050114090d050610090c0e180702122703060601170c0d090b06010f08091009020111030d0b0103 71
    0x1e41d01d0820044002481420340104039100405846c0341c1d0703268031400d22a24401d880003968820703241808100c486807654111118603010380420401c0034103800701c66206400d0b072611598010482160180d000719154050035000d140f40c645148000c0310790002c649080500d07003040d80e4100d400b0508001c2036a000c03840039900c1d0b04220240003e0b51400002901c1000c0d6100c42e007212400c0400c101003281ca40c040b101d400550000102e8045082103000c0b0324603040b680c020039407000e050401c100c1d040c90142c10000012000540005a0825917421041d00481c02070000300440c064482011400b025142c0689680710b801c2480081c070034442441660001c110788a1750307020390042000c2050a0b030b044084120000200b5040040503030351422a26001d01c5000c1c4524446407405200a042c040001c3c5141e20031070080c0c849a10082c034540c2c0c2910745c54421106184039a001d0009046001c4c5140c0143e00d0841c1306041490341040d6940c5401e0131600b1100643c1c061640c0d030001c43d1036640c1d05008035078603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 893410323 1250 893409073 893409103
    0x307020f0604240c080a030c030608031e030a06030807120f0305012d0902130f08012703140318010c080c1213050a05160911041710020d0e 61
    0x7810b0700d0000e150100466808203e590302c1d040c0c42c00030646501601d05192107130b52041e9641d0740c481251034094000c114082c80c1e500003030b00d820400b141040300001100c8401404503040f00c1d92a54001145020380d00041142000d04d0715603800000003144c4001405130a841045143c880700005000201011001703a07050341058201401008502ca10140d0504e4241c46c5e24807000c1c0900d81142000b810346101d92010355558800200e1121809103d044113040c0d6880501c2510b059030b482140da403c0e07500740c5440e880780d00c65035442490b0804a80d0304070001984203003402d010070000300c00f143c091900100c0c1c000d00e1403502a04840a0001d080c445c101880e221401d01d28010b04050400030b603680100c5c920b1200605021002c181d004544030900681a035001d02101c40d500c1640c40c0c103c0d142c00c140503500703002420008000c02c0451042c0034a04a4212508c50a41000c0c0350080d00f40b04150001c854104034098296060740030109800142641c031820f840128036250052101454407040d80c1060507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 893411573 1250 893410323 893410327
    0x91c0b0a050f1005060c0c10170108031801050d0902040f0b040c11060a020c0f0708010e0d0c1505060607230c0f09011502074103060c031302090103050307020f06 71
    0x1254460303c030030410a64805507101d54407000420320480c913098510650b1070b404541e0740d1a0702e00c0c2a070700040c020180c0040c0c406040242c0d913620002540c0340940780c00c070084403042c00b8128506510901c007524090345180343c00f050307202040c1c0204040368011281c0305035072a00c81d500c00042d402c2a008060144025250004050101540064941c400903065014007900044c40d403080a10410040c61001030840c1540c13034042c0d03144500742c001c0c0320064000c60b19000e00001d0030705290140d19554104ea030001d0742d10240c0e04500c24104028440100885d500c003605001d1900030803802202540c2020101e01c44007180041c8403106890422550600740c86054581d040c20b4042d11803222180c1181c411080d070103549803801c8420390a041c0c19811524a42c44006055241c06058414001c0120100c000140007401e224010b0348000114042803905903002d400440c3d0015840001168002191a08802e210082c1d600013456071200f0b81c41590154004680c075019840d0004940000c0803049601078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 893412823 1250 893411573 893411581
    0x6280e0102030a1d0a0801020c0a1415041b0801020304060e01050a09111011460b15060c010f0501090e10020903010b09040f2a0b091c0b0a050f 63
    0x10184240258100540c20b1130840c00c0040d62a641501e4000d8a2050029500e41c108041400c1e62030400e184151502352100034110f940100c0490410a480300700300e00c0e103096030740c0c81d01e404110030b50b02850f00b21200d1002c500090b85000a03c0610300482c8154004518680407656441c00d41d1070141c4a01305552500041c407002030500500c0fa0603002c2d040d902206002c1300a0400ea86c08d11482550070b40600413003200b40541c1d0454503440c0f10140f050300e1045c100240d017120f80380d880038524203868001e4500b102c1c81c001084007000495070000d080d04115024030740b2007003c1801d13a0011000001545c0d114100c45407003d407980107a07809803c00030f108001444074604910740e0f0700340090307500100503400500a08240c074290859102c42d81d001c0d0100c0c4090030035203020441c5580511095030a44d0210b40c1a21001548003412a40881c89030f400d035003c60700300700007010654016200942d014034071341c5221850400d944080c1d10207900501014034070b4a4154244015500b008010b240b628580340208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 893414073 1250 893412823 893412827
    0x30815030a020423130c1d070309020a031211010f090210050c070b270301050f01050f0a090906020c120702102006010f05010e120a0b0606280e0102030a 67
    0x7101060b804030360115120301c004112040f00e0140c40300e86402c40501100b00503d558240f0f0507158441d118412480c4003541e502020010440f00c3c680341c42401007100003142c0818400e41002c0f8280c0c0c00141070300fa900782c1c1c0350340b0b21080c07207500401600800d00710b0404504001007842201e1008080e900144260a52640003440703052106950a081c400c02251011488000b04441e401605c0c5a00c2030b142e03110311565034072542200700340051259010262030582c0130b040601556024801c08050100180d08000411825540d2259599084800c038000040e014416014001e0a00d003e6600140c1c1d0740111054942001d0300200d1000514604005900058031031040003111a803c074034220b0106910803407114201c0180034030949052082d140040f80c0550740e010302104842090300c941c12241240000e1210848010035112040d820840c01c503c0414402c1c000b07140e001d00010285071038242c07005d5492408518520540c42c01d07040301e03090380c0041504400c5011042000340001d40c20411700742c2d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 893415323 1250 893414073 893414083
    0x10504080d0c05190509040606020a020a05090603150c0c0c0d030921051b190b030c0901020a0b0108060f0601030621080d1a041d0709051e0f0403081503 67
    0x164100140d035460710b1a00041c420b10503100c0c448440c1c01c0076080025848030040a54221041003803203985450070029985000080140c1c24550207030610348014a8001008811400207120940502402440c81990010442220703c03907404400210784640c0300300140d501c2c0855003034040d4007420700020076101180d0082903850449400e004034088100418802150240315640000c100b486810b01d02a000702d0201030303075425180300740d40324500a1080114a020b00010313105d10182035000308017169030152441d0050601c41c5042c0115000504540c0d00c500e022442640811440c1c0c204a00f4070000d82d00410b41190014024a0244045401d040c641c220300da07102c21040c04581100756020003041003070700a070380c0c1403da80c040410100b5170322a550348500c0390078910a4030403450086241c55a04100c103e1030720418161009105003401c01c0307241801000050b00a03151111400c61040c040300100d06250f100b07070f28408020b00642010729029042001c05000c10050719007603e107140140e180060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 893416573 1250 893415323 893415337
    0x30606020a060b210d080c0a1d06070813060201060506090a0e07092d050d05062403070906080c01080906070e061b0607170c040302130b03150a0e01050408 68
    0x1900041002d03e640003c0c030000c1c4e20702144100309520007030383e609012001c5040c40005100c3c2d284c00059550f9040181c0c007030320507418003502140140e50112400e40403800c1c05040d107040500000d103850400d4652400e10303000704000c200450828681800043d0342030061200500c41510340c541804602c800146403c01203000b208410140c007000101e07080d20500005000345411081c0301340c8aa1150100b41d10030318140d1800c0b503104003035140000c4505280500e604401e402c900030700001c1e00d1741c10317158801000402809400510544002d52966400e100344002440e41110008800e403412408a0034006140c00d154140491003041085030900454020780c015002d00c2d29283d00481a800140389000d80e442400782509034840c445410100001c40c1409407101e074950b04030390300300d164a16040c1e07107040b6010b42c1900700c103010410060800305041e121001c1e11141c00f2480340b408001003882e02294005881e02e030030050042c85040d0401d407003080e100d41c0003d0000e0141e844c00b83c883c4042d510400c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 893417823 1250 893416573 893416583
    0x9060306050a090e010f0f06060f14070602091906030207020f010c0506040b060d0605010807170a0809131d010f050901020702010207120303020909040309060207270c121409010b01030606020a 84
    0x20058104d40d0b14203500c102441441d10b0410440d406c001e0109100402d11402090003040500314001100c50081c000365004c8054280c2892130244140d0703035036000e90804800950042c0c282c86405500a08054401d4041e00c00d603600141c540e405401003005010107012202d05001c261074101d0b02282c40401e40a0340f03c1d4000c070165001d6190140030481065000e100503007000e1400b400400c2c11080410300c83c040b00c2c9244d8040c103241464401c01a00c4039401b041c0101180c0f0204205001403d0800d010395134444200c00010381689403510117400c2c0040503a40000b503941d00c0c050000000c1e0a80700b05500984c03088000c604040c280c2d0b0010b55500c00900a4000710040c040c0704074101840ce804844009d40c02070040c1120341003d240107000348440d40284001340c002c0030700c00b00b050610844141c5502444140e0b0581e0004e01d440400020b2840c1000d40007044115030040010321014051403135415500c502990692070034628640c2145c0d00c242c0030034100b5050070320811115600107982c80d0710f039400c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 893419073 1250 893417823 893417831
    0x6100c0510150801051501091505041508160e1008040609020a06020703050f0c010c03082a041e030305030106080c0c12030a201c0b0604120309060306050a09 69
    0xd0900c1403a20001040311001c190406180444000546210300100c1d00351100a102507202d2015224405540004260004003194070400c441c4440b0015000c0000b01c604080b07142c07542303c04c029a0b100d0043d10380c040c0801c86038802c2c42050040303201d000380030368094500440d40c122103200055881c10b421103030408024680000c20144502c0380d102c0c41400743d0007041003030026507511000c1d48405171844280c800b4098850028004c034000300d403036520000140e68414401a02c2d0b03800703843c000c0c3e000d020800040c409914040c551090369050a1401107440302c4d080d12540342c402c002d036080070030074810000d0310400d00382000026007010650b41561290b040407100c40e82c43e0030100ca094024504440101d2240580001c9100f032030000450117010042803c6c0b04403141d030b0300c041c8040b058258000c11215000c0004041c14061020300c00c0c030740200c00d0070110350141c020300050544d40090300031104a9030f041316540201034100450780000c2c000341c10148600c5c3c0c44c0000054064100388582c9d5030403625 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 893420323 1250 893419073 893419097
    0x6050a050a0504080a12020d08010302030a060e0f34030b0601030e0a1e170c2a041e0e120a03020715020304060f0605010201140406151d0f0f0610 64
    0xd42e040d603001d400320308200c52104269042c080d019500030030161000d0b0040040301d10320184218101c0b8103803a0050000c00c0c1e600340c95500e540c01004484442a1503000f480c0140c52940c0c1c051000c0c40c900c0c0020710300c1d0344d85080084203184540851041b01131981d502102d0403c0058a03000c01264004002d084c006180303882001454101010b001e40107204040c10721500f01100c03481582103041501509c801807069600342444484c0348140002c809244e803103c0700d4641c1c00d404103503840204400c0005035a0326019070b040400c054420f803250b86040c41a40500340100d0000ca4130681542e40d0024000f41840721103803a04400c10b01c1060b03031000405800044810504c44011441100056045011541d07031078982403280051240002907506207042c130000081946c0305015241003e1607000f440a402e4485564640c020b002504030400010f600000010701c1991201807150016a180b1300441c003032608000c040401303500140041c01d481880e40920074681c54008000c00c01d0841403c0020a92203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 893421573 1250 893420323 893420327
    0x140a110409020f0d11090c0c0c0414040b0c04080307030c0240020f0c0604110922050c040c1101150b07021915030207020a0803040501050702060304061808091906050a050a 75
    0xa40c0c0c0d0176243c201021200307220002e040c4000800c001d0400905807480100d4441c10401078502000c4a40c4083d610100400d003c58403c0c00c030160814a20407501d842c2507601c400a6085800a1703070160085140340e080c29095003440c04024030000e401760f92000000003154031b40c07030080c030b8110544420a10101c40300c0e10303002c810358120b0349040780c42d069280d1101c00c5c413683c0c5136503200d0032a4126803c10b40303650304c00a1400d010b0728290040404800c1c82c541044c5080300c924103009001400c0da880c0c41190302076801c54885129505107800300b07603250717041d00c00e07402d01450030342306404001040d045d0303561020890365201c3c80c26103500b554111402008251884d0b50ba040c94201c641290100c02440f8141659507a055401008000d10075583c0841c810b544064482d00c034083c600c102404582c08000490052410500441d07019119210010b840b0780c0307808003003078144003100048a00503000100c40c0c40c05c3c60007260146c03402c0490441c80820600346540140325009070b000101c2403150216038182d01d98 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 893422823 1250 893421573 893421593
    0x90906081903020c0306180d080c190302040905040b010f0f031205090612010b0a02010e07080601060f021903030504060615140c0a02061603030c0c08040b03040c03140a110409020f0d 80
    0x144010100d641c07c7c00c244020460740c4020764415220b6109005c9244030140c00307401814825071803440d002d81003009003141e242800724040075140c00c0543c04c0001107100d500502c551805a40591b000f20055030514240c5143c0b20b070160003180d12a0381c12034040000a40c010300d11142c4030040e02d40707170340c480c2c0445c404110b4034054100d280601e141030a0010a0709102c5401401510945900a001d0b00c10103400c8140c5076201070003000c1e410740103400140000c0d4041d135038459180d0030a00c104c80e41611002070050500b50f890a040f400252a40c0074401030210303038064040075250341036a1006490000c5000390a40f1036141510420040c003045026050000f0300c41464600c0d00a000c00381d071820300c030b8032001069051260450201c0e01d000310f14034190344202d1a422700a07501c451503078034090402c003000e241c640000b00102c0d01c015070740401000103450200580a00c4801e4402058800083e00c1c00c02c2d112411082024041c03441c00a0410150791001d010076a0a9400c1e20f080000100505008002c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 893424073 1250 893422823 893422843
    0x30c090b011b030806010201110403050705060318071e0b040e0a09050c03010f0f050f04050303240a06110f0d0903021903051203070f0507211808010c09090608190302 73
    0x3164a440b403030000e0503004003045201c0e2000340e00030042e03000603003107e11050103030b07010280ca942e00000c020303c09030074400300030b5030003400134800c40e036501e400b4811041c03810038150043c542c0c2709041e403000d121150b00b9690020281020b0b4902c1ca0400d82040d0808035807236030007059030364616212150300c01030040078401d289583d507001e4001d010080c4445c083c1c101070400c000f000c4150f41d01d06070010303a8401d104058140201d0707002024501d180c50b96040e0070b01031440703104a010000c81500340c0d0710303183c0c0d5190507800c02030640d03440700850324a0810f056414440c400d44207109641100150420f0a0760141e0210284c9604445440103000d00641c0d010b010b00b4907400c010a50712410500c04802c201020183d8031607034490361640c684501c036860444040c001d41380d00402a000e011340301c0542050305101e01484403601e10300183c85080c4591290313501c51081e880039285954030105060425800b03c03010000c3c1c1303c59541404240c0ca45003099544005a4190201c026800c802c8901018801d105044c14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 893425323 1250 893424073 893424107
    0x3170411190e0a11120a0b101e020706021c0203070501020406050c060106020d020a0303020c010e0607110d110c100c20011d0a06081905090c19030c090b01 68
    0x250303180d039082814064000303000d00050a1000c4001601d803a05134050074807002e104c1c0e509641401c41a0000340c010380c202603c0030180c543c03106282d625580324111200c3c4c3c0d85020b80c0d517100045424800d03628810b1010312914046401284090004075000184003985500400316581d002000401c2203055000c0d042004100354000500049c1e043d600c00c0c0a8060803041c0c0b01034480390b0341d8a0000382d03601c410905061002d070f04814414004280a03a01414000503c08004260140645402c0d4240a0204c8020003c10342196580c841c16504000c610315003040303800c000c582c4003401c860b0030344d035401001802031013008032946200709244900346004205901404a50384d0000d01d1100b409040641529140000c04000c1400d02503070b1a400d0602e2003403000b0b00300c03001c604d061000444a1240003459843c005202c3e050101486d0351a00c500d5101d805254080c007540b0101204110040c01500b1001e10b6421082a003400815090b007400e408545402c0340016003032480300010f07181c850840440d442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 893426573 1250 893425323 893425339
    0x1706071205100605030a14160e0303030921070f0f0b070309020109120314210a050601051e0c0f0a0c050d0c060516080a020f0c090c0a050702130207030224010303170411 74
    0x1c40d03583d018101c00d410609644541d42d46480f030318281581c90104480e140c100cee40c051080f1580c9070b200340e0306803060200003d040390720304242ca80321011b03002031090b8210362044441d52102d0500c58082c0c0d030740b0780000c0c03e8603090141920580008003002c901b4040d00803040c001c903901c5400c150080c00d11a200890394001503071910984415001941c400c1400070180e6000d0300d0028541012a1068522400f1305840311030510981c0034a120401d4540301c11401103420410075094120b4040080904009141008204020052801210607042c03075100500038140804800300050b1a1046842a80c3c8245052070315200861030900169a40c94005008802d00007011088280d0115a2032102c45412080b901205200f80500c4198141101d206c154500d042c845000e02c81d11a0b001032188034001412400604a0031404c282285d0005004501684c004540c8055589039004080070003000c1d142c1652656140d0b4038003408256140002844520482c4005000c1200200c0c0e58104d2802c00f400402e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 893427823 1250 893426573 893426581
    0x302010e030c0a1206060b1c0903171810060501021f14070503090606030c1e0103091a04020a061d010c1415010612020424091706071205100605030a14 66
    0x134004a000d13041568a1410901c0c04901c44604c0320840303119104040070119668400c1c1100401080c2518044080002d620103948000008a074400e01800d0303010480c250382c0e01394030b90242c60105c4203441d8140450a11204001a030303000320700c0c00c0d00800c6c08052503600701495040031004040360300342e00360305121080601a0103a8004050743c4200b55910480380c154552030101559070000e480040d51000301d0121449022a000f200039071210010704000c01c4601d40e680d0780c05010440301c0d10218808081104010640c5040c150740700040c841400c01a03d121520031400c44040c800200b10382c144591401441d0801100352042c4060714840c0080d200d903c0c0724401c11600e020390038400c200005074003241000240d1810320842d0111006081f0013058103c404d4901d411b040a41d00020b414411041c8000828030303581a02842c00e2400c0303002030240c921f00764402400c0040f101401800d03c80c0340108101000502d81c6002040d0f40745800c8c56600c0381c0d68003482d0303006000b60409000c42c0a0401c8240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 893429073 1250 893427823 893427839
    0x30a0609120e03061006030c0504170d08060105070b040f080403060f0b0316060804142b0206010906030f062a0801030213090b0a1116050c1306050a0302010e030c0a 72
    0x1c4038008400d0341c2c0d400108001101056914501942d00700b1002c0c00200d01002003600136403014144001c5410014102582d80d111541e0103c0b607400000141d401105d02100080e9120281c2980183e007403e00505141050312a40400300c80100010000440108a14180412101600d000b954010f809022501e2100d01a070003030056050700902a120340e42146003203000350300d40102030340c5407650740501c2d5940b203440e0444904100d1940c0c02060260b07404134150703025000004180040c01c198820104190408001c1c07500c14140e1044105a1902e00d042c8001072015030301c042c000d40c00150102d03100340240580b001d0351780c0340014240003200020340409000c5d00010301504880c02200c002e507643d40c0c5120300205407a20081c0c002c01007018000024028411039010f4628070790800290f81c00c0c00c48070b80003118001c0b5607078400d0b40c00740c0c8404040c1543d841c11a10500000154000c240521460716010654074101808024144110b00110903080e4034204a0659032400c0181030013a01c5646040c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 893430323 1250 893429073 893429093
    0x41208070f060e12030903093d12050717040320010b011b02030606010c0f06020a030509010b2418130204082b0e01020109050706091d011202060306030a0609 69
    0x81d40f101809080403041a201380c00007a64440e450780c80c003542c50300418800300000301c0340b203200310007500c1c01e812400048144904485c6001c03a0490741c0300307a030b060309800000d069124211448010716061408000e0880c1d0b01031244646580c064080f00303915100d0b46810f50b886864006081d0201d62108031403d000d1505420242d120407003070300e541c402c101e00075201d051302200c031620183d003590200e000700341e040d4402c03100d0001850060f4049008080703603548d0715060740e00c98902d2000007901ca03030602089030300071301c81c3c2d100b140701c02c49001c501007403051050b85102e10701c107050448038507000c41d1500424501d0508030301501070003031251520341d0740e5041801c0250402e005440c51440342c007040c1e4041000b85049031114844c0602c03500b40c40d104c040000c07295121200120350455482d2040324000600400c000c0001e0569600d60844450034040c003000584010f140301c030f600e11260f02c0100301c0d440241e00000001078050300c3d07a9a5aa41d100e02281c07424000340001006a80750501303aa040c000001c0e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 893431573 1250 893430323 893430341
    0x140a12030e0105010f0312140705030d060605030601080a05070e1521010b09150c011b08070504140d1109150a0b04180b0f1008040b0702060c041208070f06 68
    0x2000c000c11940d035819070742212024020120b03164820074040c40403640200d45c05001072101d00d40f034403c0403c0708140e2040c6401c05ca60031078040d400480c90100d038025500801000d0031491402c40d0a51400d540020030000c80601211800c0e1742c0c5601050180d0b01c1100da5a12445000d40548020200c00a0102580d1701280d03000c0e014800fa040c1496400d0140503203079041718100d50f801c0d070914003600304010070b81c000404410840001003001411011080c00b4844055401e1100f40303000445081000d00700301002014002080800c01050088040b110300c0c0c1e40c91448161000b04011101c2d152048209240da44100d0341b081c2804100300440c1c4501c04007030a03180c02500d080c06c105540b0180203901d80194001d100d40705030b640e1049807032843c00743c1c4000301c400d200070903821803140e102e0042601c1151752850322001030b024500704024030401e2020700d41c002d000d6100401c05441e1885e00f0f07810b40d001320300982c2200f0000c00c0c0141c05002c1d0718000d941000350040300090050b440c6103040001460001c0f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 893432823 1250 893431573 893431577
    0x504140f0304031b230103150314010f021c09110d120e04140408090d081303060b0d0c270609020933090409050105010308120f0402011b140a12 63
    0x12461120b5550001c002080700c03050241c0c0203000e900303a240d1840c42c0c01645d9100707040654a00c600001c010f030002e0400c2c011802002402c404540c048400ba00b52541e4414524505004200c1c00040c205105110192018500350010f2030395042d10741401214020b0342c0c2503900041c050400c03010700030000c01c0300100315000d882d10041048013400307100903541da841c03610040841540000e00452040001408401c00083c0007030442501a60f076841c05400600300030721180200c0b241801048071038814240e80401c21180b000c1c130303c00241c0e1031801d101080c0c002d0343c2e4466401201c00c4a50b05802c6c265030700c030541e080c2c018030240d52100320200003908400040ca218601c00b01d4100c4200088000c10000c0c499400c0c0036950140014020b5003941d885441d601c1c1e00305550b00c080c5004110f0a1080314043c40c400d0b00c0003039944000040807603038008040c104820ba22000800e000041c1e03000040c48514201c2014007030601c0042d810028000c018100b81c100030350188825401c10091031b42140150b001c025 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 893434073 1250 893432823 893432843
    0x15010e0405270c0303030403110a120504140402030108100c050d0203010602010b0a0e0f150a03020604031b05060a050703180305011805070803040f0b090a0f0e061c11040504140f030403 81
    0x20b08100742c2e2101c0c602c00c183d4042d0410004140403911074408a00015104811117040001c5079541291100f2441704800008001003000e00100c01d01200d044400720b4111815421035041403d41d544800490380e42842d02581d0700054448940210140e8880500c4e0031403c40d141d40c0e4035540a4081c04000310b070a4440c00d0030f02e00c00f041c3d202c403040100e0301803140034030007440075038072441503001441040020700d0348064510b80010040e91501d001304081d510903601c000c003081c1080000403007000d440e0445441014140311410100e544142a41d01c400e40614010039505803403600c03d11018065040034000b0350a0603902d001a540051044080728802e408135080941d44618113500c80c015070141e1700710130a4000c8104001c1070740b04081c001001b802002240e003e81c2e10840002d1020090340400343c0040000c0400410345808540381441002c82c061b000c5503603e06540d844c0070788030940c0301540300e181e845003c1014030030120301082c1c0c018401011241950094101181c0e030343c019100c12550300c9a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 893435323 1250 893434073 893434141
    0x18040c031b081b2404050f04020c0c04050c0c012406020f060411180915060102010b01020726060106021f0203040b1f09050c1b0d140d0b030105040f02100c080315010e0405 75
    0x11278402c960840b200100544440b281120400c40a004050304403400d0b06000d101900c0300c81c00038443c0d25600303000075414000c542140114002e12000a52001040d90440759050201c03c602260303080d88268400721070500d1117020000601c1c04190704440d101030b21704800412141010000f5418001c40d8450141038080d95201c004901740c1c0d5410031075500513044a50108000382225072000c40d200003604421000c40020648107180c8002640301800503806149400c440c0c105803040d00c08071258000040d0304d14949911150b030b03c0300001e0b201c94a0780f42d140b04000c00c6100c1c03824440016002e02481031156040c01c01c8401560340119052602c1c11046840010862000103460f0300c2948107500c5816942c420741032301d042c06420100c03040c0b4070a81c42c1c03000050039580070310a00b0301c245e100f40c0402080c002d060045c050241e10050b020403d125000700c0c0080803456920643e940000c00040c42940722000b003004030f58080c01d00c14a10f420904200920905800351100c900455201401402e65200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 893436573 1250 893435323 893435329
    0x160305130309062007172b0c050f1c080c2b20090f060711040b060714031207050a080105040b0a0308040e0a0b010c0b0c0918040c031b081b2404050f 65
    0x6202d0910711f822619800981c0300d45005845400c80a40200251002021260b102509101c001c142a401d1119401d051002e4103070021481c0c0d4020b0b0003c0d000070305041601c80896902803a1800800001d11050f40401c1c01403016000401803518906403210b000042e5001078405401c6040e20301e100c0c2c5501c503156510f6051020036580d04c190010007a55903072440d4400e000041141c04441c80e0004c604105c91404250101003c21518640400641c0e4803400c40385e10202e13500700501000108403017002103e011540c407001541c15214102c9000610140c04000200042056440100000e001117000990300070f40c10501c42c40345112540a1010b003056000440394884d44010040076909030002190000040b80c01400c5008000f0f010b0100074604e031860682e031a80201d43c01c40e229030b40d1150a004100c2020a00b25180b202e400d02c030b1519074100f480580d156980881600303000c107101c0240c041c155840c0a01c0d200d42100559030301d02c0e80400314081d6006540980650781c0550b242d0400c2c615103007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 893437823 1250 893436573 893436613
    0x1030509121c020f0417010c08010303020c0f1f051c050c0307080408070f2405060307061101020f0c0a050c01050a1403040213020316030513030906200717 68
    0x2100c5000310502e80b20744440c00c8107114003695448440b1aa0901000c108078803d20020f0015048400c135621070740120054050a4920034002602003214501c010000070b60005050b416000741121114446107613100891068049400c1da1a010300c510000d6140c4160003000070a10305031441c00c00c40c4c5040381984403100340c0e04107540001030f1000420001c2c146a1103101c4c9103402074411001d0920b40310440c0c4544400910050082e03c1449105075910b43c8031a411072a10201c0d0310a840903c0903142260000341c841e88184101c2060080d524101740c0080d07002e5040350507120311750125544840003003112640d82c0b8074050003241c9a200321204500c0c607600980554003d042c550f0741da21403000300006130038280d400c05441280c02c030036100c000c61049090f60010398400d8a030200030b07410745c03a02008000c083e00c03000751031404a14000c11000020961000c10f410549045041503840081d05c840590160032030b00030780a09600510710040350105012501d020b641c03146500f10358021011000e058161 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 893439073 1250 893437823 893437843
    0x31501090807030c1a0c0610090f0b030601061409090103050303060306070504050f0d1b0b03061e0306040807020d050d020321310803010b120106080403050904090821010501030509 79
    0x48100071034100082d45248174000030450509580606080028800300e2522000b134901d503110b0034144000f030042c03403a43d11404524202c8400c1c203001014041002c40c7d1950418020b05c0708026003000b012502100c1c4008450442801414110b2a0b6a49040040c1c40750800d96045110340240030218103003a10810958041c0c0340000c1102060000410030001c85004101c800c48040c900c056640c031496140700c0342c0c40c0c014200304074142c3d640e280100c104023005500b0500d20311040d8002c048015a40c03000a400b43d40580d0000311147d41e58034034000070701d5200c55110b004169206140b4000ca1642d40440134007011000d00701c000700b03000550b1080210804045421110b040d9219044041841300880c58079480c0004188800000c50340e603c404415601c240c00136480010001000345061581000aa00401080c078003e401800c0c0350390000c29a2046600c81449207440d82c04500502402c50122411500402202100304090145070114200240314481c0807038038000006500c51707004143c040302 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 893440323 1250 893439073 893439083
    0x5060a0902180714030601030f020a020601050316122a0303020313050406030f020d111003020c070504050415051e040b040302011119030f021603020a0606060311030c091503150109080703 82
    0x208150713a4580c241c50700014035290401d6280e030310301410192244000c14640e602030f809008158100000d2500d000da4501c0e14415070406000c040100c2c01080060034100c503031041c242c0c502c025501a030b0046001d625070101e0001e440808001003010780000040001d02851822100b400f5651000c000888140e40b00240c004400c001c0400c0052400d4180b6225040c451500c2c007052a40d0fa1012900d8900d403100004082076002544070850300c0200911802454111001e1040346042c1d0303070340a4540450315203107400c0c0792a0008544990b039a6030540c0308624402140e4101c1cac6c5854180701c002d160301605c00390095441c6c4190000c078610340340102d40c0001d41000c800200c5030280d2108034004c152000780400203603820301284610b0004000007100240c003d50040c29014110b060000403280280c3c00103003403529084001081e41d01d001d09581d48440c44003110b580366420040862002d0006c09400388100c0e0700001045001c006e00c5041a24210007a610081c60030b0721441e44558845603800082d01e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 893441573 1250 893440323 893440337
    0x1d0604060605030708090703141501080102130b0a02010e19060534260f0a09020a0302010509060d090501020a0e0f03030706110714010614040c171305060a09021807 72
    0x8021070003418846d4100640400f2511095541d072100f2520340c20111800c82250803510342408020181240709003d4001c04000b145011042c1b04000c461180e507101d40c251100c4049420720105000b940009104d0550206441d2200c0c481c4040458043d07403604100e5810740740c00007140511141c1d05100d1248402c14002a99000d1a00441049000354000d1401044620944500541110404c0c258580f609070801030342d500380b40301c00c0f142d2a030004000540043ca0040d03101c0c00360340d442e442d0600b16502030911035038071002c51011600c80d200d1400301d007007401c0c00c02c0001c0c003c0100550041960301038644d940c9400928020030405c1d8559113040083d8035071302c1031083c6030100300e5550040040d00c1d40364018a2402000781c0e120011401c296940b02540d0b550303802d04010040d5001007c01c00130900715400c108500b00e4003000b8ac0010b8030514082802c0d4103100004050b00700320005505d0f1140c01108603042468140055406405400ca04900400b442c0501c2403400204010f01d9008400b142c903480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 893442823 1250 893441573 893441581
    0x5090f040b0406031502032a0306091504091a010b040e06060309150a060e0c040506180114070821040203100f1d010b01140c071802040801061d060406060503 69
    0x1e003200ca04502e90140d50b40f04000005208070029800b500f002200c056128a0b0800600c14a8202d58208840880d041451584034250320710031241d000d0340444440c43d240e1038054160403030b07010500c541034000d40b03003941a0342404000b8036500d00c102100f200c1071003940e8850410380c10740d001e280700e0305c0701c000890700109086103013400c0a5540112a04100ca08203401c00803016460581a01cae104a4299541c3c4180074026501c51840e90041500540b9403601d840d01c40810100e11500d44813140141031b0388540c40700f036132050302c1c0b6900c0000f000c121a0b442c1d21190400d04070700d1b4800081c48081c54400f280d00b000d2109030340d0480707100e40d80003030180006a100c5601203018149001e6030003410740d541c10110301e240c4040b0504060318200c5100000c1e010a2900c00540a9400c0d00e60800303410b01c050122208800001854006075040c000124121307100510f90280a0b001d640c010040030350a1000103e29010a40b40400284403a00120582515500301b8441201c446006075800a00308000007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 893444073 1250 893442823 893442829
    0x61211210309063117010b0d030302090a0e010941190204030b0106030b22150504020c010e070b0708190c3003050f04030809071e0501030c05090f 64
    0x1501c400414412400a011030744001c020030104452246400144d64840500c05286010200010707000268000c0040c9080140001d18040315110010b08160300044e0300e504948541c01550018540c40344070002703550710b548a400251400c5a00d00c000d541d40c502e4000c003440d221101c0f0308440c0705c2c0070406e4014071a8100c001c004c8144010881a0075202c3d518800b55201002d00c0144000c501038520000c05504001c0024240e0710f5090304203200c0d1612440504000c04030440c0d062207003010010000342c12280c0d0395040c5020304568845907000c0e00c04904003040d0719064100c9a0075081000c1a6840c8070b460b495441c5160040d0030003d88103000c18803000301c40d800c0b000541c0c40582c64508100c0d1400c8100e0740d90b80c960300d41d22010000c0c5013542c04c07040b00a40c403601442c2d40c40080c13503040a0020b4030b4030100305002910300030300103000c1010105c00700720f401d001802800013410110342002c44101444600e0265080d040c0301d81070002e450b00040c403c0c030300d1064081d00e603001c0004051a4a401601e420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 893445323 1250 893444073 893444077
    0x42307080702031e040e13033513020909030c030415052203060c0c0203150406090b040507141509010c060b060c0a0614070c03080a06121121030906 65
    0x81c40940c881004500b02600107952060003280e004401c8955941c1000002c80741207901500c809004803400c00003000203a080070048048104070126201400d40101d40400f480c1c4250380045462080002840020707501025014400c1d4000c5c0c90b240715a40700c81058035640d1288132204182170f00284000e00c040e0880711001030401080d0f1074024108039503e001c50070000c2caa2020a828007120712000c0041090b58068103070641802e0a01c07181c2c80d045600403035141c416520150324440b40b5540028204000b030751103040c0c1c1540000402149203054a4219980c2c10940111840e42046101020b414940041955131588402c1232007400d0400600c01035501d40c0c0007100480303455854003281c2c40c040c2c0300c00000d818141903810080840c05241e00300401200c944402120203003808800304142c041d0850300d05600f640e41490010703010ba541d0100070300140f160740c000368440d10107036103000d0900032020510305250000f156401400d8802c0140c0e6100240c412100681c150000e0080203014944000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 893446573 1250 893445323 893445331
    0x10e0d0f050a02060f0a0216050102070302040f11190e151603140309100b040905070b031b0304060225021e0301140124090305031c0213080c04230708 66
    0x41242c24642d060b90000310381d500004184506584003041000241d039041004503240642000d10100c070350700b1300c00000e494840034040039010300d44030010301c0b0840b000d560000d00c01c0102404456295015400c803c025205003450010014400d610480d002d03207418000410449080a6928944241c0304d20306c0310421400c00c4103509100d010783c1003031054000500114421040032014121840c5003035009411915048107107805980b0303240702c0700c0020f10001190400e9901c5000e0280e240c0d540c0707003030400c00300301410518090440040207010400000390040d000d14048a094000038201d8054400680e59940030081e40c000700d42900c0150011030a401c10352030b90000b400100e402c4180c200301c1c560b000000e1340200410416040040c0c100c0b03100e98141c0b42e41070401c0c03506c0716450340b5640b1100e03528041d00355242e1340b1840011860310030743c1d02c0754110f612002010100c0c4c881c0f00d540303440180c1c9400c1182441c1b40910300303003141c0402800190010068200182001004e2504c880c00c3c21188a60020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 893447823 1250 893446573 893446583
    0x61707061d032a0a0b030c0d0b0310060e04060b04090f0210050c060103121e0e0402030c090d030201140108070f0306050612190615081b220203090c010e0d0f 69
    0xe1020040040103070180c443c030702c50703140845960418140a1149020140c4d1100034908003d2043c800c0c4070301c0782c204440354104141404034000000e1400203052031050390038000190300c0c0400c000b40051401800030711540c083c6000b0000002c41a0902050b60034680b00240101401031480c4014980039a0b16910720103145059070a0201c4408598507005c1c0a80041d1040840004480706050b40071707814a401500b0340798415000c80c1c2a04028159903500d480c1c5901c19a000700010300e0450081040d02c00b1854018003400f80b81403103090180c000c00380500908500c0f80e540300041a01040052494216061a000710802c107280da00c0720b600404016041540c0804581c00944040004002d664615021078074521a44800c624008045070012404110005100342080120350004940303810440d41c082100008c80764500c00040e03001d041400c0720000352000740d400e95404129540518480c644074400c1f00da103010b0034401910a4270b02e00c101e5503070001c01c0310348000004580c2c855800e9424855 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 893449073 1250 893447823 893447833
    0x1406042a0905040e0c030f0c0319170f0c161a130302030303010e01090c0e010804021201061a07060f050105060301180905120d0f060f0504020a140a03061707061d03 72
    0x35100150654408860700160759211001c0885d0b10315044c010650203c00c92002044c10240b000302007034030780549418800c65103041d1481401400759884885803140c0302c4400d05984c0380204401c640d0241c00441802180e44500711451030341da851109500c0075140003481419600040200e000d810782c0c4075810001c3c03400d051403000001a2402c20103140030303250400039440151305244400382102d001102043c1007080305050342e07909982010603540c1003074068a8482c02e0b040c804280b68058400c039806030710b203139440c4600d615020300c00001610080b880346109010b0340315054902d40c180c5000b8004c165001c0d4040004200e680c1c41005e43c2000d1200da01000b07c6c800c40b55031600d904001d038407071000783d8000e030000c3d182030130100f14030039210014032071181002240c3c10580c800e8507807950f60080074040d650004200d02c40c2c0c0d0160305003841c20590342c206180d48079400d0301c004028011a108469220480301da0724800e400780480c03403e090315a1540c0b00604102c664002c0d40190101c0282982c044c050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 893450323 1250 893449073 893449079
    0x2160b2506060302010f05030f06010c0219030b01061407080406110f0d0806120a0c0515250b0f130204090206160c1a04080a0b0a1407031406042a09 65
    0x14200503a52020302440e00020b034989140009490510701e1108001007103010000c001d20000d4402d501d40c1c20160a03c1d1410b161003251002c5a080039417160510007580c2c52003000000c011961015606852407aa02c02c07034140c3d131078940d41100c2d02400ba0000c1079014184402d0140e0740c13290380480d00d14803503035084800e07410742001b0050030001034015450002d00504100002e9040c210800f0804540c628020003043d203080c2c460000c110001d0003400d10444034180521304580d1400e01ba10411070502030460388400881c248440d030380074070602c1260101400750004201d0071100011500c11509440c207000c202009500f00001402c242c0c2c400c903840042400020090340801ca201340c40d0a2190004802503414903040000c10710300840691181003080005000e1040007080c6840b0165000da210512034484484403c0549140c040e017886480110f0108081c50f54582c1120301c0c1c60240042c00041c0ba01ca010a0005441080d00b0307044c00600d00d02c12600b0036021184035410300083d40e140c18485162 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 893451573 1250 893450323 893450377
    0x903070c08032206050313020a0807141203030708450f0f03070b04020f030609060412021b130e1f060806040b0c07050a020d0804031202160b 62
    0x18031900404456400481d8074010000a504600f001c085a0b80c045580c403454440010040c1c840106007298540c00300d0034403800c5480f019115006042c1c000c0545100d5501c80c000a0190440e1031540f0344516050b510749800f4600200841e0302a0300c90307540d40e102070f540320302c00d01c0012030b0b0010441c0944220028101b01070110b407050880d10b48140031080020400002c0c0c03082c5001340242c21900e80c2e4004800080d01800c000086130f0074143c2c0103000141c156034a0000035200240c6120b03d039014000c480400401013000302e00184614495542d030404900080000c0f6501c000107000b01c01120000154031140c1d10f40ba0921210f514050b0f00003013505952422414100011005404a41c290650ba0500402001d00403803002c1d00e05c41000380044d280c6503c54516501d0090002220b0704000a0000c0034441c05102c000344040d006015600300328507900d404141f42e80306100942c1d0244102c030106d045644080360701165400d001510501541c20980f004d81d03d42d0000100c40c000c40a03a03a5900d80385a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 893452823 1250 893451573 893451593
    0x1404140c03070c320c0a0f050409060b040905160b0c03031305010e0d020c011227020307030b01260307111c170c070b1c05070302250c14060d05090307 66
    0x8400c0740d035410b0800c021440613516007900486124410b86030104240a01310280c440b20342101d004503804100c002450500070024000544140d1b00701c0e041c0550b12051000014031b41f00440850407044032a50364a0001c0f10701d46c0500a011741c541c2c0c0040000c5001c1c10703415081047c0d02ca0041000154125462086038a8032007000d4800000d40c1040c1c80c80e038040d40c0c104184600c50f4890702824040d41e032492904c490340c050700c808014050b403180311800042d900e0411511000d59400080c6044950b16a410040c000c1d00120180c09120cc902019284503040441a01d1010b03a0224000142205600030080040b02c41448010a004500c02440104803207038880c8541e420000b503516078407021114007034105180b541213107072090020041c514402c84c031420b00710700c0812000400103003600c0717218044000c2d1081245a02240c0141d004070308e0207001c10010100054803411044481664548107019040c400d0308500360b2140c014409544c038405947c014070343c0b19481c401a280b90a540d036903000506 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 893454073 1250 893452823 893452883
    0x90f100f08060f031507030e0a0f080310080607030902030c040905030703030506150f0702030c0f010507151503050c13061d0408070f050a0528150609061404140c03070c 74
    0x12174840b9080c084000d07018807601d1060102100030f08008001ca07101c00b24070703505100e0001e0264800000040c0c40c403034250130740d4000c0d1134600e05603071f01400c0c4044000d006d403843e140c069100e40540c8800614070b14003407081c4040954024082c60078a805c640f4241c2c010000206031503000820391070318a40034904003000b400400340e41c03113a41d500d94505005051500301c41c235403224011600c804030303021540e8001c0240c2e03000a80c829000079a01902d0028480580528403038181c030007208130400b00401202060760505410259803c011028601ca004d0003624114440c034910007081c80521503000c0b1102c05041d40c03250081c95030760700d071404c0380d44d50100e9040c80d113200b40e4094105880090800c0030034010081c42e51960342042e001800050126041c0010441000b0038105074403035140c5032541e0350342064004100d110820055190348506401520200ac2d18035846141703010007120050308003280302c40c02001559000c9046589644060340c03c00b07a065004e031103030300d481501c04440221950805800c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 893455323 1250 893454073 893454103
    0x1020307050d0e121204030e03070303090603051605271804020307080d12050702521a30010501050306101b0204060b090f100f08060f03 60
    0x2e18185103010004031080c0b20007107021038010103402c11401a41e10243c40420b044580702d41c066480b14503066074802021000d0781d4141c01011000802d154204405404880f855141800a651501c50f640c50a120349517000010a005024400c8405544a00c4c04440014009400c0c000002e04001035001e40a50055107001e881c01c60800c03003182801d0000c8001000101c0003000b089641485c0604446046810211130640d203800154186208001c807070308000a038000000448450100e0102440c02c8940940c8101c40201c40e4859210034400740b280803202e0400c40d18040d03402e0030800008490008019422510f06002d013094400c02440412034007202c4400b00f0000114001510192520590096041c460144200402903c40b4040d040786c809031740c0b82201c0d805960850101c08200f5454006e50028508035000c01d0300c40c0120020310000000b114200940e000810401608503c820480b01c00103642c045103000031400303500c0d00340d0007180040281240714081342c00300c1c0c6071040507210425 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 893456573 1250 893455323 893455327
    0x603081306170f010b090d150b010824060706060b1303060606030b0f1011030f0c011103070f08060a0b0f070309050111280b07020a05070504090b010618080102030705 73
    0x1c40d00820100701040c1442000c0520f441d1201841c0c4420105120300c00d00c81c04005009181c545d1110f031481d09107a8400b04d43d505500084180708000c0c400480c9440c00304080b0400f10b400781c40c805608400c407003942000c030030001c09118213010031504a00d50803036505403aa440070515914003000392462400b501040c041c01c1e41f460403c0000d0314030341d80c418000d152070500540700c0f03074440c19680040a0000d840c1c02c081641390100c111b030700e00c0310111950400e001c04142c8001003e500c00040940300701c40740081c40f681c01c40c00e0040c000c6100076500b00300488c0c2000c22042030580100051a03000c0f6004083e41d045c966240e100100da5445009ca0300d4501c240000c040041507007003e1128040c01085c42c00560105407040025561207810301c07281d03840078265030000c1c11030408648a02c480c40e80503550320b2a5050220010b0741c0c0d4154408121010701030b206000c50b69080600c10140f100f074000d41d0025499103000c606403490380780c42c4001d2111100d9000d012608060134002035001d40841c1ea5000d0f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 893457823 1250 893456573 893456579
    0xb0415061a0403140c1e09010527071e030e15010614130b07051e0d17060127140a030c06031107060f1b08070212090406030813 56
    0x80121095a00024421024440d0078a001001c1c03400307907020b80f0f80c07000512000e644450300e404d03d080c45080c8800e42c4003000360401e12114200c644402c00c0020160f0300f150312a40ca03501040104107000c0a0b032041c0120170403144403120b000c00d4000340c0104c0c003420000709804031098031145145290000d0704c0407a0b16841001481d40c0108103255070307010355016907030310755042600c0146100741c03800384891505c00125040c6142e01c104401c0340c0051610f454101c0c0d0b07800452078a182ca441a0103200710942c00d1034480021482070101e450203001e20182e03203807056a008001c0ba81c6a80c038001c0c1c419410490340384d07440340714070354005001803465031598040d058031490090041054450100720501458451108000040c00449001c0c02d5845030f04010902c1c00360703007510702c0803402010000f51034030b030500341510503100c020f84c0032500c007001c001c68020220315030070340c107a0703901e80d0948030203006034880e481001100c0414030140c85658001440421616640e4803a010b00d604a09c4d604032085104220070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 893459073 1250 893457823 893457863
    0xa030c210b0a09180b010e0906190e0307050f12070b010b0d0204030b040302010b030c0303040b0d0b04020c0a030906092102130f060915051f03091b0308030a15080703021c0b04 77
    0x814010860447d4a0802d07181c200d00b074503182c2710040d00301c14080d202003081c10300035401c0d5002601d801c2d001d1821261a02c05ca41880c0703540e4400444010b400d40648507078555141210300842d1401e40e00544c1c08081a46030030307007902c0a80c2c040a44452055424840880010b94100d4803e010310b020390b00200303541101c002018100604045000d1107030340100001c1007080b40c11001e403400403810410004079481d046012501902c00c104150129001d0a01484101600404102c083ea040b6a944250890300c444100320080d08000f10010b410f802070300d001006240c000210790306038000b00c0000ca880720341c1000c0d4006403411900034913442c80d103e079620b00f0203400b24080d48004117001c40f0300300707220281d400100070003c8a0b002d0340d208142d155000401480252259011141502210008110744d0781c1448031158205442c03032045070341084a1a481200ba6818031015941c03944060b0001c58915801c0100e14020f000c43d0368034a4420310460004203240e00f180e01c0c4918082d15205ca000718216940b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 893460323 1250 893459073 893459093
    0xf0d180b0a0b040c021f200a02010509070522091709090f042a030b0708070f031104061b02030303010303020d12021615200a030c210b0a0918 62
    0x102c1030066180c0480c046142d640040da00407504803c10084c0c0c480c41c505031030000600302d00c120b41d42006011840031003150608070014040c3c980143c0c02084180c840c24282a110041e034499103501405065070007803c10359040350002807070600e42c1b000030410010b83e501c3d0708001c1640c01820300f030312000c00c05010354140341c41038039840b801e45075208146103407a5540c04018491180c01c1440094070300890f1000c000d00c1c00f0382c0c030091f40c9c100d925200d0603c2d002c0001445640c00f2642c501c00a000c03440d01c43c88040c004d001d5298442d01542d540c50625092001c1143c8003184902e1694022244100ea0005030320280021806103010740e01a207840b6040035805000035001e1070300d03070b02650301c1007020000d80f00e0f07150068140c0c030783d008000c05403801c005240c040c090401500b25604282c08809540907240d1480e0041c00203c420352024002c0b810301e00070030384032201004440c20b01d0350044440e40d142a4019404001003090040903c011151207482b02d504441507440b0600c10308400350a80d405000031006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 893461573 1250 893460323 893460341
    0x130f0f120b150102100e01020304060b03060f040308090703060603050303040b10080a03141c0605030c15040e06040908030c0706110910030506061b03041502120f0d180b0a 75
    0xd20388151516a100040e00200510141c144203041419210380c0c2e00c00c0c401580741d10355040e402d0011826044002c0e0003548140c4040791128985908801c503420701084003481511046051132690b601c039201500c490b0300c0145070746110302803844044001241403042001443c061780003103840345003d00e4900e0040c10301400100c03500503100c0003009651000036900203656030614280c82c500f05000b104c0d9070980103000885450f2281280010340e0b15050b58003041c1290411001c69840c131001d0414091200c0a05210f02c1800c1c500b040300340701c401d5102c550150004005480052130040e152912051a00255405008140001400000d111481c0a5040400348460350146010340510010300030820321306001702815112800101150355041c02d44a0355464501075141d04d445101200e41c896020340a903511440810340c000d041e080c800516010300c01c1d80d0304000c900c0c10780d02012203c00e079000701c001014402d450b444c049141c1103c060b004a6014030582c14030380d4508021320204103680b0042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 893462823 1250 893461573 893461589
    0xe010b220605120304090c03150902071101050a0c03030b030a050303040804080c011701050904060e010606020d0228031b0c0f090b09190213051c150501080c1302130f0f 74
    0x3c408881c60400100444040390a010030020b40b49118103001d41c09090031603021074415080032030000700d41c501d54004000d8030b446600030050000c0b10b28019143c5002c0d0f14203e00004d103100f2034500010740a544107042c15200101201ea40fa15a60784103495940304660450740e1184c04102044804002c01a80c98004000d00300700f080c2c42c01e0218a03101e40c103414030607240b080c12070034046003e0042e1548000011841e0000030f100c955181e0380d000e0350318590b003030700d0a00500c0380381c1600700c80c20014042031400100300201c0c0d400c2516240c504a078103040710b842c04009045c10a07200000103003c456200010004400d0500605240c04d0f441c8007120601d01600e1f000b038a0050400c8a11001e411880c40c40421600f00181c40340991046c8640107171440e004581c0010901130400c48030081c0841e490205d5108000342d0108a1a9441c48410355400303114609550703101000c46105450001207480340c28802e9076006042c40881401000c40c613400b80d10400c4d118050b00024003440810b484c1c0c00c0301414a01b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 893464073 1250 893462823 893462839
    0x11120d0507230f0105060a060e03070b0a0212030403030c1202070b16020f012306030a0305090f060c1c0201062913030804031514070e040e010b220605 66
    0x206001500c1403040000c001c00300c0205414440803403090400300302601d100b107412100c4500f181e050150091101390303041441070f0b50700350b0000382c500c0c414040d144424001401a080702d500c2c0482041598000c450354178194001c000c14000710010003405548190300956002c40d0b4480c4401000e41f1424941c0e10b502466801001640c0102c0c0484212340d400c2408216442c0c00000101c4049060400c04035244215500745101511400100d92070309a48100400c1c5c08a40c41c0c0b901c0e0101555200030200c0140801e20a10030300b980b9180c50f24a000503404041c00780c500c0c0c007900c140440d09000802c6101321440002c3c50405441d9a070907c10702024181c04c501c0c1c000d91105d003680e080740c100c4002c020040e03a40c01c002500f1190140c5021032800035030b40000e4050b281e80e26864010a42441c9044841c141403600d0305031100340b09548911806190740c0d40320b071052201940c1c01c0c80060700c0aa84050004e40d01d42c6e54404454544080004209101c400d140ca41c2d00503603c0c0180544840e0341c030940c4039038a1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 893465323 1250 893464073 893464093
    0x1a33090906010f0c02150f071a1f0b0a0e04090620090d1104020c031209010b0102060106050a1b05060109290a180b040219080601140301090c1b1112 65
    0x13001024544640440b100000102410a100da0b5485078070100301603c0c5021a19000700706480e18170341c0300010418111451692441040c42c08505a17054442e90341031500307010010034a0303140080c41000c1151a1102035007850102080a54000c02011031384207603200721100240c000303880e103108082d0400042505d032610640c002084c05581d9400a4113142c00c0b00308040f0f0f91b94440d8100c480c548030f0101600d440b498800c5951701419400c488499880d420640d086219600c0418442d0598120361078490a15400010441d00c40d8000c3e031120751548903010f003000200d402001024003c01a10001250348400403044421030303542e1200c3c0345c106007940080311240e59500355408003034904a00e040407042400c4043d80c3d0240010056464106200090f1140c1030a0401d1101203c0c4c29035858512042e1140001120704a10145011351518410700051003aa00303d9002900149024034240302c01d694060003155500c405450b0444034403003080710301180c07414903c0c02c000c454640a000b41180401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 893466573 1250 893465323 893465327
    0x200108061e0301022514010516110a15022203050a0f02180c0301030b18061b0c1009140f03030a020706110a090e0a1a33090906010f 58
    0x314014044101100c5528980707401c2d1002d605440e2080c0310f910b8203d401c070b078100d116502d00c02010b40d0b069600e4048500078000340c03001406441d000e00103d0b9001c20a0845180007100d400b03021a811502c14010580000c000c20b10036028550f4081183c0380050b5102441200f1410b1164401040f01610310303104400c01c042007000c282c18076900e420020301c1000e4000751001590315501c0700c02d000c0c45400a103050180390407002000c3c0d4140c80c450043c05081d5290031100656081003581381c261310b9880b280000781c4e0748408103110311090000001040c10841c05810386401c02c50355100d29251580c3d00c0c05a401841080400451040410000340c210701b000c43d0300e42500c81c0310007031070f803004075400054800800146078881c1180340f28200104e80c445a940800905080943c4901104510b40c80c0105540307903040d102d00300304542d00c1c800703000e034030382041090004281d021400010004038244088160f51003803618090845859001d055031820910208212924050103150401800442203ca155 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 893467823 1250 893466573 893466589
    0x1c2d020f040b01030e240709151404090c0305040507120b04080c07050d05030a02010c020c0a050108180f0f0f06070c0b060d1403090a080a2103020d0920010806 70
    0x1a410345000ca11500920b00503405030030700e15800ca02030721803440c220310030007141080c40692900b00301044046480c2d0500840e60014240200d41d0212075102e1240e400c980942041d2180d54401100300341410342c0c03a03203c0421225103c1040020944070790070081003000a01200d1f01a1041010041d1883c1080d250300d40d41c3d034001440109448000203401c001c5a0301001100020f160041c0301181d48502882c02540b81e82004240d90003544c24480c0900c207080c0085240d00c2c540030013510070050715240000448003120301510b0280032100500d000500b02c00c003404071300840c0801030010040641da081005103002c2c521f1014640c0d80d0004011701142c10707800401420115089046035409846090004202d0310394070b000140b02d80707103403460203240c60300200141c40d00c600d0850380d000752207650f10f2104d5160b01b2001c10051a00b00c1103444084114400c0c07040464445080c41c00508080c0811000e01c1102c140850544040c02080704402d1641c081a0880b11105800e2070420b03403d00b001000700c2c8041d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 893469073 1250 893467823 893467849
    0x81602030c12030a05210709060e0307031104020d0605090903040f06020d0f140c06010306050117031e0309070317070b06240a23030103050105061905040b1c2d02 71
    0x2140c005031610046c0c220030180030780c0d142c92584031041ca080c01400542842d03403d11070000070814a02100120b07180202c0c2e4241126000300c802451050341c0c0c0104402540244030743ea015030b0b07464101180395258000034601c128174040085680c0c6060802c100c030862a10b90059045501c096006a40300d81c0c880b101000401480c1440d00b44400724541d049111300400d09919514415000000300b4480c0725008a0304942c2d03e00c248181010130b054015441c0e214011601c1418032059140c4480c00c1600c5004540c03000000c1d06441d100703078583d501c01e0b940401010341e1a1001d0808941402400000344d00640c200204039010302021520518454407081c4d00210200d41c2000454035001c42c90203000c00320610405066202c2903c0c000c0c20710b400042d0000c4c0415286581380500043c03031070421700210325211880302902d290039450b04041001905a0392001e80c1c02c98150548000310840608003140300134801d504000c81261914260130041c981c640c4151750800000c4020800760b11890f42110407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 893470323 1250 893469073 893469077
    0x8040518042a09020a0905100e010c230609032206020618010e03131401020c090a090c0911180f060d0b030106030c031b0f0b030106080a09081602030c12030a 69
    0x4000c41070340450000b00b480398414030703000d80002000010285d10105030002d1780c0040311140c01500c9100b0044030860b611040300d5002c500c5540200d0089a1082020820412030015500c2a0b01d030f040b0881e8104042950b038a900c0f64404503880c0045e102890300c4a4018100d21070900b030141ca0900000e46e909405469000070404d140201c2200303c13400e410560810b40d10340304403aaa4000d4520b00882c0c52061312441c040d821050396580030325803000c00da000320003200404c0798100da00c0f4070344550000d05801c1022208080321200015504a00d4069161f04c00804044207071600071505c1420981d04901280d1480303101200c11200066031268290381d15002500c000040103429000800d004104030303040903001000300000042002901c4480f102d140b071109078003841c16660340c002e08c805c82d059409540c01c150414401400030034801c1034155800146608003280c0c5001e90b8850455a6120f400e5038040318905002c03131020740c1810028038004241c2690003006049002400c140c40740911007513a41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 893471573 1250 893470323 893470373
    0x81c05060d0b04020f0405100501020105090c01090501050a111203180a17160b0430020a08030c09090c032409010608090a050d0e0406060c0317060402160804051804 72
    0x4d64403543c058124042003e082084141042d004154445100d0b100701c0740150300742070000741d805201081d203072080803041e12001c1e6007a003444015103031600329001c0d980404c00001200a10b01e03404010407100d21030a000c1c025070341e0410400d40c000d01d4601c40724000352036210711106000107195050340d00da003030322049640d40ca603d481d6000a03614440e941e0050301c081e00c01c40c1800706112411480d04000d142040500d4012503000d00c4111401851544520268000c410b4000200f525140190344c0308101c1c6411034601000a03002810f803070707010303510640c8180012040100c2c10413074501145510094a10302e88200d01064005080a4014018181000140300c08100100c404001044030310742d00c4400c1e20b00d103001d024801000030b80070b02404e5106a081030710000300700f8041c0d00c05e81007040c1c03d07554661580d0032001d0500d07100000074040030381041d800c215811120740c00a04007200b491140b42c44a9035145007408011181c00c1c4c44844220622628040c000040c0c0340302c40016100381044c007920 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 893472823 1250 893471573 893471581
    0x8030606042408090a030801051003061509090b01091a09120f100b06090915030f1501050406050405010b0301090b040207060f0c090b0301060e0d14010603081c05060d0b 74
    0x500e081c01540e001001c6114400b0810001021824107080980c001e40d90700301c1156030329548256580c0308141c000e00400e103101d00602c80c50802ea1a40042070402d8140880c0c0e481d80c607003005482410b1544c205002902541051108048601540c0a03c0c603003440c10350111414201e134130072140c00303003070031850100c2c400101700e80281ca48020703c24a000f020401d6136121143d018440380c0ba194028101100366203042c089208515003070f810b680700740d10003505640e40c075503445140d8005000d402c0c84d001e03414030030402180b8240f8010040351006440b1004030161552400e028072042d601c054000f0b500c500d00308001882500c400780262411580e001c0c9012800ca040d04000c0b60080c400c0fa00c01405a030f00b003419943e00000182c2011480c0003140c0d5608210942d110540c0782c01c1e0000780555000141c42c80c100154600d04001e0300c0044138065801c6e4180c11255010840c00c446071b55100f00c44014001c9000d645800158004e4100c2410182050100d841c00703030001103010318610350050480f250705000c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 893474073 1250 893472823 893472829
    0x10e07021911040507180e010e2706100305070905060607020105161502030f09010519090c0504061e08070806060108070302120703020c0c031b06031306020301090902011403090a080306 81
    0x341c40904400380082045040c12040184902452041c4480c0074444610000340750f9500325030340e03048490568151400e52a403003119a03108402c100cad0140d50130701000342c1c8186440d041c003455000c2c85101c6043d402c440c2c03440c0f5080b401c2941ea6401400000c0c9408104041d0340c450204a565050703092a100750b580341d43d00c44c09640c035681920702905005910500803032881407640114021030201140704400ea40c3e0207001400d0700c0c401c6500da041d1403007201007000244001e411105c882441460740d01c804c50344440108007113030700707070342c4400c09828107215140103031200741e1004c03405441d645c2c014003911410101043d50f100009000581008a080000b4001600c03d506445107130032000080d0742c0c41d042049004019401030003441c445030049005500d02c074600058400010500400c040c842225900104100703900010b00c1204101c2005082c0b40005040b44011806040407010001c0c05c5c5005000041044c070030f00c4004250300b001041884200d50b0005006901e041e0b10a510a035240d07144004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 893475323 1250 893474073 893474093
    0xa02250b0c1612031b030e130b0402031009050702070803181203120103030e04060305060c030a02070b010603051005060a0e0d11030d08012103080c0d0b09070e030105010e070219 78
    0x1000b5041941100c0201d00c0c40100444070543d14060354681060031251101c1c0016655103900050101b03041b1070840c0d00f01e040c010f050b0f00e00c42100510005502c0030b88408074040e640102e81e8400714061044060207180700034801e01e500108030344014080c030b0f0300f0100364568910407440b040e000300084003000940303a65400445c001900d40e80c07054a4483c1d00d850503580305500280000c0b00400e8042102c210a070a0034850380d01102d801100038020b58035810190364940c2c0c00039209140650302003080c00c0c0498400c40e181d0f802000541c2e40000c140c6000e400c6901c1c0c064407500300f12711803202040ac900c50103074095842405408101c810750780c1d1a00b907242a04402c0925008560180070321003891303c0182d000040a41241c0e02d103881c1c141001c818500b000900348a005008010480003404a205596448040c004040b044070001448402200009014032407c40344200001c074249001c0040342028025240140320a0030580010305088a004e9220605039911031100303881d441000702880303003100d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 893476573 1250 893475323 893475343
    0x61909020a08030a200307031b0f14010507030504120806030a0507150212071e2a0816080c010f052110300203210a02250b0c 55
    0x100c0900c075a03640c0070281d22034102c13400d080013049503642203450086003111414006000300003d03525140060303030180c4508110800020382c0500c868072a000240c143c0350801d030014007580c000395609e07245800c11420b5420040081c010541031400b4400020005400c05040705001c0c14801d940f907407900040703840d06070000009880d03842070100004070250300c10141c0c000800d096003a5445882d804d40e0010040c890000d00500d910745100e5003070b24049c00180d44148091241440103024040c001040c0b200c071070f684030158107903080c00c2070800c58681c0070004c180155195803e0203001c2481e04120640b208050359405061005080101c450715120300c046442d106100d00d00080e20189502d030029007890100e41c00c6081101122000c1002c0100c14046030440140c000a00451036000c41002c00c1a030030200c00302e81500c05e0034482c01440404a6104040c4bc03010049151107441e0404024a028a00c450140e007484440c10b400e522440803440d1300d4103032880400c4440d500c1d21010065440e1180800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 893477823 1250 893476573 893476579
    0x1014072604140d0f09050a0b1218070e0105130e0c010f1403011719050d0c0c03060207050619020405010c060209010203120f070f050f0a120e01090609120c020306190902 74
    0x2040c0409260480034a13900703024a0340e9600100d5807184180440b4a02c07501034003000d4142030103500040c40359545881d5004410b50701034080742c1820150745242c54071a4200b8040150850010301444c1000030306442c054080d17800901c04410f100a15607100c8420820203030410403441120321481c1e0003020140b9440000000070740d900d6a5480487c1d4201c00c45030000b240c14000e01400003da1207034100b10b141c1b0940c00102900000b0f811040a98104011a00440c0d015250100010200d03601e0307c080c0020341e00602c050720841c81c00000c4039842451001140381c4662040c40180441d90740140c02c09001303a0712040060307461b0f04943c0180d10f940242c2040c005030920300710401880340310b040d082a014160a03110f079105107900b410b054400b4050f80241e0b070f040344414456848400d108030a40300107280c074000001035095a2100d01801e41e1400201a1001e513180d510034410482004102056001c0a1800d07603000807d1b4be00003512140c019185007401c0c2498010f02c104020345074082403c0541c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 893479073 1250 893477823 893477833
    0x120902221418031b0c0909010b121f15090c1d18070819060b0c0c090c120c0405040c0e030d03060b0a0f11101407260414 53
    0x1425510041c0c100c00010380e20352410700c1c000c0760010703404100c1c0d51402c14446002e1414802001e40801541e40d0320015860b291141c00d00044082c2c071800f030180d000d060b00500124000c0403c4050000314000282c03001c1d1180c1c0030001005a05a14171801c445400000030089074a0016214101414031584c02c40c0320000d141003800000c2603000141e0030700341d110b41100340029001079810051405218200119901ea80030300240c909032007400300e59803006034002c0110000990b44074a40842c0d0a5800003150b1039000500e00700310840c03c10485030110012111010380789003540340c5a03c2801a03900905240782c2f410f003c5000110708805030340141c440900100201080c0c000300410040c00048154081d009071350900d049203109014550680d400751482c40d1907c988010112540c1329124008010000701030b07201441c12509000540310b9002c1660049595001c40d003e02402e81005072240c0140444042910445001c01814002d01a14090341c031150b541c135400c00240b000c072a82c401445078014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 893480323 1250 893479073 893479129
    0x15030a1502090a09050f16020a0609050c030c120714030a080c06010609051e0118030606030809041506020a060c050405090a060f08070608061003110313051c120902 72
    0x5aa8060506440103d0316580d2150b6200716400442d001501d074140000c21500c006490903c0c466140319201d0240d10407240c2000f00c540307a8804030343c204101111a034214039110306072403030200071a00d091442140c4040883d4400d110365a50307110180328441009148076851a00c81d502801800c0d07460750080c0b0590740d101c2044010a440744000d00440340800c088100100e403e080040c650441d0010b400303000082082d8002c0107403210080104c0394410101800c07000300004045008035001184120481b80e00c0c1c078503a01c200001da40340750702c1c0351103001c1403039004200c0c0d1513002811590b0f007900900d00042c0100c20781421101803045800c100c3c1c11410314010702c002c0e4940d07680094102c403400925205030315102d80c1c02a403510003500c221000036900d000890403614119000945034001030070001620240801f0303500c0281c104403001c0c48899548070390070301400000e120b100c0c0054406800700021032042500505907501030003102404c680e44214440c00c540703a40414064900480344840c80c0c000d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 893481573 1250 893480323 893480363
    0xb09180f0708010506040606030b01020606011d060c0a050c27130804230102120409020c01020421031b0b190b0a081b0d020619020102040b16111815030a 67
    0x2074400302c6c01140351003800900d1a00c284100200110140d002e01107580324400112425110428242c1a070611840301c030540c0e41e0750400a01801c00c0c003c0181c8510b6005042150078020f80d081b44d24010341442c2c0c0101080c05424030030b0040d0350890195689292200c0b50120f09039400e000c4002c0c03a00d5070008021a40c2010b101c81d41807070340c0051008500764a041e800490322055013028400b44e004051109028542e456000380180c0c6184038001418103030760b000c02503040341c1d00c14140e140c0c40900b21840c03c11705a0040028030321503140710a80c1581425556090b600310310080c0190602c0c0c0400d02400740c401800d8001c0b07030b4180001032214041e40d07124907200d0f440e51203a0100080f96503a000c050303489400c3c21210500c1c5660020621400c008412140000307201c1c80c0408402155400c000c041a1600000d01030440080480e8101c0b26002261400f920002d07128569144248031400205810400c940c4115510801c02403a040c2e20800001c0403e25100003100014201080115005a040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 893482823 1250 893481573 893481581
    0x1602030706020d14130305030c07060f06090518030315010503150a14010f09080a02010c172101090e1018080d0533100921050706030b09180f070801 65
    0x40712002400c1120345910280c20b00000d903041000300030547c140009120800c034180605040c600031a004a80b810304001d80030704890031500949501c558030030a10480200641080c441c9840300c10003180307142040f00c4502c4070b000420a400341000300004c00110a50042d5503000c0a428000d070441d01e066031a01c1660b100d031240d4000050000d14211000b028840c840c0c482001100d44140152450b0f256a0f001160030201520341503d4038a011101e162544010f90002c02d410748458081042c035200c2d050a4202905041e800188501e0524400e04540c21012607010051814103400180076a581002218004602d64020741525004925504405003d4000510640d0406001c4803011090408101035071541c218004041c1c48911104140e410f214940700c030302c5205414208526079550411071894114040e045030401101690b110030040d0401240d8080e1500f414148140f11000c0f02164003082e009280baa2a0808038108040190040c0401c2c610740841130306075082146c94403e5a13000e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 893484073 1250 893482823 893482841
    0xf250b03010b0a090e0f0910272307091514121009030c06060801060f0b0703140720040c120b04061e2102012c120d03110309061602030706020d 63
    0x10b030080c007503c080f58990740c0c41801421010b45004641c5003a03103a402c030a0341d40d2602c004440c0520b11480c5c264100540c0e400d18665811050012f0880a041065100a4407181c02182050b046421000d1080c4007203283c8050074014151081c210044e03d2200f4640741c0300210400d0071109241c01c0d20038042c075510808100c12907002d0a000c1c0000c1d90354950a41c00c958051090481080c0c4e11042448180006002040c0450081c0380c0072501c5480741c1711000f800c2d8451b0504840e4030f4141001d100c2c400c2c001e011031103841c0c80c04640400c20840d9000c004be082404080d55480c520f50707202d0b03400e40540c1e5241d000c80003402600c42c600c1c44510203003230b00c2030340e80c1d1590158440400c13207100a24150140a8428072046a043c2d42c0d0a4003110a5003c1c94201d110030718089003441540400c0c0389a80d2102c409545550411000801c20805821070140403600b0b0b035a10705601030f108008200c5400350009400b07030445c2042e001d01c1c0410300c10280890450140d240c005003c50f00001d0042d010070503580125050b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 893485323 1250 893484073 893484091
    0x905060309210304030c0209040602120c03060405070305150112180f0209131a071b0302070f06020c06090904260702100503070c02120705030f250b03010b0a090e0f 72
    0x2d5031a00000a00081c0411a001400141c401c800440141440703040c00d500540b0450015040c002d41807001300c451007007151a82503800c804420803556251078001d2980000840c2010480b0b42080803131003a20b02c0c1100341060600907050a9030100030503541c00442100203800030391643d40c42929169048400e101e0003680b040440340041206040c0151030f03583c0c4954880000c08012103229400541c2c010010141d00500c001c00c5d8640d00240d54580345101c40c68802d60261200508148071105084a01d4000f02c08551042d102d540203516414100da645150490b0f0904070745d900e518051207070b025000310100d084140c080ca8040c12041070006000c80c180700b02c40c3c00c080b841c83c00c0d40c212518001260b80c80006000a07401d10b0260414450523243c00a046041e51100d82d00c034408a4501501e25881010075803110140c04d102c610346080c00c00392510550103441a803850140c0c030811501042c02502002c25000a00c1044580203149200080c441c01c000248103107000803007090b062104640e9420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 893486573 1250 893485323 893485363
    0x10e01021506150d050a09020a1203080a05092a0301050105301903050409051003030203030703020d021b0124050607030e0d05010203010e0702070909080901030c0905060309 76
    0x590300100d42010306120030051411030769036140c100901ca4034074803200441850200003140255809010310740c440c0c080322001003486002d501c1400f1040043d03a10400c03400300e500c0c5c003540019034410b0b00560030030801840070030191a240121424a03000401c140d0f0b404c035030208016002580c000c002914101d003100204126039903501405008010481205080c8010000165051b0038480300020b41391441320490704060307064484c050b00d9003081d40b4140d0208001040810600646000300e80d4800207005001c005e5900d16a4065134a0001074030003070615802081c1090110101c3c0d042e03801840c01d00c1600c503d11850104528000c100d41d070350142000c0685e0444c1c12003d014469004203c2e1805041c040c501070f90307500c0494155138120102c60f0f00c4142000702c50045202400a94007074030134020081c0039800c040101a00e45401580002d217514100540c00b8046000e500c01e0b61034854003824045580214106c08581c80301158102d298800da0110174401009000035040d10121036801c2800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 893487823 1250 893486573 893486597
    0xe24010605120c04050a0f151706060d1523060f030f070e0d0f0b0a060305030904020d0b0a08030918060a260f0601051507320601090203160f20030418050601 69
    0x4038482c0030303801225188420035000c0ac0a50501c10010014503290000000c3d072000746021182e610080c5500c6024649a5054040110442551013407001081180d0003071401e0343e200d6903084540801001c0a602d120603400050000b4021101159217800050006280c2940b61510551002003e074007902c07101500030000d10651824490002501d800078005c40c1811102020003010350700c02c1d82c982159a807290154030880c1c031003091040280021602444c0c4130821002071200400c5a0b4000c491003812080511000340c0707070001c3c04015120119605440c1074140300e90b50724160300c4207118005500c503242c001201b01401083c880d0588004503201c5d103081e002c10b401c0c8840343c0a4580080c101082c007030602d0b90140080c600701752201d0107102c0700b9000110300fa01000e0620300240d1052040a800004101032441c0310040fa002044443c00c10041000d0b009000a008030308280c0040e92800440e80c084a80820810642d80107003100d4161592614100000102034503007944c2807400300e01f001182d6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 893489073 1250 893487823 893487827
    0x190305010f020721170702010f020429040b030606032e06020706020c091f150f030f020c1c0e060d0e210a0804030507060e24010605120c04050a0f15 65
    0x104d00050703e66503180e002c03442d4201e031041034500600600c0c1999030711000d000c80b411250000d0b00041140d240346081e204903849080c403040c0e0441416101d51242000180032512020050781c0d00490151807264480e60352458403600c09d00510342007003024a66241c0080148600210607040d50115030956507400d42c8c4040c280c0c0d580e042070003503aa00230798040010300301c07130240400407486400300780d01550700b260794080d00d20103a80701031039040001e25192019030300250180114485000c0d0f034a411480c0003440030702542c07540303803400304200640ca003800421205845546000d080f1400100900da84400e0f2682e071600509070300c41000b0540c011010344a500401802507065480004040c07980341600d0300300c00f1600508028000c400340130050100002107030f040e201d10000150306100400c100c82d81030103a000359040800016000302140c00042c4026940030050f40c0044001c1c05503000f4540b14a0f5924190b801250071040e000210f404000441c20090b80850048444000996000101d04901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 893490323 1250 893489073 893489123
    0x3110f030d0f030902030c060f130b030601090909110910030209060d02010c030f111203060102060907080c0409150c05030f0a0e060408160c18060f080705190305010f0207 75
    0x51080030074504074602d54882d000c1d4000e07000a505c002e040d10103066042c000070700e060b0440c0c406803000800100d506e8950404401080018150b03100c00d4038194580703440000d010140d10702401a00f80c0d2544001010042071603001e0038100c80c01420900146000c1e08040054a4944000d80c400d80c091400301d003807400c140761121740c0b494040c0d58441c1c1c2c0e4603031514291508564203400074100304180104600310001480b51020032070380c4c2c83c40c10b80d4900f08803000910380500a80344030240e8111940800058400003044080d000c02564045a0304140e414205020058076074083e40d5181082841000386500c800210701c51310002d00c003603003c1d071030703c10310340007105c51101440d04983e203c03c01140201c0c0741c01000d000240c1126540c0441d440e00c40e43c2e5020065031540c02582c00400364007510780340b040507000c0d0001610443c0d28140a103480d02400d190340d50b90368400c540c002c2072624500101d0101e950701003000f03950080700910195a000014100a6010302020b8541314804c035550340070940c417200c0e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 893491573 1250 893490323 893490343
    0x203124f1d090709050f0103111f0e011101020c010509150f06090a020d0e0f07060c050c0f040209030708070302040b1206180f0706021c050a140d0204050a03110f03 72
    0xd84440194004600c596030390744090310040041c0f0802c0c10029122005006140c80340414003401015545545032a8885032115800c0c61300c5104210038980e01801c2c003640d10110b07240c0c24074100600c00c2800380180c034014100f505550786035000085022801c40150406409a00d030902259040e020f00d035414000390300d041c0ea0044a140c0c004000c2000c0f0b1414151650300144c1c0c4000051030150038003056030031650441c00031011500a0040054071080c1485a000100180e0a040010890b00e50b078540e00d17903030b5a514051290124404005071360300c0c0d59054468512015084840694881c0d0f8a95620241440300728499805d104007180c09007001c3d801314005c9001c1000030b01d0113840c0c42e041d64040d07513410800c0070102d01c940b201650307440d40104038400040281d9009014500c1c5044081d5100780c091404441c1406010840c09446030b42c400151220381510101d0b013903c982440c1059400b9200d180c1c881d50340888004030100c01e000340c542e0103030401030301104d441d4070540c41c1200b415250654a4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 893492823 1250 893491573 893491589
    0xf0e04050f010204150f1205043e0d080705030a112a010c1a0705220f060c0c1a0c0c0d080f090f0619020f0a0203124f 52
    0x454070340b251784e01640c03520080e1041c6041000c90703610101c05401c2210b0044605460f520040803426405512044030684a500030003808615440805c0c0c289460749100420640195000405902400450015203080c55484029280d0310b1036030306030040c10a20108200c2d00c90b8002c012440f480108000c0901070803e89031107001034003810020056416140003042501c42d216030303407180c40b003071000c0c2201e032849a400c90300c0d05500c0e024050590142429040b0903600c20400300003083c80890a130250303080407034580d0b141109411400b850034070b00030031266007c110754544e5945220000141c11001d0a01d148581c01120b0b426200d040c200415040e43c81c202500b4040c0401155007092210001098030b0100036002140010809001c47c5044e441100f240461600c1d00c6005407403281d0510000f040c5007510b000520b8501201c0d0000307030b103030082c03140c1c1188002000141c02602e40c024004000529a400107505a0032020139481c1c1c0f22101681c4180802c6034008100c0388001115000704403d8036101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 893494073 1250 893492823 893492849
    0x6020d0f0e060706110301091d0c0d051507030c0f0810180905070905010303030b030d051c060914010603050108070b0313020a0e010b040315050610030b0a0f0e04050f010204 76
    0x480c060790741c0074540c00d80e01d8000b0303010025080402c91501480c0039108036180f1a1307540e50b140c070440c030b4107c80d40c604646000c020b841e200b108840000013802074400200301c80c048414009498058980807030110403590781000e03a020441080c3d010313803108002c00c10940703901c1c02c03001140c01c2c1225400001c0b143e41054600b9088140700e800c4081c0850a0ba0a5112a0014003540300b80c070340c140391092682c0041c0400340c8510060081583c103000d032200d0600280c0090641c000b03607a038060002c1c0544c001401c41d41c00c079002c0721117810803250031410080140100400c4040d401004041c1d030b40f602401100c0102c1c1c140030000612400006640d8122140c07604d440b801c540700d541d082c00e04154504400d81c1d10441340840800d041d450b089129000b06002c43c0c2c0965076601d14505281903010b0b44c4d0302d41d00024507100400c191500d075600c210035040503030329000035082001000550412070f5030300540c0c02c0050100b0045403000d0909106d81c0643c1c010030846c1e17842200d00d5000341c203038815405110101409 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 893495323 1250 893494073 893494097
    0x21903020316080405190f080c09040f02041d011d0c01021905011409071505040b030711070905070507020102070801051b03180105070f0e01090b18030a05160e0106020d 74
    0xa00e0b0510003140c0305400352440c16544000040368101701d0860380200c141c05010801011020031000740060200d0340c00750402c003c003113001514440c0b00400141c08590380b0302c140c2046550b0f07a840181103c410f028041181088401024000e110003401e89006511f1801480d240c2140012003516610f0305078000c00b00c0000d103204465400c9100c040440d820341d21148107500120042c40c16500c2031031134000501c02070380f40c521040c00400080c07000d10b080c440700700300502c240313107042040340d91000240c20044038400a64032010301c0c01505900600b0054034027400c1c040708641c01001072100b00d000341e00b04d40c0d03443e0b140c3c0311a900b06c41003907529200c0c03645810412a00f561103040519400354030001020b0702c07000c0c440d0040c0d0954504580001c00a0f030f9401a104d4480d4100e0010b13500c122003884c20421281c00c0200b05142c0e403050f000c0b07440c101002a00400441e6030100040509141d120b400d03184001320503031012600c1e0140340030742c040582c90711002013a040d100195051078401a9035a070381804403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 893496573 1250 893495323 893495347
    0xb030906070e062b090609121d090601021c020607300b0303190e0a0b090a090e0f010906203103210305061507060c0e13020a0219030203 60
    0xc280d034110700013581981c800da1011141d44141c0445e1405088041490500c1c0d20300079014828011130841884a215802d001068a081c5c85603007803401601c807101c0b581c0320100143e1409100812801c0c040c540d40c0540f02609502182c8180100c0706078070b5000743d40b035a840356510f500c0c0c3c401240c05a4250540302603000b82c0e405800c06d0b00c118101a05407460801420b105809420380601c916020a81002c1800c2041c00d0040e11140189600342880f03041590b01000500210450f2048405040c0c1310703584020b0f00d8406103c503000408818008009030340c200d14007000902034a6140e00c030303181000c1c0070440a1502c00c0c0d0846601c800080c00c102c0703c0701c2030015103144d141c4411621a2540c1800c00b80400002d000181d01c4001b03924101419480300b44400c401001e49400403c51800b80c4825405107003041d0412003030b01c601c00c2d40840c01040c00038070918120b50381c80c905c841250f4050007483d0040140f0740c4580c02803090700002c0c0d095800c03c2604104124040c1442e200080040c2c1c410814100c0c205 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 893497823 1250 893496573 893496607
    0xc062a08071407030f030212030411100203190903110f01140d0b0d0b0402090718031401021e0705060c130e07030912110f0a08040618050a0b030906070e06 68
    0x502c51008001480c0d41103500718988a00c41e04100c1c1c104101e10350745428180c041003251024448414164910714256680320210700140c1c00c42030041d007441000080c001d000b44140d804900e079406140c006803010740c2d0b000b440107e040c4030a4031913a0185c02c0c0c050182c2007030f038a0085001070685642a620385005210115584403c0c0d243c0f203485d50303d183c840703401c1e0f031000c440d040094014503044156040a0041003200040902a1018401c6a102c2103899254904200049a40012025050b0b0b010028194061f1040040341c07000c03008408085908500320f5005400c1c0180680c003102d015603111110400c1c944614040003512000000381080910305080d0190381c00030076480c2c086040c100f0385e40c42d00d8148843c010040041105034044500340ca404012202c00c03208040020140c1e05499111507903507114034000c880412502d0364503079022961140c0312074018600a0010401c20f551500c1e0701c12180c10a99030f0003110300501300401c0885205030307a20b192001c0014165407070940c803100e442ca8030b9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 893499073 1250 893497823 893497837
    0x20f032a0907170a06080607030b13060509011203020a061b0930060b0d0b0a14060f010e010207030b0702030a0e10120b0a0911040807210b1504090c062a08 68
    0x690781740c030700210b035207041405018090071864030701041400b40d60003040617a00401c419070325034525110080125645440c01c003411103926008000c030004c0c980c01e00720308080030742c40003030141400d002030b03080c43c15410807290000745001d40ea043c03201600e0302100a50810340c84070b5190040d00b44d910a41980c0c20300940c9030071482c4104070000758034000c0004248131010303120090f200740c3c0c403a0303040245088142c055004140c0c0301020450f403d117040c500007042c80d80e0110b0100e041040c2a08007664990007001110081d640140d0300720398521b44102d000f556a400090000c00040c41c03a803070701215007480740300d215100c407554032a0341c0c075500a00c000308000c202c03841440d90300c072600c003c0c002406070b80c0d440340d4104c0c180d10003655503455007000803151404900e6400041e5050340001001c285d20780d000c44006a0342d501101060f0103840d100044c01d2052015000c10380d00610340800001007080100103102150080d032206a0b0410501d540070100612130360702501c0401041c07961000040b403c0b0018245 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 893500323 1250 893499073 893499091
    0x60a0c0605090604030e06040608011208042102010e0a0302030618070b07030e030d02210c030d0c050d050612070303030b0d05030c030406090e01120f020f032a090717 73
    0x48a00c0e100c140c103480c0140c0d0019400d40180c01070205050340800d500303803124001d070340c003030b00c0c0078580000140884414406c044655000e86042020400c0c9241250000c000d43c0300051880c10450100c488840c09042e022030100f08400503188090601c2280002101d80080142240d551176900001d000c0c5180751301d102c40e90140d44004140114100003400f45607021707503560300b0148018030626113080603102680c007d40d8098200001304456402e4140444c441e03100482e61140c0b06c48a609142d80100f4401d20015418103034403c0e0802ea1050240c014805150400c2c00181c403602c0500164184020030080035410038141031010902a4200c0c0d08a080090b024600c00c03c441e403900c0b41990030095401e001a00001000c02c5640e902043d008003400c90030403901081e51406084035810122a10010b04200c03240001c03805558400380c01c041c001c2009000d0742d0920000c11403c012005141030024414120301d0342c044011305200c0700c441c1c13003041d1540707444440080c41c0301c0c0c200f00748000510b9100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 893501573 1250 893500323 893500337
    0x901020a020307180e0120070317040303050402100f051b0a0206030f0f09010506060a1202130e090d0516030804080c030a0f0e030a0308061003090f0f05010b011d060a 73
    0x584041025400510700b202c83c0c16001e9204011390313400e13100e10820000d0107a0601c0281482d0900d40d02c1081603480c0060403075aa0b5483e42d2030265010002c0712201da0035000607508010516415400c01d51145100310380301100364074580307030907034a0500912615001a0007032240320440008400540b03011603100c2d04840325910350b5800201b140c1d208070384ca129580000424406103601841041f600002e100b070003440649000800318440703002d1032031318004002603c0050707465404594100e0701131050203520f180d0901c1d1203078080f000c0780d6010344a0040d14880c4903445000d04c3d1080040c2c50700030400c40d54022020070341c2d4600f15260f0001034002c0d0340c44030003041a50a44d000030001440204500d44540505096201d4090041d80411320b00c14000d07001412a0000294407585070750703003e0421038024613100345902c400c5000b0244c51800070072540c560301c050001c2c0420100b003007000e00c2c81040207120300000d00c0011949002e400710300f0148600c01860300b11161600b1f0b40980304080d19450720329 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 893502823 1250 893501573 893501593
    0x21608030a08040b060f06071101020106060c031209150507020c120a03050301050907140a0215010e040f06051513140709030c0939090501030c05120a020f03040c06090e0606070305090102 82
    0x3584541c0700d01c0080b60527803400003d8400742d503020300403d4002c14040c05e041201001e0b035113010b0407855030300c9801c0006954035a00e68040000142c65100c01425400c010003180c03400c1740000e503440c6114034100e0b10800381042c00c0e05103c20000713030528005501d980e406040d6440e040c24419030000c09005002801240b19040300f0004410014000401d1580d000302844c002c01c800e80c070402c4206800c02140d444191080002040045101000c401d5214800048a5580c1202c2101c004074006000394001c04000b03418520320b109030003044039280e01c0754182c034403912410029110b000c1340c1c0c0f100500c5c20b8905041005008000c0e070250804000b00b15542032860745060313a01034921840603d1464a403594100e0301c00060b132011212010348401e0038204540106110068814080d9180000c1709075403141c0094284110b40d01540c1c00d032645e680d006a02c9042c04d1400c00c9441031316009110025191220001d15000ca0140d010f01903000580410f01c3c0180d551003c40f982c1d80039180c4541076100b101021 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 893504073 1250 893502823 893502829
    0x607080f0d09031707050a080c0702030705120d1223040816060501080d022a0d0c0f0618060504140103140a0605030c0603100b03040201140a021608030a08040b060f 72
    0x101c2c101d54800d64554501c6180032948100500c00502a4400c000060050640a54005504031781000c0c0d980d81460302c914041c030010340340040e1504003e0300031b0030f2500710364040ea400040e010801069030b120a2031650882040c1c00407603031090210b05d880c2021030103442d005002164502d1b080340c002d015042c074102544007407218165105070100c0c7c0403903031030004018410f418000256803800b02d201801c0d80f2090100e00c0e0081c003840c40f04444a40c40002d002c001e595580015021049074445207483c0d17400d5603804008001c01440c070601c2e011503600c0c0c040d80e1031525842d0b81c1109440ca507490b22801c00d400c05d40304040d000080d0324801e052682e5103020701620030408801ea88990255080800d19608100c00d01d8100244041014040c010074014407110725244460b42064940045070780d6203c0d9900c0c001220351410380c00350001c0074440082c018039443d5001c214039a02010014240d05102d40d40d00c01d40340c1d240301e0300800728000342010000c540001e46051885404c808000c001d280000780007400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 893505323 1250 893504073 893504081
    0x204151502031308060f06190504110c0c011e030b0103180507260709091703040f0302062404050405070f290901020a1104140f041b050607080f0d 64
    0x11500035a0000c6140da0700d0320b800408000203131120f00050b0513607042031440c40440b05000351000d40300d18080c000181e007550003d14910020100108140104420390510030305a500c401c420302071074040c0307d0b0310000d294000c58502c1c1e40b800001d00c200c14032141c0c65900b10002c02010268904040d100c402c480a078481055a699409000d00040c1c821549401c8500304014482c8103510400e44140504890454001ca445004c6440820303001c640d1042c10b142844094400a18450003200080300b0700c011300064404003541680b0030380860310780b0b4503004041d5100304403185041d4481c0c000103203495414100713500002d8000344545c04554405446001c6000c0c200300c00e8025016030218ac410600e08220f88004880c190360350b01c40c59074600111200000c0d12012990701c081c0c5251a005034100303007a12a07620403088124610300c1c2c1c210751706000161829000307081c0c5054452880b0072000c441d241a014960300202d400041010785000d00c269200324141c1c1068011584400b001e100070070201340301e409 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 893506573 1250 893505323 893505359
    0xe0a15030f2a11070f030f0b22021c020303040b0a02011a032d0307031d0306010e16020102070803090120091e0301150905100e06030a020415 62
    0x2008a40c0035403144200089810000c0b0032407030b0519440d030201c0c0300c01420b03104030300b460340d28a000242c0c00303c9a00f480f071500038a680040300111a01e00004140030002d0829002d20340300d283d2811058031a2190032080c0e012402c4848070411002c0344d444010b01c0c02801d06112003003d4100b10140e00c005400081c21908540d01c29a002c240000782c51050350b50a115080d41c418800015074071f2155407401181e600c4030710381c2402000c0b0300350071007078039401010200d0341d06130303000e50000caa54400140c81c0082c40405202e60f88500c08031a2440c508551801064142c143c8110044543c0b40d51781e4000d60500c0c0021a0840c0420355608008010110b42c0920040d80304008400000c1500700001551024001c2d2800c8100080d01060003040666a6948407000800000000d080f4160b10751500003401030a4100200c3c40710602054009660000b86c1c0000c0c0c0301d004000d00040f0340d80d513940111480c075501103800503131503046100040d0051501d548241419082410700000b03040d01c40d072600103c4a1084 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 893507823 1250 893506573 893506577
    0x309060e030c01060f0323071509090506092505160c17031c0906180f060b0f0919021e0301080601090b101413030605060906150a0e0a15 60
    0x92980d010b10300034090303032006003030103002190788034a552580145020000c038400011440c8150500400008103e80b60280c0510301c0c404610801200014241140a108081015060900241191a1616040744190b000d00503044451903034140c8031a0200f00e94407040c003441810b20407070242018101030b07000d03903a03c10752003003c502e03060980394403494222601000c04c0340c0c8100700200d005131002d1581d00400031445030200d40034075146401400f0b4600c0b42d22a0b0074140000313500c6002d100203541c0d2080b0040c001c5000704101c0f0203200c1400010504214259041040e641c0440c200d10762184000340c2c140511140103040050002e42c003009000c0300c89000741580d20100060051640c107200c00c03401001012020490540c000703012036000450861190144601ca203454400042c03101c0031121403201c11400080d000d901e030320340800207010a540042c0515180c00c00140b03507003041030155814007011004a4140752061004130b6501895448054100e10010000580060003040d000f0450502d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 893509073 1250 893507823 893507827
    0x61b02031f020d050f0709090c2d1d03070302060d0209030a0302030d0b0a0e0106230406020d020f0c01090506070f0818040f060302131d06150108010e060a0b09010309060e03 76
    0x10f00740401a01c00c040c00141e001d075030000c00e10001c690481c1d10681107903050800810a00d0610000381c3e4802250700b602c0c50002c0c0b4451800b0b1a000c805050b0702600801a100c0072180c04164840c2c0c80030a85510344150141c1c07100c0b1080c0094a800000303412018503030740c2d015140a6003800424200203003240103c002d40e00124800843d40900d0258029902c030983d04c0051151a211b443c0056030418400c54062217040054a2011481c00e000c0310300002503100119070b07c40d62010000e54525800341c11400500408041d0300c480e25001c00c0555890740140e6444000c14101020408039074065542121454226002d01000410f1440038004a03011082c0040c00c2c40004014001030303500381113084649907d000801c0c030041c0d840c0c0f402110304540c1c007000025140c0140500d006685005010701030188244010805d004108140701e401a00303003a40d44490590340d03010b00011107034003a181941e204020f2030302404000780a00262045d41014500411130f07200c95240c10045803088512000c0d56000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 893510323 1250 893509073 893509087
    0x9060e011d040203030304060e0f0601080c030d020109051519180c080303060112330312021209040f0207061401050915030c13061706040308070801061b02031f02 71
    0xc001c420003160070141d6540c01c00d8601035000079100d12004200a003800d070b0355414492400d20400103440301510403011240755507180c1205030380c0c8854120240d4820f00c101d10b241c842041c03042c0203140c0919442801020700750303020014005100300042103802e5500c60f000740801071807280c0c01903144803101113004d0b052003152400e0003603540c01107070081034844c3d0040040c8510303a680056880c9949442c00e40016803040302d03800502d1901548107601401c41c082240c009076020303885860170102d2b4400c1020382440680b008042c1d8554503101079401d014a8244110384907402c1c203400c00711400b003003a2001450003c66a640c1d104668a006901c400344201000500160500d00341883c0c1104010200c80041071424000941c2d4042a40c0c04902070601c8403000615824190000d101074004401181900d50182403e5a91800700f01e0b800e90000d4080e10200c4e11007401400c0040c103a40180d0344401000c8140c207510142c581e0401c03022a05403203440124048880c034607072496140c01401d2809a51001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 893511573 1250 893510323 893510339
    0x71418010810151409030f07090b0405040f080c030d020406020105040c061d060f04090e0d120908070813090510140301061d0c0409110c1524030709060e01 68
    0xa00034190185859084070078407810890400008200010380351411350708040c88400300080c001c50f10010b42500c607002c0203d4264001162490640305950010040041680104029103038180d8020341080248013005010680b03d00040100c5180f000440c1d107405241c101604c1260b2060b4030510060b5507480c02d020070011a141038600402d4186050108456a40f400081c8018150f01051003040d001400d01e159910403400d4034010b0040342410081c00c0201f100319a26054040300c070800041c115580e001c224100d500c500d02c90243c111074100d007418181e60f2012030750780c080c1c40c7c0d5203d03000c44100300107807420b298010184224070b01e0303911b14905441c1040f900342544c020713541140700b0b1741003040c01c3c00401d000e50018286d03090202c05421351906c961400400c2445150824417526043c0184900c1a00c401002403102072480d801b2100f00f11050f003150002d450082d036015040040c08544509060004003500e941c140008040d9000255035226410494143d544044203000c09034004004180c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 893512823 1250 893511573 893511587
    0x70b0414061603020912060a09210c03200a05030406020708011a0d14030a03021911101d0f060f0c031b03071b1a090109031707141801 59
    0x382400101018109400c107128400000240382040550200c0d4001155403070b1407044002e4464102592024240241c0480144c8404070f41070380c44500d0b144e40211031150ba1410700b0010003180d940c400580b0641d94007122640f150303407400b00c10103000785125822204c06002c4440d03141d00c520f0007995070300c1c40c004019081c881c19900c4034095901d4809007025140b031003402599080011500c00791a40c1d881d103400c681c60010103250500d244404518080c03155050350086c02c84051005000600c40c82c3c80c24111441e180031400300240b60400000e81840c1070072900711513500881c44980e1000035420840a0345840724280c800c2c0a103030f01c800240000d042c0c881a5450300035000a54242c03451400c82c100301c03c0881620384054081074000700264405118604014155511211103100d0f41a14145003041741303441401038080690300c40224a01c010148107080000c1ea15450341c001c00390044103c07415a010040200702400b184130840e2404030350500090424440160007140324413407200004201c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 893514073 1250 893512823 893512853
    0xd050a0e21100b1f0e0d0f170304110a03021c1103030d050a050108190b09010b09070c02030705010f140715021210080307351b0c06040b07080307030e03070b04 70
    0x244c90307080301c5540070660100040352004420740710048000d10920307100540820300c01010b00003503074910041d26006804c4c03000394003032402100445d0075400b14030200201e48001e40300c001c1d488004401101244204030600500a501800300034008050081c04079045034005603040308125544e000f00522650b5610419014040000c010110300141c03a41003450034612201c00360006019030000303200d510094004040c5801c020f00a4142c508141c070b4090080401e040b0b00324420f024000000c0340e1944078003000710b0200b1059443c01500303280240046c6c815030003410151510500c00007043c1c10700301e6038001801e07501c0d215040303020140382094400c8e2407a80660000d203540d404c1005000040b440f21455005810380000b40c00200c07e4059103c040303548410803d200c28210701088a66040c0c10441d003003195013080d034040e207000308150b00800c9110b102da4003d03880460418440351000c04c05043c080d65001005090018034030400b11341c060b2464000d03020031200c40703460f00100170800040d40105030f24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 893515323 1250 893514073 893514109
    0x16032409140f041101180f0303170708090d0f14032d04110108071107030c090f0603080a050306180a050411010201021908090a0803180d050a0e21100b 66
    0x61810305a5070001c4d14500302d12030f1030411250341c3c00d440c4500e12070158000109404040c2c5103c83c0d03035914029140e0703205100d98880c00d260080c000358216016814072071044849101070700f902c405021094404800c01080c80342048021030032608d92505d8900214018002c400708224607020540c0401e207001c03135640d05108141d0383c00003400700007503a0141140e18004242412051581c802c4012a214031080046128a101e000350000c24003080b03100c0c07a0203079034000c4e0060240032164010607050b00c580e488000d2901d8810000c0c0714446200d4406541c01100007010b0760b602c10100c000740810800103588900b030b115502c10a0108200c000110410300d44d00a0000b0f50921440b0900000e134684c1c1a0100c2c010f005458000a02000050104008540d03001c82041e03280d0402c0c5030008200b043c005a40c0581c0e2145039800c6030786601a0054440491059803258a14294502400f502110a030000b6030a02c40110301b0b100101002d10144500301d50312540080c04540b442c01f0400d40e4060046500a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 893516573 1250 893515323 893515351
    0x70f0f0609180933150e010312111e060f010332010908030f01050604030203031e0412051c080613020306030309091f09051603240914 59
    0x15055281d540c0d1207060507000c40099190000d0500020340f08a00c0d040c0000c41e000c0c0882525400e1541000e41c2c80e160b01c400c070130020540400c401200c03012082c01410600321b80c42004200050480351980040019450001c40f05c14106801d1813900c0316028800c00139044014010014030300c20040d0381c0e4400c482c03040603102d6501d96200e01540100072602104401d40380c10b1100341b0010f500105600300c2410300c0003040905680d06000901d40c206880d011841c054007400082c2030b2500d0300544041e250010082c51401000b5070b81d403401c41590b0582004d000c0e20503c000604207008445000050b401180584852104521122082c0250003040414400e461051045586803410034118640c0da2090040c2c1c0c1c0d864200c006031550040c1080d4660202c001420024000004071480c049215603010402009496111801c02e03940700b2690400b038880d0f00c420150201d80b10341c00c080d4008001450420310b501f5000d8001d0301c441d074a5080158030941b80d401111343c12080c815082d80c0000c501011003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 893517823 1250 893516573 893516579
    0xf09041a09160b0a02120307050417070b0307050c0705130603060524010518130209090703020309192102030c10090c030602091203040608041a06031f020408070f0f0609 74
    0x140059000d030052443d048004140224040c0c0200007440201140c40381c401c1d241d1800030802000d5a119001700780344200d6805101c0c07a0ba20002034003c0c19240c0f840985815551102000c4460360401e40c640380d0503101701d003000516500c4d125189015500f0300c01020035010b0440c1822820b607131001c1c00407002c8460402c2c0c0b0044c02464290310500d26502441c2180c0e5881a112211603e9120100d0f1035a1006e0091032400c00300801f54010300641b0020340d409000e036521800b06808a0104450a10654002d80b104100342c0755900c0c00761030044e00c0740e4a501d142c0c0340d1108130078660031300e0248504007580c4006424403840b00d04024603022800340d90000e102e090301a50b6038004c448194800102480d07000318400000d640c80b43c6446102c60503000440c2d8540b85d0f221801030001c030043e00d05070b802e03c1c0660700000640a04200442c41000040e0040004580502d40030340d0f445064071a031869180d090001098452040c000c01c001824400b4040100b5420003401100010f05648100d0620080031420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 893519073 1250 893517823 893517853
    0x10c03051e0403270f05040c26041703090109020120071403010b0d0602071502030f070c02061303030e10021612050a0b0108010914010605031009020f09041a09 70
    0x740c1d400381c0c0c0744c0f400b030300b02c442e40c1c50308080d460b16803014542400b44103450114003110000000c1d0101c660440e03003400342d0802180103560341560814176082018400b141103500c1400b00d0301464115104040300d05551100c00ca03860255041503404209994480b9501815582d010120000b000204444100420f022030300e0b059036048070340b1131300700c4c05444946008220340e020f5103c1c0e0101300001e07001802c40080c0b4a8240002d60003410126403000705501c1030b615000e90762080e24415001c4d00078005240e01d8490065606501c0c0c1c06080781e028004024401d120f00c8842ca4460095110b0740b1400c104220141c200312040f484c00c01c00b40110751003d2900e4240c08414801601150300000185412a900703040c80c40c108031200001928214040000007803600d0154003401e0128001c0c10419031012041ca0701c0360070713a5810f108141d4940c1c0203600150407240140c1c04007030464401450b0009200b00c060214420b140300f1a81501c20700c44440350f80d5a200401d1005030340c410500f401030035a54001c0641 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 893520323 1250 893519073 893519131
    0x7110a080d080421080103051203070c0206072609040506150318031323040902010f210c050304120309051c121505010908060f070e061b010c0305 64
    0x550400c000c0da1802042c2481888030784400940040c60b0314130301c4200d001c00301400c080402e1004030790521410038102014412002a280507000ca0707983c5074041038803502000700e1600041c170305842c1c0346810389090381d000c526942d441a03c100fa1100e0035880d480703840100012104000c054038003501c40d10b501c010350000c8880c2100c3c0c2c0f2001c0181e8505100c1103082100e031035400f035181400c1d130800350f609000c40d4152107004211085141c0c0342c42104018103c07807d0005441100600070b012581101d0b501c81c040d800360150b841a0f1058071941c4501880a450a0054030010181100840c2002050109011080a801022180c81c2c05d05000f1710f003040c0e0b905591000300c601902454081540c60b140200d100b400b0714940b5082651081c44420071003200c1d11400c000520695011800b0740e1300c0000e90600200e1414400c0c0080c29070035051b60307a95031003034842001c00f1413a01d038481020050340c0e40c0a0b01096602d4003c0300b01c0400090b03d018446800f404a40015201480548404241c00704400344001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 893521573 1250 893520323 893520343
    0x90b0111010614360105040e0a1203020c160308070201080601090f030305031b03090106080c010f2703120e041d030714010b21060c040602060c160602040b07110a08 72
    0x1000882c0a003506204010441c0681c0c03060000e1000c40144608200704549050580d082200d04218862645404270340c0c60410000007001c13440380300c01c0003405900a40c06809100110703020340344181c49a07a50038800701d58582040f2400305000c911401035503405510954021004c1c01c0a030380240c1007600000501c0f03110b10005003000700010019401d607606a514200c8500300103807041d00c4e420640c8806003c0d086a0103100a9031060003030200c03056225201c0c41d00d42e45529295031101c40b104084005511156640f80080c090b28600c0c00000120000f01c0d50004c90b015940b0f00640301008030810040da400b0011091200c1c2640c2ca418003541d00210444d0300040c0c0c0300c01e2000c0c8a4007022022405042d903204816808224180341c402c611011008241c80c03d2601c4040d90820798410b9900e0101b401030b40246001a48088000780480e6080c40040c003150100e419a02e180d00d0840d95040181d92103900b10452001021400d03204101c41040b1040034524115201c0d051a0709080320b103a034500f0702174 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 893522823 1250 893521573 893521579
    0x50f0f07140103090c121502180904020f092a0703211104080703020108180c0d06140c071505071d12010e0a020907080106090308180a090b0111010614 66
    0x652020780c82e03000340e101150940d0700500003c4116030317402050012001104042d101c08150703c0000c0140b035001d200700c41d084a08101052000403440701800f40da51402802203030000c8405c600502c184d551038100380d1051110a00802d2406841030000c148400784024142c2e000ca2300b0300004000a0b082140d294807101c0110b2201b1801420b00c450b20040c0641c41c41c005c165410019002c0b0340e402c000f050b040d007624000cae291812140ca419400b88013403002c0149100741a0410114211980780c080100844c0501420010038000001e41c00c0c890400b8043d07903170401c5414009a01010400c040500e440307540b490010402c001d00d40240b020f0a500c0710b05024024146144600300c0140d5100c0c0002c03d40d44108800801000000d80511540c842c4d03607c0d0280e100f1040f62000500305440b80d42da4a041e90581d6980003111403031540c0389841a085041342c1641104042c0c49003a050b111100c158000b491511004150921400005040c6203c1c0000683c06039062101c00d000002000c00e8205500e1026 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 893524073 1250 893522823 893522849
    0x8030d02160c030305030702190c0b0714010e1612032003040e040f02150c0a1b030209070f080a0c05030112051c08010e0f040b16090819050f0f07 64
    0x507030303400d20a0624081c0080c002c001c0759202100b49a03210b0080d40c403072a02a0200c030002480d40d00440d890813600c10005014403070200d414080c419400001c2c02c1301d01e00c9080c0b44000f0035034404603682036072402c014066040d489124103502d44115190749034024207402070500d4002184e81c4001786a034010a5498082540f180858031606000308111401429601034201141c00e02c0e141000d111300d072860084c0d120b00006009003940c007168408a69142c1a908001c1c00c12134080d0f0341d5030400340d100390794610642a803040000056218200400cbc801c00c0c050792202203a680141c1c024084440107001110100d1800541084142c1c003c7e04036415115114a6286441820f28100f40b400140907003030030300c0c103030b2000c143d1700000e4000c04958142c1d4040c4008840c19a20102a00d541040895024010083d81c0002c0b074420303d640c42c01700c15100003034a0946400c0341c076045000d10f031070190380c51030b15040f034558020028041c0602070019581402d5000e45201e007000e00c0d540d603840103140200c8441c0c1c102 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 893525179 1106 893524073 893524087
    0x201020d0c090f03170f070506040611211906170f0a03080114031c1701120809220507050405030d0216120c09020c06100f08030d02 58
    0x3c0a18003c00540382d902c070b108050001000a02e6807410810940a00a03001401000e249024200801e40b43c203042c0307007103000c0324501e0100f0303800b0140038041005081000c1c106010500090102426551508038844c0b10060302d40441c00181442e1543c0083c444880008102c90200a03409a0b4104126180313665206c0b0400d01006001414020040c4914100b00c1c4d800340d41204090116014401d121126880040e9011002d00101d0201a0324080c40d140569617240540100d0322000003640140d52107201e5405103c20a5108030b040111440800c107000d0715202c1c1c00d88000d48240701d82d04198001030103a61050050900174041c0c00c1002c1e00c0a400011aa40b9420044400001013803602c03130a511515007042c0300303c0300031451a00c005080e03641030014219400c0444060585804c004640b0000c03103406a00c01c14070201e00350760410070300b0004025916001550383c03003d80d60f005 = true := by decide +kernel

theorem cover : BRFrame.Cov 893345323 893525179 := by
  have h0 := BRFrame.cov_init 893345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 893345323 ≤ n) (h2 : n < 893525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
