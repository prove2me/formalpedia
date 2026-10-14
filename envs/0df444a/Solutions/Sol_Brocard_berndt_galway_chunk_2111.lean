-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:40:26.794977+00:00
-- url     : https://prove2.me/submissions/b6ef5c50-95ea-45d6-89cf-d7796f363591

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 379496402 ≤ n < 379676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 379497652 1250 379496402 379496417
    0x9060908031804020909040b040302190314070c050307060909051008030702010e0303130e0618070f0c11100c0b0c0a210605030a1401061a070303021809090d0e10 71
    0x20070410b0703010304005040140000d400e05462100255034800c040324241d51424480b41004205903043c000342c06003000310a11803020310281e4034010500308103c8400c4e80b01c0500022000c00380850241601c009002c000e08035070810303840f090000c00f42291480341400745030624021800b0450310100710f030299130202009500705060350b001115016034516030b007a00350100700400c0f03a920303643c1d00d078036009491440d000d081c00381400018801d409040d4414002505407500030302988581c002c0b030301e000710b400e20b01d0a102030070790b581802030040021a03e82035101c0c8a10340c86545480e00402130814003409080441520b81d10108402c050b441188a4400002d004a00c019100141c9001000d810303041d00000040503611417002c0b80c80d011030b018040d100e2a5414089032a0580f090007090081e20913542d403040032070300d40108841c40340640c10004090503000b051852035010341102162030380700014101d586a0034022007654490880c1c7c2e240b030300080e440b02e8447c0700a00300303e00080d41c44410b60b5a080d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 379498902 1250 379497652 379497667
    0x10309080f07020a030210030b120705090414010213090b010e01020a050705061e0a050c0f010e0a0308040503220f0501090509130305070b07180e0405120313060f020a0906090803 78
    0x480c03590045200300e031300039070030840440962a05201100d2400ca1070301e0020b1100e00450401000002408150045500c100001e000c141c4900c80c07440e4219910224400f4200300c19403400b80a4010716079601031500c6415000680401103800504120790203803100031620346180300481c2ca59001e018064195803200c3e41c208500c0c10900d004140e6942e1005041c80b0703140306460944403a9001100400020340003140f40c0c0f00998060007040b07441c0b045180200005004403001e10f495801181c4042c0a110103c0001814460148100d44800c0c8446107051080c00030003070014082c900074099020071000c5150042841c1d400340c03a040c0b0a035040180010055a20a8081c024003440c40200b02d04000c020720120001a5195103014000d444649519041c038109405014800f002688140022003847c030034400031170b50124480e10704130345450a040d540da9944800302c8030002181c1009042c1442c00d107440310300140c182d0103062012401c0d03603031420069554400702d070207a0b19070040074480d4004103c030300c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 379500152 1250 379498902 379498927
    0xc010b060f1b101802132c0a080c0312010503160902070c120b07030c02010b0619050c03120615030112030e01031b09090b030c030d0e0120010507022104121103072301030908 76
    0x161184c0b41c031f40c04650b04180ba03a960070101d0342014000070100d03440841c8802801541e41c0040303000d884143c00400801095000c90b03102c148042c41040001d80e8001340d400d0501c40310451581c040c100400076115548514a010540d803402100d000002a240c0300e0403409051060040400803040100101e0074140b0241d81c04842c050b004225200340082080f1a241082d024000340c0312508030b07480ba80040e45005400c0c040c992010720581c1446175000c00040c451760904040450940d41c15140c0a0915651000142d00402090b0380000c4101d85902c0705000321075001c8051030558100b41d030284405400e4406040d41c41c0300d0407103541e606420a480c4109540c1c82602d2010940e00b0500d0074080ca82d82d810018070810300300b8100c0d800c850b5180c80420502e9501000041d04400480300b42002e0403521008560305400b40c0d010320050120b080340300d041030010500d90600405030007000d80c0e80c0c01d59100072800c0c00c0024205281240c10618000d02455030007071094219054000c000145003070008600b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 379501402 1250 379500152 379500221
    0x901021203073518100c050403060506041d240702210d090305041d010303141602060f0405011805100e12010e01020c010b060f1b10180213 61
    0x83c500102c2c034020401642805000e202401050450010300070368550076000c5040003900e909590f9400d007810760940c0441c5d8400708903411642c00c9100043e481c1c550100003005403d92116a140700304c90403000606980002c501100320701800860440d141d1070354240601e803108120b03003210243e0004a1600e0380c0301424803006c86c201c6900003e04c1d2400069801c0754013203030741c01d603401d600203000441d062203005400c502510f5040504180c605041d0303d1645e004048507110030303a81d0495100441e000c0100e03450700614254081e40103000c561140301280d55640f150b0042e10959002030300b6585144411410840d2001c02d0740c8024194126248e80307641d003070f1080c1c20890002078205034007124a03160040280324449014910302d00140e5500342040005007901c449552580c82104c1c1040100804043d100460700b81031140c604920214510920345400c0543d42c4000040850a0111a00c07041e0b800d0401800414802c440c400b403580b030000c25540c211b488458038520888421441140a0400fa048 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 379502652 1250 379501402 379501457
    0x40c051504090608030a0906110705040e3a05040b0a03180206070302070f050f010543230a030c1b0801061514070b1b040b090102120307 60
    0x1030203803030142d46252280444203180c1c818100c9070000318140f540ea030f42c01000781c0005c1505242a800500c160f0440366255507245c400d1600c1240c0c1c829549100610034040e24512078003040007001007211405c400004031a580c0100c0c3d984220319070059118900901c00c0d0b03801d81d11200310a900301811040d050f0300604a00c40d10015502121f9030810060340da000041003a0761095024100051030841d540c90329a4558005a00c601e404031100c50450741d01c0002e440c0e600e02c0345841e80070802d142d000301054980008001d030014a80d1a0781a05030905445030b508031580c8194469405444000c001c03201a01100310a407880d034014050080102c0d01c10341c841030205010741c20140d04424015071880c01c51030350b64071101e0142d440b0320b000c200b8641e024800a11920355070810512105443c802d03140d861082c2c000007407611000d1030104140000b07120922040d03041c40c0710101e40d2280c9445900456811400070180144981040e40700040d803110240d1b4050201a1100102680000306a115208180c4c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 379503902 1250 379502652 379502689
    0x60c030210090f170a02060604060b0a0302180916020c0306011214011b030f05062e1b03050304020915030c01050c010b1e0909150a0b01030b03011e060806040c05 71
    0x7103503c0003150707008003003600c1052404039030ba61390740001348082d0400200070034462049160483c1000f142015004a42c0208420b00c0c1c01603566801100d840c0c8041981150f1541043c0f06038204141d40c543e40d14000449290f03a02240c283d0580c81003003560310b00c000d029080030050310768000400101480215500640c9080c000701356058420619020100e003050700c00000380d160080d18070070000718414941c104005031032000300c02c05100725a000b00c1054502076281400b0f030030500e2601600c2022141d00555007940c090701c140046007001022074005440c180d00c43d2511001084010011814004040d90090b01a00c1011440e90040d01c80e0f0700001910442952141d41602c140c0e40c4420280305040100c04200315503900300d4081c0208140c0080205505078044609198140490001d00f94044041d45c8007040e510006001200070b4040d5071704194056003854100541c41142d11054074038804070010070000310342ea4111155980d0401d460141541518840501c03080c00c048001818154010b03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 379505152 1250 379503902 379503923
    0x90c051c0b040c12110702030d0516080a18080a0f06200c0307030f26070e060304050d030b04090209040605131b0608070c0201021902030f0102120907060c03021009 72
    0x141c012506844031110510000340e1045108079060040744110f1800701d040c034a501c0d040c03440d90381c0800c0e0349900c40107000090080c0450034408802500303019484541d403088100340c441114520180400c25400440c5400204c4494007041d54a00014400d0010782c0040c010610030351a500c9120080404a448000d41c0703424000342850a4002c4d4001e0002180d5103000b150b0301c0c102418020460850185410104070013040c0014003000301510000744015202003864023519100b1096600c0401900308030740114000c8100801d1000c00b260105240c0c155840c01d019182070041003000301e03518180003d52050000c00490f02103001030707203c154000c550140d50145003c440d1210048040b80b200c440003000c2d104481400300b15402549281c1041082c00d14035902c101c240c2c0040e41714215403010104203c0c84030491020340d5420480081c80340d443c05c1c02190384100c2d0040f54103001504503030800c964410070400040312440b03181507001061301a0f01520710188031024010142c40071460650380b4400c2d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 379506402 1250 379505152 379505171
    0x40221030f1c0203040c03060e0a060905010f0b06190302161a0103050111070803010501120b040c09050a17210d050c040e1015050c03070f030801030c090c051c 70
    0x800003060950040c0001035140c03580000342003100340b0418025a0003e005000388400106041d050005072a0f0220011903001c5020b2800381c507180300303074401600345820440c400b003d101d13040d4020000899070082c2030042501e81401d00c401c134032400c507c4031250702e03100015250282c03013607020f003000c0b5101000b5003c5401d001c0c1c80e1803052144a100c522985c41415004200f04202449001240c100790565a07040200d03036280d00015000500c10310381848002a0034155105070740d0b010280c4000003c10070041c0e0b0f0145540101052018050b16000703c44280000c01c00d941a01551303920500104001e1a02003900c064050b007030101f880081c7e407010018007544c20403005a014041c40740c0f840c10300113904c42d4034240f5054000740014100d03a0b042001d82109000042820a21101c6450b00e414100d03070b1504503100d600e1940c4100500501006642410041016844940981200d001d40c240c1548103860f8804481110b40717944600300400c0e4200300c4802d0140d861807508410243c400300009a0805c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 379507652 1250 379506402 379506469
    0xa0b180108030a080906010b0706111204120f030b06040530010f051f03111207030f140d020c012010050403030606020c06040b1312030305041a0702060402 68
    0x50a070070651040d000440c41c10301c042c0d80400304c0c0b5801100790009013201d51500e81c49511b0b074410140050159511104013000c0b00040c0401c4810100000648613035070301c3e260a00340b41c3c40c01d4003102000040c0b00707110040e40e0f05d03200c4d00132400000320003401246820b1a21042004080c0300f08690300c1e0705110108004034030b0f111714100355004d100c14400030490244486540d0200c0b4801046e100302d64412119103421070040e0084401a2075200c0d44828a5a1306000051815102c42e00303069041d1280b14008000c00c030a034010361049502c2200c00c500303881c60106120307840d41c4002c1311000041c0c1c82005445071039841400303440034200c0b0701c148020b00603140e51401400e000c20400c140c0000c6858009010826500d03214120041419201030500c120f60400011a640306074850f40c2c0114201003110007807515210341401c001c0c13960000c3c1491078113082c5005130150400b1070f0103444031129a4100003500110240d503510440d201d0307000d07060550b125400c10a50130078081e016005003009459015110304c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 379508902 1250 379507652 379507699
    0x20a020708030d051510020a060b01110304090b040c03290f0405150102150106120906020409090b1504050f0c0a020106080706051c141b0903101b0c0201080a0b 70
    0x1001000c3c040786038584018000328000302c00c1004c40c025aa0fa850b0f0310b00c916400305011411fa648504085411b00030000100c2d0101c1c09800d03000e200e40400503000410f02c41030b07801076041c01d0050740c0903c11172503010343c10303801c980c4024448254843c24842c250300d030240002602a03500310091039100700d040c10f94046800c0b81c20840c1e0003c5003120100f142c1c0000d603010400502c40c015248405d00c000d40c140f00c40102903107030003074141c0ea41c10703240d60158040000c0b0340c043e50040e0003005401c001c0c03842181824101c800c802d5a080b5101d030020184044241807034003030b0714801e600a220307102c0540c80d840f060070515840b800c442d0045550b1130030003040403401402048010085651403a4a6803418240a4020040120848505480c06035051130f10324034400c02c681d0240c010100c81d0300d641d011401e21001446a810425031600440c2d440003281501070b80594400508407074003a11a616800040e82c070100222000b80c081081080041c0714201d03e80c102c0000100040d00d100891b00c1e6040d013030000c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 379510152 1250 379508902 379508917
    0x20d05031312030e030d1211070f0b0f150906010806041506050a200a0821090604030e030d080f060604030b0405060402040e1609110424080a0902010e04020a02070803 73
    0x740042103002d410f0590140b000c15218504501400d00c405e8808000f805c1c8041544c1d0307200800751100841403807a4021825202026000f201d405150b90051030051007840c821a00400341c6200c0d03e01081995009468070151510301501c0c0e000755071100e90064810150007821284e00039100c0c01603403201c040060800c0020011a118962906d10b60325024002850340320f100d6050110101150442c0d910010364071405940101d2441c1e914002800039404100c0b0700015158282920780c20b01c070f6800030000c3d84522030390103640d5400300090100c04142c1c42d5241c00f03039620300203004031011861403503000802d0307504a000182006d20b065071340c0d920040004c508441c00e4034903802c640c08120a504080c012210044001d20240c94440681030b484200c030811401461001c3c1d030b0711520b0030551843c4808603000b41c65070400c0714405440c0130b01005480580c664542000400c00800301c1d005901c10f005003150700d6030507100c2c4869100c21409020003508082c16900c114883d002001460000c01e00080040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 379511402 1250 379510152 379510169
    0x70807050705091b031b041e050a06031a060a0309140d080c18010f021e030403020a0504090506010e270a0512040510030b1903030c111f05070c050307170721020d050313 74
    0xa4602d040e02b0031010b40344903404078080c18244409076600d101e41d40e10619080000701c0780c864403001410350460003010004002460038810503040403410743c000507504900d0340c1c6ca03075a1961982e91490042100c0c01041c4542c80c0500e50032181000c25070003804010242271640c4116001e1804214103141140d41c4401100101d800000d000c3c015414450003800c0a001e00b031720144a0590117959440da184414803071880b030401e1100200d45882101c60a111201f5080c81078035151229448004d44c03600c481d284c0840d4944680c5064807208000d9030b00740e80803120300428a0050181004043c1c002c0c01c01c1165880e40003201c40ca4050494515040400143d4000d0b0f548941003800e40c500082d4ec014100c144038801d02c00518180c0f101000081525459840c1e131a145880354010716000069110580186034540509180811940c90380409144d802000380b08582c041540c420041c2052108601e10f0621100441802302c00340c200812a402c1c5140310301308480ca13040c5a0060280c5481c0a41c000c03156 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 379512652 1250 379511402 379511459
    0x91c081308042601060605070b04031101020307050903010b0a0503060c09010203391506130e0f101d0a0209070908030a0306050f040203101a070807050705091b031b04 73
    0xc0b2010b050883d460208041c00208440c07800c00e41d000d0180c1c000c505004060030b142c038000130b04152154070810a41c4032240025903e07414020740103892908030f40700d00360080d17180602c1c181d40c0c2d1900c1c070b600c0400c1701c00240160030b10303840d141203d40c0705a00c0011502d055210030060042c40400a2800000c81d12a240030718082500705462040e5280082610711000d510150340350428120098865030082ca00f1600003000e042c10340040d401610b05a0713050111801358051103107469034045401e44413400f00d02010080c0100c1403404400c4210b801413101c6155011505841c01414901c0c602a00b0000500f800f010440c6c7c2e42500504d1948600411030010382c60300070400c1642091501607042d40b03c00c507410340c1180341101d00a450303045140329401e00359209071140d0818a04540807507084541050581341d4510040c140160b645030f481c4901070081d420800046c140c07694586942c03118204541c9042d1854413030009505a066001e0000006180108400516084040d500c030003613503859580c020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 379513902 1250 379512652 379512689
    0x2030c091906081b090906040f020a02010911030a030c02040504030225081002030c1801030b10030e0c0301020705030a2a0b040605180d03050a06030c030f0b091c08130804 75
    0x42a00c0005041800e8099800d0310650118040f130701074401011041e00d5081d0f00341c4d1002c00040141c2032555100e00c40303a20014845d040300b0307810f40014203098003a1919441100301c85d000d0665841070381001030005514030321014014a03080d00321b01d401a0080c41110b600601d0940f118420b0307400f12005002546c00c0400030071203031b0420312000088800b0a00110b0442c03030103010f8005540705400440c00d4136000c45407900c0e841d80c069030001d10101c8016150380d950310f0040001400421503880364242038414030f0107021042c501402141e000b02e61100285040c4a28030500f907030101c0300045015008400349221004c1803007210400c0a000703000c2d4020080505140c20040c04540014118100c1c1070101034222210f4480021400560101c1c1c0c40c00092555903208500e00501c0240c00c01402102001c0c0000240301e0040b82c0c1d801c1d202c0c0604500c1c0383d10780340c01c01704565440458002a013030048a41d240700301030740a0b0034001c1d0702406400b8400c00c04a4965a00d40c295441b0360005800f5504042204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 379515152 1250 379513902 379513907
    0x61305060f06010e010f121518020f040b07050a0b0c0a0e04050114120f0105100302131509020c01020d0903020f0d0e0607060b01021c030b2d0402030c091906 69
    0x15000649641c1c01001410024002014542180c0c091418000710580c0007030320a01c03442480304405034540381002800312202100c824030380c00e8071905002400703500705104111030910881ea40c0c428071041c083d01d46858122889142d80100c841990940102c403810703c08100c1c40007403144503a8050503903a6440810f60005080900c0300c11403c2d0140380380400620035a40862030b0009003030f004a400c1c100c031a286461180c5014440f5050701d07903075401c02041c0108004940b0202042d603100701c03551140380505080050445881040d25892403100000401102c0d555a0003802031500d490b0000d071601c883e01c1c01c04e4054540c0040f0490059100d044c10194804050010060050440c54441c4404c5481d400203407030f5001c2c42c038001c0c0403207686005c1c27020180e0003006448929070010002441c02181007402900070001c0c02800d0b8020300481450b0051000c01c10480c0c090300004120051604810358107100003500010002c40c40d520f0104810082039035209035182490082c500d007d030b0042d0030250300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 379516402 1250 379515152 379515163
    0xd180e07022b0e04020f210618070207030f03110102120916180b0a0503060a022203020d0311070902160c0e04020d1214070b0610141c0905061305 64
    0x75285424a0b80314015901907201c003c4841c075030000c440250721241d215040b2100ca1040003903142c20381d030320010b0080354064007c540034840c0c142114003d10360141140c0450f08560119643c00061700401c40500010381c0106214002d81c1c0a8940881c01d01c01d00b204107403c99004841b0420405040420404242020417070920003080308034034540d80710701d003220200108a2001110108a0b00c42450900c2d0342c6511000100400c0000d003100d4560810b41400c80c000d42c001214400071401080807080741d05000c01d565401c03070354050680b504200150301c00301d9401c2442c40d80c1c450365005820000802c0189400980114103c1044800030480ca51a203840600701c5640440000c0c3d001c01c0400000d030b41e40d4824106080c0c3c01c418107111010240d902250f200c14010003420100d0b002258640c1404141c031400c42c425032051f1900790041d445880c041d124940003a5800c1b100010402c25600180342c107081c0490381c00b4000701c003c2911192a6669414000b0458000d4045070f160300348403090000c104038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 379517652 1250 379516402 379516453
    0x3120f070b27011802010305060321211b0706151818031707030b0402160b10031203020f0d02070501050f131104110903072904080d180e0702 62
    0x2040020f043e6041104d00c1100000068107044e91034000510742c3d1818040038403544007500090b0400701c01100103401942290140c031140c0002400410072000c1d40c20300840c0503035841044032032019070007080c8545551101c0e10495445d6200c42031181004245503542010b041c180890110b850401d401c00c404807142603d00242100c42c000f468804250002125134072455140002c881560714504240d000c1c1c21100b00d0190400d01c0082c140b190550291540d81189225440ca44000e403510180364155030118040501681c0d1141d40c003a801d640aa03005000840c0003005071070900b0846d4444600326040540c050b501170b5121800c00c990440101121075018a83c2561410203020f56180c0d10351900110450300d000760f80d502c106280f0940104256861404010b0446000c907495010b0340780c803d410260a01c1032080381080b24012520780601365410782e540c05e4004c0080300104001224944000307003401c0c080c001c07000000b181c02c01d0382d410128890741580e0000d1031504a402c1000724400030030384 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 379518902 1250 379517652 379517731
    0x20d0804063c180b1b010203040b060907090f08031801050f0702040b04090204020d060f050402090102060f0402060903100501360f060b1c0b03030903120f070b 70
    0x2d00c9501c1510091489252050322902c000c8051036140c8098400d00c05400349016180c0740c4410029089071920001c0c42d4003038926500841c882604140c19081c1d0100391002020b1300e003c000007910608042d03c0c9141e106003103150414516655000e14889a02a9004400d80d600000f8a100440550500e064040340c0280783c201c0c901000300306007613800c2c02204002031146459051044403a82c03250400021690010000c43d40c541c0c0c107140e018002c0c046807140004c2d040c0c1100000909180ca4820b94051a5068000c0d1110750b580850b814024240184100d90048003800981c0147d18104121403100e00f4890000400e94107218102e01b40c1464400080c558005460b208040200c001c41050f20410007900c0100703c000d000320100025103582d4108508181c0082208100311250381c03035920002003002c000304450001901819100d00c94400c80c00d8044e4800d0743d4524400410784000c100041800c2d200c6410404e06603217651500c1420780310381c4c84820740c95004c1400d003494500b006d5840384846 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 379520152 1250 379518902 379518947
    0x1050702061320060c03090102010507020d0c1407031707030905030a03090b0c070306111c0504050304301a0a0e280519031b08180d020d080406 63
    0x40c080108040b50352002080031440001c60b90030038a16528454860030f000b8a115168040c0c2e141143e0b5a1300004140b90041d820103000c54112400410403000c5c682c1e5669418900300d103541c07510305035421420360100c0c0318401c00b1400804a145a5911030074006110740303203951a2460700b00100302d074425801c00751094200d0500c0700d00103074210500000301d800494000d030b200c0000d0380d011130509000d0380c0094411406c03e0308030001043c14100801201052104d000403004c0c000201008407801150000d00c0c55104100c1400b003a041184469601d510502e6414200840c241c82c01200b100800000c0f226000840d49100201c0e402401c041e46c0210300c060100001d6201c4d03a0240da03603443d070b00030844100c0c0c4400c03001080026000c1da404403154001c412144c8494540c480c01600d8004044190001090714055038101e0403200944040c65400820140c204198031540b4070f07000d14019050b540c4030322100744101c0182c072000032402d01c02d8041d00400c0e84a500d0140081e06480306140c800522141d070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 379521402 1250 379520152 379520161
    0x20403170a0c0f390801090c050405101d0a110306030a030f02030c0129011b02101b0336030803040f1b1401050c060f06130903080402030105070206 65
    0x8080a070441d4000115080e11180c03424040007520102c1c545012030040641c0072440a803130482d50038041c24110310402401c40d0360b099014200d82103048000c1c9001004902000b462401d80c000e45d40100c9205042e1500503030360140307070729a40000591348c0e1842e8030800410880c50081e11441407960390480300586540341540001ea00d98280100080034814610300e440342407071080040d11542c8060740020050200d442d640801ca0705200c0907038403a0001c80303281e2007440794494007943d80801045207560340c0220b216420000000c1503c0c121001700004c03014020382503102e550100c6501030182c0ca8104400042034040d01811030401d00b40e0001c43d00d1500d1094884a0700344014048a8004c4585a12a01d42d49407201c804c04070b80001420780400101100c00803e1440e0840301101c0e4950b60903d1403039004001519603004907003e00809400442c0000c07040610070b0308003640700300c009050504a285c1030003100111054904140c00059554040004500b42482030a810218a0000f40840d160 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 379522652 1250 379521402 379521407
    0x7170105130206070f080d021321020604060809100c0c030314190e0a060e0d080603070f0501050d1e1a090402030c3a03080f0603030a030e0a02090a020403170a 70
    0x11020001d0130480e00f800301d0000e005070003080e240002d850540555440c0001ca1010b1103000302c90082c1a460f001c80019003c0300443c14074040c0308158050703c00360603b880d00c0c40507a1400300c002c202504a000381503200310708415503c215482c20311140c03620f100701151410010112100b103100e6107066644a03041c001e00c1405800a0f080c0640c01200c080f8160464500c0d03282004030340040200385a00307100440600c40804035100110088541c0c59000780e6403144201540d03080c5607c64950031452055040c00a540300d07000800701c1992803c8041198240903d15005181948800b032940d103a403a415500300030815568184c0c401000c488000c0c8030305083d0006526240d4200781c1c24400d02062a41d2541d200080000d030441080b010341100e00d40c10b030000f00701c0203091000700440000b00c0c44000103160601e545010707409190007038000c509103440503200750000c0000345c4108000e0b2040c400701d20b0050f0744050455102d10000280540c4981c5545422312800c1c00c2c40b9446880c16409000581c805035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 379523902 1250 379522652 379522657
    0x50106021009031409010c0c0f06020d030212180c0907080106030b0303040e2805070201091a0f0c030604060308180a0f18090609020301051f1a0f03100807170105130206 74
    0x1400f800c0701e0345d40c0f6a00c0d03200589114009500040c800301c00707207000181c00352810b020038040701c0068090b540400c4c4590760440032849107101004020980340003154984c99055100032203100601e0489100a081400040b5220400c031521400107101c0c60040c05039030b9040c00b401d508601e094000b035040c113040ca6000380f010340c002041c2150080d4540e0020f031040d03204404a200c94103013690308101c1410507aa00070701812440c0070550300b622207075014004c0c152031440c800c0d210700f44002810007142c445e8107041031594070190500f0b6202c3e407622004000305079100002d00e03055049030243c5820b01348200a22408044560248002c41800c03482080f504c2c18010031032081418403100001c8100c03030b91400707070000e003c0408065003641c6000c007000902880000e00c2c812501c2250820314000780e60f01400c9215005409410107007120600c140c01008514802440d0817055807030410401c0c98403a24071a10708826580030254040c00700c01640e008035400c1c4039140d08140c102c0c1000c02002c4950300442c2461 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 379525152 1250 379523902 379523927
    0xa02100e060f0904111918180b03120c060117030319020f040b0a0c02010e03010b01020c010e0f0405090304091b091203270807080c090f04030c080403030305010602100903 75
    0x140010f40b61966a40c652003c9800d1851314800350b114072885440540482c2c400c2c0300b010204060380c011100000c0200c45044c12510101e00c2e050100611145400c0940312803c501d40e0184030340301128083e415a50003401e6803011b000000d0159616104c4422503054103606580f400360010400d1281c0300c020b219103807800e40e104000150355030b04010214036142c411540003a07000000498142612a401101050054000d80c0d03a5a100d40c6030301c0805080304e80c1a805e0a001da400800001b400e940a15280c58000c000280440c465850003000f080a50350201d540e0b0314240c000290510010702a803085170030442c1c43d0081003110f461401d2000d02840074074014001140b146480000401d803290b54100d8080e40e0840400046440450f4555403140c0580901c098502544402013440c0800103000c0345405002000d20001d501c61074502e03105442c0290099040004a41e01040810074100c0148000c612a80d0002032942c54800001d04000d4018640300d551402c15040c40c0c0407a62040d0240006c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 379526402 1250 379525152 379525177
    0x320c0c0a0311070e0106050c06150108060d080f040f0519050307060c060912020c010905010305040f0308090f150f010e060310020c010b090a0903170f011a0d020c0a02100e06 76
    0x25a065441d02d2440c210041c2e01c40d191080d205000410120740c0714024001d1074900720708075441030b200c1e02506400904a4a1030600203440100060080c0c500022403681d2240104002c901d02041861a0341c83c0d6402600710180f9000a400e0410050034903092600307440c11250004007130b807401c1900180d02ea40e940d10850b4100300490700c450b0184a03195201c2c0a481c1d0b030085c5940050030302800040d40307841a03060000c0c0030400215001a155000e8040c1c60710440e401901e100450840f50350644202c400900090490f1140b0201455403a0041200d4001c1f89155841c10f4480c2c07512207110b0b034810f03005070407030b0180d080703401c05002c0b00d6140003440e04c01d002c0442101588428084d4446c0e4014400122403590020200050020310b50455011080050003580c40300d0036001840340b0740d103a0801c2a0342c18044070b03240300c0041045540d001748550034200d641c18010303d0a808006a0000d070f0300441b01c41c10b1103401c01c52441e011480c00e0150f0000c25005400c0541e1780000c118000f5501e4054200303a00391 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 379527652 1250 379526402 379526417
    0x8030403030b1507050105060a0906080304052b0803060f06090913020402090a030c030501050702120714150109020306030607110d0c0501060510080a060605030c04030807030201320c0c0a03 83
    0x242d954880d0303010b0b5041d0711078440e204d80392440d03030070001d01910040d03030b4039030141c503c00c0d1000ca604006401824252464000103615280c5080d0a10400c00e4000300540517101030802c182c80c0900c919820034031003134000c40c15240c480c1090010885500d2998982c1481441d081103c802c654549544681d0b00616400039a040c40070a070007c1f6000c1e01c01c1280c06507100507951404030070000f426028105480c00384008000d6903031030785400c0e03940705184910380302501c000b8014940001d0002d14200c2e1031355110b81c2681c02600804110500c500401e0b041001d003a5000310400c0154181000181d50021151800c80c08034003d84100702c0d00c8141c0880c81f10300300700528036600305002c03007500140018800038015000c4140e203020000c080c40001e5401c0c01070075007404270005040740305105880c0140b00c61284103280602d140e0721b0401650002c4c4045040d5529000325503201c00c08074481c81d004150f240013028005681010343e00a4180041c4044401c40082c48241503085000840e143c5a82e850306081c4e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 379528902 1250 379527652 379527671
    0x6030b01120309030b0702150916050607150c0309030e0a05090c07020a081b030d030b03030306040e16062313120201020304080a030302490f02040e06030601050d0803040303 76
    0x2500300f80076400103000d0721421010703c400030b1b600107066104c94140d15080c440c3c80e12070900d140e48500104e6a00c035444070780303004248a50314104008010b0a072094030342d02e0b4441040400302c0252054104014040b0740d407981141c080c1a004900844c1100c001c941d00c8580a041ca40019031803440036000f00c513030002c0030556104540f034414018019142c2002111002c0721010060310588403a851981c0c081d00030307040c00c008007030701900440107021001030145045030b03a5501800010240e90701110641e201c0c4001c0c001e48034940d41e140b900a0700050b0f840711000a080c114191081c800b8440d0381e245440100003c0d041c41020008075001d07508451045100d10125000407442c60080390007800150040310b05203070406d03406a008210581c0342c070100c0410b800c400c03203025401c000340071040403c2007000d0a40304040e501c8545d25070885171400307200280400c1000206000c0f40c006800c038610018246041c80902c0c5030406c02e190050204640340840390410b96a0308030280030151000302030545401840d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 379530152 1250 379528902 379528907
    0xf060c0d080a02130b041a0a02070b0a09050d1a090708070918080a0e04180b06040903020115180501080102190806030309040f090c050108060303040512070803120708090106030b011203 81
    0x1d0b0040210300043c0c4c401030392290090b0009038020303c42d000350f42d4524082512000208010b4030030f0740b05980c018103002c03454801001c050f940092081c100304260848081025650240703040b400700d0140494208020696800900c240c0c0050001c2d4425400309504206440b0000b64201c142c038900038000c20301d6902c0321440315030308a00c10401450311101050750105540d01c10440d070140340080740e090041c1050150040c0c0b22002e039940140c070341c42007200001d100342015041201e03031501c13a100000b040310308490070114ac0c1040d074020186c840d240480007480c030500e40c01076501401000e802180f03480b426100819404894098410600503d8000118240e400780b065414425002c0c01c2404000410349901c402400350303040444d03180386d0380c84000c101c6500c0748009030302c200f50190040d45000d0500d4104104002401c0e5040300c1da00c40d1782c0c0d0104e0401400d002402c440c99051194017840d0525040c00b4092803001005c4040c260b140c118100003150f24050340302c1c11100183c11840c108503032404e04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 379531402 1250 379530152 379530157
    0x32206020d18030e0f0a0e040c030203010f020d0e0d091512050c090405070315090906020405040e0f0607020a02011707021903021c030b0a091107200f060c0d080a02 72
    0x240144245405403455548800b81051039455200e82e0355000e20031544400c00180300e140960b1075412940448081c403045d21801d0900c4d401500840403050200c1c1c0d00d500003400e507410301055181203900440d042551820a020700d89490013542c0242500c05040071001700300c038656101e003492901414403048449802904160410400b4140600507450210404903140e031181d83c0640c01145014000392480c1d00c2132284204007890400e880c404140b0b0314920703e0241c20000d00603903002d6400c04c00007070b0643d81c0f8840e40d410821514050241001c074035026600f0420001c10610030754002c00d500c0c10050703030300c60750400d0080c0b201900000280c887c05ea0481c03034428161003040c40401801d511400f41500002e21044125900c0308000ea0803660300411416195248281e03038100c511b10105010015541c0c1040300c05004040c480b5090040785e8860307500812070240c0e803092104820f0040e900c141011204100020001d5506078034107c01c804400d555001088094000c0098540119501e142503404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 379532652 1250 379531402 379531417
    0xb0a0b07060207030512070507140105070806040b150310050f090114091324060b0a020a0609080702061207020d0507032010060b12090c010507121808010902040b0603220602 76
    0x5a0000c7c9040d0001800300d81c0010b000b511400c0b03580c0d0580c00840700500076180300c0e807904d81d07480c00d5139200d000074803000d088050781d0681d000711506850000282c000f005184144c0110303500c00c001c0d5203880140115080d595034818001c8440304014014400354040401c40502c0507101d8140d103030f50b0304c80000c3c98000040001000b40444034a584840c2080c0215001c0000c250030040049d00e540342410401d6100380b1200c600075801542c3c04001180c0103030300043c2e07002c1c0504043c42c0707001c01ca40e000030840c3d803100e034910040100e90414000c0440d8100058040e20f205c03801d09619044071a20064104a0418010740c000f6080d421115120441030008000c0165140c1040c0b01160b1039642e40f900d07540001d103004016070886130015940b0103000a5000c14150183c682c0d620300440c5880380704441078100341740c41c00c4c80809503030a02503140900700e07a0020701e002800050320403a14070400c01600c4082999511a190510500800244c030b6082000302841c191000420800c10b850181c020380076028 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 379533902 1250 379532652 379532677
    0x50c0418090f0803151903020105030a020f0f1308070605030606031009020313110a0b22030510050103021008061011010f1a1201052203030902030115090b0a0b070602070305 76
    0x4580801c2180c0c200144d401507010080c206841655401031040c02d5000020b40d021000c0b0309402013000d940684001c41d01f0a100ca0303409450014010201d44030740d4006400782c2d031080000110030340703403aa4090f0600302410340600500085468524000d00c0e500024210138800c180010108092074102c0c4549001800c14040944d1246026080362544845208007521491031210300c600b080d01d4260354a50645070369507401420041c9042195012080c0c0100021902034044000700200307000f00085c40342c0c0428503030b02081660451040c41612004079803034005220300039040c46803542d5030280342c001010132803030300e160725403c420441800b6200c25154110110728150031188401000051065500c0b0180c03060640440d20811080c00c950046a98a46410011100440c19035030f600b80c4000c400d000e031a001c14004071540020b401c6518415160100c2044500e00308010f4103a0700074004400350445601c00200d18102406200e8820341600609241d40003421504040c02281514010310115 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 379535152 1250 379533902 379533923
    0xf0a170709081b0f062d030603010c020a0b16021504050102030a06080307170d0213030803040303060608070c03030c0e030d0809100b0a090b041503050706080a1a0f24071401050c041809 81
    0x45211080747d51050315405d001c6c0d4280400c1c002410b0002518500c3e603136116200740d4940e070b1240c0207000d41502100c0c0d240c0c00c500402d261003880500818109008a01441c001030f500d003001c0c9004004c60b2125403002c3c070b80d0341082c40040d0100703060711106001042d443c60201c3c2c1e1002e5444000c0020300c01c041d15041211003680001c418001640081c511a0307100fa10200303e403d40764441550441802c440343e5002440e0000407070002440703a000b110720606541006a503401c1e2440011f41001031541041001480100130050000d004000d188008403060804105420540c0d001c2000f01d070480c01002581503c8003142c050540b2650322142448000315550303e14107403285402d94961580740304100004036142e01141c216141c511841d460780001140b01c918801c4e00005000c400750300e0304009a40070201c0b03000d449245000c4220350101d2000c4000b0240d64000702e10b0a940701a07030440d039001c050b0780351000300241200e0340002c8030141c640d0159107044030081c0e262041c0151907603401c002c0070304410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 379536402 1250 379535152 379535227
    0x904050f0f01061e12060c140307050d061517180a0804080601090203100501030c031415030f061608040c080706030501050108060f060f0a170709081b0f06 68
    0x1980700c1d20584d101c2a0412540d680501c50b081454202c5010310a20050503a51803000689203604c041c660005906051440903110000c0c0300942c0c100320f40c24008103a00040c10038400071103103d480b01401400b645143c040b10104c20042c81c0704420004c1134112003440000c00c83d02c0c000f141c1248074482103003080380d802c4051440c040e02d0342c0d0018072407240e09100d148004600c4041c280207403482241c03030501d450242d80c500710044018001d00034000f130a0650320441d03061180e4001c0720541c416041801d10f1503418410105061800ca9a804910080d07000744003401b00ea900141c21401c580340d101c0c41c01d110540c403241845503081c0d10b164000120b512031814000b81150b01900440c3c12100c00f42c940d01c3c1c490381d0382014006141c10101d4181d0b0304c51020050303080c01d0281400a881a20351524004c90303401071031803c00b400100103980c4103000c1071030304408120348981000300ca0300d92000111181011100c0201103201c014a01003a540315100104090040c0d190781d001c0103440c000d0b01c8110024200391f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 379537652 1250 379536402 379536433
    0x30209030111040807060813050a060c031503080c10050405030909182401080c03070303050a03090506090a170a08010308090111060a150b040b040909170c1b0a050306060904050f 78
    0x100c1780b0030000031a01f100d0001c2c07d448403c1844442150b00300000c0c069181d4990b0b20b03c4000c04955004000345030380d40d054540542e0b800030100e0099442602b44d940e44450b41080316150000000024508600303190030030000690100680d0a58902640c03212025100c0807598058490528642c0e84180700b10038040d1035a204500b49400a1610502d20500c580d88800b8102e895001421b40c003030f050360040108100192180700100702d481c1052030000faa001096841d035080900c151241d881c40d03489a40c140e8103014807240d8880c000d0360102d4010b850400c00000280001005100140009a02080380003099001c0ca034403040500040d01030301e8141c68042152801030002102c5a81d40f1100c542001c00d0786000101201d007511000d0031114181031601e03010350003402c090081151040c20f0700d002c014100300020094440407100c038024107880728a49400f074240c945020a050b100b0100d00c402004a0f4901150b95500701005840185507580d8070700301545400303042510220b81d807054440343e81140a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 379538902 1250 379537652 379537663
    0x24160309050d081209071203081f05150a120516020c04050c090f0f0301091a09060103080313051501080705130b0a0b0c01450803070302090301110408 66
    0x921940300d9031402615a4248203140301425001040444200180000d51440d9503440e0b41c0110310100712044540c0b940c404800310810200110081151502030260802401071841d8121b540801c18041e1140b5041c001119101d82c10a22179510800003041c0c40c2c0300d40304e045000c1d456095460140801c0c01c19200d884d140003a402103400050007040c0740c012085c40c05015180c0104c0409040c60300f403014080420689081e1502c10f19400031002e00506440c4d10300b03004a0000500601c09450400d540c0010380d1a0aa8020701442180c0c008a0052002170007003001d60380c2203000c120200e2014800740c03034003034079029001c1c8540c40c015104400000702d10400040c02c000b502e000f9200c04240b50302c4065500140d8013003041442e80b052510b50140606254034015100454012001048003425a0040c00083c6c175840c4181e030710010b100e848a2900b040032880740c90201e000101c410842c03002519022410b000140c104010560001a400c413240e90940001c804501c400700503d03070b155a12900c00e0f0307468 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 379540152 1250 379538902 379538947
    0x120a02070f0f090b010c11040b030a060603060605091f060c080c060a0501060e010e10111002030901020406090b0712032d09060507020d0203040603020721110f0c010e24 74
    0x144c2c10182500c1c555442924480d41c842c1c0d101002d4031981c25aa020000030f446002c03402038241c41401c44000c0400c0701c9008101c000e5018050004100f414802442441d0b035005001c0100701c3c2001c41ca501e11400700f26800780807a4050f280c40030342c04403070349408842807240e8020385009100d51018080e50000940c8024101d51185e00c0f218800c8c1411401501c80400b03039600c0c0d80c0e12100c1c078081810f4031360084001034090441d11086d2480e01c45200e012000f20b03041554099030076907002c6424002640c000080f0009032200a0f201420002655213620407031003001c160404150700c4110704d0b10380003121020700c2c401d500070b0043d07100240c02c403900c12401003a0009040c0d0b68a820540071030f00c51400825074000032030700c0e039024510f010f062000950103584850021910104801140e0380594692003c40d05264280d555060b0081905100c080c60300c100c041c2c54805036000300788204403d83c0c10080848005109403405100d0b848488102c01104041d404050140b2200041c440000c400c02611200300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 379541402 1250 379540152 379540169
    0xd12020105010603270b070c0c0303090302032b0315080a0530070609020a03020a0b03070801080601122405070c0606060806090a1805100207200102120a02070f0f 71
    0x20f20740103241c0c4003034600005500785171842c0b15410350b001042208031280c1d40410581060078034445161744036600d114440d44190000f411040c81441140703814003504c5000303000da038034140c400072400ca10700108c1911542d1031818590340d00e5141141c49040c030031400043c19824142c459901746814425164803800d01c040d40003500a400c05103504400c050350b4001c4407c6a0340450070300c80940d03200c0c0d000340341580c41680e003d003d030400040160ba4035174035940034052500190307441e4202504054842003040c3c006102c250403d01c018003001c032502c1894800c1036048000700d000122240743e0b420000c0c2c40444560301d038909000c104124160000f0301d081c00e8610520041241d1036564508895030b4030140c1d82c00d9440b03031401c0003040b85c104894004040081c002861040b022a0030b60300d17286807448050404e8440303900402d00d02d041c0032a2001a03040307603414624040304054034100003901c80001d0105200840ca010a86c06a614400c004100107450300c0c00d2808890707500d0303a81510b0014043e1082188 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 379542652 1250 379541402 379541411
    0x12032c01020f120301060c030c02030a20041a0121050106030b1503090a1401020d0f0b13090f0f03090b13090e0a15020912100b010e0306090307110d12020105010603 72
    0x12000302c00901200c0010440c60380c1c605507400c0c14000c031004000d8035016001c0140703c2a8a80169400740401300580344500240f0603224440c00008a000c41260000e0f403180d4035000c4ac42c00c1c500940121005042400d2030003400700002540c1d0612541d0102e421214524506000400c4041d00340e803020716080300c1150030720b060b82c0116920031304903c4116044092a00b0600b1100c0c0002c00d49224a0a0702605100150030b21407071549403030880b03100100c01c00842d034585071a001d45085c611001120750401c100c05002130340705a1111a180f200d00d03180101542c1d240e0080600b80f52141c10480080c00c8a1404541d0360700361050450f102d41a1805010211481d044039070b41c2c0050000b8010a03410352140c1e02c104480da40f1301d41c5800940029804d00c1d040b402d0b4584002000d00144040712002d841800001400c105647c001044010102401d502aa0192044c0300c008c2c1d1000050301c6580d6403000c1c2c0515501114004030b0404401450010281a18000c80040f201e4045d044103050303c400e507a0400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 379543902 1250 379542652 379542673
    0x50312070c050607080d0912031d03120903040503120703080a0b010f030c140a030f06060f021005040c031a0916140f03010908130602010501050102011512032c0102 72
    0x40288240840284007a401c120304020718204800900843c5010303000090506503200c0404050b21141503046943c07004074061064015014402c5d41041d80e10f00505034010603404103001d5a070711401c0c0400360301002d10340001e22501d00400c22035000e4140501914807441c1181d00c40d800070342244000300c01041c41070f000220350504c507115200c1c7c0020142c0d1401c400d40741c000d10540c010315000c110901080181420884050404402403185000559001a00c070100c0c0307a01c20101c0d01e554003c0c104020f40d00802079542d5500040f44480d120008000095607102c0d413074030060100183e4801080b000010303840c0600071640d030003454841d1341007078140c560b4514202801d0480c407045004940480e00c8100d210080c90800361038400584501400000d0b1402d89501d0b00710840c0c01820310008819140b11043c0310441c0e081c080d02b0300500b0203000034050b466041881c0b400c03051050051a90800c82e400b110401d05120b11042d2000710381c0190507101035610314000300350f0030061840fa20b016105444151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 379545152 1250 379543902 379543933
    0x702031e0c0d0f0201080a0f06080d030b040209060912030408060c190c02091602030d0609060f060f120b0d12020706031a0a17120f0304120302120105040203060411070506010503 78
    0x10b00010780c041400c04094a080e401920154006040366204a689004083d2401480d12542c0003030314908008066902d40350b00b008041e103c100400c40c1c00f940c0180006038803500c804003580c4070010101c0b183d024010486407000c3ca0f5001d250b04c00ca80e0743c841c800500981050600003003407058000c0d40445100340c120348040c0c0e00c0d542e80800080d000300302540000c80e0301074480e400c20174003111841540d14105036a4400c2c401c2c0c4c1c0d0960002103d07943d8650b010031043d048407241600410305420720f81c8551102e040c004c0d207211305003060954800d07204d00003c038182d0703a115034024495a0243c2e42110048030014000c2d500c540714060034000c203117030030700502e240c8110f041c40b0650403000603d03c3d42d01900303011030640c02c00b0403072440d13164a1141c0400d240403446003001425900b5000c503001d82d26031030581000c6400c8550310800805051040003c010450341310b110385030640d0b60649002d40d59445420206004201e074006c9018004000f00300d1500700300e00031514504032402181120020803082411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 379546402 1250 379545152 379545169
    0x91201021813020a0801031e020a031202010c1b060b040216031205010603090819110303040501020a08070503061c080d0609050109051506030f100b07140f1c140702031e0c 75
    0x818003241c45c1d0401080000c044040b0700380c0710f84c1e801102026001072540400c4010603140c00071202c13111040c4508241981c244a510005109841c3c00c10914107070400000d0a004602000b5001a0f16034417103503e183c450703804460f0003040031000206214100c0c24001c004031110841081c1981c101000003401d1842405440d4007075411108280c17401d4005402002101a0252a0024030203002c83c1d080a1000510280d03204600407800980c0d25214154018004500101202e040c031109000348400d45d265480410118901d0100c00c0001c0c030302c1824488030794000c01c0490455a41030410100d6005456082981202c03204c0000380181e803a00c2030800c81a0180203a1140c02682c1440050b4041c2d04400c110f40d003001030610004a0a619200f54044a03807100d54192121043d030b0190144102e420044032020400d2140508001d0400001c109912115500110200300321034002c20b14444c0381001f10b03044540d0050840303885410400c06440c0c0c8008c0d0110b00d00c114005e000d0141c01d0303428000c00c3c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 379547652 1250 379546402 379546417
    0x2011106100b1303170a021504120f1211120906062808011406120703050714150c0616030e030a080403020309040f1505060403080f09120102181302 65
    0x240580c0142002c4500d1400e0b08074807405610035070186400400f0400c4103503100180140c02240950f01c1e140c000b00645050760809a140c100d66911003000041050005e403842011800e1030032000b585c5001c081200c50b039030002001a59186454003e801040d01074005007441e450030b0741940c5159441c6141e03140c5440c0111800ca4000b071803481000003e402d1b56a9450440182104102c00b194031200c7c0e040c01c41c1c10340d00080580751101c00030700c080303440d00450840040040d800141059811590748a444048034420000307100c0c00c099100c0100d0351190307c80341c1c944003400001a2619900c04201d680d4460503109121a03143c55004181210300c24001c41804441c400300851402005d82421551044010010750441c00b040c0090b54107035507a40160340381000f0105001c182e00407080801000c0d01c0c41588110310500040100700002840007007513035010314040d40c00d20313140c3c0700d8200814500a03112030b0104085d440001c5040001103091854101c05600ba1a204e4020001140e030b030b4224810341c6d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 379548902 1250 379547652 379547671
    0x16021009181103130f05010c17090c180907030b0c0301090e19080a03060b0c010e07140109090509150903040f06090e060d0201031d0f011503030c080a02160e0402011106 74
    0x10014000304281c641e40c001c960b105074517010591040380c558508544011450b00c0004e24172151796074000035030f018040d4010703c1d510b014010784c22000d00064114842c203a480d280900c1c16500144c0c000100f40080e2004542051070f00ca0700e46801204080240e00034011000c01c545070403a084040d060001d8400708540c0c40d03c042210049d000e484100361500501d10f41010180c03103003400b10f50504510003030140d007042e4100110340078170451031050030a4a2904082c0f1541806611a02c40740c0c0c1c0103594000701d1f0001c2d8000100c1d40c90388507070340c0c1c200100807140d1800fa420040c01d01281101c0000200704071407603000050403180c0c854008851044a601c01c0000301c40340240800d203203241518a2a880ba40305040010302000d140c600c14464100070103010742c19412034551001300e04421300860b155070a1f40c50103c2c40103030866030f001e0220340c0043d2000d400fa01c404250440f9503070080041c01101d0000341d01d8050195961403040900d51001c440407800a03450180c904051040040c405019103c0c01c1d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 379550152 1250 379548902 379548907
    0x180528020d03120b0604080c120c010c06020705070806070804050f0a020a06030b010c0c0b040302190510080a0f0f092f060f0d1107170301140105160210091811 70
    0xd49089420289400d0483c2c0751540d80c4d03003050582d54807070000388010308422000d40b01612140c81000608040c070700e500c2003950042c9245121603a40b21010440c281d6009200607104d420741c1c241689030070104d4011600034420300d0107201070142c0060306148a40c0c416001c03104c1041c0e951055545031007030f03050000c2d00040a03160505c0240c1c040c1d040907602c0e42d81031400d41000703c0300340ca0b4000050000d9120510600e000541032040d414009081140c8c003540c0e403070344c900c26480c0101103545081810603480420100c1008540031840036081807420354200c00d014881c080204805900800c01c0c0c40f021210300c08182d840d43c0302c8540822454202070040b0080aa1100c2e0000601120380d00c600380c0c81c840200c04000a10003101c03648211800040b400c541e413170b21290a4035003400c407410841800400b20000b4001001079102c11203070806034950030300e00a034940071000580e0b00340616000000b90f002e01d0092028101e1903204003074204880c000078850140b6005200310500300c81c200c1a5003003000108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 379551402 1250 379550152 379550179
    0x9090d1d0102010b09010608090d02010209030714060d0603121b0506071805031c02060106020a0b0a020f04080109200d0b060f03030705030d020a02101406040e0118052802 75
    0xa02500c058038a00600010521510b00000034022000c260498000b1404402c248500403004000084003014180001c500d0094482c00090ba03c80e410701c150700c000e82010f107010000e07407901c40660310903040b40c6005001d0181c0300d1800c0121807042c8a40ca400081d503003c0d845025082ca510306c001d4454114002c0c0010340c6440074115010810002c089000658262000440351020001c5401d11010b802c00011034032200c1d64003d04000040e44403104560051840401040303c42c1100350b00b00383c103ca40141da07601c8041c2e03110294081c40d80034000b203501e444141003d21001e40d101c0080c0d85141100d0481c440741d9081004070000382e84201030000040c2c840061120f0a000c50340c26680341006044038204030a5658440c510b5201961400d00e10b45c0120300c02d40066010001c65032032410701102400041524200308001c401c0041c0291b10032621440c220707010080c29800071610140131700e071801086009060080c0d8a03808288885001c09043c40410348034103090005640035a4010510000c9122 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 379552652 1250 379551402 379551437
    0x60609060d02040c020712080d0e15010b250b0402090f0c040b0f0d02030103050f07060f1e110d0e0f0409110121061701051008121608030a050609090d 66
    0x30381013002c4056114140c0c001c140711801c480c40e0031215100e40c44030350380c40700710721040020741e5028140348100354400c8201d100140a01c2000c4c2d41510701c42d00e5010703265036410240e00d05a000d204044540300a01060b5001070066000c40c091003a402911100d500b6184d800c620824280200c030741c00c45402c1c0500040c07007003100c1c0c000181132980220000d581071a4002003040100d900c2a072084403c2d60091b40d03080c0b804242840740d03070b0090007213040940780b508552074040c08403008054000104d020031003505411a01071035105000043c00b50403140c441300e2800020f00540c1c0f0303001c2c01e01c3c0705140c040305048441c5098000c0081140e032140c04011861907250054800313880a002d040050714110203865100c0415104c0c0300014000d20301031060b2207020300142404c4030005070141e03840c01000c1d00c050011440c0001e040a01e03800e800855a075900a810302010820f0040307000500c0c44000109006540981e9007000d801801c0403180702c0700c1615400505d96032403401e400070202103101e25080080e40325 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 379553902 1250 379552652 379552661
    0xd18020f040e01020f0c0627070e1e0a0b0406080f030a050a05070f050d031107170306030f1b031207030c0b1504020a0c03020615031c020c0901090e060609060d0204 72
    0x40c42d500000d800c110080d0820116904202090340042d48910204160548d0a03a402110303a40660078103056108501451903c800143c081c03c0c60441c00d030408a03460000113110118a1040c0861410460030f0241686010f0060701c0c0f07855111b079040140219031404049214442119004000d40c80e004030240d068413150001c94002050245c01d0040e200420043d181c04031a0f2882440a464801c803000005021240d843c00318a4081800303126090010703100e03207134801c20b0311000581d040d02d0703030388101c0020f01d04002c21588030583d00a49950403010004902507401c2000101e00f910301c220051a052000e5000341040500040c01c202c070008041400c80c0300851701301d0540380f114030342001514041800da80c00901c0b10800114494904014190b060004a030801c3e41c8501140c49054030b8000243d1f1802c0c68400080407804500d00c001e0b04600800c00500d102c0800760000240d503070764050b10f030014580c1c18010259801600c00040301d91802e40c9880b40300b5035000b440c0440e10422502400000c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 379555152 1250 379553902 379553921
    0x60f09090c0c120201020909010603050103050a0f060b0d1109092109010905040e0a060b0a06050901032307020604141203040f110303030c0d060e070807120b150d18020f04 75
    0x10001c007080700440c3d120892200c0c20080e40c0c0015a136400b500062001404050b80074104241c644001803001400205032245510303000504400891494100350303004100c880b000d190700c43c900c182080200302c030014100709000c400b1500100c055071150851512540d0034180010304a001403200c03090700c070307000016003160a81071420019958540001c54202c0b44c060b0361100c151341c0400c045004000f018051803260341da0594a00540501e4008044c101d8003034460307140e05040d1281e00d83c43c5907551152018030790000074413619800303040416010751180015102030710f4045900e2110540580c0005080c01d2000501c2103262841e5500e0308c0700c0410403202d42d021110200403002d50030070f941c1c040014500400548807865680c00324070035040d0403500d0680c03048003030690010030000e1091700282c84503030140e11814001c81d1150040301c080f0060058101082d401054243d05440351308003207004e4201c07018850020000f190380400901c0e10400500030080d8440c0084403c0802802d0507005a07038003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 379556402 1250 379555152 379555157
    0x2414030f0a0f050c060304030302180f0907030c05070c24090614030402060c0d0908150402090411150406180501180303180e0405010902180c070f081b0115060f09090c 73
    0x10107913000003080c50340b044c3c8042d40003a8012034174030b03c211884540d02d01410002c40c0c45d00e10760b5050303801061441800030516428103503900fa261460500031030403150496440f8040750203143e00c490850743c0e40302c0c0f40c0b9101411000c014220a021078012150710090ba5a035455040507420313000701491441d80b00802c103c0c1c00c4841030020f410455020400603020300f54944810b00c00301c1c2801d4481d464140d1040040e0343c0b00e00401c0605c009a165002c040ea0060381081500d4a00c1301c040c0701103000c016400041e4188682c00040008000b50700034580108000c0c0d00c103082c1aa20f40d6003004682d00c8114170441e82409458600030400207014842e5640c0342c8441421031009203036509038211004c54222000d407104d035120302e416001c616000c0301d00200c3c400c40d03c40210b01030600307103038060040c000d8a000500d140030b51000481481000c1d0152588600060422103043c1440420240070b401d1488180000d20211040811018003650f04c200349125555148079455245c03031003190240140c541c503a4103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 379557652 1250 379556402 379556413
    0x1e16120c1a1903050115020a1e0203010612051b0409120804060b0a0602030d11161205040f061101050c0a0c0204180f0f0b150d08090102012414030f0a0f05 68
    0x940072000c0b941c0c00405429240080c00d98900b4190000080140d103180045410500c110b000007400301400700c450865020b50076840d42c4261011a0040a01da0030078004070742480300307503010040c0c00142c008949801f60204102100340000b0301c802d035519610002c2642d00700c040d54200c0580304c4d82a1662044c040c4001040301c8003428040ba100250f15001000180c20000399212032071103e000740100c42029071001c900e402d100b80341d0101c02102d42d010080c1000c400d5011943c40314820010355001d0010044000c401c0c0340c3e54200607152a8001e8441103855003807200041c3d40030480070070b4541c1001513848a01c11b03140790394208801041d154202201ca20074001ca02c0001c9a4455081c01c01148140e0914140303042c0344c1092080407100810740c04004c400701d601084651110280b50240d268060000342c2c072140500c1c0180c0c098004407600004088401308400c03007c02140205000b01c450103a030380070001c074241c8181742d200ca070242c06681d5903500c5241200c001480203185c0318255800f030000d40340c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 379558902 1250 379557652 379557667
    0x60513210219030e190e0c0904150614071b0b0309160509010b090a09020a0f120b0a030204110d0e010b0a050f1f020f030a0e010305010806160503091e16120c1a 70
    0x843c00341c055655207146040808c0c094860f041c2841200b4001c580007582c00030071490490001c0c104480f4550b07403060800d000c00d1310320030800119112222150101c91b01c05440351900100703101900300711402c03072180c0315050502400f004c8241503041613030b90283c80840c59038249148155070342e118068298020346140c83c000745444080c070250412180581d15600d00d41c1000f80001e200155a50002007480c0c03030220b0040855440300300000850b541030b42e011440c801071080020190041c0140e0b50500d60520b03090800d200d00641c441c0c0403030302045949100b0305444405008441d90200c594540000304410001d2040404004400b51540940b0407151500309106d542c03819508018180303c080f82048451403160b6030503010f094050074500c00100b4007458803001d501218020418280148240000400d0003c80d081c08201c1c502c0d1418545100c5060041c1c000e10f07030705c06441c12072011100c8605004101e0284d88508800c815070040c50481c80641481c0382000b14407100b46141c03103032000400c08103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 379560152 1250 379558902 379558919
    0xf0f09080609240906060d060e1c020f0318060f09060403060501050307060302032e170303220302031e120405101b050403060513210219030e19 63
    0x2107202d80d0081002c0c2c1071202d110403070803541c0038440201d00b10480410040001205001071721560005040341e882281c0310107814907100030300c0e00420000203070240c916681d1502c25400810950588294202c07405440c081d200e01d5203a024443c4c000300341081404003d4031034503042001e00380f0540031082d402d00d0200100001503240d4440c0e84101c500e241c95a0042020303180a2260000a00341400d0951441c81d06880548400748117064100381c1541c80b41401c0042080058060007500d00c514085940034403104020350b50750021515a03860758ad8941c10b40f80f80118a00c10603c419915400442c28000b100100d500030310090041d0050742403051203007032844070700801214090384c010030241a5180007807000c001511402c140568990b8004000442e0745507010381100c003101d8100740c00290303c0c0c075604807000391f0300400003000c2d241c9910f8103003c40c444c0300e00c003031154080c1425408889002224204503400040c079050040c011030041d082c01d40701390030090351038060354070344480c1480c105807241e004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 379561402 1250 379560152 379560163
    0x8070c141203010f03110907050a20060106050d050121021210020313050f0718020703020718020a0206070807050d05060103090c0f050301060b030919030c0f06050f0f070f0f0908 78
    0x1a20501d1540134080050040c841c0c800c0044450649a2084c245005480039000f440340c0b40202041020441d400410061400c000320206901e0394150380c0f0303d5070f5540004000f40c110100751410549010b0000800c030003c0e54041d9402580c9800544012840d40c00308a00d0210018103400e0a0088040c200100740951009500c0780440105d0a000d100303090920798036248400f01c000d405588101b4050180e51b144035a00c084001011102595509076490120b0a02c15141d0041c54508044503062a500101e50003500d101641582201e406948811044401d40d405a0b94040410400c10001409500c2d41d0441c503401403060401180a0407030b55659142c0350210f41c0040000062154284440e1800380180c03c01045036025403821400c0401341c0b2500d0b592100f26510b102d0644802960825005204922025805c5814181501000d04164025102c1284e26080c507001a4000512540906030701a014a41ba40c1da20350001c41402415100700c0e090034500e9040c42000c003c00035524404224 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 379562652 1250 379561402 379561409
    0x6070515100305060708100e101701060b070f1703010e070e0d0203161a0c0304150e09010305030306090a05070c02090403050c0307110a060201020702090f070306030b07080f060108070c14120301 85
    0x86101c421301e0b0507812001d840c501c5230026404400c501c824030180c41c500880001c2511420784030300101c01031441d140c03030041c20b550b440b541300d082e00481c220003401030419111058a010f06125401054070082d0400c440c4024080c0c2109403040801240c44244941c0040030070040141040e007a032421a000a440d00c40c0440f020f40b88601005000e0111103c0c482d5006c58100301005814200703404040f10310f899005d24025120509162545450380038450000c1c0344000344003030400f00c0956100d0038801d449500c11100e841c012840d903004a012140c1501c1014410041e80d5a6050844071903400c02118540107841902001814007004042200600c000d0269600c101c03401d84121015009019840480e42d002c4401d40e40305110034030150710765950051f4407008040509040c1c1e0b4495500b50020000e6404c05840e48c8000400c1001607500494400c0c0502c407030440381c22040e40c4400c011540c10004550090015013150055400034280b036010304441c071a45403d4600c01ca1210681042e1074100740d2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 379563902 1250 379562652 379562657
    0x501150312020d0207050109180b0d0c03120810170c060d020c0c0a0608041704080102040b0903100920060903060403020105041b03030806150d050103050d0e060705151003050607 78
    0x45001c0425010082810305a4140c0050b00f5160300d0800041c01c0407109201b8042c40080070082041d40242940c080c103115130b0002c0c882e01c519109030800300398203c00c500048480410462007809503900580c212486140c132050104c42c04c034241603034124031b00c001711104441842031262581d02e1b03030307249000b400b10380201c4d0b030005844441a441881c85c041803078810038050305503130b001804101da010109507030054000c0c100c414a45202a104a050310071980040c00d076500c080303070208000b00b50b900140f540748001c8040300c5141d00700c04003c1c8215507120030f000345200341d060301c41c008904407081c22985114004001905044180340400d00b062000c40e4102d0060759624200000c01c806281c01c03c01d9280d41850750600a819503901400c81e000c0641103d10030007844e0078100d50290002c00301e4100d03c00d00102400f135960740f03161041d9180802140302000c1800c038030540308141050703400d440096410070014103803640203054004072050040c1c0b8640141d20046401710100c2c004010490250300d195 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 379565152 1250 379563902 379563923
    0x33011110090311150405123103062d0e1f0f0c020303090a0224070302010c0e370b030702030a080703052401031b0905040c030b03100905011503 63
    0x60803d0078001c10f84044d054031121350003400040b400000744102d614040b900c280f51f5030415144500402c05520a42d504107601e001d0456850100d40441d038022680310710005d010b0f00400c00b1400800081a40c2203842641800544552145580d0411200c802c801c8003982d48003a41040303a02c1c642c400c8040d0032034903141c64800150030400544201d6804d0201407001d1815404c0844c9550f4035008040c0c000f9100755140b0304e03174241c0645c0b1426654005d02159000950300d1096160103406000c0d20181c20002c00d4600882102500380642500c0c90054008150b040601902a4001800d84000d41c2c10324183c815820102c1c09420002c01140501041d40042d17449050841d0b004103802d000030108000c05d0304200a2180ca241c0041548426410403d0b00b1b0f540402c89800403002405010b103101d01c0b44d8038002c007820455030490f1442080e1802564107101141042000f5415070b82c2d0890f4054256001d2841d1604070151540000c480c103110740008035221001300784408400300e054200b5124803008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 379566402 1250 379565152 379565177
    0x5030705030102070b010b030a1103090c01020c01020d0909110d0204180f11030c183615060d0b0306070302090f0d110d03030b0a0b03330111100903 65
    0x10021040100000c500940ca401c1282d0b885a45d08541032003200040d0380c0c08404200050031580180714000a04240742d900c0340f40c42440b490341c42d0030544140d4091701a1600ca0702c20740d4070100e0344149091700d40e292028a2881d02d040d5000500c4100400294080140140b080c02182d03400100010314428001000b420a664040700031221044241c420892a18050b003581da00c0280640380d001c0b54451150340c0740c8803026460030b2200c2c1e142840c00d520410701c168422200c80030303101800d168507107903041106140e008615129125426500c2c049002d0005001501c140742140003802042064200402c0220f01c980220349401c00c25134018010a801140804050400421809105004803000b02e014401500e850942084442a15020701012014201410300a4000c3c91911101034034414180369501d07407018068000360791034a50300e408c00d2030750b4502500600c102a002015403540341c0c181c0002000548080908860418035070040c00360a801c5044075104103c1c50b00d029480d8614099203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 379567652 1250 379566402 379566409
    0x21c1208070804031b03020309092809080d09030908010c09061e0c061a09040c08060c07120e13180c05030706090e041407140108060409021c08190905 66
    0x9004210724108464501084042035201001501107003d401743c4000da001c0318101282513118200c1e415820a01c0442403010701e070314a8229941503001050b10302549102d807040c441c141c52101c40f001c2d021020501201c0c00c44205a070001c090385100f81480654141e4034200942911810b0903014040740c10140104210b94100e06510340b003400d070001100000344d4102000d084580015000352100703980390140000a6400340180c0c0440c50000e105e40020720300307403a044800012600503400a40900808602d105040d0740590744081c0c2e1094050148840e5960111811820f0303200d455401504111040e006c910240b1803201b500800c088046000c59a03428296a80321265000a000e40c2c08640e04004840d0310280c80d50039207a00300c414001a843d181404400112028001d1815014070000081c040411403c481c071110000e8981803500d55a2400700b00c1142c0c6c640300302135040700148101c1540e0b080e0030001d0785441d40c440c08145041040c00110034040022148241c0c0100b80700e814180180c0c83c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 379568902 1250 379567652 379567667
    0x4090b0f070f0c150f020c1204140609090a090302031606050709050102060c0414030703020909030a080109020301050906091801180302060907050d12050403020d03050909060f1c021c12 81
    0xb08682044800710340300d0354488070080d90b040c0348151a1030b500c07154050314003102e804513600c0d4800c00e42124003000b498039200100d94014803483c2c0400da40f003564000c943c00c201c0d00b510714070b81004260004d10707a104400381e0040c0401007811000c5000c100700c03000100b40c28132144494580120000201c0c2c0c58142c1001d80940640e1304164107540c0038030104820009103070111810b50b559081d42000c50462070001c02c1c545002900b00a40c04200f80f0100702c6494000000741c000c1843c542d031030100c203903600c00240d812880203000da21b402c41c031140300040c058144040031980250040319110300034001e00d0a002d084841c640c01c5100b1800c0c0194030817040c19030405c102d0303030065510001fa0804030b141200140c4244101e24004158505030548002011700403815500115009460741e0319421003481e0091256200950755445812800041441c1c0d0404501d58a051100901010940c8441c15054200b021000c1c80032030b80f0540c400c1550402008801c58480c100744070f021490f500c08000340300548000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 379570152 1250 379568902 379568927
    0xd0602120a0b0f011407080a0206070810080706031d07261501030f03090b0f0316030e0d080c09060f0c010612030504030308180a051b0d0201050f030604090b0f07 71
    0x141032044a02c1e142c1d40740303000c0303168080702400c00034520304180082c0e201ca4001da802c05400d0340c90101e01420402e8001c1141c41c4a003240c1c0d43e840da403aa41e2000c500d2107a0310103002c2d0000c80da1180009000040c003d5201112401c580002000e140202c0c05c1a90310300242c1c3d4111705501500c40e01e140c070001443d481483c50700f5140b0ba010341414816080c04000040051202900288031a80090b090602817507558016048907080c00303959030352502404900d640140c407082c4107040c1c4030041c1410343d8481e11401c0d8460144601500103c0d4681408a6a410014155039800101002103d40c00e0703903000c0c0103050500341d031040e03692100c81007550107007192507560003510310030600b007080030000ba801000c49056a0b0315042101c0341d600c41d2030340c45455008040b43c210592050001500c140b00d800500200ba0760440c507580b4200c9130650040c0008003201030700090103d01c040c030510903084129005103034410000b500009005015868028a00a05403204c0640840d80c4090203000340d03001240d092907 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 379571402 1250 379570152 379570171
    0x4020a020d080a27140a06050402011e052a01020a090306050108070315020f04091d06010618090f02070218190506010e01081b0a0f080906010b040b16020d060212 71
    0x6008804104030f00c0703c0c52101c804000100d954a130410000d00e00307000110ba078103200c1260799003a030b541740c0040104816107050740490081c0030f00403181010710341c050075202055170391203003011032519070101510107840012041e5100707081055040300d0244080c00e240110384d035516401c2844d5041407811104182c10000a6030010442440032a0450061861aa402020060350baa584811011040c0102d401c580329581c00e0a0300707234040e0700e070710382401e907140d0345d94402c0d030310181d0343c8200c182c6150a500c584181c00e103020a0040200030b585501c0346100000c40030015160200644c0001d180c0003183c480010403007007440c14032290720780b0342d00800d1420b20510801c01640c104030001805000903002e20a040001080000b004c650010007080101ca415255058982c9020b51010380300c0950490028000740e9445c000403810304000403860304a07111444210b1419007800c805c2252030380302400501d04101c0f55010100140c03a00b03900c0100140c024030005071101420003802d60040d50140428070f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 379572652 1250 379571402 379571411
    0xd0c09050a120b040c050406060e010f11060115022b1202040501051c020721111204120804351b04051003170403050106050105030903030c0f0904020a020d080a 70
    0x2401211400b20310400b504440c05080954641c50182d402e003903150003c070380041c00d00000056158020b00302c0c800102d801d80b201c020340c1200c180125200d030886014115140d10a0004002e0b004071039006400c071411600c180c0b14a90100c910310a40d0340a4031444040401c04508800401580100c40d8450101c0c440b0041d13107414076040000b080c6008046540e00c04588001d41550192240d07811a40115400b110080100c0401c00511903241c001d50591008221044044c469140d004114202d408030405c2030f66042c00e0900003004c0c2c6610f0140d80440f005d04d0704100200c0d000032404191040c02c0c1a00306008203521120601401c41d0440d4102c0581503881000f405220004000d01801e8544090710300040c41d5031800030f618081c10b11a4409000103542c2d8007201c2c00f5604510090003564082d000901c03500741d0300d100444161008880300700854006101107168541160010800a03081d0348000703080c052007000103008c0341d11560211015030700800e842040300c0e400c5803000740d000c86041c50401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 379573902 1250 379572652 379572659
    0x518041214072904080a0302180306090a020f060418022a030706060f080a02040e1002130e090f030a0c02040b120f0607050901050d0f0f05101d07171005060d0c09050a 73
    0x60507806074820f14407e050f00800d000c18080c02d0b08100400c800d038001c044030308c2030515884041e11847d00c4101030380070701d07000d41e1a043c16040000c01c4508444070400a140400c03006031221009421101c0584542c0e035a1002c5c00610366601440c600e010114a03014541e80c81851501504503000e96000080701c0c001110100240ea4001c900f00b10700139011b5501141004015000504042c0d030841100a040d201061030440401500016000d40390300c280000120f46035030180b00c3c0d640d000045100525803042011041161081000d0342c5610700c0034002082c040701420003c1c07910403142c046840154005620038940032020400280c11820b00e040c240d140c0250300e80000d02d0b91040340d00130300c0055200c1041c8ca00c0c40c411940f01c1078001200d200c0c200002d0815140420444180b03100700d01d1310244146409900c03211380c07810345c0c1c0296003586a03117140758416040c0400c00e19004210403800340c9010800980c41e00c8480041010030407000c80042c06802d94070f4054142c10403a01f1442c0a68159042030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 379575152 1250 379573902 379573913
    0xf13090507080f0601050904090510020d06080c060a050c0c180402010807031401052806050c0f0601240314040506070207060206010e0a0e120712090518041214072904 73
    0x100c0d04030078203203441b075600c014400c00705002d010801001000c911680742c24201c49010342e806401041d0031501c040c08800c0d990712445030740342c0c51400c45035481102001000d402c0d0340654010545503031075900b41c030400343c0e8440c0050f407003618540ba05101140c01c0f5040008545e406614603901100d40d007410402104000306101c0090014050705001c0e1212440c442e288403403454145111a02c0344012480103034603603800500940084080071a0761082809640c040807001c9900382c1038038840014100344a000c09046110880442e4000044c90344da20354000441e05e0300c03403101c0c5c4650301030001000e250074040d07002480e110300d6502031811500488010b0000000c0345403100d810600b016000328180203010030704ca0400780c0d01040d8481d082e038001408010040400700d054010807080d00c400a07250b42c0d45090021210301c0ca000009040d144500007000100190742011400040b440c0400318040011800302c4664090346080c0d414010311a060301584c002582240d00d01403403490305481c5800c1c01d640c0d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 379576402 1250 379575152 379575181
    0x110d080105130e19021f02060c070c0e041407080c0f0d06060b0c0f07050402250c050a12060e0d081302010215010605030712020412020d06020f1309050708 68
    0x40341c0c4141c11201001155820701c2c0c1011041c0300341c00d8103490b44007016901e030b804c18252a480403402154120702c0d01c1a245420b180c0b803003001c4204d4014041d60ba5903840c42d01a41c1d8000441152059107080f00458028002010325120ba8403400d0350300e502c2c0602506451501d500c0d0350015410382e1080e840c0580700d40380d4070800e031000f11054840001d07540382031030000080c010b15001303280f20000120f55441080700c002591440e00406000340e400154450080c402a8410844081d80d030700e5602104144845c070f0301d010009078500900802200c0c50301c460005041003066486041240e07201c018110070f000302e034801c000040300c4e500010300005d400341001810009000305080d556052541d40704065900a01c140d0000310703035015819140e5a101c24000e002a0402d03201c450010707049844c0004001107074403ca90a490710820300c3c4050903c40e50070440d0701054480c0483d88039800388107503444030807018080c11000307130404c1c280390107541080d40701070445900810400c03c2010710340501600e2003070200e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 379577652 1250 379576402 379576409
    0x31303050906071a1006031a101707020a060e07030f02061e0d0f05100302130b030102040b0c0106180b0609010c020105090307061d06030103170a0c06020301060906110d0801 76
    0x6106840384040c50000d00c1038014401c004d0000c1d0340c003801c10740c401c2680c643d01600c10044d8009540342c0d00d84030308045080307610200c800046140c4015000c01e45160680c8040d0b40c0f06118905010075003040004901001030681b601340c0940e00c60408c000c01c00119000301c01a50140200505500e441c40d184c2d480c0c0c0451614000e405903000141d0000c1d001103034401b01103100c0d0f007124001d50710b09914205000602144550090440c945008035400f003d43d80115022a40c004200c0c85d50b158504450304000d00d01110350700c1c0d0641d82040006501040c4401422995540d9000021a45c0c58003d16100c2c00487c0010030380348624008801881d0350700c05080e00c5400000b07181078590f8421920050780d4610860020303e5051044500003e03096030f01c16500010b10030343c2621707207090b00d60503028868140002c3c040144050f0b02410207802201104016080c40c1304036107407030240111207031a40b1049a1082e001140007078100c15090100b40d400801200d88a6008401000607040214004042007018003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 379578902 1250 379577652 379577657
    0x12050c07110604120b04151e05060a0e090f1213060c02010309081306090501030905030702241c06150c0f21120c0207080a0308070201110409050402010311031303 71
    0xc240c15003640300c2c1000d450190507074000c44080c8510908107401d504c030b021942298004024030784c400b150340c281c3c0a811049400d4040c0900010084103030314018104c014000c503000804142c00142c3c401e40d484005000e07014034000750030b001140d10300e400d0806401348a0404014810071400c4640c00340c012184041307410500e04070361900f40c5071004901400c407448028083c4400400d03e154400c00304488281110016110416220b60303650040d0240c030705002d000760482c0c1081c8041809801d00d4070035060050500048200900c086008082650308003003529800f82540c5000c1040e10a07007803042c41c02a0050b49803401c10820141c41c01802c041030068000e00241c031071181082000001040c58903014902c0400e08642500c1e50030040c408c4c4502d90441d08041c2c103040301c4001c0c207400881c01c03500340c40a0034060b000e055140e48058511001c00380c184001c5660752103007600710042ca2006013000d41094200401c81d414580001400c1c5c0302d24404400e420b0300c081090180b0380d4815100c0c03411065050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 379580152 1250 379578902 379578923
    0xb03070905040501110c1005090d09030206090301090807080a080705030f16090504110d0b060c0d0c08071e051c0203031503010212041101141602150c0f06010612050c07 74
    0x500d081400740518000402e071601c0301082c50031ba8044082042991110000c8041007a591071190084d910241d2400400108a1100040c0b000d0b042020042004201c0035001090f4101c032961444203982c080304003645d200d000445c0800b034141d4803002c0c080d08407002e454403500350300f400e80d002140001c019159244840c8030000840100b03015860f500f00510004004220711001d03000d81c0f4980354055298600700702d24110380c103c014548201900c01d1080315000400107158180410f440c10403901c00140e4100c441404201c00180a4413050303100c550b04051204c28a421910380359240040c0c071141c801190b131201d10705404480e80001907030351011446013030004103003951001c640282310f10240440c0c0d08016804010900c183c0160810b40c158080c0e94109031032660000c0c05025003c2c5c5902e0050320654240990054070f08100c4803031b00c0c920418601071601e0204001286002d06070032404246401c000c0c010040250084610314280c103907100c0900462034603e2015036640316686c0c0040011030300c0d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 379581402 1250 379580152 379580161
    0x61707081e07030f0f051605031f09060e0705070f1b0f080d02060709030c0e061f0c0b060102150610092616061205090f030a030b10030b03070905 64
    0x18580c110442280160100309040140d0000c0250850502c1c8107113076420802d9040ca960624819984200100700500281c105200c20880311540b005d006c00000352851040401076544041000c0010101700c040005e00700c2c074200c4240c15584000304a4000d014041c81013401188083d0001d0221a0740b110110702d07c1100341c01021f41c0c1d418503030030007030300628031520100e1a9180014002c0880032903408030b400542d01c0b00811199510b040c08020042c2c50805000c0004051204c0402d410100040180d001614400c549a84202d5807030101c1d000590001d01381c10030700006007a159040030084c40917009504007500c4445402d140501071900616502101e090014802e07004240070f84101001c00314015805002c0c24194210003614000324004c01c541c1800700720040d0f1610048413120784030301c02942c1341d0141c5400207000c003d003a8620b0317000300d4881d5248001c00388000d040601c116100002d48071000414401c0f000000124441418680f030072600a0340c2e8001000022034400e81400702e440c0c4d58 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 379582652 1250 379581402 379581421
    0x403081624050907050a0609061b1a0402010f0504080706051c0c020a050c09100608090c03030c010c1101050c031605090d08070b0907051c02033406170708 68
    0x100c4260000100c808914020760107101e50045070150601c4011a41c805480c1c404110044c00c02c0d00c07039203020540c03075a400c101e028060300c0d007104550120540000d05c10301c40c3e250074003c550038440045003ca85202004110f6800c40b82410b40038042d4540305040605041d803031680e0740c00360f00401c2d06201c0e010400000d4100354105040203411160003d02040c114554080c0d521802920212071038040c2444e910f156003001c14a551051461111144061740341c88001d0358502000380c681c00090040e02000d00558030304100078604100715000001e410002c0980080c003289d4808410a0180d04200c280a1540c1a010680c1d0700702051601100c0400007071007081c1c40d98800c401509400c210a80d01503428048084050605140111514840c6944903120640c480c00e0030b00450364080c201000c20f0701e03034070381c2007500400051001e022140364405105802201000030b4503d001c1c1030f0350006107000100c00c082000780003410b103810200c448420030000c2001001008203c1b00c2000100b9000031034210 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 379583902 1250 379582652 379582673
    0x408060f1b0d06051519030506030c0405040201020313150f02010603080403080a1101050106020a060b03010905071a0d1109030c0111070e040c0b0a0e091605030604050a0621061104030816 82
    0x1c000305504080704e41c0c5c80c240381c400c4c0c00080100c001c204018004404c0d45009005683c894940280548010010901000018007002d4001d90451006001c0340c651880c1c003900000c00381c040310001c501c1c0401c4103c0c0041001036064040c00459050200c1040028162001d075001da90b0f201205944850349038808880604002034110080d43c2044000205d02d0b8001c140c005550b4050901031201803504c47c18542640c3c20180300401c0303a80440c3c000c10009400d1b516084080000b6443c20740341035966440401520140c0e04003484000c000190800c462408024082c1840400c2c01c0c507113903100b12841102c0d03d0301440e114107044022028002000c2240c1700d0b054102070014002c072203444114503600100507900c20082c03240105d01c1070011800c60100c8181c1100340b04080d90b200307840c6070b880500340b0002d400c0281c040d0b80003e40300c22021403941e9944190000300c0c91040d50040c40340c4418280744c0203507046070380d8840408400300001c1c0040b81601e0300300e9841c80300c011920035141a6510380704134a00d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 379585152 1250 379583902 379583909
    0x5030d05040e0c130b070c060c0f060f0e0f06010e09010903050313020a090e030d1d070501031a030d120f0209010e040e0a080a0e210c2407080408060f1b0d06 69
    0x10300c0c0808040351710300c020701c06411428000c100013032425442d410180d440006144014140e0340c0040d14400024650350407249511703c20000110304002c0128446240c803100c0c10f102c05660300094014810b140c2d15004080e4040501c02c02030100140585020b0b042d4480603203125101d20700300340c24005544500010704024190150100015500807201b1612170b0050612001443d04010000a805050b01c031604141e40362280907198551038880150000c0c070030445682028010034101a000d50341c1403001d8840313000d00e920f50960346c03500d1b05802812685118910340c0a20b1043c410403ca50b648a25075a2507172030240d400140d20400c0a03003403860007284401c0242a2030300043c07400050740c2d0020007141d00c1e280903250300c00c20b84440540f8444c460264440e1441d00d40c0001e41802c2c540c5094090091480c000702c0019600805084090040d03a0280e2416959081c0010341000030607001c1260030b6201c0c400b589042c842c0e0510103e40340d404245405c90345149000031461120600c120390049004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 379586402 1250 379585152 379585177
    0xa0b0d022403010f230f0d0f0c09020715020c0a0f0203100e010b0f0102060f071808070902070b01050103051006080c040b03010f060305070c08070b0406090f0c0f05030d05040e0c 78
    0x32507940380545824540705001745110581c0707030035241d0584083d1034100c0c518a2401040001c0c007503912014017568014003002903445c02140c0035090082348a003042030313000d02100c13480540d81d4500c500f000107510404c0490512110f204011b03104048801003040e2001c07942c0800d002c83c080e03c150002900e409208220040c0c240c1c0f0b01486003802070015403200b02c082800b940d0568501d030750480160f8490030211b034802440092200050840f92007030f010740110760b41d8100c0c1c01400d6620790400e24640b4dc02074120359840303a4005901001d02480c4102c00740180001d18043c80145070601010301804c210344511000d000d00840400c8070011071106840150011080c080d0301da682d00c9102e49400c50711031060754042490b00d4049002503114420404170300750040c0c54035161000d156110b1055450061040e114190b4621303d90b40010000d0a05000c100c0c06042e404c125181000034001c40c40d100360348294400d50104c00c0c6614401c3c0c000c0b05907401c44240c11401001952030b01c406031140d01c1009419401c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 379587652 1250 379586402 379586407
    0x50706140405061e01090504020d080a08010918030e04110423040f05220309030803070e040608030a171503120304030e10200a022101050a0b0d0224 65
    0x149050a0641940709500600c11181d90342c49509099030350303074003220100d580010362900501440745180c0007140c12510291070f00100b5802900e810308540c00184800c030005450f076004102500d040d004024075044580c4c441400c0301b00301e0b03401400681441d24012301590f19186a600200761400581e0018035845220f030702e021002030444943c074614120307110f01c207500c2c1035480600002284106071040f200301d501c005240401e01c032060f00c203854801c021000c010b0301040c04030000b40f8400146025103425145c81d4101444101000140c4515400150342607000384410405680e01ca04081108007031605004e4a54403286100b104400194203000d0b05441281c5400c24400c003140029403140c0c2c06581c400707103094841000c0110459400564000040c843d040b8544151083c0d107042403e160041d00f245c4e1002d000d640070825507980814014152285d41060104030202030180b1540421864801c0282c002d0400001e0969207000c0b1b070180c003466801e0081c80b503807410880c2000e000005421901e8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 379588902 1250 379587652 379587671
    0x51302040218040e01090309120c0801020a05040314061005010309020d0c15110601180e10090602250c140a03050a0b0105180405070311040204030213052d0a020901050706 75
    0x5062111120505003d1807611401e50081c2034188500f849181e03040c1c0c1c81a2502e450f1a0720b010010710181400c5daa45a107803500041d4516091004241c2028a80c0703505842c0c40c030350b00349624102c29000d42c000310707504410100b01c0a51041482801542c0007400d00180302c800350300104184000381900181240400e10780032a245d0608e00d918005000141d5030f02016180c4000116201d203020310940740d0241c82c81521030381c0b000303031500540d100001d00412104410b0380043c2542c1941d008410a4541c61b90000d12400c0c201204440380602c0007002d00d0301640b0250f6035442510050161140312131815071074400c00f510703a07200500d070801180c00c20119100e284185c100250000030078840ca41c801c034003454000c04040d000038480391240d07820001610117103103982c80307001910300202c1a03503610507801c0002100607520034035003100621200c03070006002d00c0c10500701c61018070000030070050b149829910304110000a480c4540c030001402c0c1c0941c94204000050300d1034040d4a0000703217240c2c1001c900a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 379590152 1250 379588902 379588927
    0xa090e090a06060b07020405010f0311210a1505010614031f031208370c110f1b03010b2b06050a0c030c3204080f060f012103030513020402 61
    0x2005664000c1f2000c1103640d036100b1001101195a20000380b070089090310100c024606002e940c19643c41765002d40810203031071000d2904242c2141e1046810406003c00f140a420712841001d01426041c01d1050b4a000d9012000d030040c013006200003240d51140204206c4480d0300e0b11450000d5900200c80c88441200180140c10388004030340e502c20340f40d60b43c1641e00541d000315500f1021041c007142c1c1242c4072200c04480c5000351201c00040b400340004405440b42c082c004000000b1700c01d8021024144001d0300710704510761141076401080c440e030b060001040181d034035625103610400c44c04944a020100b0103d00128888400c8000f402903480c1004201540f03280340c00c030903102c0c03c1a80c2c08100d4280d040c0001d458030300c961030302d50107a1041d146028810100d0b1380310400040000700142401c00d0f42d940381251500d20741081514440c2c00800602c0003805000000c00d0140c03940d20003010f01c0c0d00c165000c020785d00c007203200050101601e850224146802d070010603014650082d2003036544510340c0742c1e070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 379591402 1250 379590152 379590157
    0x50c04080f0d0f050903071701020705100905060105090a0b04060617130b1609090921050a0f08060418060b0102100204030b0f061201061410050a090e090a06060b 71
    0x210340c40340c0036401c0d540410305000b0070000c031084015200c603400c00c0c4054400316010707000300329841d8261040d0304010400341410110602c0e802e9642c4005030b5198101e01e4200c0c1031100612101c040d01c1c0c18100705000041e40820603506499055656003c259a820411000f414200400e540c10034901034020401c6640004212281c2d1150b9050848540f101c1e45a9100c01c082c41001609017060103003c00e00403461074444e185524020b02d841090359484450813030840300c0c400800c8900c0340c90400b8a004404070101e500044008500b8410f041402160000d054106001d0507030f03040100034000503003190703070383e91008217001700710455004030300880d2800078014920344120364054458101c1d1100c01e560075001b02d0b000c1d6a17003d9020203075520b03014050a11104054221079100d841804003280b405004d01c0b8030001809031518901d40d910b440d100b03010030800003201041c10030208224401c0c949412180c140121040305200e50600d643d080d00c654100148050002e0070641800710000703485600078003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 379592652 1250 379591402 379591409
    0x6030103060510030b040b040b09030307120e2d070e090a2d0c030611180904020d0b0c0403060b27040309080106090f050105180106031104090507050a0f110703080705030706050c04 79
    0x107000c00c0b6899075440140cbe82d000403280980060200ba00d030351140041500100d66000441d01124800286658000d00c450110081c0b10820b201e0a04a140c602000300256070080140502e58101c0d405c003100940d817242d81e040070141c8098440f00304001d11003480e40c856940031030b8081112401045a00c5d04c60056a00c510007036868509200d014104100502e0440710201d10090503200038894060909c1041c2c0360041c416640703c9085640d150201c0d010700b240a114040090720550b40c0d500303500e416001c8500e000074580c0241e050b003961080000415504000680d10340090088503070391850212443c4006400dd1113841d42060000031303041415420011001d6a0008240040d030f80700d00c280005121b0071b550100b4001502c1d8010003580b402a1301079030b600f02c0118009460a42c4864039401134980988202c40002c80000d410380c1d4136079100408400c920024600b240840301c2600109039566000d020107450100c00188080821008000300d448165001e44140400d1402a1750080250040d12 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 379593902 1250 379592652 379592663
    0xd0305090a05010305061309140d0203041d1b0c0a0503191119031107240210050c090f0105071b0f08070810050a0b0904111e06030103060510030b040b04 67
    0x201d020030650300078029544180e00c041c0070055040340900c00500504042c50054030600d5055141a80c0e1480c107001a1502e410680c0080d41c4e04c5150080601081003104001c0400768484c0b01404002c0d18030070104031100840d40e00c482c0e00d0f6890000e09508018000c40000d1482c4000600500b4074000351050411903000c40e1140060701c1e61b0030780003980364104910502421580c04540b0f800181c0250fa81c2040303903d290007140e402d1501c803000010310307044528001c28041c2c2d500801d4040240d0401a00c00350b003280c040103108500b00380707820100c2d5000d5140c00318030414601c1102d8980b80d1043c002d440300355400078040301a040360812083c81c03004c3c4a0244000115600c2d001060711440051703060f01300c42d9008000c1035000001845c10005001c0640071903101c540702c0c082001c007070b40c400c1407150165001d0841e100c0700c01d600604010000348000c01d0158035151049039404a40c0c1c5d03480c2aa070440c0d030002808592561880c502c0c2170654050307040204114502c078140004d2100012085204600c0398 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 379595152 1250 379593902 379593919
    0x403030617010e0303061c08030702011b0c152003010e0f07020f07090c050c0f0610090606051c0912030e1009110d140102040603020705010c0309021c08090d030509 72
    0x105641c01e0342c0d84002400701d0f5030700800210b402d500f08010781d1140822284511241a405170707a0300c101ca46e00540c0d1060060b9116841503520000b5401c681217040c20a04056000c910507a59085004140d91807030040c01d5500c40840d03030020020b20700c94551a08030b244160356583c4421080e86154425a070f02207401215000041006000203843d801001000d4000c20700c0c90710344001a0081c3c480c03001964200141440011401d031801c008003089545400040c1c1080d1038a41d2541514140560181145504140c820031205030004101c3c5d0803c084038840181c551400d9049901401d2080700003040089105001c0203030541c180c0c45065003002c080155041300c1007441c02a41511182c004c082c0c50001808541c4250703203003540c07008100c20310848901d00f00700090300000f400c80c1c12950286011940004070041001005e1007001128001414100301c900441d4010600311001c044100c440f8003098030700708003400f061100342c5400400092596010000354900242142c100040711030080300403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 379596402 1250 379595152 379595189
    0xc0f061a0a1e08120301030b0402031c02060702010b060f04030b09210d0506040203151002100e010b09090d080601110a020303040f180501050913080904090c0305060c0f040302060f1204030306 84
    0x41940d104e0101a5400340303007075034216240c00c0c0c41c03000040c00072a450710400105641d044e85800c04907004d0030391a0007130a028580900080c1c04d40700c01c0481d95200b04420440008107000c0e10054034152900301d6413403c12640c405074110318000c0310320240d41070349142d1130b0b6004503100b0039002400d042007010320038072881e2140402c2c001a800281c03070081041d84102800c104908012140016811a51040315003032841c0021322802c46414601110040e512855000743c20700b0a01402c0b500320703032a0001840e040b1188000140001c41c050442410420011b039001c640190800000800e9034005090765511980e8a2000e4006a864070861b0b204400c1e420350105080301c21b01c02d040c100c64020b01020400d5892480ca488408207001c0c4c21100080103000002c2e00e5241d901c140c000603807007400306918075400c2d81051468144010410040700400f040851104017104080e90f0460350b040c0e421a450b14181480041c0c10301604100b01c940074220810031061580c140c001c101281c0300300300a036490b1202d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 379597652 1250 379596402 379596419
    0x61801020403050309040c05070b0115021e100c0c0605070e090a0921030e010203040507051206040c15030f0e2a0105030121021305160c0f061a0a1e 65
    0x1c6200250030703600203011218060515802c400102107044c54428a04407aa580f004061342007a0000752695082c4d0480c1c1a01c0c58040082c1180e00d8204031318500c60910800c0c030159240c9201203462401d544034050401104d000782e25101b080f85e40010207010700c1c81c10326001040a240e90740c0c680c1c03160303000002040242a55100d000c211a8102c10045906403a100c215030440803200320100400d6511004c16a82e84000c0c806103020354490006080464608400c2102c0da0504541d00c4042d9003044c014170000031407c1d031802c0c0c02c4811902c6a605280461503098004040b80c040c0d2450a60034200c801058440206003009181001e1003000002001d00c034420591040c0b81c50304601040003003006001c0d440c41c40e0702d01c0440c250040d140c151106060307400b08401000711b18400301da260300c1d1400d0018450f00c42900488545947c900301258403240d84410410032611400608002d544035815000c40ba41c8401c660310032507000e410801c0b402d5940c40000c140c0d02c4401c07040d4400222040002c41c0205 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 379598902 1250 379597652 379597657
    0x3080403180605030711030c0a061b090e15040b0a06020d0206100614031f060c030801140603010b090d05061911120103140a020310061d0f070f03110c06180102 70
    0x1182d0f60b036040d0460b5103140090305c200524048000440c4800d100f0008028010071851401d1407181e80080340e46400030704018008001c110a123020300c00041010b00c00c14a0324000c8550017596030700d0100300e0012060200d0700403c1100704868028424190108441d0340004814060740c40c0e6038200c500a6441da1801010010b0070b005100c0002c019020460041384041c010b076402030300380c40078203002d840e003000345804c0d000701342d44803401003401e408016080c1504240c1d40e5004000010002ca42003824100240d078a200502681d52000c0380481c0120203038135200b0498a460b5400011220799003031203030b0018420780003c1d5041c2c1a036414000d20001c0d12038100282c2e541c0000140607003865900390b9035031000e0003400d840045494803071000700c203001d030f6400c001c10030300074500f10340008150741414245010011800804203100f8806014440c0b8884942e400d42d6010a5900e4410062001488110068400d4a0500401c031401140c4d24561901c08204c8601841044510004615103900c156080c0d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 379600152 1250 379598902 379598909
    0x3040b0718050103091407080d090b0a02060a020d02130e09011a09010e090a0501050a050a1107021503060604050a0b090109120b04020d03030e010207050106060e0319060b01030e03070308040318 85
    0x16545140c00704490350180d000a002e00b4400c80034444040000903540340b50141d1071703000100591101d54002c1c2000e421111180140191010a33407414641c51030180d584c9201071b0114030f00907800201d24036151620340c107032413075001c000f900300f80032903a522904005070b10151019440303546800c6880c201c3c00300700c1100218226026103207a0641c0c0c605a0701900d0005c0017402c26829008000514000030028424540b15810012000a09003070a6051400311900a14144c48004007000610013690700c91045066a0f5500d038209541e90b69904049040350049501007078104c0c2105801107400801d060152004030300030303619440415924840c94a00302c060b840042d2550a8110210f80035052064400320f8860082c200410400d0b00c05030a2800c80c0d210f24820340c2d650750b5030030f014088140e01c0312000c07011050450061941050440c0020340d01010440c004101d10307501c0d184074105074081c0c3c0114003850510b1043e00d8507441c4c1c909029103c2581101c0850000740310700201500600c030a6120705c284d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 379601402 1250 379600152 379600187
    0x70e070c0210031401140d0f02010c0b041202060709080c0f010504080d09051203040f0b160b01080d11060603100209120312040c0f0b070305211003140105010b0a081012060203040b07 80
    0x41c7da109880388001c4052100c41603040020f0104074030041000a0211805a4402c00004d483c0310808900241400c9003e0150f9007040500201080b00307079400038404951002c211003d2500903407450059600d4421940507031164000c50b02200300e0301d0741029841c0101c51040e0349214551035980b0490780c81b4411030041e18011a0002d2051050400c00c0d0064101a04461841c105054894445e42c3c5c0e410002d80c42001194852310244640c6a40101140340c3c1620b4080140f0b11410b144000a40310201c1c500c41c2d20b075459002c2080c0926549088092403480104400d0740d981d012644881100c0500c115810b07603a207501080c0004d00c4400b007400b0304c0205d80328220440e0600c82c2c1035030103d40c00c0d44a20302c00320007540452840c044640300d42140c1d41c01040380503501c036026461440e00d200741c0e042c07810b14400c0a914010040080c00f01e950700302e4285401031700c1d00034180c0d80d4201801c0007180d22500071841c40c000c955015010410036600440c0141d000d4000300390155140312003100e1414249600408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 379602652 1250 379601402 379601419
    0xb030307031704030c0c2403050114121614010f0e030607050309011d2805100507120203070f09050d15020a0e0303030a05100b0c070e070c021003140114 67
    0x1c40c0100920b0a504a8404d103083c004403d082e032180d100c11a2580c1010740c90444100300102003040c0e500780c1c03002c46800307800e0a01c000e616107222113114010702910b00d4001c40081d66102a1003038203015180c003030b0f00882c50311b030300c080d0300e030072646600100440c51280402e540b44002074690740200d1101d13034107000007001005561784807002102c003900054a43c5140303640f00c4044d0450030001c582c6600340c1ca500500201401060b0946140c190101d010f90100c0180c8240300003400b02c1e001103010441481604000b003000d807100c000403580008a00c0c00045110300c04401e0014a9500c004400003103045a643c1c08105c40d1503000700043c03041e0318040205a0388120540d03c250025540141c07242030307200d041c03000101c001c1c0ca011904641c4202c03640b010103580e40041000700d8000c0c0c0403540240c0080f614850400d0404038500e50351320072034090040c00701c0c1004000341019100d8242d4081d5640c0c0980020000c050380c0d0000703009800d09204030400c40b881c0ca000031650013001810401c01d114000c08041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 379603902 1250 379602652 379602677
    0x1b0f0c03370212010f0b0d1709010507020306010f1d0c0304060b010504150309061406030a060b1906050304030e03030c1f11120a05130b0a0c12110c010b03030703 71
    0x1100c00c4941c44280314440d002007501580c2d40c0c0088040b01d034003e00c0046030f1018070300030703010441d8404c9032281c3c852000301e802c0c0303008502080400c8102c8510868404e550340c5000b07005960502070024002c3d403501c03480340041104907181c80240c01f00c1344507001c1007000d1618103001041080717003203590f41c1c14101c0600018000c00c80b55040000c211006040880c030f02910703006c10700b019600b126901d4002c6604c0322801020400644520140031202000b150624144080026296044041c0140a082d02c41000380304640d0b80d0700e00c40c0848880c4001e03003c00140e440802508642084a00b58046109000c002000782004003c40b401d080c07850004d410520b0032082d80c0d02c3c14100b0009400303840350740d414510500100303100040c004040760225812140c500441408181c2e9001071410b88814822441030740003c0d4541078154005008850114405c0040d0800301c41e07003803c3c100801c603194205000484e000c0046001008441c0000c0028022075444500b815075a224014005000442c00e80052 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 379605152 1250 379603902 379603963
    0x507090e06090402040e0f01020c120313020118081902030105090105062805030d022a13050702011b05090f12060705030709031415130f0809061b0f0c03 67
    0x25034010310040000a0100500580c81c3c1f4152040108003480d070b600282c491004101000324082c0e1002c084012461417600040c802442591101d009050000001d80b60001145032203102c009010208119804c984488801d8440d003218004264060751170f14020a03100385060003143e200340000740c441c0040310030340080c018010006a43d92890442000c81c0401c2c0366800341301400c018851a80144400d01c560307039001c01e0390642c0c000040408000700ac0c07c8801a2640302098000d00f0181400103001e541c0c0d201c050380500240b042c510003071042b44e002c0c0400741b80c10030041d1103035110036030300102426551028040b21101982d40b42005910050010302040d00c11001940e203d9460b1402c054496620303030340c0d0500441c81c60428920754021211024480d80d404441c10341c040c1c0c600c220740d400b0b19229160300c42460310408002d01000000595450700c1d464003001c4801c4018040b5201a4000044541c1c646a0411422080c098003401002100601d0700184c01d94003192840d1280303c861100b40c048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 379606402 1250 379605152 379605169
    0x402010f050d0e070b030105010228030e040b04150f051c020409020d0b07080412050a050901080a060506070b040606140a171c0809070501030e0a0b041a0405030d0507090e06 76
    0x41242d00754641e608100c070080c041c05903400425182a10383e440c0e50400001a0a00200d03d0030801c001c8507840400386034007581c00c0481140d07909414642d442032083d50104010380045600540c1050401c001101900740110740d070001c403240002c520a5003510303442048030a49071040c1000d0311000000644016140035884211064802411400341120310b50b81c0440c08038040f51082d01082018027040180075840005500c010b800d0702d4464640f85042c600070f04a03008101c0082d040142000010300b00ba0025403200010b000018041e07511081103180c080e41b501000c850880340309040187c006401c50b075458004140003001020150181d0514110310b0000c8540480e1011034402c01140c01c60301d0070380000b2502c82071015034800d5503501d403019a2030714040c2d0652065040502c0d01c12034081300c110100d60720b0000c9501800e440781c1900c0390b080042c0c1c216182c40b000c42420041405002c2040000401410903081110f01804141c0c2c0780b010a07a10750007541314000280b80c84034002030007131a00d42213 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 379607652 1250 379606402 379606417
    0x20a030e030c040c18120c15020708030d09050c0f0901151e050d0506030f030f0f0405120a0507091b051615060618031a2520060402010f05 61
    0x1254501802c00300003409807a82141810007113503941300800c041403414042070b0043c0010040c4000000010740c0c40c031100b440c1d58811103020024400180604134800d00003d00105244411251100902205500149040c5004441d01c1c410060b4010b40350414451504c14500010040c4c030041e031805c2942d103112054524540d0800c000c0038035000d5910f074220107950322041c4c1655459151a03005803400212100502580d2103580b181d080201081b200104450031482c28581c03840d00c0b000900841c00d1680180d401c9198071651264840c1c8910070000350b500b4203103020354212820300795210310315021210020404020010407505070495280900010030364250311000520f142e0000741c42d44078000954019901da01c9454550811005e5402680245540b001e150540e2410346940d03600d10901d10b00921901c40d80d64031400041d0b03509020402c034688080100200d0241d036109000040084079078083d0b18541c050804070012022000143c414481c5a06031039001070080c9401050340d03660400e08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 379608902 1250 379607652 379607659
    0x904090c030803090f06270a0615050f011706040213030b0103050d030c0801030c0605031302130b030106060509060403020d0c081501050a0603020a051204141e10090f35130b0a020a030e 81
    0x224000600301d100707040004940041e5a0032b036504202c100541100980045410400c1016a04045020b6015000c1e00f0541c12900107035601c98101c0048410a0f40350720241045503084000800d00c0310200d02c01d080c140040c0e904021064078030009803a110704c28040640039080a48040c400103005000458102c01da00340000c544040c680c3c009900b9103c400c2c2c0315070f69070b5144c4000d40e00d28102409480301501881c00c00c2c608080d02c88000c1640360041d480b0181c4030380c200f250704030107008030203891030050045a000e81d0100d2210b070b01243c054150070700c00c0c1400b40c010705000040340c0d440b03071003603541501090f500c291a05d140a02502c00c0d48401600c00c0d907090483c4410501c4103207041014060001501011b043e43e400500d0313a044c100001e100c818040b080c100880800010050481c290190703601440302c0070101e142160003a00d201d011040c55060b00031164110309443c0382500505000882d4040380d400b1039898550540703990040150032005640b004281c600042c0c02201101e8007e140038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 379610152 1250 379608902 379608913
    0x2070501150b0705010b0a060c060f020f0a05070b010b13260d231305060319060f171c0309020424060813050a03050904090c030803090f0627 62
    0x641c00034055503070310800c241d40e400110071007000020b018148049804407447c4d00400e140c001c014000844091008000582c1c820b6984003030065581a0381400400d1146261500090b0310003520075408600c2c25140202400b0000500c3c080712822101c481e4400d0ba648c8071281d01d400c130b42d22540c2c80340000c6140104003040510030304200401c0300300c40c1003000c0d59905c0c2c8190014091200328400300181c02080031800c0000e150031420400d810b008031402500c0e09640c80d604d48403580ca003510200d51f819243e5052110006499500ca0a00c4003070302c001001d9010345160403211660b4812011034100c4550900c4184941454041c2e801761039618009880401c041012014222003204440221241803120b04005c0c884039501103007051b88448024032000d00c0108940780d0a030364155054004042000029085000b03480c0c60b0011a84035030f01c1503400191544a18004100d90000c0f00c1210a5101e00d64030380d000c41e500010303035502031101091b075000c12485980c09118070b0b400000301c074070a80c400c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 379611402 1250 379610152 379610171
    0x1c020d0b07110a080310080604080403020d051006090c4a0301020d02042c040204020714240603071d040204091a0610030203041a100b04031a090a0c060302070501 71
    0xd01911480c0c6110340e141301d0352460400b0300c0390f14990703440d0440b078105d6210764100000210540111402e99404540e40314030b04a180c40c125103441d00d2000400c2c901ca0030120002a04071440d041841228120b0f02c0ea41142c908815041081120407140c06403030203e8400c44801c00c8110041d02c0d0b881e010401c800102c01c656080c0400d003640d0264024454040d130025081001c000880b01403291001d41d00e1380710705401d0180c2c18829100300080e002030321a030740c00a40142007110340c2c010140451180416107010b03110b044108680b10441c2070b8401e035070380e4049000072034515002c64000300352016102c174003d880c480d400c1031403e01782c4000c0040740c0003640d804d0050046041818140030080369502076201d40c0c5861402d014604070700c2450502031500510900c00081c490805072032088258402001c0c3d07507628044a100f0304c00a40d4000c0d40610400180842808442000200e010606004060494817000b071416510344000c80003402c0c04070354210622210380b2903001040380a01800001ca141000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 379612652 1250 379611402 379611437
    0x906030a0e0f011103010807080706050d110403060903020307170316051b010912140304120c0609060e0c0108100e0613020409140106030e070807060315031a04021c020d0b07 76
    0x1902c2d01e40c00c4c5051004401005a036038204542d01c054940080030303010052928001401d180903800207402e0954444000c0c0b032890b01e00009803401140c0060090003a03650310708001c0d40fa980901c07400e90f00708843c1583c000c42d0307141d01000c481c0500c1c41070300d060008606200040b1603075045a600c10100355031404d1010140c020174003600d0301040c021024504162070441014240403900750303201c41c003900107100b0440031805481440750a00340900f41000035a4107032601000404c54110014555850a054405c24200015031403115820a0302d0f8012030342c551150b00455494148949402070115500003081424500003500741d40403044805410103880e801042c1c180c3d482c403000000d208880100400220740c4c50f0089804020864000c1c0c92444d080c80741440e1903400c0c1c1e000e4032051548510703106654840403480c140084d90000c0380d030040c04a24280c3c2807410070041e201a407296140c101c844801003400002005a5613000300051344000c4103503259400b2400041241c2d041c05030804401c01d20a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 379613902 1250 379612652 379612661
    0x81b041202130614211e0313150f022a151c0b100c080a02160801090212060702031e041520120915090d030306030b07050906030a0e0f01 60
    0x102d5000b0320b030f01c85107500c1c090005034582c0c0d41c1790340f01c504090646003c2c0c0c01c001003002c2041404c404100c405200240d03103460302e035110740b143e01c03101c0030542d04001801c0b408a0a203c400032910ba511144c1c020a051b20032030b90307000300d1144110700703040300680c481c41c850304020340f10b2868001500c0d00e400c10680e680d4805d42c58005417280c9440310752800450150030344522640e522203908841c4401c400c42240002030010001003c000c01082000407201700f014000c01114140d1544503510204598680c454103001c1c03c0c440c10100d001781580c405212500e140070600a105008580c021414441d42900454044d141c2c1c08488510320070400c00410081d100f1000128110441d0b00d40d10740c03039290102520303801e40075418208050b80005c615130b4400c0040004881c40c211089848080c078040e40e602c489200d20034000d405521103c4054510109038141e0042d108580c0540121710056651100c140d849115207a8500c1e4400c01c1040016000342030750340020398142241089542d1505034070701e01402c42c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 379615152 1250 379613902 379613909
    0x6050d030513090219030504033e1203071d040203090105040b01050f0f12011d0d03060605030c0d020714010203010b07170406050f0304140703030f081b0412021306 72
    0x75400502c0d1082e20742107290303040007042100310841ca415403a211440707114400011030001c0645800200d07080c580700d00a0b80c0c145048600200d041d030060307440070540c9180840403c030704114040c219a00c05040c04241c4445440c18503010919564618034225580d12880c41c042000d0994082c0015982e181e41c0302440c0300b00e0b10720000103802e0609003403110000f90305920140c4a900041d512050759240c00040189800c01a5040f420300c2801d01b0259000d004036010314088466481c20a90a910002900e58286492902c0411402e0b4407001d04444500c0101ea55600748078040100724000703586a801000700310700030f00c1e601c0440d21101c50401d00b6640280c0c08600c060402080710024842c400160ba01100b035686095440d0034600718024046000350914400c0c40d41d0048009414010509507440c1684165020b440ca525180d01e4040c04000c01d803070026000545c4800081e00010408401d10107504001c1820b50800e403600080a007583c901c854226000700303810010705150252401031034080c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 379616402 1250 379615152 379615157
    0x5010b0301081b01050405100c0506090616030e060106050f07050624010302030f1506191707020d020c1002100504120e01050717031506070f02030115030c0b0d06050d03 74
    0x10380d4500382c08a460648101e008520400c03011a04111903a040310031201203e03002d8800395030206072806e00791010315040c00042e01034080c29082142c0b4a50119145205100040007034480d100012412002c598804406a40940c004401403005034003402c007a1590b20621461940b805010365580e600380301d02910380e64070a10744401c072140b05e110104200e05190314280303811400e41c900381581c1d15140c2c01c05002c2401e9054409489c1079246c03200011140d088041d80101180101e11090050000000b0781d003130944c2120240100304190f2000c50f60865640c00340e0f009085807105601040003d04803481540c0c154131404440420228042c020140b0460180000b20041c0c800340001a0060082c450f80b50304002c401c004500000f020302486201e5041d11102042d12035683d00c82d850b6007440301c034a41a85c1700e14040380d240b04122582d6150b5540c64400d90003808840408551282040c56500000300b100d400c0080502010410001078410500714140c046030490743c94000c1440c0c0d1b062080103800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 379617652 1250 379616402 379616407
    0x40603060f42090f1d0f0c04030203030a080a1505060706050a2405090106081012062009132d1b0801080c06030123190902180d02010f110a0605010b 65
    0x1384402842c3c0300001c1c038035000e070a00307121185070614000000080c125126200c1200101d820003c0030410380d80519405801c41390ba5540d4058043e001607c200d4500c404542440d10038025110704000000c1143c60290005007044141e0380c601002d040700600ca4441151b90f0b40b0006500250341e2a040680041107a2042486040006020400700160028814007170414240b00004803d420500200ea80302e0340703240700320b43d294540100907002d00750803485100c280401d409501c10100b40140002c200485036100c0c040c410700000d82c00d5401a1180b0545152050f0701a40d40107410300c543d080701790124030000784038010380304041c5a1000855202c070000c0c142c00014010303101c0800030780d07221402c12561917040d58505a000344220210f00e268181078200d012003038455459281c41c804080103005641024140c481100030300035004425a030209415036840006141041c82c0d1400389250180e540040d040c145220541d640300c000e000e02884d07031103003e0810021413440e2140750301030001b0a080c6036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 379618902 1250 379617652 379617659
    0x9010e06030a061706070801170a0c0f0816081209030f01050408190201050c0703050c033106030203040f0f02031005090a0c06110a110409140102040603060f4209 71
    0x105907900c0e46100d5200c591021051054042c1c001c003005045481242c03517800c212189d994142c0c24905003080c003c091031552034001c141c0036441c11810301954186401c07210500710100c0c10003115840c6102c1c1240d1030300404080400d01800d100107201043d405001c490000c040c0030002c1d82101c100302c509460700e2101180742c0310b132900e400481a000b40600e2000f0301407402c004020761024812810002c3c01c0c010009218200d41d042841501c844101c0020b102059094000d09580003007c43c002c2c441700d0803500040464005d000e8400e0703d0140d0340004080d400750109644401210034010700c160392511412445502c47c55050140a102360b4004c07004e0024510b02e0f28243d49a00c255402000a1042c2c0c1403202c900d0180009415240c15080100c0b104101c00700d2010400a101e1450090003664195058504064054000b00219032a0395400c1082a81d0b0341072201d2240c2c101e0240c1d204d031104200280078184803548803050480b00820030070340381052a0096107018900380240710301140c0f0400080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 379620152 1250 379618902 379618919
    0x11a120c151210030c0e130614060103060605120402060a090b0f040f0f0305060402040c18030605190c0c0b0601051b0f15060607030c0c090e060a050112150209010e06030a06 76
    0x10b500007643c081e041c0304031410340c0d88140030f0f0900c5000d91540b003444800015200741002c5855051590001401c00180f4010059560301c50800c585040c0401e013001c00004010b407182048403022608000c81c9646501d40343e0800046a0011f801d18040000180001c20704e085010001c219040c0c0c134001940d900e903c0d0840381b0030141e030980e0000c00d030b01c0301d40358041000c0361001c6400c0d68020740c11030b0005806841000180c90401e611000820807113160040401000621780c00580500c81c180362983d042d140790f000700c0003941d4402c81c5d180d00162413004050000703046c08151a401000505245003040d203964800c000701040050351043d40c3c1d0080a00340a180403c1c080c01c0188984075040c10000d14210011507980c4c4508840107042009100465040c0072215032400d000d043caa0078140100c4003010941e80c2d4490041d070341d20020a290030000036184445030805410b403984203040c2d40100810703081c940c0c0250014460603041c03059100e507041030f6550742c41c02144902c801d142d00059503410400e22 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 379621402 1250 379620152 379620187
    0x904090b090f0106080d050d090c0e0106030b030105010806220c09020f0415031104150302040b0a080601020d050408070605090105090d030f0201060b03041e051002040305011a0102011a120c15 84
    0xb44800c1e04030001b07000d01c20746d0103800c55034000c1c2c1c0103a010820350341702e28100e400c91a0340e9225085070000755001180b400c1d455045503001c10401c400030f111503607c5d1500303a41c8456040e00c100c8e820010f000d000000402d00c548038450480c1c01060884201540c558441044c0e0340018250003202000240a12030000c41c0c4075600400010f0313140810058800e511005503600c2a8061003c2c0e00281c00b0b006114039119030120740150002451240e181d191808016001d4a403e032503486c098050080140b20700e91007001910110303641c2e00024a0110301e070040a87d1554405c1410b141008020050080d040d129600310311800d5100303940320100300224440c02821210350341c0042035602404c00500c00030844e85001906c2c40700d09014034040c514401e2400300d00c0c0c007008610340e4801c0d034000b180000900c003041d4441a4030408031b9542045e0080082d004900300c4004d640307082d080250044485603203040c046800c4000c95414402c0b0742c48102c9000000e642c1241050348501e0012000074100f090f0401c5144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 379622652 1250 379621402 379621409
    0xa0306060e090a0b0418150b030319080a0603081216090311040f021309060608060103050609070c11030106180f0903050706050a02070212010c021e0a02060904090b090f0106 76
    0x1041c00880c00e6900000381400d0010344906031107602d41c244c052040d91030303074880703150741080c04404801c0410034903125008400840c60103168500e480d11001a500313001c02240e658000c402d540d282ca40301d242c01c0a40e012400600b000c00d200381e65010200001c0d4191000380400f0141c010074100307030306c3c2201c403444200e040e4480c00300c1081145401080001c00c42d00d14140a10421100031800c1c24450004400074004e06486824001c03e4580016894001d98460000d071345555507400e00d150340c0d01005500b0b5450550701c15401a0790a800244094401c102da40c00f40b5101c0ea00c54500440c00c040001e0954010744c0081d2888201d0b50030103c41c81e2130500c100399503030780709070028040b03010643c4018040340102d101c0940002e440d00d0000d26a0341130750b8115040039030700070001d102c2032000c60074550007014084245009441441c0c0c9810301c1e070400c44003042c10aa42000180441c101d294244140d9400c200700498210791104060f0f0f00103030656080c9403090b0070082c010b040c901100d409850a5911550 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 379623902 1250 379622652 379622657
    0x608010c12021b0706050408160e060d020d0b0c0a030516020303040311030c0a0c0302131104060e06130e04022103030f190c03022a0c1002071a0a030606 67
    0x1820351041d401c10301c0e050303211079101401a111003200d031400320f00d141c01c0b4568201c40d01a5850219010ba0068058003e5959107000c85090401d43c82280c000b040160150300f41001d03041c070001c2d0041ca4209902600244054420203610441c1e655850034071106a030009611940856440c05142e8035101d22030348121407012094025211031000394507448081e20103020012240c2e0101100d5108104440201c1d203442d00b00c621500041c209804c1c0d50280d40801c07441003103030b01184c0840180c14000c200c0401d10200c5210301c2c10340b42881c01d4518101c10428603402443c2406001081001c5070200310050403140070b84242894540304010410707400e40080110103044d6011001c1c070760000800c0e00c0c0e010701c8944030180700f510358500b26406c00d40042ca5554100341021055189140d2540242c24015a51054401c5203141e214481280903c1d501c0c08105e181e0101031290864940540c080402c4555030050b1846a91a15849104a49031b1080035011075000522108030302c0e030501c47d0400901692 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 379625152 1250 379623902 379623911
    0x30105010e130203120310030b0f090d0806180405060412020d0f0c11060a09230f0f040608030d050421020c0108071e180509100303080a09170d060801 66
    0x10480714400e00000e000300014a051807010011514200710003840000c260781c9003501c0b40340000d02d00303843c0e120a0000711540c40c07120b4081951602100940d9000d01c19407030240c24642400ea50444900c2d0004102ca1b0348050b20401c1400040a403c40c0c40d4011400355010b02a5440c10342065105034022104540c11580241c92720241303190f0010910410000a1034141900070a43c24550704e9090340211076a40850001800100c85400038000c001711f400c7c2e410140b02154140508410824221030500e4001842e8068500b00d490050540c103013444005000084c002d40300c0324950311b0b64003c8115010361076038400a210500c540f0010840301c00341319105806040b223410714020348460022101c141030140d04401704003014080c00c80844400403030160200448c1070b00138000c0c00d00002c1c0f41c40c0750040fa0b07030240c0410303541048a13840b4810a1020042e280c00c030310f0355504031955203000380401030740c0341c0e40e04041c4005624461003000006000481688842e001608041103c22136070250210ba03162 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 379626402 1250 379625152 379625159
    0x4030206030c0309100203070503150f13110c0a050307110d11120c0907170f09120a05070b0f01170601080706031e0c080108100b010c060b131406030c03010501 70
    0x1140d0407207074440380748103141c0d03100c0c0c540903507142c90420900a80a00d5070f0003c81001206079102c000345102e81000143d1110101c0007006100c80398000e5202c0c190401d10071104500540c1d080d4021406401c2c4208100b4604130303060003014101440311008640790f0b0400181c000070711040c810a4045031400304c0307982c0c079840307902e527240b003014002041014082e05103800b142031060000e0041da1243da502816028140c038125600901003000c1210481d4080d00b00d40108102c0c2e4a580c00452182c019800104003c40c80c0744040041500054240410402e04001040016504510b5903025005d04071150000754140046800c40c10110401108030b51702001c0100406403000800b10101d51050400003120703450389100341c010242c3c1c061021641030504100400c0d0992084100d4100c480c0f641c10780d0152802d090482080c2c61514200c64001000441c500c0045015176011f01e040d2500100517205026aa0b50710f1825600e28507245e041c0c030952181080342c00d003002d0024610100e411030080010f50305 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 379627652 1250 379626402 379626409
    0x1061a130e0c090d12020f030f03150d1502030f160c060b130e06041e0b0103030e130f050402100e030a0f0f2307050109050321040f08010e06010b040302 67
    0x4920915502800007808245058802000c454281c40d02510400460641342000c4030001c880e01c54500c018400c81c1c0584c3e500341004010b079030881940b204043d01e546c844003051030512402864043e0301010031a4014001840383d00701e46240c03060f4038000350f142c0c45d002c080001c68000007010341c0003010f440f0f164400c409511681694599520020004502140d0400b03e40c61300300c4109607c000c00e2038620010a002000a205881103209100302d00f1400d15050400140060148008024001460040c00041c0c06103944603d1054050000070100d81c80c4121001602c01496a10820546e40c43c20310056081004800d440510300e81080d0070803107495404a0341c0c030f20340c4010240c4480703a031500b48020020741c0c00c0744c01b0100e9000035028041c0d0112022140341d016100e40270038030380d101d4000c0004403940150341d40703000c0320001030103400090f6028103211f000101103010800c2c0a0420000860034410004020000d8078440c000002c4122102d41001e2400c42d040e00007040c080002d00003080181c0c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 379628902 1250 379627652 379627687
    0x7140607091a0405030a140106050d210507020303030c0703030b0d060c020c19061b0b09100605100e060901090e100501080109020408070611011b050d1a0102280c0801061a 75
    0x80c0d1040307d0400c20007141c5107181c01000107410079640603516404280603c83c044059803100402d40220a03902c0200c2d810540700d41c400c0000c000d401d50401d20001d075035020604054948180281004908402d40c1c03000039413411401901112a035030345101e5814150707030400a02544040035030712001007180218204c10001c025100d45000c0000e0300c40480f0440014410454010f5446540292641000076005450382000030511440c6454020002110f01d45181d9a5203000705a40740c3c6190802e8502c01e10909034444116039041c88002240003401d604a03140c2a445100342c004a6001c260800d8001420503006a00c480310741401400117010345400454000c0440358107040c00c06c2e5600c1103144903405040c0003020720303030b25500e404600c0c1500c41e00b00700180400700e00c610341004040842900000c0e1403214210142c0168000221064000f0740d125440e03902d81e02048001a6201d02552408088481c1d41c1100c21242d448060821495100000e25826012f0484c00281032640703810541c8444c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 379630152 1250 379628902 379628923
    0x31a0a0e06150604030204050405030406080a0c080f060f0a08010f0e0318061b0607080103120c0c17010609020f0909010f0b0702040f061824030b04020607140607091a040503 76
    0x42e02075180b5000260f8490044900866014006008906e02401d1040d03c9800502c5140c012039400e0000030740241061003080040170441c1c9a45845880c0e00a614200342c01c001d1203540c00c000d001e40380c0001c55407603615403c01840c4008c0041890f01a000740328059410310b54446030158800d0103070100e0111084802449a181950720310384070b00c840c415071160700b030500141c00700c02d0003904213000115034005185416240a03c000542c1400240341c2205e1002e06160701820074030700e030354060010241c19004044010407480000c1041602c1d90201401c9070b01404203041403c5c03000840711210b007000d040d0a4010402c52098151551a001e02180c0f42d104d00c20009104582d207021050003226940d000f840988010815690108805405c0c440102030311100c114521251400100f02007800101d0b850a43c2e60028502c100c80d2116801e019490f044100120784010102d840350719900e070300b0082c0600ca400e40b41d17a0301d06414540ba0090fa5044928007000390582c0c8200402d21294800194506ca413 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 379631402 1250 379630152 379630171
    0x6070512070203030f07110a15050d090c050307080c040b091b090d0b01080f011b09090e03120c0d05060105071218031401020a0e09060a05090405070f031a0a0e06 71
    0x10790607140700103401c510805d44030074900500818084280a2015210050040b0070b80f40e1004160b103540d00c0e16500c1c0e0301d00790f07070301c000603010000b4a007486019001401582d100b0007111550a42350030019061003d644c101a4056212010602051030640180c80386204290f400141c00d0402d402580c91780140200f02c1d00c46d94100040f0f421035500c130502501107141d0010049141545c40d0030401e901c8070548441600550b0030009034107034a08409840000e240c00a884c4c020800d0f29094002018080c483e45600301c6000601c043c0c014840e50301403d0748200c021118144c2e0703407440102540d0889402600080c10004184070040024500d141c8052901d580f900b01080c0d00d038601c1d10f191401441582000f01080300030340b034100f1429415009015801c80a4540e000c4a485070310038480c0303d02046804a6200e200c40700e0800c1a41410455150807c0c080d1090b20301070351302d4080200c0c0ca0f0840745c0c01114090f034049803040c042d60580356a01c0d0824043e990500c54903058140840d91000702900c1242d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 379632652 1250 379631402 379631407
    0x5060f1c06063c05060f0f0d020403030e030f190213020d050613060b070b0405010906110904140906010b0708040b1303031b0b16210c032a030209040b0d060e0c06070512 74
    0x105001c1c01b8040d16030300080b02d030100d641c4000c4104003001a400603c011004076003038507a0070300c0034640401e4600042d5490002401602c00900d07460a01d000f5103803082e80c1001440814185c0c41607940010080e851081e0703400f190f507051180c1800f190000e04203a00009034038004c1c00303102c5108144112140c09030030180d8503c2545840c24200d00400d24080b00504d0207181a0b12000c86808030805444072800480d0200708000541401c8041d1a0007110004c0b9503407c06401806010400f50141505500031060517080c9504c1e800e281c02c45034006076200380f0344240600e08100701a03120b03117030284c0c411031600301140400e01540c0b502c5040c5c0e030282c80101400115014000301c10312130b07580c62240e900d03e10251041d4248a07054000100b00004080c40060300b800604050000c140c1c0840070003490418814010040810341100250005407881d640b00d5210710b6a42c03440d036682c0700340302005030041c94001200140c5180c9246803040362240d06e400b031501445000c0104d48045404401d9550710103c481c0e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 379633902 1250 379632652 379632667
    0x4050d03050a0b0d0605011a040b030103020d06021b0718060803180102010e100203090d02070305100203130b190b04061a1e03010e04051005060f1c06063c0506 70
    0x4018108121a558010800400400a005250308121f040382d000851443d184418090409450f10850141c0c52022008200400c0141015a8403029035401200d00506260b4800300e03c020003001c0301c400044503070000b0410f01440c0500c01071a080c01d10009070801c515841c000c40982c40c0d000c3c1d407401c4102010000350041680c1d000b900290f003000c1034481501c85450801c1e40030002034100703640f1401e032445008003c94840c0e00000310801581e0304100144440c0c0c00682d65072000c0d44c00280449440480040c204001031510a12907000304924080e180c072240344001c00c2800c441048113114032460410408001d400400d00441c40e20780030f010000e9648150b02e11032980041c4d410705005034401800000000e44140740400540990703c108140d620303084000110384244d81c0709550041d0f00072151000d2049514000205002c01c1c0382c80e031110303184000152a00c0040321041d501c04240d82c09039401119400c140d6001d0b040041c5203041462030b4902c000b0350341b10301504040c01000d016007400103400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 379635152 1250 379633902 379633921
    0x816060c080702210f010e0a0201021f1e2a080a09060b0d06151d130f0203100e010b06040b070303020306030a120e15190503130602190806010804050d0305 68
    0x50f44002c131000d914480300c0700401c8446660b102c6480900707403076500e014403403900315602250000755150141e004058140c0701a48006c3d50350b080c0c0407c1c41c0d00a94941e281c1c9542c0c0012981d481c4e00c0342982ca40000c8140d2242a2140100751024034000e40003c4d44125980c2240c120101640250054400250b21825450000010006407140e10350068855441d5402c10040fa005002805500700c000046180d49502c2c0c20200d1a9160510744640c48400000310340c04c1000940303c621600800d40320300d2140a5802003810020030150080c5c101da01d928401400c04402d00601045400540d101c2d40350900c9c24041c80300502500c50002d08068000001c03c1c09070303404218400b00240c020035011001c11882c40007401d9a105198200c1c040c1461907440654800c42d80140c8409810780007144908186124048030079510080c01c104d600c114041c800310204d00300d8030281c02c410405100c403c0080b555508003800340e036001000da5042100e51010400000d00100c0c84000d1760f05a0b00b004500c0780c841d03c0c0303803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 379636402 1250 379635152 379635169
    0x3020d1101061a0301090c0f0903061a0405070305040c0f0501021b01230301060f030e0a020904031808010609060801020a0207031214071b0b0a0c0305090d0611040816060c080702 78
    0x2542c0c10b90760000350b040f84800000660407500511020031066401000a80340400c141d001c44001c035094080400111314030350808440811030072003404000c0e100b40c00040464400340c981c80c0000340d59608110800c180c41c000e090140c8501050030400c0ca1410300000e41e59448401400d00c40c80c494032400b06940d002d0340050506403241e84050300000705c07110150341d15802c244503020006d1041501c1d51a002e0080c0706200e40040a20003900b603001858083c4050344101410881c01c102e00f0340b220600e030151041e8000041c0903414008a80d491801b0108001d403410b5070051540e5034410405030359495000a03040044a610401401340074030317902c50949454107061400c0d0040200014201c04200f03045441010300303c4420404c54101d601d51035603500302e008090104010803400d44042c40803a000c1e401828440000505d441600c8040741d580d503081d81d5020440300ba0740100801c2c00d00c68500f0500010a41c5100c80e182640d546140160052200d02c0d182e034050202080003400303000b9915003421 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 379637652 1250 379636402 379636409
    0x7020118272a120504110d0c0f080f0c150319110d14090d08180111040801021c090c050603070c060603051b06030f060105131505030403030608060403020d110106 71
    0x104100084408011414003826882c0c1e07850003c1d505a1088041c002c0502c00d403401690054040400b1a002500303000d000081c40c0c80c165035202d0301d481c0000d15104078600b948040c0800e0703c0030344a007078000c00b0008c2c036014816041c58800e0441010100c1c0b880130790810343c1e51002404800e00400c1c401112000e00410100044e13180c903410000b0010090a46604900104544107218000342c0d42d40d4000103031181c4130000300400043c10f440c00300300d00104403114603003050040c00000400107107440c4035810552180e0f02003411a5004500300c0d4042000d14822922a010040c060004100a565030a800b2200b401010b108000c04000b1680c4c03648161403104480b036001c0350070405952a420b029030b842b004400e524001c55502485400a41030202c292801603001e5103494410b501d8a000545081d00603c071248841001001e000070040803900304040e00186c2ca0312541c0e40d80c00c003030500401b503540607004054164401c6051000280c3d001904c00c210b080c4c2458000d0705003c2c07811804d805070405a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 379638902 1250 379637652 379637681
    0x10c0807120503100905160f030b0306010909030219111e270a0c0504030b090f0a240207122d1d010806011706130606050702011827 58
    0xaa007405126003040c003c40c014442e00c1114090103039500208000d40c5c20403a40c801c3d044901c7d08102c510180a00e2243c0307010b00042c00c0c041103001000020030b1500701c2c01da0101c050103840f4603114082c160180800354586060b540103907000021611104810718071000400e015454803040c800307461000868000c4030302d9000b00402040f218840e0350016542160020300c0e4a10b0728100400d5030071040d80308030141002c00d0344503a4109403942d1030329008880014200129401140c41e49a203412041c072000144a1041c41800d030540c64ed049450364030406d0700c80c0001c0d0315104210310f4012030100314042d451142da505d4020000d015080501908090800ba140c20100344030000b140b8064202c60211080c65440200091002c0344100440b65544181e61090214030764820402d290b02d503444045900c00c40181403000c5c22082c7c45003c07400c481c102d60190001602c0850400c04541e4000381c000780c00c0c400840100309036420242c0d116081d0758205080600081078408012072106590401c003050011070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 379640152 1250 379638902 379638923
    0x60606170f0a0b040912090501030b0f090402030f01110315030307020607061e020408150c0310031e0206071a1f0b090102070506030408041805160f02150106020f1b0d02010c0807 78
    0x1131400203200d42d1000d00e80d00200710447c2000c541948240305480090800815220048030910203102200d20041c0c416601402495405901d421090280254410081c00d00380e941e03150409031194803415100c02075101c2d809c10054080503940709010fa1303103050f030420000035a1940c600a2416400c1502400c0c2c0c8501c0d00208000805d00400308001c091307250f034038420004a42d580001083c0511080320101444030700c151091006c6010458a01403a0100524009444c11103400042c815048540c04a0300c01210082107000030088995107034001449401002c00420350b6400c039846001c1d40d00820910b0f00c80030640fa03099a10030000c00d402040050801907603400c2905003268154010b0091220350243d85504031503500c010f100701440354010941c0240841c1d01c0f04401c1700e00554410ba0002140720b003130100b8000c1480011494000c00650b001088c641c42d141441500303001c035400c01103501c016100d8820705c01c1c0d11108040100e6960904c2c088988201c03900e00000c680c00f40450203405422070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 379641402 1250 379640152 379640171
    0x4080c0c12070f08070305030f09011803050102040f0503010c090302012102040f09060b040303050403060b0a090203090f060907060806090601020a0c06030e010b0d0f02150405031504060606170f0a0b04 88
    0x200c1c14030b041d64991094600c100340c0300c0e541c00760344058510004000d0303030040026400702205800039100c0100c05150008050880c081c4001c680251504103807130303d1754001070412014150840110080c00b0a6000b80310030768100c08007805541d078921000c4c0c14030080c20b5400a05000080d002e0201400b03150046442e00d0b1640c505c6285c40c03010b4016000801d1815801041820048090302d04596041d135600b494182035640302000703000c0209410780c0200b04a070020404220f2400514410390002000300105184105558a0210003800301c1c0c0d1290810041884819444180340740d2044040c2c03000d882607150440100d281003103101c00608040c41e03841000c60a20342c1500300451020030040240071148030401003007482e402c0c0341801011007a49820100041c1420014400c00c0c91341048a00d050030317920008a070400b00e550022001d498044020802084064031404003e80500c2c0751010b8401404003001000000203440f00c500300491000250141c1c24580004007804400741051043c0c009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 379642652 1250 379641402 379641439
    0x10305010b1f1b03200f0717062e060e0103060603060b040b0c0c0d0c150504060e0915060d0605120c06070f11031504150c050a0f0e0307060905100e0904080c0c 70
    0x20b55803401c41d09006101c000580c100254113040d852000800103043c3c50303214000001c003024ad5003c0e5400c2c1d00015410b01000d9010036410250003403c0721748842c1001030440300018111151900302d0f0003414038250b0706101380700f0440207603003c0d6084442c085070707510780c403c1a15141280c84500304d07034881d4800c07a150341009000c0003000308a840342d40700030f80310003002c0c0c0d0700f55254001d40c0070f40c10005074406038401041c0740c502c01c440e80283c0707010b60081c2561105400324185501c00300154108503194801001320f400d2101d00006401385041c0542100707894640001c1013841040320180c40307110f80030804010301000e6900c6800c110f5000b000c84400748003140740d01e101c10604440c140c4200249559104040310503004196100d0705a9403094500121180d05640c11400c2d03c0c0c2036000c1081c05454080d064a081120f5000382901c0d07210128211324020030810010b01e008004000c0103131035aa080c40945440c0b1080b5013255100d010305441d4411441342510f1b1150352002150700c0714440b10783c100d0040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 379643902 1250 379642652 379642663
    0x9030702030d1106131b23120c061b070e010521120a090b030f1f030b0103021e0603040b090601060e090109090602040b03010305010b1f1b0320 63
    0xa10a50540304480c10b40e680c10760b24481e58041042244d00b000001901c0c00034000d131013640c0c1c0e5101e140541020340d021144a4004240740c0c01c200d95104842d0205061503581c011001c14000c400c0710840304505034002d5440d1107000140c612030180c00040751085844417910514900c1052180c2100c0010341c4e146c400141c03c140078810507001c1d00c0070750901c03400ca104030126440c1c0340031124000d004001c0c04004540c020750012103031004100c00d01c0000304101d10200015402188001e00c003207840d00340360040118490f48684480390030107028808000003580c00c071301c0700d0440342c0482d00740e9448060344600d0403140204108556001c50000100001c201d915240f06011307902000881d005a80c0360201550000b501e00360b00c03a40040074800421000d10541c0101c800c41d4400c61016007010b56034403c40e85a5002a00300315a180d460b02090152414001901070200c202e905241150b84d40712500640a13a0000b00031151030034030a0001030501d4000d1070f0b40792102d8448042d10300802014130501d0340301c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 379645152 1250 379643902 379643917
    0xb12090717010606080604050c09010804020619021c0201151e0b070b0403120c1b02030106030501050405030c06070504050108010303031d0601090605130614010c1a07080411102102070b0903 83
    0x500a01c001c00c60a00b807070710a1920130001d41d804645442caca120300550ba02c0c40002d2003240c2c80320303080040920054203203081d01c070895001e40081070750b1142c2805c01d400c0e00010200309021a0325096080d4a0151014104001ca5880d092016490986441052044030242c0c2041c0514a07000a0131400c10282c0403425102c0e9007c0c1d910716981f4203066002e181500e00f400f00500c002803040d0b00d0044080c41000e441c50840e4402400050420380e41d40d2000d0a4441c121410745503508080751012881805200c800d500182a2400b1480c1a00b0100040c0c504401800b0103010103030b4035244200351840d5038110f620603079a04d0007210740941c1d5541c103140c0640907034010303140110200d1003084901001c81c0a0300d015208031040c040c1d81c8100b00c000441e90b2413600401074509140c0c1c454800c03002810255258080d040646d103488051925041400d90790350640145405010213012042d241a032140010303240e01080d41c034024600b4420301b0750401034000c48031b028091942040134844102400001040310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 379646402 1250 379645152 379645157
    0x1140102010b0a0e0714220e070315120203011e06080c03010216030e1804030c061b020a0311120c0c040b09010b03060d0204020403061401050f0a0b12090717010606 72
    0x4101d44003803100c40c141e98403400d81044c00f1500420200382c080c1c4081c003150103a8407041d904203440321202e1441c03034601c81d405501c038481d030036014060340c0d4034080038545c8180300d13040c284038590046044c1c0c29600e030f50b485681803001e2500e8010045541c29044081c1800700c0038108030b03030420361409540081c02c940c4560540b81c42144100c160f0760406009441400d0094144448288003644054940071500003034503030311072818580004000c0b110380495020758065520395181c2211490b0200441c1e50044104007040d800315803400b03519500103110326150754546000c0c2c0e039402c043c20307446107850b003541c0f0046114040440d43d000180303c0000d00c4078030440111810320021104000b4060701180a02602a0040007040010202d081c030009506030548007410061405590780c40b850704403454502c0c401594800d642c0100014642100e90100c014030844240341901c2c40c11001d90400e02c81c580161810000200008002280c14003540c1c004040f001c10740341c51510b1101409000b0809405403001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 379647652 1250 379646402 379646411
    0x1809050d080718141003060e0c03010915051c080d06030302030705010f0209370b2109030d09141c0207120f020121150923071103040306050114010201 66
    0x11074481c40100f003100c101e0000c200000a0000511201089400c12030042c5611070000251224442124a10898044d02103680b207505000500b02540d980003c804264550f608003400180e0b503420360442c0059080f0803d030841c061525041c1e03a140030390348148a006150400000a164010009081d081e1054008100c640400f02ca48004c0f8002c0c900140d80050758180b19020b61b003103c80c0444411b62402c010100524240703066800c045900c0e800090441720003040c8807189009010050390320700f050407130100e8107180001840f40c0d01c2c095039400070319107034031b880400c0144440215880000c60406043e40d13400c8072001c5010b03180040460f16000140b08500340054031150f03021004460b6a8880010f0100e503034540c00464910b941205548401829120940c040348441c4c8122415111000000d540161411080b407085860012000c0d5034091403d404c40007085039252100c4c0c2c820700d24285808940e0b03040c00110711714000c40e0001071441d40340000205d080c2503803400380f4103000c01c02d900a00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 379648902 1250 379647652 379647677
    0xe060318190b1609272a020c010e040b1c0311190206070308180a23010605060f1b0f06011a0c0d030e01021e030601020d0801030c1809050d0807 63
    0x42680105100c0c500000d25080014450780d201a9480d14804102040407000300300d01101e00c400300d902003642c4292003421061131181c0300384109009000411b450001e09400d40c12500041c1c88040070260b19407103141d65032941c0c2c1c0c0341e5a854180001c4448119480003a650140ca00a40b450041142d0210a8440c0da50403003500c1e200c81c0c048480107603003c2d0010b41080c3c02907030b00b55050200603014800c2d54000600c0c1c40d01c1c00004002512542c0c0c0611584156481001c007101c1c007116680300c200c1500d03410440180001d84501007181c0164503080003c0baa03034580049a502e04004241a1401c540030795119000046400680103051b140030b100158440001c04600c9030b8103202e0200174003241c0e0031103500c21118038040d52100003034a081e1400585450809141d503411003050258010415201000380714065904101e000030300b0000e41005070855045407188c0342050180d10409582506407242161103040741d42040302c00c20ba0181c1200c2d140081840d020b04044030845212000560011a51 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 379650152 1250 379648902 379648921
    0x6040c0509010803180409150e070501030e0d02211201120204050c03040f0204151e030c050901050612070207170606121f09050a0b010b0c0f010c0e060318190b 70
    0xc841807032001c2c0709103040141003400c3c0000740c040311070155030702c00700750b00d0b401601d600c01c0c000c2c1b658130510080682b404508180026045440980b000c9695a002c0b039040100b4030b80000f021100c40c801c403442025040f11004881440348684621041e4003103480c000090040d0140030181c0850388203d9040c0010b980301c1c026401a1700003142e002d013000d00041150000350074a6808030b04242155860b2501040c1c5810141d1007410781c4240e0b0b0040c039080c00c0010000d009a2003590009414102c030301d46210351425002404d1030040c1014001e1545104001c01e135614000c11501c0007c241c0300200380e01c5d80c0499031009032281c004580c0d4900039140e1303600d42e40ea0150b010500c540c05080026004252200b1012000e006000020040302c4510170801c1d1400800d200d003084600900c074040c003041d40c0d100a242902c4c00c00c2c0340c030b101c0c11704580c3c140240c1740c40321900085054103003241034031200c1d200d80d502c400b043d0201405c81481160b42c00350002c806944005080440030150103507481000c2910b503060340303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 379651402 1250 379650152 379650157
    0x18021302040b1210060323090a2f04060602033709061101090206160812041b06020304030b0703050606070204112505060106050f070606060c1403130618030506040c0509010803 77
    0x100704440359207062101f690300040341d1540c00c0003500c03040303420003a9299034803600170100340c01d1101010106202e214030001030301c040070304809040d2000d01501c0e01c2d01001035941d014203480414852104803d4000000d071810001441c1a2002c0c031020135200c25000243c591701e10b0740126400142a10311a8101e40c905000300080c4a6020f403c02e4540146010201c0c06800001d038101c507000d400300041c00c9200d0041307814500a078060900300f20507032603124068140451315400203045d5082844208049081da800069101d50542030100302c0f5a6002d001900a00c24520020341c8241342910710000d610400c0060030380b02c0950800101c6c11200617900680c501c030300650081c0303a80e01400c01803240074400c01c05401a40080d160250611103240c3e110300590381d032500818005150070424505118007910540801c6040102545c03034002d1880b020540000203001d01814806000c0f840e0b064600456204001541c102007550b9190401c0d2500d140220018851940f048032030720f0002c50300c05c601008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 379652652 1250 379651402 379651421
    0x507180e03130b0f0c010212010e01060c1e0f02301914011e0203040606060c03020a060c050c0304060815100903060504060f0e011e18021302040b12100603 68
    0x703141c001e14500341a442c86070344840c2c48181035074005d102801c4074007024005400113441103260420b0325810f2000b003260403a0168000c1042060003240c0e2000b08040e074400681842000480340c49003002810284004160301400035008201d03080800305c00101c160180f007241c1c00101c2070b881d40410303901640f9a00c20fa03e40c1d02404a11000a015000502c0b4443d1044c80381e0b01e80d0008141500045a610400070100102022040c0c0000400082004900c9418050445410f043d2820f180c1510000d59a5401460007400c484d92911003224540c090300c26507041d003040c0d8080702c0c0d80c0c0e6211500102581026a01079462800d039042515203031030007214459140304a0b65500d0740c0140f80d500d600014040150040d514143c0e1030401c100c0d51119401484108802c3c0000440c0b41546400415152100642c41903903407854484000c1070a814800001081a0102c5100c0c20704600440c6010082c421a440102c401c0c0000520000114071150b410380704031045181c100344103907110025415a908000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 379653902 1250 379652652 379652677
    0xb121b040620011803090f140607050a0b09030d0e0c0619050f040e040308060d05060a0915180302070602030703020c13140a0203060406050a08070b03130507180e03 72
    0x42032028911600b60701c1c007194000d928004034204400709140c212034840901a4a01200f4407420090540041a0030020a98210b80b80801c918040ea6014455280c8078190701c54600004c2c800d040c000c003000007070207094006d1042e00301c500740402c8107a941d5001181c0c8a4031141041ca4149403908049828900c210303002d004245000e2004851220120f00b915001050201c2481040004c11403e00500003810405408a00504003801d020b802007100070005071040a501c00c1a000156021542d150011613142010400032541c3c50071414a41070380018006043c640066004a6400a0300c1c2d081d15a00a07001d980d400c0d600e035003003213032607200d190405070150340814840025801c0002001d11a08264600003e1050507022840c44401e01a24420101600841480350b00c1c94180316000040c4400c0b1a90a03015282004207520b4403924800c0c020355660100000320540201d90591400b07135031150566088c030b504ca0502ca040c051480d0201ca0b0400d25088481781031040c000200d501c00c42090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 379655152 1250 379653902 379653907
    0x301090f061a070311030403290709140f04020d2c191505090f0709020c1504080909040f05060f04031d01030e07081b0105030103030f030207020301060b040b121b 71
    0x6151514066201e848203c0822134030400c4111703c03e1061000e031010394801d0680c0400700e580744400d103104004100c40203c0b109044400d0103c0a9040904803007115410440784014003181000a03042c20354001ea55a0024000076000d0140c070320950001e5251075444000d0035866031240744c8045c80350031070303c0511010740c0600c0b6640c85000b141416490032a00c00e8a02c0304c11081c480d0b04003401c3e5102518660220f41c8100e40012200d801801008003600b106a811030405490001d5160388080103215140b610302c500d80400c051080040403581103410250116441e8205490458282d0020441c162282c1c01004041440c5140414010b4001c64140c2e0b124045070609800403009071800a2046045c075030344c5d00d11807403220700174410040104615005000d0039452240c05070342400c6c1d002802070400000700700500c00030340c00600c0c440581655140c0140c64a444c0c2c13002ca801801a40c0000391440b43c00300d00058039451402c010501c144040b0840c0025450300c555448240c402d0100c2c809080505 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 379656402 1250 379655152 379655189
    0x120304170c03070609080d0b062b110703170c160b4f0302120304060902040906020318070609090b0303130e01030b0106020d1202070206070b010b0301090f06 69
    0x121809070010342884030a40385450301075668a030849644030403c54011341c1c04a00b4420030b05545c850501c013041d0568050b440e14500101044134808040821030390182041c003000141d0307000c3c0d8410340301d0210316400c150344d40006003800707000003c5130740071405440f5070440041d848590303210588141d080d4a10652650050544e60015841001001145081e510400d85a00640c6000c60007040300b0801050101c05103480d01c4c0300c1d040105441425114011441c0303c4000690700045007815400401481902c0e500c03280340800180c2908031000e507125047c44548820301140d54010760281e01d5400c584440c0c0d402c40c4981e5611400c00744118400f158105904203c0040560088501205d000701602d11701a82203d07007001035031154100b4001d5610590043c0204080686180d024110900003000354000e46a4003d10701e00c241c2c0b0880c01059000f2038804115203408050311015680f2840400d959070b1a000290744a80013445281c1c0300c6814020f40b00220402e900c150760984c0d103908003e0140091 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 379657652 1250 379656402 379656443
    0x307080601240c03050703050702090a020a030c1404050f010908060709050a09140705160f080405040b0613031b0e0a0905010609020903071a04080601030f02012a06050c090402040303030e120304 85
    0x1101b202a028003500300100801681c0d00c0c648944500840d0030700584074004c441c001822150000700c88000e1140341c00681c1091005a826101100e0003210020020011000101c4401200381d200c24450322a038024486180e4004c40c20070151034090329000415030769021082d041c0c601c0720380e00c00705600c0c8810101da01d5510583c02051380c81800d50300030400703000f40c0c0c0e25103603401044002900e40120109040c440303840c0038099450b42c2e034011121a41080c07500e030420b6984420b41e10000302205502030806e010b82c0d00c25042e04000740001542806a89805191000504014407003100e99502c4c200340811500554420390342143d1014006111103414034502e91160a48030022050303285e014000000e03180e0003080300d2030185100350324440d00d00b4024400907080c89a2050840345c10002480d0b0100b1500400c2e40080d400c3d0307045680858645c1307a2940f032046612030740030120b030000d0000801000341600f541003c0510310041c403c0f80c00d001c40440d58101a40816203008040d40e25509030305102e440c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 379658902 1250 379657652 379657657
    0x5031609080a0303150608010e07031a092707140105160c230306060607020904020112060f1701051519050405042a061e0e0307080601240c0305 63
    0x112681020840103854105040c0303840740350b0303808500080d00d901891085a0b8080c981034001d00050802140703650410306100300da804002c2081013055514088180d421035a1302451042c0100509461300904200980710000044607851034203500c500500c145a070f0303c2c0001e01c0f0048413070f40c4001c810030440d008011201540104031600490485c14801004600380e20005001048003000c030069003810b1000d103080503591140230170f11907040346042003041e40f100340440744146d504440845444c1d42d40e1005071440003c4034281850185802c002203504e958038000c20040d620310141c0816290805081e45003a030310216407082c50003030b000340c0c01880340c00c181000200340e051084591511944601c0440d0031034000302d070251906003a10070000c0303070200a00d548068070420b120034904894100350018000c1c3e1203107031981c240804c06a400c035a07650700c202402d807480c06006007030b100240c1e80c40c5078171650795030203001e07240504880f00c20640d005030042000303642546041e00e03080b00340d5207540c07420349254 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 379660152 1250 379658902 379658941
    0x18030f031803100c020609070f050334060908120301051f230319090b0708060a090f140601020706093501060311060a0804060e0f0d0c0b06010c030503 66
    0x6208001030300e91011018051844d410949500404c0309107809011589010b02d154440c401c0d0800b102410b001c0c1d600c0214410312460428503810401c000000311009010290341e1910403192101c6401081d0254856207400840d00c800044a9055818400542d103a200c00c1c4120765111180000054510640e182141c2c1c2c1d405450401030789140d4a203034000c255619950542c4c00b40c1100000308054042400040d00700381c143c1c83ca080142e600f8a41da0782c00c2841e0040c0800051200c2507000a04070740e142d1610f54003600824509000c000701e104043c601400034503140524207641c1c0000144554070024083d41101c86036590301071aa450102103041c002d02458070070501000202c011265000c0c40d00d03140380e00034000340000424504c0d5081912491a495903c0d510031841000100c403040da020302c15030740141e0481c00019080c420928503920f404401001c004ea00c0c050010b14020323281e00725892135601806402d0b0441d01e5501c4900441c0d504050440003808142c0500100d01c4400b4100080300a8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 379661402 1250 379660152 379660159
    0xa0e0303041401150e04290a1a0411030a06090504120f091d04060f15140f0d150c080f04030c021203191b02030d120f0204090218030f0318 61
    0x1c2004801d10306070b600002d504860360105c0380500744010000b1110103846980c200c140500c0050702169428a10390f800900303421019600e480c00c4003200c2ca07030340604010042c030091080000c101404d82515642d0001c0b039003d040149021000113420010340591f0740b0a641c004120040118101c0d42600c440c0d81812a400400c405600049104603844c440c849a103841e10b05508100c3ca0540b520070243c0307100b0010011058100350070700d03e00c00301c000181c41c103451282c04d408900c000074402246c100d0a82c444110f41c40f82e0030000b01d0080c81500f0282c01c0003201e0358101030201c80807072141611611010748251000e1545440041d021a12a80c50b01c401c1e140700034140003025590260592454010405805100c042020340031449a00601c1c4415180c14260209038400d038182c000030b03191082801c141051024800d6a1142401a94404000b10f482200c045480340d46940a080080d00610314003142c00e00e0345070b034481c2146400100c101c40701d28594029898501a190030980110341040340580 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 379662652 1250 379661402 379661411
    0x1309020d0213060b16021002010603020901050d0201050c12070c0e04111302070b040803100e010b0909180a060c08090a0c140f060d020a0306060c0c0603151e06080a0e0303041401 78
    0x6005400600902a000d11000c41e000c5c0080300c0c0c0104070000c10440d450500703681c94041d081006071940c509031030456004569450b6001800c2c001603d2500c04c0300540c0c41c00b4040c01044014402444010f820150701500503005460f441d074050b0300036404181d40103404494080821511440e140c9401181c0000c2d03800058140600303035840c40c210407415141240c62200c0481040708991900310303841c2c020031544000e18150752400144034014801c1d203140da8004c14039800000c1040141c030090480c240c5525085469034a80d5003007502c02022003017895030001d00390401040110000144122601d0b400840b03c0d00401c0c038061911240307903000c01405401020175002038a907643c8400c050301011414920140e030707504281c07800804072440c54212006210907824500003088040d1410010b031616030500151b110700345a0761106e5175085901c2040042c000d05003c800d0900c10508540032640382d5101c2c032040e40c139500c500c0c00603244c1000d6099202d500c280001408030b01c2c0c802c2082c0081212000005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 379663902 1250 379662652 379662659
    0x1052e030f15050f0406030804030f0606050d110307151d0103290301051003080a0c0201020c06040803070506180309041109090405030a020f010b0d020d020a0b0a030b1309020d021306 80
    0x20241c482c4000c0c9075040d04041c50041105007050702003510361820440b01004003034116a42c00f0b005014a00000e003440201584950810006500402c081c01d40108446101050380c601400741003810840c1a009000d00740c0001600404440340090f885426242e0f190305101c075011222030441c030f0a6480f4101a281d8100480070340580d03580c28401c40702006460540030b40030041c58203640000d4481840c0c44940c4200708085110078017036a2008826240102e4103030901d00041b803408010303800719a03010900203800904000004020118240304a05440041e620b42e03c590709204010320035041c0a80080154040e40c0c6015400900c020100843c4207003000d110402080c2c1e0200e040ba42242e1583c000206102d400d074040000041c21010031000340001690368002c03503440c0116280080c028907440c2d42000865031031f529944050000603e8050300c604a81000030003802c00c02c08924090766204200c50b840b50003034010410740a8004e0190201507000b9400d001c0079081122141603020380e00c02020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 379665152 1250 379663902 379663931
    0x903030e01050c2109040b0603040308060607080d06091a03010c0e041d100c1205010b040e0403050d0504051c080103080f031f030309030309060503090706030c0e0d0609050601052e03 80
    0x1d1038a081920704c81d9210011401440201d5003054403003841448103008020020754041304080e0300010a0710f14940342c603c14a400d0780180143c9260003c0b0500300741c004503000d0750036840214000f1210002e012403181c0c0a00b45801c13070f69003080002c0020100d44460300c3c82e09041c1c005040e807004001d07607400f2410040c1241820000380c16558101c40b40c6803c00a0500e952010203503a030b140d2005410021545829a224613900c0fa610603a00c8082e400c600140a1500401c241c0c0d05103d40da600038811072070300380350840c2c44d000303031300107034030141c440d44060030b02043c41001624182d80d8029405482c0c010034129900302508001c00a20680c80c240c0341c4031103400055299400103500c2529a1101d0f28118500903203c017865420500410000740108800140000f5055040700e82e1390400007406899800100c40c80403035401c1440d044800e00790a41c040010303517401103400c280680d05981003030740c0721740400428100610801c9114030b411102007030a9002d48508000c214003900380001d0640c0d049003003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 379666402 1250 379665152 379665193
    0x209010308031812091005041509031e020607060905011e15090b011d0312040f0906060302030403020303041b0e0f0601030b0303040b0403080921030d0c0903030e01050c 74
    0x49958034030100a210325501c0380c911240c40418904007030031240c5400300035950b0900420081c241b0800308400c03642d46090142048030060901d14052201111000034040c081001a20040340c2e8a040800300316403600380308012241c2c0b2940145940d290507041c5d100d14003c0c100761070040c0c0d41d55594000f0490750210701035144418040050012900c002800070352201c040390740e03001c0701005040490f102d040781c1e8001c0648000764111140c030540d01d21a0b8000ca868403040303240882010030b00040120f28001200c80480c11503e203001c0a100c2a80c558808900fa804203071001030240e48180045000941600841f0101420b88200801c101e46e480d219441c4044041d034100c40540d040c14140a85568540607101d40d00c43c0070390065292618013223210f8240c0c4a6448050884a4081030400d07031a0344014039401110141110a00e903c503114548076200d900000900001c1481d1041d448651802030f410740c0120f0780c15846141d51544404d006407550f070300c042c0741c0f50301d04d0107642100707207101d03500303044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 379667652 1250 379666402 379666409
    0x20415030b0f01080619051018060906092c030c060403050309060f1b0c0c03010e03091c0b04030c030c0203150702120319091a010b1c090c05040b0607020901 69
    0x10550090401200041a0b6003060300b00d1841c5801001c10495102124594000e000d410411700041959a1103203140c245a8283c00180c641100505140c0300c0511076040b40d001c1c0c510300f00c2e0801001e075840002c682190441e03102e81035084801c40c03041a41d45843c0c00d0000100500c2403c4d00c0c9405080003419050000440b0100c0c0800d00c0401130042d220410040107903c1400401c60003030a04003281c1090503062070b4403018403400d00008038811040303802c1c05400b562030030180091159000300580c07561250828504c40d40610400030002441300d0500b50845822500550300991030788854800711030f60150301d08150148400002440010f840403c8240a101e604242100081c140003400904211012000c1c900c801c60074024090440301c03080f418454100c0e16140007440b0806854242042d00f400000691241c0ca038400009268032148011300304500c0405c043c029140103801d803141180d0080300050030920b05a9414401e43c24954042040458002c084508104c0d4a60004425034801d80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 379668902 1250 379667652 379667663
    0x30d021902030a020c0909010908030117060c16020609010c24051f140a080303010603050114060f07030309060f0905071508240d17091206012102041503 67
    0x249120050540c5009000988003407019524124070040025500ca803500207040c82080f4800c0447c42c103190035400a9001036210b0046178076036a440103003031355641850054100f540240c1e0001035003002a10100c1da102c0d2880c100c1d989810038250240030300c0b41c004007800390520054040e03030404250001d04400c00502c41c1510300c40903402c41c1c61518180c440c041c081d00c44c1003508018034005900e202c3e01d130701c0a85910b0400c80c1d07580701a45000400030b82595100d20001d000000022900c1a030541000e816141501400c0455001c1c0c1d10600c06148680c41920545400c280252070020780311360481080f2a00820010030318840c0d803107480c012604600002c0700d10385d104001c20403601111104e4500d24046506101b0003c0c9040312515004281a00c66484001005000f49007250303242072a55001d943c1080e0081003800e58494950a030780d00c0310540b44e101d400354200c1d5200c0300b12300081c1c5d0342c1680c000c0000725006038440346100b07180288651089a00580b14400c0550b44080c020140f0021400742 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 379670152 1250 379668902 379668907
    0x908120109020a0e09011a030c070b0705120709060504090518030d0b0f090f04080c01021c0915090507060e0102030708030c13120807200409080c0706110a120908030d02 74
    0x8603c081c2c070b02400342004070300868039900100300c0a00d0780802c2945103039040e0f1302c003552559203030300104d0103120f9160020803e44021080c002a56400000f03031500d22044000d40c0303032640301e0880075105040c06219000000380e04000920880d07c05400c60754011103000c1c00450ba51508131300442c1150001d028801f00701d55100342d900403074a00340d2501491100b0948401c41c05003452061181c440c8001000a003103800002000c02c0e07180000d5040f2400d404255200c0540d0f0400c440c4860041c01003840e0603602000c0000c0360900806546c4900f40c0070a0340300c4004c25100d8941017056449202074950141940000d02107070012525032001503110300e03a40d1003016034940c05100c1000160300c0e1600f20000c0d404500d8610000035040c04101c0d58015003003006942c84810081003600140071092495400030304114030503040126140180050104042c140d84006450700001c40342041004880001e55000444480120300d8649410a40f58480c1c076051342d04030384030149079280da4441e0300702d483c255030700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 379671402 1250 379670152 379670167
    0x30f0306090203010503071e030827061201030611090415170a0c0501050912010e07061d1c17180102160501081513060303020321070c0303090812010902 67
    0x54829a800342103100c2046040d541400c0c00300303031f81d0f0307501b4000d800c15101400b00b46d103600c003502c0300000025503100c10b47d00d80d242070840502c120b011068039206610040c0c0e600f201000c3c5800c0b0291424035400314103c078201d85ca140c44d442c0103080601c03043c142c000300411980c265a08c6070b004240c40020300384001d0010903c0d1801c90680c5420740d5481e441c4ea9003145244d000025070740302e12401290800d207805515088080001628640c880c009040998606428004031080c089420000c494194035011008400c5228201d00710540da40280c1d4400030700c802c202e804244c0505a0030007240100621004810f40c0d0007039805692005c401c42600b1005071820030155a410000c0b40d0203095001c51b00007880d80b03004006441c07000040c220589800801c001180c042d05c8201c01d0210b10720800c0350910107140e030707030034003030341b01e50120340706120001c070001280e1a807088102d011030142145550f1881c1036141c584045004101c01c800488440708100b006c3c586184401c4000c2d8040c002081c00140e50340c48 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 379672652 1250 379671402 379671407
    0x5100506181c060522020102071e05040e0109120905030c040e010e01061215060e160c02032a1e060f0d110318010b06090d050c03010921020109020f0105160f030f 71
    0x18034041c60b0300000300b170417004010f0742d021844208607103400903651000d01d910411550300341c46070340049400c2441e140a0358030000b0305410103003201e4000d1076200d00004042208a800d035400e4007541da0140e21165504034541469401042a040390f10b000180103000b030030344a0701b9608035512580760503402004141c10b00001c024400915880681d08000c5c840c50704403401d000900061180c0114078065281031032840c0149185140c1c19402026108550040c030390105030310240c055200740d01d01165071000118189000d005494048a55030740403031440302000c00004d5401020b00113640d640038890b8075003080a40c06146510030000782140d859152221505051681c01114162268140509011952900703001c5560469095030300040c41c0342c0307504207145081841008148c1561804510348203001d00f00401c00e07100f841141007508058140780f0102c1c241d400c40000a90301100a5143c204150700820060081c182018203c04606203992902c1c1410402400b00f41c0c04a041003040c00d82903030303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 379673902 1250 379672652 379672681
    0x80f04121419030f0c12080a0b030304030b0402190e01030308040b0705070218070908060901050403020708060708070e0a0315090605071106060909010605030a03090905100506181c0605 81
    0x71880030040048611032100301140c1100c2c0d49001c0c06004c040701220a13601e00c5003a030319088941041e1a100c1030310762240014640314048801646491800141c081c2c18034001c41140e0841e03030001c01d4213415444980070400301401401e0490400b1600a50000f6016400c4080c1402940646c8a00e00d50b450181400088000e00a12503020403a0401c007941c010703601c00003140e002940040e0128113507a42c0080039114012a030b001504076106140c1008560081508820301ca0380c860360a031960166104007903a580c001c10340d0350130040b03031580340000c600d1807103030501d51480c280081126007650369a859441100c1140c520700420f0300e0322602c1e4202445803d02580390820401e00d0000043e6440e14026601c0d0038018001510a280003c0420801c078002d402c120040d01004050386c400741c0320380c0b9002d4084011341c0b2608002c2c0c1d09160000304102519140c0e14100d54014002911b41038215400109561a80988540c031807103010b0f01c1040c401d50504e150104a2080c540000d090030940d50303040c95003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 379675152 1250 379673902 379673933
    0xd021506121b01020f0f0a0c08010c021b06070807050c0a1502030a0c140114070f0504231210021e03011401260703020301060e0904031b080f0412 64
    0x500c4102644280781c0c200240120300002510b6010b01c1078495000101c0c103004a400c105070321489840003c24843d58041881d03000f00f0b03c41d0100220040e41d81c0d0080c0d00303a400640f0301d80096040381800745d00c00f080380d80c00c4140c00350005107910b24284441c2e0320081d50381c201c54026903c0da0f0000000d80b605050030861900500024429901c0e400a5118002d603248a4003c000b0100450300140d4030802070801908030002c4042c4000748100d031070441e041e6690780c0080321410000b4822105d001c0b0030303038000e2048a041d14030582c10710141c1301980071800c003141c1c210b40d15907400684425200c2c001c01d10500040c0c0f200c1901c1c40001d030346c0301c075a042d07000b4200010020b0034003144400c02c010405a150f00858520110302820010729203011006004010b410411311301c40b1010b0100d00b004074069141d4011410394002d500c8400c030031602d5a0501111140c1120001c0200350100c2161800c4040148411003051140c8401e0b894061030f000240c1c880d8100f640030b00e030f0282501080c4c80801c0840002130000d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 379676258 1106 379675152 379675159
    0xd020904080715050603072121030f0e030a03050c070501050f0a06080f060c0327070e010501051204020f01030b09130b010506040f15020c030d021506 66
    0x6a5110250441d000303c074480241d45a000300340705490044801030028140a0b0400c0c1c0aa803c11100890b00170790644411440d400003481c01d96805900140724140c02000d140b1a0b50142c02d569400050b2868141402416140e0010020513100c2d102010311700030815460780c2001c0001885800d10150443d4201401c1049500c064003405000c0d4550140811160b0381d66100786454501022000d8200d80042c03001c181449029809140c01c03100d40403402c0550b40900307841a0440c48013030114005074200302c8041101c2c0b12000302a030300400d400e01301180342c421140131200e4001c400400091080101c0a03c041e201d9100f580100c40348007020340407400c070342080c5403400c014944421046941c5824980007142d1410014151070441c1e15080c0905a41030600c480384c0007110190000700114440c007000b21845907010403a0424072021071300984501c21643c0343c404801d12004054502 = true := by decide +kernel

theorem cover : BRFrame.Cov 379496402 379676258 := by
  have h0 := BRFrame.cov_init 379496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 379496402 ≤ n) (h2 : n < 379676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
