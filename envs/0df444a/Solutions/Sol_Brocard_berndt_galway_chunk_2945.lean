-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2945
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:12:48.357709+00:00
-- url     : https://prove2.me/submissions/480d39f2-e52d-4ebd-9d1b-1b392d5280ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 529496402 ≤ n < 529676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 529497652 1250 529496402 529496423
    0xd0e030a170712110601051309020d0c0509060d0804090b211506060a0f0315080d020a0c0e0f011404020904051302030705060307020a0303150e07080103030f0e0a09020304 75
    0x801d5104281001d0041c00031141940c4201c1c901d0300400d04910141994108007210030000500380012a07018110b810031100e1011804500800c94000d10741404001c0d44007424012000800101d20b86880032174004940503d81c5550710014002010201f00300203088120030082884250703031550081201c114040c0c035840036820301110b069000012061101d5040c1d0140360f10060f5202511002d5502c00b4050300c0003414010107217000380101c0d500d07130341c01d07024162a03000b000401030210329004020410b4030101c0b40700f48a007083c080e4440c4000c1d00f054600c441e55031400706900c0090203111f4040c051a80a81c06a68a80402d110082c03141300503140d80617400f003280203001c2d5102d02840c0c2c0200f481034a651054003003841014548103440c0e00550041b041402001051b50b008561030000c07a8160501044126100030080e20b2412281c000c41d5117081c2c05070270722042e01d0303210715041d041e00d20175211060341413410001592203c5240301401d03402030fa802002d00016803240c0145800c03c1c4601c0300b052 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 529498902 1250 529497652 529497673
    0x22104030b040516090c08010e06040b09150102060c0306030a0209040501090605070f02011b02060a0f0b0402160c0801062111032506080c0726130f05120d0e03 70
    0x31107488103a4003510550701c1411581c0308981c8505a60b0000c1402000070480c0000d40314018004480501c1344600000e080000103200e9296504128589000101125203518000c003c1c0c1021452104140d4014032854001400000c101e41c2168040e40006008000c1e60056070308000250900134803c5401d0b549410920000030040d00600e070203482c40307843d00700102c50032420003030840341480c400032030790000c082101c00724540120b04e0540102050001051087c2c00500d03440140c031098810b640c00c01d00c00039a884030300007503101210589100d181400002941e88240d5426505140990500b500301505051504500107001c441d180c0c1c0f060b10002400c0000e100041d08051221800781c6080b4110701500504d60885134a9001426042c00d10b5009400c08030780b03020b0180110000105489031a01001114240f45640c0001c0c4004a03858a55603042d03800a03859449828861805034460076000030603c0d2828040c00c02c0000c0700c0000416800604100844004c03030b50149182e018011035003030301b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 529500152 1250 529498902 529498913
    0x92007140f0f012a090e07031e02070204110432120607090801060b0405040c0e1c020301180206030402010315122f0d151103090a050d0e0102210403 65
    0x2030040b480b8a03000007031341c882031502c528142614644100202d582030050310132198200843c41d081e100b240c6004903959540c648150000c00c0401d503500c07200c2890100d44008482d49070000e0080074800d50341401a070400301c2b2304c9001401503001d04282c00403010300281060700c0140d80c0c0c1003030589480d441d840260003103011907030550181040c85580e800400421004d9070f00000351400520324034000300001c9140c8154241c9901030340c02000e02c901e80742c0d1481c1005910400d00a11855030080132020341c400381c00c50700410300020540884c00f0754201140500e4500c444104041c4464003e410589117130345642c0114000c1284030460900c81d0f100301804a039500c0b03100d200d010300382d108901c0c0240016a4494130400004140c800d541c901041030310008031601c84525080311039030701c210119810709100d507410024245000c1e4849000c1004410003403030703000006680003036500620542c2c0c0b1a0546030400c650a440c0b01181320f025034840841c491103010030546020b00ba02c048a0f030381d0b0a06460f980e88 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 529501402 1250 529500152 529500163
    0x2070506040b04060612061b0f0c14070906231e1210020d09060501121a0c120c1902070e0114041e060503060c0913050a1b0504092007140f 61
    0x25138489640390301c000c80c1d00c2c048e581a4000c5100e1030604504405000360001c200da40c02c07070740040030300c5803210361000482c80401604015000c0f404041c4111130311040090400007515407240303100144040b020340e16041c038440b1030070000d00034948140001200f40c14044940a0034180d614140708800710014085000d1000e000270000744200441da603007003428035000b0340d80c06802414000b40d020118800107062921007011945031322030744000307a540d91544a03056004030002e072a03680d0798072020000c0c24219a0020240d0a01c20310415288800400341260341d04254014459540c0d4804014030850707440c0010030400e0200204089840406116881c4a20f0000030380103a4064031410184103d16051002c0303580002a01d9031641080c0442000892106001c10608181955240403815040107500208040600043c001108140c81d4200800d07950183c8190300225103440f181c00c2c49070a00780b659034120f21006e05118104541c2d5100c083c031010080380701941c50303ca40b401e0000d01100900c41c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 529502652 1250 529501402 529501439
    0xc0a0f06020901090f0e01030f0f0b0c0d0f020c0d0e221b140a050a031b0f020c0a0308071205130f23060a0f02031e1305030102070506040b040606 64
    0x1016859081010004d01044000d802030f00200010950900082194030702d1030b41184d8210341c180d0b686002905001c40000500c40b0040c0c2581502d80c20000f11205007001803081040f00c003020042d200358440001d04030301031a040480d4a4000145812406203d4414001d401c00e0040010424202a0701034003140b4a00c2c0540a10641c2c0701c2c01340c04503003500c400c11503806200ea410403000510410440d000d40c0e20030488048148400480c1c0c00c10610321a610000420b0707105117170a0100c03130b1503c50241240604a0200006205110080d607242c102107d4010803641e11000e0345040100035a9554901e80e1843c500404100c002d02101794007848014894000b0301d041c140410540341001c01c00f80b008264800031410704c40217042040d201c9d0716030200301c0e41d980060340f410100c0007208001c100c2c00c510400300c1c4044ae023001c05107140a031400d0b5800030001601c04462000c0b10344d07914000d060a0340506107000c4d1441c0c02007c009008600204215980140314544c0015002c3d100c65004564024040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 529503902 1250 529502652 529502663
    0x804120804142a01020c0310150f0e09011a0109030623070507051c08010b161416080a0807030f020a05100506010216080304060e130501080a031404030308010b0c0a0f 73
    0x10500c9065400f418426401002c2c288050000e04004e00c002c26603410702540220412640c4a2601107071041144c902c2c0301800607490040781641d542c40c900011001c0c01c0d1180110b035440c190038400c103007228020405941c00b040e10340d11602071440d26100010100c1845580050200038060f89202802419451244a00c4d4031030f141c413016107080c01440d0261241c80d80c43c100da5844010400541c00681850445449070700c0c45513190409598049040c101305e400034000080207035004900040802c000c3c0c0921089280351441598940000356110b09510003d4400001000a000440e12600504070615090300481c1c40c40c02240d5203080c0ba080501c007160640d2a40c5006006983d0b07411720800351001190400a40100d0401c0704264072807145101c0c400c144110482c03000180d444e1140c88040b280c00c185410000d941c2e495141a0700c443c19502d0403400180c441c03281c0307000c1c440707040152415240c05079244200c507820105072100345c0e84000c4104c0b8251040d900380d44005041c7c040c17071122251084 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 529505152 1250 529503902 529503943
    0x60206040302060c0903120901120603150b030a15022a06180f0c040f110d0c03050c03090a0b040c080d0906120228050f120105030607080412080414 65
    0x14240207041881c01341070031441c0182045042859680010101110004141183d56600c62880141c545203080c4c040410440d0400c0000000d02c10780c3c0c00b1480d207514000205020081119040540b1100c261f8401480d001500040001d41c801950142101c01401c00c006451541a001c03080d00c0040c0020440c2015031040c000c010340311064682c40840d42c45440d00508080640c04050354036158000380752806150786049500c81100c4a4103ea016824540000b540d01d10300c03c06250003911801c000300340800e05050100d206189284200c134403400106001c3c194034012545e0303011007400c0161003551581d4155074007190700481400f40c0040125145c03161080d40f45048030103054503840007000d54013030348144404000c3d001415524019100100d0200b902d080d500d8200b69542c0c000c00440c0780ca0244046407400c14010081c0001d0f0507140200c04039050b60366400411500818122002000400c80a181c1c1e4001406280d0b0a074002e8484d4200c08406d00000910318a05803c3c0255a944500c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 529506402 1250 529505152 529505161
    0x603090f0115060f030c02010f0c1e0807090e0702070b0a020a0b01061e0e03010e0730110f03010b1f080105030d02060c070f08030a0203060f0a0f060f050403020901060206 75
    0x2440b40e88148000e000803500b11502e41180900404040d41d4240f0038584c582031036040b9907100f07510201038074080400410201e001c4020082003100c00000c422040341c130f0000540740e464005c411107071049503645c0c2c40900c030b5410640c0100c1d110f0300c0036040d0070035845070b00008200b500c1e0985c05401c0d210816402000150114100000d0501040e40b01c5e00622540c2c208851145950600f101e201031801e04004601c90070050100340186607807030b6446858043c0640c045800c1880140d54243c00c030040c1926600c0c440412542c2d58800d49201008140200b074176160401801d249446a001520043c000541041505d02266481c86d083da008615003503005c0700081d83d9608208a503001d428168020050103400401c0071b5078800c0080c10001c03800c100464450100609040a01e503d1644000a00c0d02c1c0e00303188001c24065007082e200f85d4030500714007941020604044460328122a941418088007928080098620040c400c200d041007000c02c001c08800740c0c0740c1c01d44841c02400d041c0d0041115142 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 529507652 1250 529506402 529506433
    0x6071407020a0e091917070c050d120207140618060904050a0c11030c0d0813051515030a030e010503072a030806030d080f130b34080f0a0902060309 65
    0x10880400740c04203c1d07500194020461b80414298991500c000440da00c030510300f01403070a1003543c2c0c012070b445150003c10344100416401140c5104942d5000c4511490b280d60500019284030b00d41642c208000740294013600c4000b98103020f61b00c5c1c0c00f41c581c41c07a000c40f41d0081010b88500b20b812030601c6d40c9070422411115440742c86c101e10803411070091420000900141501c64031050718003000c0000d00808a0801c1801ca80740360003480e405401c50759840c0807084c0c20070103c5011a40803400001c08468030800d0700300070405244860f410b80d03450030510b004c20010f6906420107022242040002c0041c201d089102c0841246000301444c0e41c4e0340501414a002010700c0d20090001d8082e401540e10b030740500d038000e80c501d50450101c24080342c0d10355500102c1c2a001c01c5c44074001c0c100030800400d01c1039483c55846044429294419005a449082c03d10740b000f0040642ca55000581b450000070034440d421581d50741c00c1440c44902040348a02c41d000108503410030385003506980c02005030549401d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 529508902 1250 529507652 529507663
    0x20c0703030f0905150307030b0d031d0a050643110406030f060b01020a060c0f020706020708071a0c01020705071403010603020a0306020304060e190605150306071407020a0e09 77
    0x9000f494200006800c01c804504030040010890b40c035480f01202080c1050300036006000c1c3e00ca005441c0401c002074504000300403659060034040308100ba0800b50046051a1401e4001e90740301800d06440d240d0404c40345510241c0300c40b06119155505000f100000e241e4101003480311003070b003881c140d400b042420100c3c01c0b000d804048504c1985800c41c208005540100480317041c1c1e80000740003509488140040c1c1c00c006404800402043c6031440400c00e142d040b007000700c0b5103402030f4212420b00f0707200d60041c2d98030350450080507081da10500c010400c0e5501211240c40c00000006807509020010fa119800d9030068401180d242d04032000500800048807403011688804038020b01005146130007003001c0c60450b00000d403126170004001414456241c1192231720300001012609032161100d0000a28514030b0012a00d00b420140480e1000601040a81418400501425036502c91250541b1440c1140e516594160028080b88015a403011600b07001018911080c641901d00381d030b9201e0506 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 529510152 1250 529508902 529508927
    0x3050c03040521040e010f091d03041a0d020f0405030f012d09020d0506221a07021204090516030903020c0f040e03181206010b090d15020c070303 64
    0x4028001c10011500001e5036042e445540544401075001d008080f1000d841070380c0100d04400307821400018101800032480c0100c4100482c200700c107130a5030221a1b2581c0e111408040541e00038401804070070300308c02d902c090a20307510a44600c0d200c5211140780070f981101801c0e5942d101c002c9800c000c9802d040c8140e803410031180000300441c4502c070740d401003840d10302406007210b4146040e402200c404141e01ca5559650000c0211004003c280741443e0b483c0360072288010741042e03034003041c0b0b411040d85480c1d841140d480410608520280b15030501c0e000f90050a40c402c41c8603214118034144c51500c000e0015201d004004a01c6260824410340304405086214081614088146020a60128502c14180c800b1078401a000d0301c641d0014000d00701460300746915000c0000c8003c10058001d11203038628600b502c009890140c02c100341512a04244105007051380100414002072a2840c0311082580c40750310105000d49182c0006070890f004440305a12070f5110348400d00c28140c000740c004400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 529511402 1250 529510152 529510171
    0x150901090c05061e0f090d0c06021002090d06050406181218060e04050c0d0c020a1a06100804030309060e03031f060903060e01060305010908040e0912031302030c19060305 75
    0x401254100544c16003401c50811442404007003031711280f090b114030494150b01c000520001400506003040d02e40c0d440c041c803500340903100d501c0118810107030303038005d4540b118402804a0500701c816119040600001801250010758800260950440721903217148402d025508806045806640140042c423080300209011060100108216075202840011440302540d0125103a110506090300398094420410306550610a6030008142d000405410041c00b6009081c1c55418044042288210a40e841500529080c07100e600850060713003040d800c1446841e0010761200241c5506048609580d13100c00103070400010b10000d038034170350091841c9107030300818601024070f0b00c01d0203814002d080c032000708103589503001040a010207500110013184c02c03a0090054551524203031140f544a400386e141c40d10860408281c004030002002020304140911070340c03964442034060208002c10b201c0807a490b1060102101c4992221502c002c050409001c03840101800c1c42c0000c1d051b1800204680003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 529512652 1250 529511402 529511407
    0xf0e041403131e0e0a1a1e15040b030711160501081504020f040b131502060606070203210a0306091e09031b0503130e1504020c150901090c0506 63
    0x50a603002d820004031512070710055a0100211180070150303883d40d01040c000112107003000b80c0d4052980041a01c49403001110340700411903000c05c81113919000d8224041410400b00d1110f0b4101090200d00c8040c40360300060820790780d0401040c0d16801258010001098080b4404c0c89010070040f00a03041004803607640640c0c10200020f00b2068000d000c2d90b610752018102d00600d1b00d45a04459650804441040e41e4613141c0c06c1c10a82c5520400d180702850300754481c0020703071000c6040032507449503003540a0042c946540c803c06c05140c01100059a00d07015504080740760600c00802c44100d41d05100f021900c40031952005070403114258001020203081504c2103a0300d040340c6c1c0c510100100340d040c0c00a403034245030038121030200c4001c85004156080c40004e00a01200001901c03101c0c802c074183da000540c540074000851202507400c100c000410038000d0086141030703000b41603110000b200715941c0804c511004c641c0c1c05015503039000580d40d1115110103200d200d20b00080504001e4402d1032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 529513902 1250 529512652 529512667
    0x70b0a050c1204120b0123010807050714010c181a1c1803080c070b0103080c19050c0915030c01030c0e030703031d0103050606070b0403090e0c21010b04030b100f0e041403 75
    0x110401f07a41142d01d41089038000004003d54010015202c1c074541108043c03000201500503117008081230040340d0041009407400c1c08100c0b0741000c4070000d480c1900038010f100041078020f00101e030409094196a0480c0c2094400511914070951502140764052520300036000d00b0b000e403401c0400717480c0ba814104c08000d844082101c602e803a90442e503020100355590000c0c074440b03d00740b04000d427110748802107a80c1c0b40c0080c4000042d2109002404845107030181c2c440c0341c4012015448141c00c15015040904040b6840d0702a60000744401000c0c00c026110030400c0c00001d052892a8104902240d8608110041c039600041050407401003030030200300500b404c100280090190050040004807140001003c140c8100405001840220110718032410f0000c07030700c10141c011513248142001610140300d809004a0380d01030485106405c82480c06007191140c03d05044024005040d017015250002900003d0b203200398000d100ca5955442c40d820946008600b0000004e03201c2200d50042c4044d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 529515152 1250 529513902 529513949
    0x6010809030c120342010302191107320904030912060204080102030406020307020f0a030f2703080a0f091809022806030608070b0a050c1204120b01 65
    0x60031652811585940b00c0d070721039917000302001c41d006040340c0e8040f40c422421840641e10740e00311480c500984031020601c0800d00110102e01990131002c03080340c3c072505600e25060290f511441820000740c2503421040e26040100f14904240f00c80c812011b001000110f01da540c0c2c0800100c0b1031804840540c80ea05281d02c00500e0030303069002d020302110107200a8410080964110340050058200a548902d403a080c000c000b900100c507c200035000d130b04401e080220000c125210300da07070316842e42007488141c140120b031a0742e030038080c1200c00a1000449007210140303228000045108041c81035845d0a0181c4c000e10051024180906002a1070020711620000f41003001400704016000210444030f030002034a5003420032a03c80741104110800d91501304000701080543e4560b80b014064036560700745195581d2401d214048058005014800c10544150010240c520806c8100c0b10111300070003d03004140d2155004a41600c0740d07205000c10030182c519094010410030101c4041c0f001c0e001c0a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 529516402 1250 529515152 529515163
    0x4020418301e051b120a091e0905060f0301060b03060307060801060906052817010506120a02130e010902040911030105060d0b03030d021c0615050d0504030c06021206010809030c 78
    0x441c0244240484c0c0019130705204a0007030342002010044440d48010382e1035403030a5500c0410900005845000c1c08101c00076181c0d151002c4100400c2a140303001c0c5090782c1d42d0010b101c06030225501a8000e18082050303a001d0280d0000f40c061442c549640341450410503140c44c20b6503106c60140111b98004011050f04605c00c14100c5100e810440e41d01d056140700c50080300118600031003500004520158155444130340006031b840b101c00807154503603d402c01c1020b10302035801c00400405104000038030aa0454000c1c02c03109001d00c844d00100364850000000484098003e841140c1e030200c4c08000e507510f03501421031058251603066155504100100da21841500000c0120a1b1076052000341518104200c0300640314000c1c0454681560703080b0344502d2080c80502d0000c1d02e0509501186a00003440e944009000944410780390103468150794014160081c01a4103001e2a01c0c881c8021841c9400280a40d80756148440e21074a8180000f4001e0400a81440841e0340148007980c11400001030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 529517652 1250 529516402 529516457
    0x1e100206150f011b0201140406020105040327050d140a0302100516050a08093d0b090105150c0307030309050f0a03050a05090a0f03050c0a06170402041830 68
    0x1d00006a00e013a00060703d120180c12490034a070071300020005485270341903201c240a240b19a4841d5400c1d141b80200c11910701010255072243c02540764100014034182d210000c01e1880b83d090345001c0250b1309481030070714040c140140c0260304660401c44003100b03a4130800703521120220200c80b800300d0b2210028240d00503680b88000b8810300340c01180f0a100200040507170203250b03409281e01c0e59520301810071606003444000070a031021035420310031841140194035810602420750b400c503130300e80002c01141031b0350314203546488101040000018001400100700c814003e403000b142c8480b5624000c3e01d440401e02900d83c3d60303085481030b400000d500100700c0c0c8518899150803511145c004d00015841540c550000301d4846007408000100000410a01b61080d4200c90b007402c002d0b40c440003540e200c481d000d0f01c4031340c114418001800500d095030100801002500d0b40300e00c41c244590f10455008840c42841d10a18402c9900a0364500c1c200b500c03440c19105480c20789070400c551010705603909070348107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 529518902 1250 529517652 529517687
    0x80f03161505040302030c0f07051e1f0302090f040c17101206140609130f030309080d0b1509010e09090f030a03020306010f0c02030c1e100206150f01 66
    0x44600090000c102941e10603000d10410400c040d05082c50040d56950040600345014013440a61160510300495000100c620250200094036071040c2d03d401503142d07404860b588500d603c14100b440440d46001030b800030415440c010703a00e105500400216502d107034410340c810390030941c030078844517442009440c3c01490000101d446840311b51102c031240711503400000700490464022028000c041e00140d0811800d410b4030141e64030b0310300a01c50550300c11510713515100e10100c1c2040c0040d40200403180264002d10340094903040590321409a544042000c0c1700c0d041d25204100e10b98a00b8151141d1700c204a0b02d00c6c5c40c41c100c4010300185ca041900c150072403250805900081c20b00105110110850040c0c0c020b880d0303034420500018001350000e5546d1400604403150000710a40541d070300c0f0341318a170010000c04e030001901c030800c80c80e2030040441e1548083d0f1203d020704d0340c4d2142c010061000741590040d1586240c01050441a185140301c0a442407411503c0b6012598000003092208051070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 529520152 1250 529518902 529518937
    0x60909051902030106081014100302090f151c020102010b040b0d06020304082511090403080c0a030b060a020d030b04110a0f0c0206070605160201050c09040e0c1c0b01080f03 76
    0x2e00009004013a0b139030005185d4069001c20b602d07400c410342d01005965030340503a0a94aa21100705a42c2d01a1203800b00940000900740440d001408a01c090f551102501008401c0380d01d01c000400d04440301040060b4a0100c0a20350030115030302070042190f0003009a0b41003011040c0000080d410040d0040c0180070704d82c0c000081403d200d1181c1c11504041c480c1c0307401d0503203812b90540a000c0300c081400181c44003075512100f01242d1034480d0303495004e250541d030382d1200d6454114100780f80703502c0001da240a241d51822200704075240c01c070251440403000d40250050351940c0b2400390a81d0f4104c040c4c0c522840c5404102c4c40b030000464180e60030881c803490800c4e580501c0e180160380c010007400700650b0005000c2070703481c2040407541000744240c4481420501c0041480f2099090320000c4c3c5440b009801c1c14800140d1a0610390301550181520100b1100a03107280404039080524400c078900031603070203c0040c01030020f81403d25004020840040c403000385280005500c034007605185030b480f107440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 529521402 1250 529520152 529520203
    0xc1707080f060d020d0501060e091005011401050a2001061802040b0d0e03130f23030a11060f0c0609011d0a0303050a060b0d0e0c0a050109050f1219050106090905 71
    0x444d03506485d40342d80103000700074035912454059514001210000d0b01d80c0b1908180d02d4014545000d21070490f000b10001810f41c400341e41c010340c2c0756004054a40200f01c0c09100d549407103400760000124400c841d00001070b40702d0815620800d9a48100801d028042c0100002c002c01d10b00c0c58202c0d020f40406003000641e801c920b0341c40328154452940aaa9039802c0c1560100f182c6c45101418400c8401042c0342034050368610002002d50360241c1c0342142e2641000c030241e00811490320840010000c02461703540381404d5074020a00c950042000407250398130117010420542c03400d01c58106c002d8000b400c4005010241c042503552800b08100042c2019107480200f0b003d0300312500410060099414100d0301c0e144510756040092801c0c1e64a03091920507050184140c0c181582c0c0c0b0b4081d2101a540d03804001d080c1014044416025910b0756009403409154106100042c0046800e402002000c50314481c0981011801e60751035400800d0001d00d4505a00c0003d0800212440c6040201c0c207070100d103484 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 529522652 1250 529521402 529521409
    0x9041401021201081507031e0b03030c0a05010b10090b03070e010201021611090a11040b28090e061f08070309020415030605250804080d0c1707080f060d02 68
    0x1402c03400540706818800101e1072010210709030f003108030890071904840c0d40e824011410340b5a06022681c003c41090740c440844100b0703400001c142c01d030180440e40341c20300c2c600716079103042070055043d40ca40c2d64840917010f29140040c2003d46080380e0f4039102d629a410110001c07058400a0100e80511980c4038441007564001e4040d82e0b0b0840c41040c1c19000203c075420400700c1403c070007041c140b207021440000389006500c3d2140602c84081150010f0800d03003021403280d15039100030011490281c0001c0300480e1002060f210b00d080c64410f41e90340003c00d20b005480c400c00940174005074420300014149820441c8040304190010080d480c01c400540c590341c500707400504407100040e400904010f00c1c010b06000000c02e4070b0880384201410051683c8014983e0b100d49154140a00b480000700000910a481030221540142c0030311182850403080724010400ca404c10411103001c600c9001e00c0b070041e00c4030041704940c0500325080c038101ca4035042d08000d100300e600400d62071103050000c180c0407e43d03c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 529523902 1250 529522652 529522657
    0x90b060603041113020301030605060d0302071512090804062627010509030c07060c0804050f01050f0d0606030e030702010905060a02010603060218030c03030408030a080a020c190308090703020904140102 89
    0x4070b02130141c02c802613086000101135402408180c0b0b800703040c0000b01e4045c2c286075018502080d09035000e000820f0030201c0510800d072040710450204604032110141c0500d80d84202c01c4901d2140c010290b58070320742000039000706802c0c0180f050044800e00407400340c90901c170400364085884600c203507840129044400030002c019407000200d61070402080840140040142510001e0104031050305035100d204403001030302c8040003050514103000810841c10802d0003040c0016050401c1400c00320408410305071070b04080710350480545c5901d01080f2291709071040d00803802c001c1001e5072516040d50000303400b103c107c0c0b1070680a540c0004190199620030343c4841d002e91360212066548072810b08802c20b000c02c12020244c400c3c0950103600c28a03103400012035089812400140d41081c2544000362a5a80000c081101554007000242d005c2c000c107000c101d044d0301c1d003017503454001122400c00410340750001305000030a60114200380007503581e407a40036502551049803103101c3c10840e419240a030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 529525152 1250 529523902 529523933
    0x3050d0b1c0606051905030a06020d09081210050604051c0303020906120603121e07020a0306050702010507081b090f031c0503010e07020c060301092a0e09010801090b06060304 77
    0x24072003001041041a410450403100d04403a00007042002d9948081811064403440b0f41c07517070003448140300140c10303038024210050709070100251248654482822076480b0302c003d2841030136000100030200c6910007441c03000d80b2069808504107428100402c03105060340c034032030a072880420100e804051003501140c516031009007240d07440c0c0c0d01c40d000307444c1000c4084d00c00a200b8029000000c04038074484041e900032503000c590014011a4001c14010982d006031030590700144042c50100114000380a0a4007444055000113003500e00b40100030080d101c080c060a10720500603400c2c0a005c040c600075100716850481d0f001400c0000f8a00003071501110101e044031584031109403a1300e2503045805035040381c500c5850b4081e0765407840000c030388990044030314550210040c4014400b0000b250b1052005526414110011184850507c1500c506144075940041c1017080c4c004041c1c10b00c40552401001417800a00042c1ca41d651854503602c07006008074007800c2d02000103400d009040282d44034a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 529526402 1250 529525152 529525189
    0x70807060c240e03090f03010c080103025506020601150e100504061101020403020a030803131403180f0603071119060f050105030d0f08093f040303050d0b 68
    0x54140f4410195125040500c52902c5112050303c0c0e07142e00d003010f0040d400300c2039640d0390340c0460760b08540c204125410b8080f010800403d00c4980e0603090107044c105003068108280d880010103810206400c111592160000c1c400302d04600308205050300043c0030303415240d40c01000020241c0038a0100c41101011540700d03440141e012034292442e400030000c0003038920b1940c03600340c0720001000d07090a0744102d11009400074507541040000c6071102003c0c5070800c1c25184903031030f0104151510303d00c0300501881d488070342e080040c4540d444200c000b005000c0c02001d49140324103a10801c006056408020241000d0040904003610f0882051008080e03c02c0f50b155051182a520b08200000b40741000d907001c1014075220012645207000200039209044c150b841c045090f000110446a414024060005034402c81035040c103609042c640d05400c1e404c0f45200303a13090440250141e15203035101403021040030784c1044180042603122085410140c405000400c42c0600360300400c0b803c29000d8620b107071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 529527652 1250 529526402 529526411
    0x5190807020321012c040f031403071e0c030237031211040509040f060b0a0b030402091b1608130e1506090612040f0b010f08070807060c24 61
    0x90f880c0c043c03180c05050355800e009102c0007000780c002003815001101c00703008401e604080090006610751101650691280c0350141c1d5100b044104000f440d0815207010012661f221000019101400744684e981041440e20398181c03a09610081c1d220f4425101602e04a008108100721b00c2550201c040c50782d181d0a21100380b4000d4508008020013002012400903609000448020400c800103550035520300a00400054840b6a00e000003200420811580c070f540320000b515075580c410807488020081c002c00140d407450113204110800c0802040d006681142001280c9461500010780702030400003150f4490035032003070614601a00442c80b6140303d401c1d0700c41c0c0200e20760b20140b00d110300580007802c01e03400315815101002041e001c3e080240d45c02c41c10900284412031444a0300580250041540e24060a5030f52207610f00040243c00100d400b00102c03008104250381006240024204040a005524203103500103196100c01c02d009060003012460110310395010000f424003032040043c0801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 529528902 1250 529527652 529527697
    0xb0d170307020706020703080418150602010204050127030b0405012022050f06130f1e06091a0714010f0606022509021e03041110051908070203 63
    0x1055500440305940107000f500310000d01503000080a0095170b5100c15142d06186c00d08a004c1d4400401c6120404110740312204502108890800d41d00504038541c00940c3c5c550904001400d003001c810504c41840b840581c00001c162616440003064951125101013103868900748030f03015141c00c44003c0031505002000d042480c45000081c01410791604030074a0840e155000e169080300702d0700ca003a0f00b202226130544214030305103004000888412169900c0b440e2140700300401e0143c00d4003d85040311075000d080071448001075100e8000e00980c03410f00e64030340c20000110941c3c03620500190b0302480c0441c05c0c10400048964400548488000070404075030744908610180c01a0311031800580107008000030a13002c2c034040c2e4800000c218502407511850602100001c0d444540000100070300300c9481c00845648000460041e809844c7d0000350810f81c100704640ca5005100341070a102d4104440e031506042c02201c506900002d05084801e03541c1e64006030700794805d44408540c0b00e00340c6500c04c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 529530152 1250 529528902 529528943
    0xb0406200102030114010e031f020a1b0804030303060e0405071e080d0f08070e1c0204020f0a0507050105060d110f0103110c1b0f031e0a0803090604110306130201030b0d 74
    0x181105d1100b40d891300071194846052644400040c3c5519114000e021030f0f01d03000c06240e030018a0091505c0c6401103007190b0908011122203c042812541c9020001c0c0070000e259040c01020054518888040f0860a040d80d03015651403540c40707806212380d10010388000688000e922400105480c43c140c51500e00f01c20001845d25803946904000b107110303680843c4481c0d1141418041074200a805015500a18079480480d143d4422007241d02c0f50b02001001d1113806d80c2d0b4041c201c038241c22707196192110708502d899402d4450003800280581e00b0704a00c400401c1d10681482d043c1314050381c032051008103480041b000307440d58030024001e401002424005d1a400003440b58580c0528101c05550903000508100e400d505200445501d90701411071030030900d20a188003400b4504080c22034125590640c0e802d8803c1e04203d070921070076040b960400c010300c0596090780d04110011409040c0720301e4940a800e20825641402904040c2d4807041c0346041e40302c00d8a0350140c1034000b040c0b110248522100d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 529531402 1250 529530152 529530179
    0x216030b09010f020c07231c0b0c0c2503170310080606222009131406011404080a140609070b0f130b16050d0c0317150d110a0506040b04062001020301 66
    0xc680e984c142c0400a00d40411580c103480c40d4507110005053341c0c00034a8046140f0b07410f161075400c0380202c540d2001002034541502e20309045207002d011600c9180c0154000501c040c2d80d8000425a0031038000c02c0041e40e00c50215480e081501d413416090808624a02c200809400c1040c81a9411300404140e4400c490700c00362294200860b024003024098500c0b4400351000141246101d01c607040116541c2d41c0115a05510803c03c0c0d10003c2c182541c070f1217400d1400710031820568450b0f14602092400700e000780400d9511254030b000800015160500f880414841c0082031401c10502042075103040404e60301d0100100141101581c654040c00f1454401e030209000c1282c5603c40c80c4200e0f150741d802042900c800c1d9400d51036046a260300e00c080a581810028103600710103501500600c2e80b43c0c4c079a60944019401400d05030744401c80e5905009502280d03411051007004280700422542c40183c049a05440c510701d00f50b11006808820440000415421400e06500210012079100e010350003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 529532652 1250 529531402 529531459
    0xd18061505030c0f0d05150709050a1403070b090301020f070b06030106120f1e020612010e13020d08070c03081207020d050a0c120216030b09010f020c0723 68
    0x44840300c40d601d030105a0b592011499031504603102100740c000c4d51615010240708140604240d5000344140b640c3c01c080c2c0c0384116400004101c0d0f044052082e802d09240282c080c3c07801280b003112107130b0050b0000340e450045100e0400001300001e0042682d49003901610313000300100034440d8482e0220700c0c200f030f0001d008550440c0250302c1e00c0d0001481c05826416401c031315412122800c2c00c51840d40380c800c00c2c080071124114000721150043c00068503440020000000e0a000d000700a505010564041c500f01400b040401040009440096501c0380c0b103200c401070340b00740500d6540310945403501458015900142480c0400315415910107100136082d4412102c95080e03610780e0700c2c1c0b45070680301c3e03000704000fa1000680301210400040d0b040082c21000c100356004440c2c10344014004100101c3c1c0320741045400c500680280040480240a011800d0348040d13019428864008001a83c81c1c116211351030a1040d502910423007440c3c84040481c5040c0040c1005080c90300400d4a001030707034001c04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 529533902 1250 529532652 529532681
    0xc0f0f0314030405090a0203040c0f0e0603070510050a030905010f060b04034b1b09050105090108151302030a03080906150319061e090b0c03011503020d1806 69
    0x401d111900c00c4040100c40c165080203140003078a4880041c0400250801041100c1700d80c2803072004500c04410140703038001842e400101c021326103051700070305041825030ba02544c0203c500d5508544120340100c140c600030f054a14000850022909009002d8101d04260070315080c900400816a09800001002942d000f0f4034103101885415018001e005081c000d040711000e0062140c0c8290a0840c42c03100042401d680c914400c49241d071500c8540341021403d4400c0d08a48030800c2100c042da501402d070051030202d41100380d81d0b2500c042c09840380d5070309410016441c0201c00090310886162442d2000d541c001d8112014104503144c050b0030001d0036a08c00c0190311498000580b08022002d04a400d50409400b4090f8020130140d40080740d0302c101012920a5118940d000603004412903080c0c08864007240407a180603d03003401000100301902e0690070070010401405040304141441e0305140c0d40d072400595850020640c10000d01c0000361103030f2402d4560100c5070901406410202d00d81b030f883c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 529535152 1250 529533902 529533923
    0x52109060603161211030a171803030c03030a0b03151303171501230c0c100c030801140a05060c010f0c0203070218040f08070f17030708060d0c0f0f03 66
    0x2d075603071000c3c2002d9110340002110910309900018011002c0300a0030540602200d2480260fa43c3d440428429401c05c3c40305880082401100c01205c0d030310390021100103601843c074050581c11441d86a200040c02a42d1a907280c807003601140d1400c0103042400743c0a2480c401e10780c142806074120b0700d10050003d90000b00d4482007486080701c011510ba00401403001940c5000260500568160003818000000d0400401c0350b444440441401000c0e0007071201d024241d54044001000510060005d00d142000138506c41e05002942100d02c9506490054ac01c043c0403142c0d0b880001c40340d601c1c40e08a65041440491510311025054100b442c407041275420902c1300f94a05c80080340d90303000705071010b0360113084222281d10481d120407101da00a809844183c070048640c0d21242195409241d040794a10341041380f041c1849070170340c103034000e030510b02c06030380c3ca542000100186100d0014103c1c6104001240c0c5100400c001107400380024a408944804403c2d03841034250180c51041c070069807440c052 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 529536402 1250 529535152 529535173
    0x41505060c1f0507050703080414030c070504180c0b03040804030f110f01050901210e030f0403030f1701090c0c0209100305060c131502011112071101090c0501052109060603 76
    0x40c050b0f9403040d000340e41c1c0c0a04001207504c2c115182440500150740c07101410400c114005828001054503262006c010168240f808040c001103540004002a504400d5107682d40041e0b40d07040320800700d44800c04d81540702d403280e042000c0c091086510082400c01c40c03410300d0341045400700d14140d91030310485032090743c5040900152090721420000c5800121800840c0540700841c2c0960b544074000010002180c0310609040d52460703100c0240c010581401140800c10158445400036150425140100d030403400700c0006002003c0600441c01000d84450060010b513101e1ba480300d0044d070b001440b43c1550300340303451014a12101c9000c00e64450082c1000104100d5146084501c14521080741000700c600d844c403014840482c1501003000c5549541185140307910b40c0c0c018100c00c105070200da1000f400d20000c0580031041480e02d808059044c00441c4002c2505000482c2c1240c0d801e00b40290313503800c0c00e040c400b000da405c829014000c0e507014003404105200098418442e000540c11070718940315 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 529537652 1250 529536402 529536463
    0x6090c0e1c03020c040903091e1505070503040b071a0f011d0408070b06030304080a060b04051f0b2a010f05060d120f09230301060501030b030705041505060c 69
    0x407000405005079020480001c21814241d00070b4503010b01901d0503102046c6c6034001d280c0e111011035107640c1d5180000100b44040811503d0a04141e400c904055140c00140ea680e1512409240304500b032403100411106d091207840541d440314a0684070441d0014074201c1b10701c8840364004e001d1012848403240e0b02074100722442c1c034003601a1350005075450810103070b07540d050340c41c400041c0050b8041c001448005a109401c00090300c845124180100342c410b4104284422508006d01103148000e000403004242d501008040c819120880c190540c0c900400c04032180c00000481202048000b010030200242d106602580056450403003d01064a0305000c02110000f03002d0003170480410440c5203859903000d0780c401d052600c50790405107600c641e03421481c000f080b030040e0f103504a08007040d07a04245240c288650350282600f400c1c104511100040480e0f9a5241c6000c1c032402256100d148141100c4060010002000d0080515a55001d47d02c2034680300c900608851031809001e0400303408070346 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 529538902 1250 529537652 529537699
    0x1e09081c03050105060a05030112030c02120c1c030c141c050304110d02030607030221010303021b0307061704050102090406060507060506040605060336031c02040f060c0606090c0e 79
    0x3c000d80d50346230a40e4200113900c0302d07144500c00101c060058003821400180c4600c144404e01404100c0070784001c8840381d09000c982e030300741d0541e0001d4a840d50f140030002500450380301c96454214001418080c81030010510340441040090540c0d1080401d00c50701d15440401184260320404070044010604028400000c0c01c461000394140c011a0004030520302c203a0240c05034455002c240182c9075417901c21583caa59080e001600160040c004201c02e0b1090080601c1280d40180d000381140391400c00c0c001c1a4034030345c0c07811141c3c414086000c941404800d40559540392802802086003960302d54001d04140c1c09481e0807a249420403000600f82d1400c3c0c49003c04a81c0d02802c0d151450755018010303400030854010031000c2c241003014032001108450201d050001c002c00045545881481c000fa805898040c50b590213640100014000305c0d00c03440c405812510903050040102ca071904c0c124020305103d8100550b070320300c1c2000c0224440d9010040700201d000a6604801403040c0d02c640c03079001d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 529540152 1250 529538902 529538917
    0x170a1101020f0412050106030c0311030606010f081b130620030f0a2006311e140d02010207020a2102060d150308030618071e09081c0305010506 63
    0x1080030f10040000a2008000811442c13091000041a80d201d9171403030180c2055420035203940e107600160b504c040c01e00301b10316900b203082420807289441c00c0c0240180ba02c02c0c02044885848903004118048482d603034190341441a403200c16071001c40c0c494600401c5103189800c041e1285000706411040c61001108684030202d591020354a888240d0341d080d50900c01c04e07040c00c401440d10710b0921844c0c0300e0a20406015480c020f01c4049860440d08105c20300710000903075440c581805407803400014851050308120b8200c954610301ca05c40d0315051880c00708a810a803100b01c0d000c3d081f03482c0c0440b64190300828465108540014446841d0300c2c0400030b4035000e04142525004002c822005442d085e4050081402684000b0405000001141d44116455801211045000703c02d0000526100c44040420044244140014a00000010b28203820440744041c850b11132a840d417040ba202c0c401c40406858200e084030005407540080c510a540c0408507880000d240000100780c41c0740080849000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 529541402 1250 529540152 529540177
    0x60f0b04061d03010c0e03060c2d0c0a0b011e0b09040f110705070e090a0305160c091407030c020c0105070311011418071409180703170a110102 63
    0x50a04100301612240c01241c2140c80005482c07403851a10358090140311600780440c1e842c0710b8400044e8060502d0520080c0641041810501001e40343c280c0740b4403c4510382000b60008d00f280850510041ca4034480c0540521440c01280d92020070710440300010360480b45e0b06036900740809806020340c0341c1000e0303900841c41d62400402c0030346500c1c40c05030051175103001400ca002801081a5190005503400f4800464203900411820480700c615000e6655110742080b0142071600001d5400a04600c50350381c3d0f0003001340c03000d0340c2034040c8041341d07240f000600f0f044001041528901180c1a1b030041088072408002410089000c5401c2d1003c20301441c07641040c3c403564189550741e6000e42d03100407069490105590f98031304602004110000342801000400c0c0d442c08034080030b000160a02c0510341148050140720b000e0088070b41c54000e4402da1200602c10300421030850744070786c02e0800c5003d034400b43c070310203043c0c4101d010701c091a0005c0141185070340718103c0315016048060300740d0148d45400b506 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 529542652 1250 529541402 529541407
    0x10c05030103121827020f04030201080c0405090c04080c030c030c010c0f0c1e140307090e0123090f19080a1413091404021e0102100915060f0b 63
    0xb5510181e4060303000360034106100303000f070380f500038000d0207030b55610050f2040040d4400d1700b1994241040b200b80154607450540c41c004442c09140c05512a506c002410000840700080d00350030040255005040010440482400c10780d0100c0c0e1070f90400c3c000c451890103445da094038245800140d82d0002d8002501030016250584010b441c1c51150b8841900c100b02e074104120300099124400002920004401e030000e0071500340112600e64043c1c00c0120f14805028607007415a40001c1c4940481e08810305c0400c0311001c4030f0260340034090b41c00400c0e2480c4d4501078030300e0710340d43e01c242524450200082183c0080100701c0e441c2e5550812407821500050780909007101203880b0200400d00e055450400319411068904030f08990b078403001c02001c201c030301001d052000d11410b01030401c4101d072506800040d030600307800041801000c0f04480301e0780460000c007851203900a00107440351014448003048000d45c41e09181146888010241d40a00d02d040340c042690401c603840c03c1d0989803200c45460 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 529543902 1250 529542652 529542659
    0x103140103200612040c0b070b1302150307020a021201060f0b07020a1d0402010f051810090801020a050714030a020a080705120409090b06060913020702043308010c050301 75
    0x218840b0750041c01840d40c4000002c0541070312103500038106450001440e000500c0c1500b04105240042d4000446440c4100211804a03075107080301c90300a03044045540c0c0d5807229200141d409642c89000c2d0404030004020411100d4011604030a1503001f03641c40a40d02d0080c0c3c0e051343c2211000c0c09000c440390000c450511404400070080c02c24148013814010b0540d46a800395084200402c90100a8076040d104210031541c3c800c0080ca00c0d10f856003461800d00c0400a8442c07820300300c1600742e600030060200c0b060f68040c41603204800a2518400866494881c1100180594400c81e0180e4240d98240f00780d94401070000211400120a54050140c03031204d540d0303410540d80304020645040c400d260400e088850304c84020001450541d200143d41c1000d86450a20140c00801c090f202d01401c0c480200280c030381601c40d404152821000581d190503d10000e801400107440c444c140d00803103000c640b030308540418040c0b011700240e15407101199035100694262042200450000380c410710042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 529545152 1250 529543902 529543913
    0x18030605130b010f090f150e060d0b09031e03090a1e02040507030903020d03050c04090c1b0c05090a02030403140304151a0120070314122101050103140103 68
    0x10703420001640003411800d0240d111950001800e82018410f03400c0004200048a0540310300c3c0840c501041c2c1c141f02d642401512074615042d1449544151030a40303001503e170781d4450203100c0754280c0c04249040705042c000c0d16a5501d4201d51706030f04040e00e80c1e400c005a00c1001100744c0b031144450b1001002c00d00403a40d94440b14881141c1c80c40316110004d40124010f03a1580201407081d034244d940000c501803d4140249082004107100050520304003c3c40000107282044400b51900070f80082031041c1002d604a0b6110101c00b0003802220100c02c0c1001002070590080301103580032181104991641c40941d070880c0710a40e0024045114120400c21040340300014661190243e03118410710700c4080200400e641c507020366000c0349101143d1206417583c0150070401700c0c1e0381902080310602d00e2064032960b0b900c07c0f0700000d0040b503440e008000d5641401c10503204841a800101900d0f08108061035400c070070301140311441c10f803003080080385a51080c45a11441c50340012803030013030707441c0d52200e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 529546402 1250 529545152 529545161
    0x70f020f0715031e020a18090b0d0201030b0f030111090114040806040f081603080a181e0f1202011e0c0e091915050f01020a050307030e0f0d08030901050106180306 72
    0x4401c1c1213020a6103003201e2a600d01c050800c0141d00d464042d40c030704440100c3c1001d0140d90300204801031034400f00c99215162030402850850f42800c00048a500c000b0004000c1810b02c209c0603450742c20300b10b0070b80c00c1090400141c1454035003a251101200c40c00d895582c440d00071030203640e600b9880b01e170024000c95a903216900c07a0340d0185a4130351611007031081c90500a18810303c1500410036400031312071000c3c0c0901c40c40140c80c1c038921010914040e680d551140d0340000d0410500800c2c1c2c00c03c141414050f142403c034640c564041e030f10304214641c44a000e0b018150810b10405c0111049891b40b4000405000340c0800c1800c981d60564118105030412a24050140000d8028201a6462030243e800c41c03107003c000141d84000881403500e043c04121580705c020320942c1c11500302400e5000054070010550b1641603042c2401d11a000818012902e00049540c03290b600c02c043c14004020712484100441c014503182001f4406a03803511303020f5a00c0720300c2c250091400000c01e4020004030313021350300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 529547652 1250 529546402 529546421
    0x90a1b0e0118080d02100501080d030e0f0a120201060e0615031503030d0b031011041a070503070b0f060f1003020901050c010f02030619050f0906040e06070f020f071503 74
    0x1041c0c2c030004002c505620110070740350401d0300503038002006501425010410700042d490020000d215a606005066888238003c5659000341626004a440c00070000d00c404850b0350725100460b5080209820024020001e890b180c4001d9483c00304041410340d0700741c401d05d00c1400064101444011900c4403000d0603400209110154000700a0403156690244000d1011507070901e80859500050420507040c2401900c80242c2245001c40280d044000c440c2a40c044800e540e244141e2600e035030040711140d22a0940040c00d0b4000024220b0421082c8018a8092034000b60341707502030350721017003805081d0030800e0200340c1c8614264203881e03245200f030300104a02013041c50490304104038844028255080c04034003212840d00030003000668100407408460455050030200310700c51908022442c101c0851a00302c5c012103403580069070544032508202c00f400014800c40d800d40c6070001000700801030300c00003d00103004010310b01c0f6242c0d90029201c0d0030365802e200088000803080f10300f50018686041c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 529548902 1250 529547652 529547657
    0x1080612060403080a060f05030712030c05030d050a0e06090c130b030a05060406111e030717040506010303020106120b01150e060f041505070b070c06060504060311090a1b0e01 77
    0xc1544050100034032003140103a01c2522607040d582040c01d0154140d035146c4d0022000b00c404020204020b640c002503100031610550103000b50aa80c9080407950801501406400b5100000700a8040132550b8032040c42181d4094080116400c0e10503030079258a030035500004550300880d01030f40207203040784031104c1507070b00382d41d001030215400c0740404d041100c0701c0b106490682040f01004203110381c43c040d6001c03401d641c50340285060311051580342c080480c0044583c1c103420100000b8101805190580343d4168055848241490b06d441e00742d1343c400003400124010b50810000144c6202c0c0000c4047e525039002940c80d4a0b82e003002e26a00040b0303052803c0390b04014030484401c1c195210f41009201440501d0750346a80c40d8100b003c00711390320000c00300180c1080002c012050210b5500c090003504000b0310301d00311845903241e003007500182407103400c0594001d1030700300c2c00010884140e4404007100400c0d0707005c4610380d503036100400441d14954418081e128244450544051295003d1a0302d0319050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 529550152 1250 529548902 529548919
    0x30510050c070632040c08070609030303051b03010b0c12160f020402040b0c070e010501090303050f1c0612150e0618030f04030c08100e031902010207060e0601031509050309010806 79
    0x4030707809190703c5484c66450140b0703100c0c903051105002104400801a1032800b0083c00b06610346440103001c103509200241c2010f80d10408604404170f41c14403048180b0082d500503459585440740516682d101c45a110541d100d01c40c4480000c14101c0c0c1a00d0a52007010702d2410f1041464852401c5401e581400306d034015420000460004468400b800004002c2c40003007244504002c241d107071000c010307044a4184400103c0c100000bd60120803501c22011070000c40e51603a071520407083d0009205158039240d43d0405102181034000c3c0c482d001250340c05400401c0b81b00241103d00021504404421803031900304000043e40017440503003d00d81050340b84202c07441d024030034011007c0f0780c0040d0030032619680d008408010362541001003102c072001c80c031010018484415503c40d682d11492401c150131003d25003c2d0400d080c000c2d810780d20400d8010405000200d12071201c0768441000b400100c0b8400d01100d40304001412078071500c04e0780c0d903110000b5498440f80304019103a444000b0f0415900c403010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 529551402 1250 529550152 529550201
    0x40e102303030409060f0f0e150409020f030727150303080c040e09070e090c280e16180f0e040c050d0302060115020a0f0807020a0e0c04030510050c0706 67
    0x1910407400101b440d58243c5140b50300344009070007102e405074004401c1410140c24004500711072210107180ca00c0842e00010b0150725403010480c1591a5004c5603450701421a0000f078040720b61500e14940c51080100600e05000203070640c00720b5680350350784051040b0b03a00091000900684e0b0a9412001d20500c2605007551041d9040c0c3c0c0382c1044509030a90b8005c4942000b80b8140582c050780c02c10000d038003400300c080011020a08800b00032002d64401d608031001c0c00810641150100c014010b00c0c12064030700c1c5000c910400c00d080d1030100c0140000c07190540030300403111001c0c0100a440c903603040c4503500c514007080c3d600c1042c00030300191088200d030f89001130243d85441904403080d00c00e402801089d031420310b170b2812003144840524255049003402100084100008854035a84400c205445100c2400403034549e1010360000c0003400503103014400c0c0c082404000d071040717a100c3d10440e504060729440e807205030760083c1c540d45036640c014858800014219000360a040d0019906140c21351724 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 529552652 1250 529551402 529551419
    0x1b200309060c2d1605090a050601110f0102041406040302090705031017160e150d0f3504061704030309060f0b0a0504050412080408070204050705040e1023030304 71
    0x3e004643d02c401440e51080ca85620041c00451040c8601360744c00d03081c0600e1310b0042106100c004141d00c4440c4c0d641c50002d5400c0e07000f840b158a607054200300b103c14100307c400310706000f075009010310043c80c05000c01400c000e00d4030804550640741d01420020007600c0306081501c2c60b0300083c1600c100040411808074a007007110101ca084811004014000039640500c944100d4155030000003400403500704100d40b80c1e034401a0403104c0a0281d031404504822030802c40041c01d08130754001c0c40110300c01021801c8882010b64900c50305641101510308034254120080b051196124541c0443c8034107512014480f6140c62a6510502074100803664407556030340d0408940d000304e0132840b500d940b4080c07070080e81405c00b201c0014010980e410407150500303403558100d03416402c08440400c500d840001c2c0030050f240307040d9144d460713002c1c00511040c10312600240191b00280907425142420303c3c002952007990328900800c54201d1911038143c180d1081d008102a0660342d0825018801040001544003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 529553902 1250 529552652 529552693
    0x91008030f19030603170d140901051e160e0d0b09030a030e01021e030c04090c0804020f1c02010f02030c0601080c240904020310091b200309060c 64
    0x71110348015941d02d608181c81032008201c0c521034002c152501030b050002074204030120001c4200618429200c100500d1034038080c1c020b40540079029070700503003480312240c015008640100054444110f9071602030a0300c8610030811155044039000c0d801050485034003842d41d1b281801d4002e0304260300c0802c20303214172500324429900354445031320025a010305182d1510a00e46008800b40c001d619118011000d00c2c4201c41040c1d6982d4034040000c00304501d000d40da0120703002006541d1050219000b0014094410041268241d004104900c000340381d038549000800c0300720140c480c9035907413118a038004540811003120000c0551108112706100c2c0d810420002e802030034460001c00e21781ca110300621a050901c504a4020440b00c0d5100a4188440d202580c1c2c0c1400145d9005850b41c0e80c040c03099442e05026403241040a01d05207010401014503413028a0003800c60700d841c90301803075803420602804160180c4501540007400000058904a00140a100b00c4034088420302c5101d101d0003070800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 529555152 1250 529553902 529553917
    0x10e04150e0c1504121101020109020d0b060103060909021e0f030708160e010b0319020d050a05070e0f0f0904020609040612050d0203090d030e1f0c06050901091109100803 75
    0x303501444070084030749461a10801c882c48007800c3c0718141850402411907112246100030b2401c589540e000c00a03074801d5000c045903503001484900581d183c3d081031180e03040d0585400d800607040c40004944192a40901120258068404201004940c800403440d10000c001c079580680c201d040001280e5007001080c0c0688070302c1014004c2c6842c0180f8884030001c0c0b42c0d00004030000040b004002d100101003c2da584481080d0b40140c0c6070150b4500c80c0000e100c2d0f03900c9198120f20788030501c241000300750301c41ba100f502c16440d02c4410110080400a51801601c0c0c9280d01c044604410405802c3c54049990480d1015010b207080405020018090344c10350f40044110010903000c48081c00002c00000824003141d0019519000444c0e000c125410000302c405400d010300e40e01d072036102d9200c0300440c3c00391440744090800885050344005090b04070044059074002d0520010440244061040c21905540301041d10000c408800c14088040c4c001002c60018138201d240c0000d040d00c0500081444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 529556402 1250 529555152 529555181
    0x1207050108130f02100203070b160e01020705240708040602011b1106010e0711010515030d05030603071403070b03010603021201080f121b07030c030c0605030f010e0415 74
    0x4160425000501201c401082000d115008801c5a00400c00c5102010300e0780350140c8000c0307610303800f0501c280d280d44601a8024010ba040030f0411010984024456100c9076560381c5010000401000490782e07460300780a0540c0c4528150891182000ba4892248000750164080303030900e0b40c01d44a0400341d03001540050b0250351500380c0002c1815001000c0301550398181043c50f58045034000040c1c1e0362005014030b007082070041c0003003070000f40681190210340342c00c030300244242e10b070034407000b851034a120001e14001d10602628022050185082d64031900d80a8000d041c160714142d00c031180c003607082c4401505400750280c040303000180c00c40107501031700c40c81d01c02590720380340d010700903c3c4403005030b02c0030764560800010814010400700301036400584103000283c41d200c110440c10f40700b10700580f45c0a202e20403800300004100d1503140f40011240610281d406c0381d070f0303200001e840b1132008541841c80301e80c2da0001849198130050320590003074001c031100c0b003155480804c1c0302c0890390045070031240e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 529557652 1250 529556402 529556413
    0x70f020a021e041d060402040b040f2d0903020316030509060d021e2a010e01090c09150501050a0c0f020d0602070c060f0212031e0f0106030f1a0108041112 68
    0x542c2c2c2403034040c2032000c40f072000211300c100d4040290300e41ca610000c3d00007440345d80c8501062810741e0716038216042e1a150500d0410525000384040c100b40d034007070140c0112030351203170b1040003842c140d61103100c0005d905900698940419103601a030000d60240d01242408003e01981c1140e8980e03001400500d442e20b00c0059403458100380c0004074012000001c44000c5041100d0050a29218501c0d68640302d422070294141c030751200d1050140111001004056107072640c44414071140c0102d610840e119040e0410030741c513074207480e050300b0798060042c6404204200541c0448605c1a000c03040214099414055108107a50002e42000700c1030200340d4810340c01050030014401132003515002040582400d601c0c2503584c1c08040c0d21007040300b4454122280100001d000400415284202489428000d5800b0328111510311128002030181c1c1d0002840c15500b4803081155100b440302d9401c1c0800d0480040c0850001180e890300300030402c440715a85a030030a4160b454040050303001c0c000c110f02501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 529558902 1250 529557652 529557709
    0x20303070905040b31110405100f032706050903030106080f0711161d06011d04062112020604020f040c050d09150b1503010e0414030d0f0b0f09070f020a02 68
    0x81c00d42c4c40d180b003150946c00d0100402c007c103aa5008200d030f128555400e0180d10809060700c1900144503810341d03105e024400c0005140c9810000b821401c050b449aa005c10958454004059a0f400240a14000f02c0d01030720200700c1d286d60000345140e2040c0e070791802c40640c1c000100032a04052a4111911a0001401c0c062055072040c040400c80e00c05008110140c5190900009080c1502c0c0390255108c11b001429081041d00e494100102400e0320f1101d00088650f02c01c2541c100b240c0138041503680e0780241e028089500d20225050f40241d4004000d00281d09006007003100411a008410041c0042002680015810790150b8002c45004240301d200c0401035504981c182e40a00020034440d034200106090f252018070300340c80c1522144805484d0b160b41d5172500f034a46201e01028000e240c071021950081c00c60050b042200141c4c59090240303c82c0c032180e000d1141c52400d640000303a00c10075000000d50058420841c039001c0c0340241c41241c0d40c11903580c01140c96000520f01740440f0420480014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 529560152 1250 529558902 529558999
    0x6080d110102031005060306030a021e0a0b0a081b0c0604140d02010e1b06130308070c090b0f0d02031603060509070618030308040204060315021207020303070905040b 73
    0x8200140da8100075032540c41d12241e400070a070164060070b4030401000c400f184003628100314000c81c00d540a4202d8206810b03032449015029249845244030b80c005000c0440c101c41c504c01130303401910b107036203440500352280e91415800d00f0381c0d6460002078500500011950000030001580218003440c00b841200707060100060400e0341e6110500700b903a0500c1c5000c1001400000c200d00c404505a41d00803460300041f00148461242d40c0c00080c080042da84040280b041344002403e00030b12480c1c0301100580d40c0c107066401c4c3c1d44081c6065600c4400c0e4400491981007091081314240d10080c2540c0c0c8019240070f03a04c154014540069900650ba50200126040308102d8140502454244001c2100540900c0b00700b20794280402010404080046011901e5640041020b07540c0850361002c200410300f8405c00942040c000441441e010317030003003801c0750300100c205d0b801900140d0f81c000d2402d0924081c0009030a512180e0b940007a035007000c50b03541c920700380b80200b101d03201c2030800310b00f015204268 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 529561402 1250 529560152 529560167
    0x7120c060c020120030a1407020601150309080405130e0d03090209090118020d030311040909120c030905041e0c050901021212070305070309170a020706080f0a020c030d06080d 77
    0x100c1d0543e0f142c0303620b51209401ca034000c03064003101c00b42d88980c0c0340e5030b1481c41c00c01f0309800307180240c0c0c4002c3c2100f4083c2858020a48034185c1e50240d800183c442c0241348100c080d20035034a4041c20f40a0104030620060900f40444240881750b00004940610404c880500d08141e5540328000255a81e80c0030742141391503c042034101401c580248859021500b400e5980c05c04013000a1003000714009403410103009405c03c02044400c8070f00300c1d49030340c2c0d12481103000c1d14a50300c04480451202a840b0f02c540d0040211051440c1c05545288125081c1024030009181c8014590f02442c865423684c0c181310118050440340c0081951400c2c0c882910000191619101007803280800105008074040300c202c1c0150503500c1081460701007000c1d1900740064008113402c10001c0c1c0160307900698948010030b00401008105215070844081c43e5507050115150403040c0c59984410820002082980d42c142e00504100070071502902c1c42e10107650b0380907040b1181030340021803c0e00030002d00e801381504003c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 529562652 1250 529561402 529561421
    0x6010e0d0210030b012714130c05130e0f0c0c010e030301030c0e060a0b090f010327110a05010509040c03150f090c0c02060304020d0c0801021209010608010605030a110607120c06 78
    0x110311107603c01e9007806d031405680c503014030604a00c03c82204416a6074074050740e00a5013030301d10b08202c460000500101a984921003001c42450030450001c0e07030307001e6040d000f446440c2c0d07100854103c0e2100c0d0900b1210b80d0124161503801d649034235a0b000d041c00c09000560003140f08028100390503251103c46510840c000b40f542d482401140d900f000300350048000c45811000441d50361200515000059000788002420f8400d420450450300d04a414284405405140a480c605003921010000c22190100134014240000c02c240300007146420642c1160a12201a00b03022401e24200e40140c02840110303070144c0000c05d0001d404006144d15849228070955a900d413004500816401040c0d10b172002402c000e02032103482d00d5000c11b11480d41842000750180c1070007959180d00c60300d0b6521146106603104480b65203004000129144c0c1485404102c54001e00070708169100c1d5205c2c0e4424451141046401c204104491030004001140d03001d0f12000d9615800401d4090f03090550445070b0000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 529563902 1250 529562652 529562687
    0x301050a150f0e300c030f070b0c07090c051c0207020d080d0e011a0a0806040c0e07120f06180608060612030c0f060919080306010e0d0210030b01 64
    0x1040c1a04150b01044091031a981410081c034895205000b00310100492500204555074504030039401d9401c140d01c48490b12001011a4010881d500c101a100c940140740750101d54444a03040004120034005007421304a0030301520050303681c5100c5c03601983c0c0b030b00042800240c0b0018010904845140c1c20302d404c286821011400c100c2c2ea60701081c540d224826018003003180100d41e407800380c0501e07003002180e114100300030312244101043c410b10507004e0100c007a100312143c0e00f0110b090350001a145100d1070304403048442031443c01c400041c9080001e0504010030031010494855444980604968468200c5001070214901141d0102c890303445482d441e4400d05010302080014000550250010021a050000350703030890005031548c4102107140c0703801d005944200e02c09000216450b8032031003529007643d440c8050b04145580c600313811031000300380300414408921654483d0b00d0003610800050108551503c0d26000a290000c54046040000e5100d18800d149941d0002da1101b0049a0b107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 529565152 1250 529563902 529563929
    0x60305010b070809030a02040f0e120f0a030e1e060109050108032a03071502130608071d120102120106031a0904060c17010f3f02010908070603020301050a 68
    0x14480c02500d1203542c60140100b10080f507110019a003e1001040259004001300000540c500301c450240805020b0381c0392900a02003c088408104422607150f01103542c0d1180c40c0c4807001c44180c000b00302c4000003079018800c01040030140d03045426005001c0031190014202c540c0f4214154080d103205811402c0c10f80c1040c00020981b50458504100901e802450b072840c611014018a166019030328014211421040321590340201584c001e16036075400e030345071800054450005030381d6a070003a26450001442d0910001010381c40402c141d05110004114001604000800070f080e070b00f00c0000c408030583c00c0c1c4010001c1036090311a035002070380580000b209060b40000010000713000140302031704864a940c0128000d81c814565a80158608855012035503101e0384201c80344241b40c0221115082017169260a2000281e2110b400090111044c0e8001e0403021040841c040c4038402207042c021a072801151000701400a0780c01f829140d580141c40750b1500c4104401441640e01200442051 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 529566402 1250 529565152 529565159
    0xf01091406130e0307060209030d0201090c12061407020c010e0906060f0d021b030406020106060311091c020405130308010e0c030711210d0e01050f06010c0203150403020c0a06030501 80
    0x808031264440000c480c038100d00324045031030340040c000e9900d0846142c040080e085040008039805043d10002c00d5040b01c1c402e401810041e4202c0d10010000707041041500401c01500100340750f20b4002a12a440104d414000729440c1c06a011080d1000000750f04808465041940e010b0543c80740000116041116404c1000110310284500c110040a48100041c036488038102501120341d01100925840100181030302565142d401c00d018100c015420000c0009240b88680a041a1202900c2446151003404002c000034485109030307069010980591040240c5c1e2544107003485450400c2000c5582c0145203030080442c40142c010304400701c001c60500050503500400e50307a00a0003400e1a0010010f100d0703010745801c0304550000003800381140311b0080c0031160300c06080c1c0c00520020a04c5001d034100c03849402d0f038000f141e8240e111000d0000048896203c0c0d9904020103002500f598414910060f000420343c0c0c040300d041d00542c1c003508442c2124101005504c00800c0e0900d0204030a505 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 529567652 1250 529566402 529566431
    0x70f02030f01050f310317090106231810140409080403060519020d0606031b0f0503060612040605060f0117130c08060f0603010f0c170a0e03030406050f0109 69
    0x5800c4140300c0d00074000d1858030040c81c0c01c815070604240394200400c0c5d003481c5001030409010803809100c00c0e051001182e04108140201c40c10b41d1101c1c4a201000590307060105641c2d0682c0a40070b512018400c1645080061000000e00075000b40300f8100280d41409095031078009109003580c011f51134420031101060002d4242c4040e640e00000102d401e844250018640300c1d04249907500b5503200040007071440020b90301c85000c0b20016107050041000702804d22215003016070182e0041012130103441c040502c83c20085031710410080c000380c102010340ba06403004541c00c0348e04a920983c1c407028058103181403400340f1400082440d042d0b12580f0703540c1d034015065034094406a24104c24190344000c1022002420025040310000c480c420300d000111001c0b1494282c413450302030352818800b081c0f0b2a19500a0418182041d280c10256100041e2149003068000304500212640c3c0d04001341c00f0502803008500840c000c0d84003040c24101410b44448844042c1d014150340340c07414008201c1c810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 529568902 1250 529567652 529567681
    0xa05190c210801030615051906030606111b0a09020a0306140a0f0605030a0b0d030816030c0215040501020717070605062704110406060207240903120203070503070f02030f0105 77
    0x81d40070902080484c5540e03003a003400011ba4000d594005030100404400d440783c801c400b001c5071040d43c0c080c40b0b00d82d55000142c41d103405d8440043c446800030480c4000c403501280d02030080c000c0140c500141c490350707604130204a8112404100000303803030700ca08015000400304144142e4104a841d141c6062401c1f102031701c4030140b4813a0070103004011002800c024a654041c0030001c1000d000c2c51030501c110710b0010322070001107807000781066840c1e002040b018424464500a00000d400030b08201000b298040b0b94994010800c403980d41d003c10038600003a03a0f000c0c5a052603181720f08015128a41881d00c1ca0584e07030b000709524040c003074114140110b210603112101c0407989071402000c103a120350030000c40611550410582181c02c10100284d590360000b007400441d003102685241d041581c40f03454281e0a220600700780010308424081c40032031000d80c0c400185114030300440340741c001c20340d44680c11501302030015141c030042d14200d00154101445110400541c0700d008000780e01e4130384540310101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 529570152 1250 529568902 529568909
    0x1140f070203072a180f0b010219050a051b01110102070203061303030209030607050d0e0106140628020c0f1804080c0a060509012403030c0201050a05190c210801 71
    0x3001c0c0d0341d06180107100c0400701c0c059552180e02c070009080d19440f80d0030301460b06005410826246c90a2203a8920f000c1c880c020350540141e0252071001003401001040c0c104090051700d20303006441c81940003a004120461003480003001c2c604941006100141c40340c42660022078890340100b1503800142d802150559001c1a0340184403400070040c2800c50080c00b034441d6594040c400c0c54140301d05c481e084000380144c0840039600307002c01d604107100c40d07090300d400b03200d83c4842414900004c865850710501902101040900072410b40407880318101620418070001409030700840c0d03a403011800d089800031292001940d1040d035000c10398219841250700108081c05540c0c01140c0c4800d0b1200503c010300505400400502450034840701550080115200e4015600c0c2c40c0901440034601c00f0605100f103903010703110340e02140311540040d1002d600110b184010000100061800c0b80c0801006018110481e40d80501c581c50768648465411005d04440c01768071188050701c20700031781c008002c0f41075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 529571402 1250 529570152 529570163
    0x60a060b0304151d010207031701090b0a0905040f1b0501090603050405030306040b011206080705240a0c0c090c05090415050a05061c02070821010312030b030a1401140f07020307 78
    0x3121a2070a06004c02501c080a0000f0350001503800300340343c1d01a01e0b0314040745003070815500e507990302c0f82e440048440803c0700c1c039042034100d8810001044254403da42c428044c66105000b001709649003018001c405074110311a0aa0f440c080c0103a590210445001d002c05041c1003015041940702c541d507e00000b0981881203440f149020041c3c0d01c40d4004052407900b02109101007529002c4217503ea910900505000c1c41301045149560440303400b401805812190449103007401021040319810005c1c1d038140ca1407090b68078009444500c0388074081d8103c0f0305940c0c0c240c03100c041c0c404200581e01010a074001c0c0081090043c446580c0e60740134041246d6046030480d03960900e001c42c0000c1c010082d44500f000d984007040540902119100800214140c0c10302d012120f40e07004410f071213100c0c4c20b000103480c6852580d103002417180280d0041518074401000c56030801500e9403040d400710000010700c031060751207070300003040540c0091031190010900c894091852a148200070b41c1c0c4d00520001034403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 529572652 1250 529571402 529571411
    0x1050f03011502120d0f0b10050301121e0605190501050907110f0102161a10090f0209220e150a02030714070821130b091e060a060b030415 61
    0x42050080006103a0b0300d80b5251a50740700d2941c0c5c04194028440d0480011082c0d040c44100000b80c5000204c965071403040ba1580c60959090010210106070200001c40d4181e805240d13084410000000d00c043c0c0520500010070b1601e00a40c0702e041d440007008422105070f0905005000d03c1d5660601581e1149203403502290303883e40c1102084c41c043c4524080701c500d510019030070400c03c02c0c070720121501314001c201101c1c466982d10781c1900890411501e01e05480c00240c0700740801d0b40301750450b14003200d92481c0503003000016030014003a200d248414049d042c6c1e201545c01440324560003004a0005008094004240406401d02d131800000b00a003405550000000e8030302402119604100400f00031300796150b241078581480c40303602103040c6a204e0014041c11807903c98440d440d8520414043c4404051586555910400401c0140800d01d550040d0030b440000a4103410120f0541c4041c00e0050007182003410040e000c8901e2030300404a010001c00802008c204000350428119854810026 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 529573902 1250 529572652 529572689
    0x120b0703020309030715050f0105090f061009090e071e0509060d061404121202040b190908030d0203100e091e07030206070f0b07020606030d0e06070c030507030b0601050f0301 77
    0x1800c521445c14010b05210081001d483c100d8016400b451240b92041482c000690725942044481c0a085507018610000c180000f60316042c030149103a49108079040c03140020b6120b00400c010340b1008100340d11240c3c07001c0810003d41c1c10216180c03912041c544150020326042102058038880c005000034001d04416000408022884e4003d058023800c0c5045c40e5502e080600d0081c01c80d0244c503045c03500090480300c400c690000c1500c2200c003103031204075002c3d1600c8510105003540100c54003203101030028541000600700020300003400460109000165203143c8440040c4503480d1540041c010701e04154100b00c0034120000e80400b66004125109030003401001140e4945020303604020b40100b00807031040f003040540600c0141c42849151480c89560b24140f0890340c444040fa807080d499400b404180b200745000d100c892860500203480545030080c9a114420240320b542e00c1280c1c0d5500c50354041041c400c404000540042c400d2a01c1441c00d01e10140b884042c1c00180209041703120f550b4905c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 529575152 1250 529573902 529573921
    0x611030927040302030c15150d030c0803090f010e120318010b1503070e031f020c0c030d02030a180302150f0904050702010c090f0f030b07110304120c120b07030203 72
    0x39140d0345007031244003610301442c00949a4100142074001485071075813220b40c0707006800440b4071034200840245101180f0f9010000d040308000d0b000da0a000141d03920b00e000c0f440c0da80c002c51242a5510007400341c208124041421654000c0c1001e03696000410541802400b02040340e030010301c5e03501400d00d1011701103041c0b0300600c2c2440740d003075002d401606124482d9401d64081c621645098480c01a008010340c04c0c11386508184006d0a4078000c4040c6001c180109580a04007003207010040b03d0340907003204042403411034a0050540540c0c0089001e001d0a030b44004000482402080f00c0008140740d903010a40f0001b0325542661402d81c041411690b90440e0340035076072414401030091005040c11380b0040d000b0014590510700141c0e21034004129440c1051414080f950b42c58644000d103403840c1c845141040c0b000d00810100b0141c0c44002d11030300410000780000d00700710300d0701000b5003845180c0130710b40700200c2d4070004000500d401d000001ca1812010399034000c40c0c41c240507989a8400408 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 529576402 1250 529575152 529575199
    0x91b01020f150402040b1e1302040e0f01090606020d0507020d080702040f06080c060c0a0b1807150f11191716020f0625020f0405150a06110309 63
    0x21072005116288006020807440105075009038002e031010414815841c043c0300d03140d45c040e4001c060907455644008090304044d820256910088100103040036158454080300e04030690300403102040c0300c40144000c48032841070134010012400140002a80f000c8050403901031884064413401004201000380300303020040707840d400e83c01003080141110144c0c0c040001c001c14083ca02c80703807040c903059040a041880c22a0007196000c802403084a1599468031640080201115586905540154406002045060b001e8690f0440365444d0241c1e0400040803840502d02a01c10002900c42c210342030306002c0f440c60305290596468403094141403c00c0444508080304000701401c0020b0146481480034201052082c422102c54020181c140304101080c002c60050800311943c403544800018030b0300c0f0400340031728405000540d00c9140c510000b001c880b8200c45290495000090b144007a02c1c00102042c0030f0030f10360030110000c60701c04600f40e5903030048040c0030b4011500302621009007040017a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 529577652 1250 529576402 529576423
    0xf0903040902030711161d0402040603020d2a0b03040201050724242d0801020a0804060b0312030c09010c060e0a0c0e04050309040c03140f0618091b0102 67
    0x1c0640d0f0342d041c429001816000102600c0303005009104c07610080e104950356010403601d144100029400c1d52440d109104140a842260f0203661b40e5400001603d4603c01030082c1c5015000f0b80c08280c100390800e882c1c100c550184840207031800c02044c89170700c0225058a400907020718000f9118980ca05d030005c0c0f0281c1c80094039882d0f0a0b01c181085007103415421513840081c0340000242d61040d4003a4000101000c3d0140d003411441e484000e031980199420302c0c90110721403807400d01c8499502d91800d82280d0025442e1000942d00300c00300000d105241c001e0606020065000307060143b01034814195a0001800d4410860f100203030b21b820f141e126407980c5000350b810400422006441c050030b250390703121880b01141c10b00314801c000941541050300c1c0d01e10031500040030b036142c828204100001410700351740490070b06640e818414003000c1c1c00c8200c0c1d40702d00020fa07019503080c20a64100103030070343c0d1f005059400800300d100b088010711b40807c1c8030354a004084e00b100803113061500141d080164558 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 529578902 1250 529577652 529577669
    0x1410050706090501060e0108010c020f0c2205070302090a0602031801030b01020f070f060e061305010309020d1e030e1002030d0507020a050f0303011a0403020121240305060c040e0f090304 82
    0x6c00e00c04031102181c0e048401000003000b903071090000583c1c403058003140704826900084100e001c81d04008003400906005809040420582441201c080b01e00564800300003907808281d0610301d060100d0762001601c2c09000660805d01d02a00c980c140d803105180007810592038500003001c59000b00208a0206205000d0f1218562549500201d601da203218050016000c8403110101c0d040c013a00f1a50b0942a0078480d00495043c4030054002c0c06a01c482286c21282d080071040100300c140c0c0a141b042e071440c0c40c0c2c21001c000c0c28203004085c0f07c090300201e4400e81c9250451078070190008121000540441c1d0b0110701356840c1001a41400d21055000c0c003180246001c6409988001c801103068588c41070155a04400880208000d030245010090105500400c0c18110483c014030503c1a545002c5000c510901d0b04524549000c902d400071210a012440c000e0003000070a000c59076010f140c0308813040c2010301e0308201c00c01111002e8050f140240300340020030141c09051040728060041007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 529580152 1250 529578902 529578911
    0x7080306120304080f03091c0302100203041104091a0c09010918022101030308071e031503150225021c050f03070f03260a0f0b0a060f091410050706090501 68
    0x540c1031036103c1e44040c81c01880350700e001c841c0d081c400e94188112300b10b42c0d415a0040c144010081c0c5000c0096001400c1a28242020710608926a40390b00821221038825006514030720101448a201440c021300100104075050026803403503640b01900c0800c680d010b43c0009041d10389095480700a22640340000011000b07001c2c1030b40700281c40e1081c14102c0c1c1c440d03a40c0b00039694840108545c01e900c0654800029503500e00406045442504040c6115803030340760b20708507541d980e9200c5076005564030403400c0355078010508041100043c422107031100c1c1400031301c543c4400c043d8001400b03038030000d0342c664000c1520290780c014060100881b100c070410748011641d41d403e050619a0341d100003490110001107070300103091074824804000c01e0b00c0b0400a5440c2c0144c0e1102c00002e00945551091040e041e035441d45080210360b1410020001808140c45850115541c500000c0c1000301680000c1e00b80481001c0b8641951141603000318080031516040351601290320300324010b407040e03220151256007003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 529581402 1250 529580152 529580173
    0x804050402040b040e01080703030804122001051006031505040e10050a1e02070203150c09041506180b091306050904050c0f03010e0703020918030c01090203120708030612030408 78
    0x4030300a0096a40000400c0f2040c1e03031f902d0780c0a030f5a5070503010050001e8050004507000810107920302c0713940759282c01e2290003286800d600d80032968520400307150f5a03450314148402c0f50b01170f02d43d902c003602681c0b0b028004895940a040a680844c1c411140126030700c48a003080c42006200c4a14a84090481441075080c95400ca1001c0d10314120458164901612081d8200610388212076040740d02501415400246504c0c10b5130380c0754001e1400d02400c004001e114016587d03441004010a000000303445441c1c00c11030b0052000040040d18070407100000410701c00842c0c01400d507415014100c48003851903907585a04c501502c2547c0c00141c1280c82001440100b0402060903404002c1c252415041e030081789080600303940b0184c00424090308402424009801e121000f40e5100b40c04c00c0d0005210703040c8040300c40c9594055001881140d41d200705400441c03505000020390700c250540035509041880c0c0329a80c1d2444041d00e114030400c40048840c040640a00517100141008810703220880ea0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 529582652 1250 529581402 529581419
    0xc070507150e041118240f03010f050603040f0809040b1210110421021207060c030e1909090f020a08010f0b0301020304050304030b1008060727081207080405040204 72
    0x20032080d02445541086407076150484c10380140d681c20b280790381c0200c800d100312000f03003c02c405080d0300c45001c510400f17103840c902d92621401003014034000d00d42d0340e951b50f1421023266075820992b0405440f0300d40810601021980213001d0041191700000020b030b903202d03410005402015074040854000d050b141810440c0200800c1e1151545140c42c1e041c0583e9148107901d07131b0b103486540a100a1803254070031062406541245200075a440940f4041106c40c3c01e2000c2e81c500465a401800080c0300c8000b00704c20140d211146e000d43c4a4103849002e10140a0300048901201a0080b09080d45d030342c2140000b481200c15103c0502900908208140c1c1c0d110018140070741540380d01c0400c0e0710b0622411090728241482100d1040b5000320186051a085030ba03000700301a0003400802924003010808180501c0c20b10100f0f004100588030303982201100102032504031001d8000004031078609804001d0f10b4004242011240b0b07a03400520303512080f034500300c14680a80d400c1650440d1020502040144 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 529583902 1250 529582652 529582667
    0xc221d090c0102011b030e0a0f0f1502030910050c07020901030503031515090f21030406170403080f071214040215030c0a0509060d020c0d080105180c07050715 70
    0x8502070760305036003494006a00f40c4040914014291001040300081c0710310035403101281c801804180c0f01d540a45132101ca130b4040e10ba80040d40e04100a009030b00c100a00d0110034070058a1410302581145400c0c440307640c58000282584000030744510004080b49400d00072241400c0d8000c3c1582078650f160304005580340c0085501c40342c5514040d014880a1030200c268080d07124042203035074540010340050100015a1241e5160802c040c61507c240c0c4407200d20312224400d0b00c9000454585241640080c650403020718280d800300c6c80501404042a07100c10b005620401c800b03411078079078648000c11103c41100203050700c1341910b4001c14284180b00701036031600550003102e2070b0900480c106941c030b020344401c2d01c2d188203000007000103407141d9005102404658800030140c41c01c28100103074100c141d074440380340c20100d50001d91041d45002d4210b030415001d0001030f50382c10340c0c40104c00138610714002d01030320384850300d0f401049100400c8000c22440014000e0600c482c1e0445031508000303000300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 529585152 1250 529583902 529583911
    0x90e0705091e1824060312040b0904060320040506040221071202070501050906010509160f020a0c09050a1b02151312050406030c050307050a0509031002041706010e0c221d 75
    0xb030001340302043c403515001928003080440d0761074042c5401c3c500450340030a41d211325400c40d04070351200d13800408607006813000180c14400d10f80a600d103041c068100001c0300c600810181c843d5105014121000c45105160403001110901894094031010001c0e00c12214590030305201d01c3c0001a04820020f064001d1405086200704440080e62104100f0149001c211580801000e40000d041d05503842030040e10054145401920b0690703105442e401110950703a008800c200c0d0b154428440c03d450b0034820704041101502421600c10030220009444030040307001700c0c1028440d400070a4280340a02e090100450b03000200d1405141c0341d160190642d00980b2030070303002c40c8c909100310001600840c12070b44240070a40c0e071140b8204610000303491a400414010384c0504c038100e61110245028401400500f55140006da40e004441d40024036040050b0408100303102c203074050104020300c88064502e0080c254058034881c0c075011f002007400041941c00812248480072001d165101e1054546004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 529586402 1250 529585152 529585213
    0x1060306020f0c0f1c1d0307030c0503060a09020f0409080f03070903031707140706140901060515090d0b0c130603020901030e0a030e100306050406090e0705091e18 72
    0x90120414100e07449401410788101c0e2201001003410010340302c2d001b41552484c00782c080283d8541c0000100e40b80060360380007115400c490610501081c68100411395000314600c100b0301000c6d400e44e002c00c6020751700141e035074044c40d1554950700070880c1e11815211008806e03240c10f91a890300680c0100505820f100a40200d5448000d400c150b0380000740301c62045036a9211400c440d003a205000c0c0c13140c0d1200c041030350b4650b580c00d044401030304840e12540c040d15081002041e02c4e8240401c101c1c2c010340ba0171480d4803590302004a100c03541c0702d5109004503039400c0340c08042c40e41d4581e14203c03030038400d00c0060664a02c14102c085003403505680541403482c000e0746c0810515138040b04596032641841c0010340404d580e0302d0186c40d035213050100c1c820913030028035010542950380d10112f0300f62030803a00a9010300d078446080c1d41d1280303420008c50005241c1200c00e02c84c1400c06281c0d001150584005408450541100103440d08918284003804020500c00315508419000500c41403020259a800310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 529587652 1250 529586402 529586413
    0xf09020103060f12081c0203042d0506011502010b090403050715140f04060e012c0705011e030902090a090501050106032705240f060102120f0c01060306020f0c 70
    0x40d9070100d0040001a56126400c4507603d130916114580790360401c000d5204a0040e00c030b0794003035046560002c1d40c092440f031010508414150300d518a10f500002c0344940143d418914040042400001d03a5411902035000410340780c20074a100706d0140245002403500f110002c0d05010406034001c1c000c10780c4500800109455010905603002a03034090640e12003c419800089051644100801a04940b00784000150303d44001c0d00ca60959582c0c000c0c03244000000007540b00b414185003a0407160410a1000d096901e09000010700143d5040000c0c0301002c8110018071200d9000781e2001300c800c1d4004101101030300c0d02400f00005021414400c03602035081200010310980617000b44114040d2440d00c00941d9020b141c2000550700070414281e0ba03500c500040850760382c0e00d41462019607401c0d880e01e00000e01c2d001580c1d0035240c1000d03061504550000101d00052a01d0106a2746807040030107101d5621411007070040c3c054441500054142c500c00502a400d41d4400702c010700c15410850140c0e403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 529588902 1250 529587652 529587659
    0x4050a170c0a030c060e130609020a080907030519080409150311030f030a1211030a05040b13120311130803090a05040b0a030209060120031b0d09030b0601120f0902010306 75
    0x6888900c0004c004480303c08081c0603007400358240c0d0114000180c0700b460545000307030506054820540c060070b03103581e0000304e0301540c1740e010066960000d501d80087c083d0610f90355429940d84500480442c03404818503120040061f00f10450f0300030250b0400520125000420000d0b0010040c80300702c07010000050542c6079414045080b125000f0701c0f2000c0c5003040150f40003500d00e00000503071800c4241c0d03a104170400106540010318001c100310600010213160501d444041d48601070300184d810040311225800041480080c403040c044186408598480001c0d041c11181c044d03204c1001c5421445030010030311400003c040c01143c03104460001003155110140021901444450703508002039240c00d20140c141360b00060703042101850030721080392546c0012000c0e9100000360b80002e8000103013002006003c800034a80440224000c0e00740344007038442c050300301401780c4402409045c030341c1c001034016802552003013032952004400b404074491f2001a0402043e4a00e8203e011910300740010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 529590152 1250 529588902 529588909
    0x30d020c16090e070e09030d020d090b0f0f04080a1b11010206070509060414030a0203070b0304050705040501050d02010e01140d050a05010602030a0c0f05032506050c13030204050c04050a170c 84
    0xa80f0107035820400b4006060601c1140d54880000602c50001448100202c840991032031004040c08a82044000b030020782074640b12051a00141030400000024001e001c01000d04440031900f181c0c1c0081038070360310361000c2c0d02075500c50221505002c4d411081e824020a1004c5034044440c0c14909900b42c908503955210151654041c0448054000302c0030f2205008281c1c2c2104074421380c00c0018100c4003c440558000b901c1d00380c0c1604081c80002001c0107100403c0401c02094010701001c40e000e0155604180104030402ca8912000e810070071400e44c042070780d9020301d401c10403104003a01c0e00342c0c1d0b60441c2c02419000d04001d0f94100217251810300000b4a103880071068586100c06a502c1610b140c1ca00e0310740c500d44507996030382030f180750104024400a1a00300f02860001140750342000350300c48140e00703080048030002014441140000c11070121002e0070f607803a2100ba00d60440c1d002415032a1144e0f045840d010b036400064120486001c04206118807482c4601a0310880040307903250b46265091 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 529591402 1250 529590152 529590161
    0x619061115011229161b0209040f0c18020903070801050105090714131203021c201e0309091501090603020901020a0501060b0408070506121305030d020c1609 69
    0xf03085101030005121000541c1002c5006003103080c0b000070300350483e2072509031643c0280c03d13a030100b10a91801701481c0500c2d003050a255540300806040c103c01c44480d0081040e401c8000c0001349005a081c03d0700c0200301c007000400000e03145200030000d90201201111000394040c1050a12900c90300c400010000014001c940c1654809003440031142ca5181003618070a13003035885200110002d2026400252410b16150000c4c07850003504003403182030342400b81c24903013004070700480d01c001d40c41c00c08000d54008425820400703528100b141e00c0002e81244500303004070b540c40b030540696170300320100300780c2c1d00000035104018040300e2034151034594095188480b40220045404170b0011141003005034020341c003603d850101801503130f0b80344030315642e10307030850340150402c164030b00d4085801d120350074003080a4030242806441c82c0345000c446405806003088020803200c0702803461046c0f401000000d2045c0c0360201045107080d51580c0610358800e84400720410011040c10003100d0014441c000e9005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 529592652 1250 529591402 529591409
    0x60b0a030b1c0b040201051e090a1d070513091d010c1d1c0f0f0c120305180301090812090606090618040507120311010b1f0305061906111501 62
    0x480e642d02000e40d070321040521001841a810b202e003c0c49164041c11003112108001d403003802c51640d64140c07031000c1064009a135000001c404c501e0302d001d075100b2050503040c00c2e00400113080080c1c903140a500b41007100c1590303810010045040160300103416001ca04100003e0300d060000340840c41c8403c5084030b242c141c1072071030350301c02c210031050150320f040150703008545826240c0603060001040c1c032403243d0301e14000703021036161a54044003800e000d030310700034071020300600c00031158105d20a8400070720078003411030081500c610403292414159804d40c8000ba21542c0310032155124a246400c0300c0c86600708690004142c024080025014a040c07582d051203480018144ca1601c440f603802800c041800400441ea41e1092110101d00e15417580040400584a0754070a500c0c4d4420301c603950b003502c1c900003045005104801d002d001c420080a00c02815500c18940001d4542d01e45c400140e0500c1c030340c464811a45c20310000440d2041e40803005800c03482508088030b214096000421000440911 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 529593902 1250 529592652 529592689
    0x2010804060f1407050307020601080c03123a0506150f0d0902190617040323041d0609061203181503090706110a151e060b0a030b 57
    0x14002030009195502040e42004010300008201d80440d01180c140d140c203441c00c00205a0120401080355170410003180500554005010010000c070042581e46800102d403100242001c100050818002e0341c007a46075154201034034810300c60f114045080c0010700001c28443d05d06010000703185041c19000881c003039410b00d120502d0040b00fa9141c02c05a003203181405c0c1c16644400c80c60002d40c3c0d039110a00244076800d801e1407031480c602400540b002104074442c901541d4881c0030000030030b8000d003908040c1e902e6000803880203455100241074621454121001b0900a00b0303807808030300c0d82140311030b10460007900c04d1401510340b42d080080c812140c25111203540c3c02007100c0a540303998030b24412460180a0202c4441144450706400240c00442c0d001c9290b0780200c80400020f0b0780f0013407040302694070710040c109100290312103a40117045840b01072040d581f41c030000c00702c000d101824000590131a20040201984500701523825a110441c02070009007440340c01182490183c0c2c040b1a1000d452 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 529595152 1250 529593902 529593917
    0x901110a0803011a13030210030b030d0525020306130c080a0b0403030e030711040f18080706110a05090114070203010e0d081803180f0a0306091a01030f11061e07120201090201 77
    0x19408c1050121440b049082090b81b2248010000c5d1810082d26100402c2030310b0b0075403a610140e010045803e00c495001140001e407803032610241c0c41c0422000d400c06480c0c1040c450030745c01820000c24075240c5900244644c4107000303040040c401c2e031521840c06541f11741d83c00c4c424240714030103e43e40c1c2d0181c01000748c000407246409070401c2c5801e0f40182c06a4019a0000c035844a00351a1204000185001502c0442c3e00150302000c021042c458408268055042d40d4203007503080000410601803496042d040c420002440300c00c04404205a44460303030300a00038480480c481c64640c2e2141d202420242c0800c0f81080411405900c0340440001111004010350030880350b07200c001c04804050710401c0e0881d40501c40e089440d114080031002850080c1404914445540b40030b004009081c52482c02c65010100180006207110402810150704202c451500081800004100e4030500c905840d454522880030403d8241c00b0010700440790085000202d07980c0d212405a080c2d44801e0700003070000703492 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 529596402 1250 529595152 529595159
    0xe040b1002061602011121010902120103080d0615020c040506091320190614040f06080613020d0b1906080106110a050303013b06060901110a0803011a13 67
    0x4900d0b00d901030580500c00070481c198001b0b4541c25030360090254124840168400710111141800c2450040202090440c0b900541c19290085020706010040c041000080c0e6105101c0c00364200e1005840c0e5070f00440d810440c0100c01a56888034540090f01903810400041d58038a41040308a115108505141c5900061903860349010031498040c000e00e1504012942c1e0161281009140c00c5c0110292076103040782440c0014100d5404a0002c80a4840400042c0f241e40c107805900c400300e6009080ca0112911540c0001e260803a2801200036100c0c40820700d24480322142d00710510052064881e01d005487d0b180e50341d10810721a00806011072030700401001100e01c10b00d03034005d0380841c58041d0b590003081d5030345280c116482a03001520504440048030010320113a40030355107440702c0c40b69490240c02c80d0481c201d004100202460302c104404144004d203a40911034820140b4821416220202139a24110805030000e01a0188400c0c80074142c40904660310b044601c03501c01045800c544524 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 529597652 1250 529596402 529596421
    0xf06101e050a021e03040807080f150402180408040515031e1b030406060e010510020706030209010509060d05041208280912080108010e03090a17010e0601060e040b100206 75
    0x10940d20000c61040b0907203139a15240d104801911241070b10081c40d5140e2034802c00500d8040c8a8119000c00c0d00b1946c42c100540da800511984524040c0c01142d80d9558ae40c0009208105035020fa0700d16400002c08220400c40e0410041040c0d86044464000c000d01c0880c0248103404100c5003600c00080070148407501c0f60a1500d0142e0003180d1441c1c00c554581c466180b108a5042a201117980384d86580050103100e0f22601c2440c058603083c3d4441020800c1030070000c0d5240d149101e40c0040c140c0c0080d450a903a44240116400107001401d0242d569112502c1803004080c00c403070558419100300361109000d807107060003034054100c51900328090622815030b813018042d03005043d080d481d603443c0b014002545480441c900d81005848030070b210f600d020340b0142510240342030301030316030001c0101032440ea40c0d0325802d4003a6039400300400803a40e0032424a600414600c01001e03403d104650001035405d41c4145c02c0d009184080d10180400d80b000c20620958140ca1800c0e0f41c0560459000503d0b40f00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 529598902 1250 529597652 529597657
    0xa03060e0123040f1d01060305010b12060a0515030a14060703020702060301060f032703080c041a030c0706050c0a1803020f090a14010f05010810120f0602040302090f06101e05 77
    0x40c2c0c4000004a0140c485421207501d0442c1005d10410303510b8a07010001e214082c400c03007800c0e0703000717503100300001020340540c50300c42d14001c082c1200740b076403080030841c584184040101c40b00f4010701165152030450410901c064004403190b492880b401e070000d02483e2090003626011640139003294116400c0000a84e4008140502c0078201036039500c0000544803580a07a4541000b440c20303041c0001224200103142c20002001e00c6111081003004003c8030b08401500b150349041d0300c41c1c2300d48903190078000c0040d61080d000c010b0201d038105401d02441c01c004100610320180a40c075800c24040b00e425803004d00094a2002035031007100904441d0a0b8280611002d9000260180000d00c2515030000c5802844084c8c02149210044c1030003801a542c020b070b0903540118680f03400c0d05035245440c0e01c5003e042c1c009540100b82850203050182000f100e601500c001d1075000344a0341507440c150903000d0010200301e81480c8243d80150345100c4007409868800081090340c0110507030801c8922090303507107a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 529600152 1250 529598902 529598921
    0x12070510020702011b1e0b0f0601110c0d0f12180807030b0403051b070311040c090e01030813080d031a0f0d170f07112d09100b0a03060e012304 63
    0x500300c6e92220356600030184002d003541840b0b0902e101e942e040c09140c002c1072140003494507050100d495038606940c0c2d00000c0b500c01d002821201810300d00c44c90301d441c00c9903007150040100902c0603884659145508078442643c0d1800d85511390382c61507500c102141e44c0ea4260b11010701540017500105000c2071166000b00303e206001c40709078100a0382600c0342c62900403903600c291a8120b441c0303041042860240520032011011340b810481e800d0510102c1c00c440729040c4001409070000085c0c1d252480c074003002040042c00b41c0740a8450410641381c000e80a040c90032020b840440842402c503d49143c008000223545501a103150f01c080c60717681c1c6030103c8410000052000c0042844002c40c403800b500d00500c031881c8514200400540030100f48130414120404941041003d901c807503210300590001402c40d1482140e0011140c0c8940100c0126155203800c2904196000101e070001d164040c3c006904a0742480c95886180e0b0741c1d41c1858070704041d0710403110314000e050601d0a90714038082e003080e90307607 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 529601402 1250 529600152 529600163
    0x30c03050a03110d050118090519142512050d0815041503020f060301050303030a050a0b1005130803030c0a20030a080412020c0609120f12070510020702011b 69
    0x36070082070024040d64105003a132039841a1101e0040c40b038281c1a010342c0c40300c0b89070480f0a100c81c10b0646e8420340c582428801c10305280700c8550800040c44001c1003020091010b07102640c0c41000b00c9400d540b40440c0c245959249503900c0f400026410303880028a0900c40c3e00080a031400d5040000d04603956000a03240c48031001851051a5003075030b0b035209070002c042407004402006451841405800117030183e11500c01c0e81d00703200400040c2c501004a0b80d1040074410700142030703941d0f1030941005000399186160030418860711100b0307640c1c01038000c088800c0104442940150786841c945d03513a110072141e2100c56003080c4640502c090081102c51240c1c2c3c90310b4199044c40d8468840d00b07240d60025141100024081c2d810300c0240091042c102d031140382c45101604680141c0300124505200780658140103e84095a20316000410310180c1031f4541c0c804207481462a00196401c0c083d0401c14007520349024001c0c0c4101480740c1c0d442260403081c4d040e10355941851004401c0c00051a8850b819a074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 529602652 1250 529601402 529601411
    0x140a120b0111010501080309010e0a05010804080706020d110c060f01080714060c01020d021c0507050315040b0301140a0c030e21040e130311010209150f0d02130e13030c03050a03 78
    0x480c2c8081c05114082c00f6000011070310b0b1185c20000405240e0305000c4140034500c1e800d401d0100d0b9074000a11644140c00c2108035580e4a07403440c01c40001e00c40e100041c0f6400385887e03000318620290200074481a1218030880740302c0c0c4c90710903c5100004003840f0f40408c2d60f01c546410010311482c0400350b081c01d00c004159500304040c10303125a080e03901c4142819461640081c0c08800b040b00041c0000f9000100c910400451130b00340809055448041c0c046900c00c3c007604000305460350349030400003510101130001d22800040d080c00310078850003a2500701141d070600c440000c045109110351500c80c1e503000d000384150f0031001400042040811501d0a28000401001c2800340703005600368001c0308e481c00f89900c80c03102407c0007400b4221101c0c1051076a40100030b90038265441e1101803644200041c0e905640c0d034107042d102c0003548560441c0101d400e00100e074185040c00c958942d0000c950b4400900f0015950340c6c140c6401d0110720300341c001c010441c6199000301081c0b25402a00c2000c00c1e0303003000103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 529603902 1250 529602652 529602677
    0x6020a030f0318260d2007120503060a08031204060e0c0d08030717010608040629040e0106050d1a0711030a0507020a0302092802030907060e0f060408030703140a120b01 74
    0x89140d0044444407001a10b031110b81d41e41d000c0360702c02000c3d022588010b580c07c0c000981e1b07030300b0400e480054070442000004008280721340d840040900c01085181c04036540c40c110606d80c0c8040440807582a11440d14142409800d2000410804080c3c4d00c000e201421102e01c07035551010540000d00990208078a00086655410000450601803c05621183c07401c0c42c052400c0070541d0710480481d800d030301c880e0079041c80ea1030381c030383c81c1c0150010b0484012803402c0081056600520041d40726651004500800c24144800c4050000d48881c208030300c524141e903041401e55108540031720181e4281c0c4100480c1c401a841030b0064104148010b1003801d6035071381d90300028a80102039405410b101c10584106d0088055a8004003401c840300d10158214a0090750854032460184250018401024a40d204070381d1521251002d6003002040d103915251510078050741c9411140d0110081003014000202e411003101c1945c961615a82d00c5580d144c1c076071000350000d030500545080c18800c41c00d50030b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 529605152 1250 529603902 529603973
    0x114070c03030203030a1107120503090a060f09061a0901050111070801021209010b030a03050a2001051501090e01050a0506071104112703030d02130f06020a030f0318 73
    0x1600442c003ea00031916800d05a01c41412a0a002565540350008102e00c0001030810440e15030301c1c0180d07081c080d03140c2d6241c00040b41000080030300180424134000318840300505640c0200c401034061f5108124500040d6044070100f8040381c038896006030b107500104015840707070440209114020065500c0c0958503010310f400e80c4c018801103000018103004010030040c0c24400d0f088901d004034000d14002415880251652041c0c41c0001c08110092000c012041c0401ca800b410320684c60700208141d1a00702515020030b0360040c004c3d800200b00d001c0c006150039240446505031074005113015152031500303003000308a81c0145011201d14900d0040c1c100f140d40d440c41100038400c558040c1550b07864142c414009600b02d24440e03101c502550344d81464160300c000081d5a254002004e0041c1d850000c0c2024450031002c41d03001201500c600c9002040030b0303501148000345984a40c035624490210340350181c0582c0c00c4160052a00702d0100144004901c1d07190107091182c0f0030030b8810601d00d005c12003a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 529606402 1250 529605152 529605173
    0x804120f0b160806030c0f0f0a120f1b0f060c14010911040b040204030f0b0414030408030a0909050c0a08042415060305131106040504050702010f0b04020a02030405011407 75
    0x1042c50988044103201c0303141e001015141e00130701c128060100000c2140c0040c50014080c1354403801060f90804001e40c646680c45190041c0103130451200e0303604a180340414400c80340c0d15040706c00c0f00c609403000c00c0141e42e80c09003000355522b83c00720303582d001d0800500315210280c480058810601200e5a400c009100b84200b5046030300407c9042c2854261030705000540310500c1c040e0340100d10400c010000b1031201010129110362100843c1c003261500d00301400031121030840140c26000c006000a405d10000000740400107190b1151015290341e446510110761003140c61880e140010441603812502c00e80b036865200c0c2c40707402c01c80c860b0f03066007410504254540070740908003a40c4005100040c80c0c415258001032a442c40c00344401d00c1d05603442582042d40150003020020480307400c0790642d42e01c1060320b0180601801c00c000915007120000c0c007034044c05409151461400c003248010741041e008032044004c2980007546043d00c1c200044510080c440c011045d024002d019100004452514 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 529607652 1250 529606402 529606411
    0x30d020723030114191109063001060503070813020d0f150c090303020c060711090712020d09030315050901170a02030102072d0c05040504030e10020d0f08040804120f0b 74
    0x2180c420080d0300b0349080080b0f406c440d03980c0c540840c05100e01102ea45d03131003049881000c010300d00446002c883d000f0500c2052130b07440c001110400001c001140da641d110000d98442c0200703695100c0c081c0c45900303000341e11402d58400030f500560081800004107401c045501e61092244c803a110011809003138100842c0c0b4080060400140049020024180d04000500424104a40042c5081e5260340e034071000c52100f200c414082c00342400024865130180c1c50714044604152015552042c45068200003464220403c402092601d0f1480c000101450196026500b0141000c115a402c1822503d42c6845140d41c41c8903901c0340d4142180143c4084c005049014410b20501c4042c40203c3c1c40310190700074801d028032102480902c240c0114494400f0702044070b00c00e881c00940c5440b1800c048402d840c800302c8403a000110305014600c02d580c001250885070000d50340d4000c0701b10b00100e04840e600d809940c081c16814052105200b501c41e0144102c1081344108100300603c001075560b0542e00e042243c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 529608902 1250 529607652 529607671
    0x5071409010e100e0102010c02010203160c080c01020a050d050c03090c0402130b040e1b03070e2422050d020f090606040e07050903010c0e090406050406150b09030d020723030114 78
    0x482070184c03542c0900900030103004a000940c1503282c080703106104910384c88201010014010070340014400c45204499000c0000002956549144840608240e01c22142e15103c646040f002030b20620ac1070742903d015503d0800a040948039120800c0040d4014140703038104000043c13070000c0e010422000520003001035403006c882e649001072109030041c403d038038411190700c4100b0030442c0240c1e026003540020340044542840100002d440c1c5401541140720030b040800000413034501282c0038204a84880320340c060300d4043c0c42e03200c01c00d00085451011300250084441035066070b05251608000d03520807000342107642003643d1f860507081d58901c15180c000c01b00b40300185000c414282801240a60b020908000752100780c64004134022140040005d40340c140c0d074502241c00c20055401881c0d440c001d1402c3c3c2c020302920307000508519070205401901c2440340074514403031240040b9034403086892500026450000c40c902d80c01c0300007811030025515551390300b460054030800d078180c24016a10f10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 529610152 1250 529608902 529608917
    0x14090f15061603020a02090703050c030f1b030106031a010912021c080a0c030801082d071a1201120b04140a0204051608180319020106030803040503070b010905071409010e10 76
    0x1b8010b200e0f501c07401074882410541402d0401c0544d21210f82265044144254a5030017540c408213079200c3c1d90b40040e40400110400400020903030746c1a009021121510b03482903e40304a1200199a081103074450a20808862000040907207040d80c014034003100e10380340301000c2031180d0b5103ca500e5488011581c0100c0e94101d581d2080c5940590200c0c050300c5040003c01c6404900d001442d001c0122650a051150b01482d000d500c040082c00100300824800481004e01c0507080c18000c00e90300308a00c0780444011031000040d0b042e4103d01d4200384127030080c0e803504640d181d40c0c03126442c0b50b410400b11061071044540400058460b17125023032085551019a01d0701001c80e88005240c1e030405040304007900c54080c0d0090f4a080080110751071b00c07c90681c080076120302c6000a07405030200341e03c054000d980200030001884030200050800c40d202d20b8a481451303807190f215030211142911448001160016052071b1012004004d0250030014106011340e030924000141c90b044152034030a0002c0d854 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 529611402 1250 529610152 529610173
    0x100b13050d0f150513080903191202010b03060c040510051216080106020c130b0a0b12060a0803130501030209180717060307120f020d150614090f1506160302 69
    0x390703d5288521001d40b0b8244410f0803c4100098008a260f13406082d500c400241001c03560f40c100040c1802207806924039441035414100030104903802d205020155080035100074442c5408258107100322402603070a404c25081c40180000159030205a00911504100704000f60001001e131900c00c548145030b01043c083c1c6148000d180c48410b90200c025503001c2080100c00f50307915810034000044815001807042c000d036000405000890f0700c01c0300c60020006410102003000b601c828071400040e1100041d00703940b401d01c1036403442505c4d0040303241c007901c071030034040c0c0e6110340c0003090b402600504c0c5210311081403003400980360050b203054000c6441140d01100005c01c2c442810303480f040450140481515140e1a00b04003141c3c0e807401450b22003141c1d9024119521030803107450305604002107801e1001104110402840c05000d81480641c00c042d925101c0d15001850705c0c4506400c13110a800d5455a011240301c11401500584d0b03c40c605000303001d802c1c0c1c00503044210362806540104001102c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 529612652 1250 529611402 529611413
    0x3110c0d02010c0c02060d0c031d07150207060f080a20070506150303090405130b040b010e06040606120207020301110d020a0e0f0d0b04050102090d0b041a100b13050d0f 74
    0x109200f1800d01104120907005a034400007a5500030101c1d100101d1210200030084000700700c45464101c052481e02501e1030000c0001865406540401000300c013454002c0030107030703541c00c0b00d4403410000038065210043c00714490715003681c000010721804200480e02d2440c1c0b8880c8802c4c0c010549a1040208041c42404010080d42e030300b01009542074002e0807c52800301e910b078403c058000b40141c1c2c40d50b0100e80c20801d03142c40d0608040c0c00c10318081c424102460300d00e0b4050340a01c6400058844413012503040c2c9068440c100440310640c650084040c1c00c810400d0194100c024160b80c955681c001c88030205105034000c00000310f00050040c1e81c0c041c0184090004c00c80d1148450140680484440c0b03d6100c1c04a801002a000b69614425603154034206000e40701c0e214006402c2070894a08504000c80d016406002d144241042a81e81c10302110103c120b2204582014800fa0f814004002d5800528018100c1a680101c81e100c40307915900420070038400c08404403108103100e40e14200340302 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 529613902 1250 529612652 529612661
    0x32703071a0604060f05100203160602030f0a0b0a0302090405100e0304060219050d030b0d0602040b0301061e080f060112060b19090803040302091302030a030e1f090308070303110c0d0201 82
    0x42c002c42d0100401414405002d0728900c40e402028002d0400e00321868140340200b00352103103610a0744441002c08103c1c54080701a41040d10201060411100130802c0c00986000307041c42420301030048800d991070358007000036411001d4030940d03d90046400100083e83c0381d0081528440100d0000c40d500ea29005000f40b40c1540309403202c1c0a94100711240d0001803000c55a01381008241c600414901c0b40400001d034111171483d40240070741d100280c00126011642c014504880701c90700c6002046030717201407685d0703072010f40756100001403684400541182001d00b2031a0b0440c60624200c0c000040030200e44045402d25080000702100102d441d000c0c41c228403c040000a680f4680002c01030300e01195550b59000d94000240f140e0280000030b0b0440300441482c2c050705800404560070100c1c2400c01070100c00c0c88d40040c50250045800140516403500b441c900e1450041e5142c2d101c1c146592585521074009000480416440b019001c10200585000c0d04030000020041c00080d00520400f03402c65 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 529615152 1250 529613902 529613911
    0x3011b08090f0a081810120606050c06070c1b080f060a0207080a0f020a020a03030f11031c020c071703130807060e061605010c050c0f060c032703071a 66
    0x142d00038901e440400300003041d110038059124140d076440c0c10307554600c00c0040d109042d410b84c05c08402820001950340c400e03043d16000482103c00c0250646810b0300b101d140c401c0061014240e030090002c1403400c1c0c86134050900c2180034459003170306141100101034202045038485000c60380540c0751802100420b008454009540d8141145000940d68032200c0900515951000380f01e00b0305d03d20b0601a00030311038008429801405410500d48034134025103204010b40f8501c0000d4040c0a0054014000104495034003880082c030103100b05100705d081c0060741c40901d006109028a41d40001c900310b2020429000c084e103c3d001d1900d0310150861064005079a41c4014610b6004680030402c03144c10203200300c0c00034001e03078503da40c909485250f99410b40304903500514540c0392080b010b20066008c80600558002030b815510650b0700c080d5180d6840ca41650ba0721000c010800c0402d41c0352010003004040218608112502000321031806810b40d000b402043e90b00c8912500f650702c04501f001c00350782c0d01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 529616402 1250 529615152 529615171
    0x2040902040518060315070210020a170703060b0316090305122214060f1b0327030c0616050604110109050d0c0303051821060f013203011b08 62
    0x704d180100c0040d03525072501410114241a01e070125152920a000013074100c80e8a40d805d666070002c001c0b000b81a10b04000704060b4001999004c10580da10078001d040441c1e024408660035500d807800000452030420f210f00d020b100d00c044002002440c10b020801110080a031a26121905000c0880765046030781801c0703940003000002485007640c10095955401c4040d40d400e0344407403a140e5400c130644a8000d21081800c0120300300c4080030800401004004d8045004540e145800c0600c00a003804c0786500310b034503401c07022049144e410644040c01940c0e009240c4040080469221681403c0065805682c502003d254449640d60000c44490003400180e4280080c85200c0c0c03a288400311a50000408010300055803a008110002000e080c0728401006111304c0c0410070405100c41e52100150310a07406540009400d98440c05400350480d0801c00c02000001015008036103011201409400c0c00010b8201180b01070310241318800710003800c10842c406c0c0060594016111041c02000030790b8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 529617652 1250 529616402 529616449
    0x30c0d0803070f05071401050910090b0c161205120f041e0624030b180304060e010c0605130b2206090c0503030a02073b070909020409020405 62
    0x52008040729400062840c020740440400102243c1e80d20440a016080186c14800c03418584c10640c00680180c03200701c21034010750038803504d207001d4503d55080942002031400000c1c0031040c6c0c0000074801b09816650030b402401041c5c2e281d07111621100f10a500181c808110010b0f400c1b080d2110079000364a030346041049250555604030100d0b061003a07690a04090322400007080340f076401c0f00b100e10000a03005040c00100c46402c40c0c0046152000381d0700000c402d40411078851000100e4000d50b60150041c5144c54180f0409564403066160290304101807580f440340451200e12070940a4121a02c00818071810782c1000d008a800181982c1c109810b04182030391050b11480c1c55aa401c0d070701c00c0d0041030302000d90804c042d03000e440c0c1e440f80790140800078001d1030303190340402c41e501921040840c0c260608003c0f00c0b840080c0b040b42c0744404412459400540014002c010b440d54045511718000e040c01d03444540c488160380141e1f1015066a802180510803403070a03605000034181c5007400001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 529618902 1250 529617652 529617679
    0x80f060a0612062c150c0c07050d03050c07091a01090e0112050f0a03020c1003110304080d1503060b03010605091e0606210115020c130c0c050a08030105030c 69
    0x10703403404030008003c10b102d99130802c1e002c0c1d0407030001c1d00d01d2030300e007001c0d840400071002e81403801d881c1c0c2c030501441c10298403a540081d00d1120101c0135104201d98280042c08410302301003c1c00318808001314245c0c14014180b101d01e02d52801008040c01808000c400402c109182a0074088500d038025059414003018038414409003010080850448454010241c1225118103203181400c2c2201d031085540c0c01042403403070900d0380024049074841400d45103400132107034590085040b5071036000700803002c00c000c0010802040841c3c0c05469502000f00c40043c0804010804080c204c4280c0d0044807d070740c82d00e1380c040311880c0a200306030040105642c030b50300a103016002d0140d101c1c01c0850b4401c2c60305054002c5041c1e6140d00056a4440000740c40070000c1215100c144030384164244a40603261a890585501c03017440450150b403003000140001800519071140701001d044510601420040d000c041803001c28010841c00e011140074085066403541010281410404158601e60003811031f0251309 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 529620152 1250 529618902 529618919
    0x150705011a0108190c121a1206010b03010e270c010212090927070b070c05060702180403020c1809060a0603050a0f150608010b21030703140405040501080f060a06 71
    0xe1414a0703000c800059181007004054814446e1005a4503100d07140c6034000d2441044002d1034054810221540350780609514501d981d160320074000e0030000c0505000401007901c008404d250490742c12010001c2c0d90b9180141040501c21040d00c0000540c0309400c0b0010030f5070140084141d11141004103441c10b140503001c40c1081d10058003e0001180c503401c0400300040394a40c1e0810340768110141d03034801e41e50f180300c08103e030091102034401b40048240040d81d844c001c02101c0000742c0c040e02c07030f03007881400b01054966903600070815415400b070720942d102c0350381d50440740180c0001000c00c00c400e0350514076006450a20014800a41b0502d891700a01c041071000450f105959400101c4903021001440e0803141d00c186003203566001d60030801c02040c4d25070190030504910206583c0c1d40c2c1640c0070040c5100c5540413800751607000e5001048180042031040c4003c40c0d141810602d0b141c030785580c0d800803c0850304264422a00740e0825000e420885006016441d00030512120070b215450170420030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 529621402 1250 529620152 529620181
    0x20315042a051c02030c0703030b0301090b04021903050d1110090f0215190905010f0f08191404030201290a15200303060a0f150c02150705011a0108 65
    0x7110700707006001c111540720100b580c804203940300c01c000056450781440031001d0900e0b005a03904801003424440c000d001d900f014810f030108250003803032070012a1500d80a1041034051802130807850f50182c00c0c0840802c9040250300c003a100c03e50744200240010099150a1040c20403c01c010340c1c1c01c1c801e581010841c43c0c000540000c0c1c048071400b1521400c0100300c1c41510032020300c0508a102d0303001b014903035a040f0500104031082a01e40040d010040002110130448416917000400c01b41008a0503a030303520400e00103120302400300000d0382a0409518110813008a90840c0143e440c1d00c0314580400f841081010101c4074411031004e100b445a0000e80e2480705070081000d4281c2442811310864801d2000b081400c40075200f4840c900c107040ca003581c0741e500071141d0900500100b080007402d0005100040d007243c1400301400500b042c000d80480e251000307494203aa0060700c142138070f960040b4000c014aa001e12441c0005000c810018119060590f013403043c0d41813013185810040303005c5d8164503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 529622652 1250 529621402 529621481
    0x914010501050a02070305061e092b02030f0f1b0f0606090a110c01060602011d0304120201020307080c07030606240c240f110f0d02030c090402031504 66
    0x3806903c5644041080307203011203590015040d4418641400901b14600f5000100c010013892110000d507640c0c1321081d6140854001030342c17810b00600c241114800c0c1005603042821a51055074a0200c4400203401560001c030703260030000c81c0006510b54110864006c01000404031000b4102800302c61120a07143c0d440240f101d800750b81500c2c00a10f120111ba401a659407543e102250745591413007510500a002074010040076618000301e80008000d41c80c1c01c64100c2d84603000440c034142c105140104000d228500490551009205035400030700114003030f00150740400c0080500b18914200941903400c645d20404042d400e086400e4a6000030980214150340382d0f05060f10754a01c10715150a45400e03007012040465410071800122661940001d03840c02198142441900101290102284652045500d84090400581c50104c403140c0180d5481040400030b1030038038400c44003240c01da80c0f08883d60f401044110048003480c0c178061040d2525480300303d64884109080d91074142c080d820307180 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 529623902 1250 529622652 529622657
    0x2280b0103060213150e03010c320409020a11070b040509010b03060a09020316031109091609051302042108040b07062304120c08090405150306040b010f0914010501 72
    0x8211a407241040d884c54000d1401102c60744400c0f4803410018104411101342034030039400c02820101ca00c3c401d9000d11003000550500151707105001c0300600c07221b600c05000701582c2c0c00038040001d0702d101d10302c09031106407199143c0042850803034140d00c1c18001c203030300720b21f0021320140014031441d00c41c021000e042d510b001445c552f40b600c4031700020754018840d40c40421560f000101b0480c807803003544040100c0745226107050080014100820ba000e004890340150005041e000044800d00d41c0021040382004030f00b4080101511341d00400c401c0c2c0c0c080700c00c4411107a0001800c111103005c403950307101101041400ca10402c425982c0d048014400d0384551200741e01d000c00e000e4140704c0983d01c0080d00400c88030040b00e0792420011b1943c00e05000300c0d03069420015809034494018011031621000e00d03070011400b0b2801c4545003c01c8001c11028000450410959050504540301008907134062401402c200318198500345600e4043c0f060b58002032019070030420004810076800b0441e605450090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 529625152 1250 529623902 529623907
    0x406050a141c0e2808090d050607020120070f06050601030b04021308060106080f0a150e04030801080c0a0b040509060f2215060f0e01020f0d02280b01030602 69
    0x111003080480c0100e60400c50b1203503007904400e20070b0030070343c0c0326050030801103084d5408a480004c1c0414481c24120120381c1e002d600202c0e19000070f101000070011641c0003041880000e840f40c440c14603001040b1242c41c0175030f54400705200c400300d003000940f603000010701b00d1a1901c100b9942c2c4052040d98004010700903038807200400d8060b0300940021109003009482103440b501d500c621040003906070700c00d801c5107004901c00452001d100313400042c031600403281c4d02942e42d12200c0900700200104081a04120001c00700072807164107802d1502c3c002d9005c2e9035612140d5040090080c1040c048890382d5101d100c00701400c0210005a505580c1103800c11204141159504c00c00b2540e5505051021507102c1081c1007490380c030940310a000d03850594581d0003004603034502c5100c41e0708000781d0300134140460040e5003082403c91081c503403288082d10603c10744100380c0b000d454251608201c2040f000250300450502d041c07511b00c081c40384901101060300c07000e0242070350b207480b5400704042c0805004a07400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 529626402 1250 529625152 529625177
    0x40203061b0703030f06181b0309030815030a080a0309030f0f0f031a0319150b061209010b03190506090102031b0307051309060509091f020a02010b04110a0809030406050a 75
    0x3a0b12400c0100380c0d10030382012007140700316800c0c02030400051008121038540d07405110180702b4403440900031381c980c1b20041103840d60100d031904200b24006495041c0f086091031070000e1501005403905840c0780c2c6011941d07101d1482d010300503080914060041210b10041c0c00d2010b580304414054440c8241800602d02c007034080410500342c80d9030035450300340c03140203074043c0001302d40700740500b0003030190481001d58480e00001d8810746005003409640024144011880560150401d070f4000c0010000002c682e05000086401c0c000800e11074016104e282c810307030081c080148142030748420b211001314551301d07141030b09603040d21110102c1c400304071004c40002c009038000c3c0105c464081c01680b0000b4510b030351f090400c0180c1321034020300c0e00400000c00030491131180081d040c60500b00c9000703000107000e208001c0100039000040010b0456485943d00789003911144100805603107030f140f0a0740c0d038092144c005800c1090140980c0c543c0c0d4010801004200e500a06071901103055290441040c240b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 529627652 1250 529626402 529626431
    0x10e130608070609061112041512060b0903121303110303040e010801050a0f0207020a0308030703060506122e031b090e010c0306050a0609300506040203061b070303 72
    0x941e00704682510540340c0110328203801148000440d080c80d51071018440e20f404626489449400c2c031941030300403d0000348071204880c0c01058450350309140c81096800c4600e04242981e103503500040800f034000443c2500790a0030f000c1c001d03200240000803407401b0042200d901020310f41e803001a184410801041c13002ea501072048030001d1805400601d1656120201c55000b420250b551528092a01410054408107030003941d004940081008003002d1840e110309041d544020100800c150355034a000c540c42e590a80038191122403015070803100c0c40c00036200880800d4400b0007034620100f500000d14584100c1008500303407507200c3c0d82d8481f841c0780c0491003048401d1a41141382964189000103800400541c80210300110980d4140201039559040c015801554050a00080c2050005100a0a03180712401c0c051260800240301e091600d8501d1000001c4c108080b9004c0d0802c900340401e500e01040743d00d801004a0741d001c0104052080c40f0740303061140704002024191501d050162101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 529628902 1250 529627652 529627661
    0x21303120203160303060e130f06051008070b0301090b0904050a06020a0c0803040605100515090409020f040213180612030e180903040612050603030412060204030c06050414030c010e13 81
    0x1002c4002d20000722020f14000e400b42055020b1f00d403602145800094000c800321511008407038100d01015602c20058895001130003004001c1c04501100c204005100c0404010040040441c140c005e5240c2d4148402102a944045d002501c1210618140000f1400204003055440d44c000d00050766800102401d4440150000014203000c002100700001d0049a03000b041c89011300c1088695200c2d19041004400d00d40c000e009050302c1c0091104641a04065000c45510b07070000300210400b0000700e0029060b640240410707044404040701c200800c0941c86550664172840c40824010a41401110820804165406410801244c40c059496103c0c642c1e6120080e040841d001082e1600805950f541d6126100791070005039184200b100100c0380d80b180328051207006020310324262800ca41d0802c9904030740016a803142c1e08100000020300250081c4001b0700103602c0d015125458409085221102003400d1400381c1c018100e440d040d682d00c03154441e40d159003140c00181c079200c542c51070030080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 529630152 1250 529628902 529628917
    0xc190c0b0711041d100903050d0c0e060309030415021b04090f02090109051501030b0901030b060a1e0906120f0308090c1201022212030507060b09041a0109021303120203 74
    0x5140c1340305180e108084440030007501d50524116410000d40900103021560400d0029000842c1801000780c13000d065009001400060b160100165041c480090b203141d2041d1680070069100090030450310f06c0308112082032125170300281c038014008071054040542141c080e14451a9a0104481089199801941040e40103051110503603181c041690080ca410b031801100403c0702010040d43e90300c0f9003d00012498080c081d4142e9034a541e50310004104054213032076020040c07080111b0080c028070f000002211440f40c2c8901c00c98600003144040380c20301d4000d00342d8604c05004d24000710b0300098080f10714983c14035220380c413581d455007068105010a21a01d51003010101d2210326482c05402408400e815071151303001c104440700708541d500c461031285035000112408101c2c0420300550141001c14020800422110441c10010702c00c0c0c40308840c202ca040d03d1400410740e0040200015a024191616086181203c001c064600c030481c244402003800e00e0b141e01c1e44e1913040c42441541c0030f8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 529631402 1250 529630152 529630159
    0x504060f03180f0b0603160b07020f04110d050f060907020c010c03050408013b061902090d1b06020706050f0d060905010608040b060f060d0203070c020a06050c190c0b0711 75
    0x88400c9032408403d00716003035504e07a204c0c0c804d4607007041910f079504600c47e085480140c5001e10b00718244c0c0c24018031740c00c401d41d016030056032140310020158503840182280c40b103170361000426141c0a01c040c2c6014402510845c010460007080100346500020440104882400c25000180b41454111001d02c00c0d41c0040045500f84255611003906550b410112185480c03035007a90ba403a0070300c0000300541c44581e02c07007059010b000465003450014805404d0403014203000351810106402188103800841000c481c0c200e91a00210700c0040c0b601a03c0f0007a000a101a08045140a50041c000e000c1c0359544843d02400143c14044400d5a41c090f00041c23112041c10300256030340300e08c081d108510845050f9012034100001500ca40f40174480040b400e02c0080c0500e04124041521400940000b0111400c1c004546a09030140e41c4030708481004040543e5010ba9400e501c68226040074490021035021a4000d421000010100e603c4031058802d1f14807465145c0b0114100003035419030040342d081c0c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 529632652 1250 529631402 529631423
    0x518060721051b0d0c032f0f04030b040b160810150917010501060f05041d0a090501110307170609011a0f19030b240a0905150702010e010504060f0318 66
    0x3441134003500500740112490300d0401c0460018004100380f041c044a80c405c0242107114111100741b03d64003d04911b800b055242e904194590f070360300e2010304003500e045e5400c500d500100303c0d240e600548002000e99040ca800740650400880540e850f111901507603079800e1925102d2083d1622a2071100d00500340880d403541c00c0b100103080346000304001c4c020301d40000c459106140c81e59009504039800c0314107103c1c080000c00c0f81210354088015015000c00001919100c01d600414000d0145d5020402c1030004580d690038540b02c05810f443c01d1035107441e1000c0d1441c3c00c112295488840460440b460400c0720100100c40303134484e0500b44541e00030b044030700c0004034903020340e2510b41002e401c1a0302140c078100310310401242003000001e24010103500101c0003c8600344400c1c5910058149903000342840c01c0da02da00c0d000003965050030122000360751354010441ca01991780c08818048800000e09000e0b19040c00e1850042c59039084048a0702030503102d00031b56001144080b2501cbc00a40c00248914 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 529633902 1250 529632652 529632667
    0x9130902010e01050a05090d0602070506040b06040b03010b09150a08070b031006082401050910050d1515110a080a180506090303040608090c040518060721051b 70
    0x400908449200380d0001e240d4800148140d409a4202d0714640403946580d801d040c0c010301005079003030580030200c6140340c080c030100d40040c008114141c01544142c81c095910710701039040c40b0444109e204803e00c80ea042600145c0d25450744c04425400158580000c03030940340c2c11000c03032204601030b809580341e8031411000080c04160040a035000b05200080c00d03030311560700c0e981244c44400946035021034281520400e41140700e808900264500f040c1006402c0442003000a80808409510704d0040762000544807820415403144c0104400d40c02c4010914508020001a00014032000d0b002400103024000154500400101c0407003948055019a2020f0942e001840412148213200803d0140b20001c00c0d185002410356801c410041c000b18145407500808844c0500040c0c240c10041c016211034217003030784881c050207100d8001945000c0031452202a91454050700411940c04c214000c6c000b503c50401000b900c0030003c10310b00c0c000c290380c2c640002c0700345013500001d202c1051501c00100300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 529635152 1250 529633902 529633939
    0x906051f0f0b1b0f0a030224060609180703060611030a0503060118080109080a020c0a03030806040f060e04080910030b0603040b0601020102161101140c07060513030f05010b0915090a05060609 84
    0x100600d80c801d60a81302544100c0e6000101d410001e01c03680fa2300440400007509c903061500c042c012001008103203080800450080c40000c03282543c0c00400240c984606004254014038103104aa10000007149410032092009006001c05840b140c100100082e0102d00c0300c21070140709010300003250003044071340c000d440d01c0140c07035000d03604560240c0a0011503541e24901001c1e10313400c880e015160b049450741d40900704030041807020040c102c03942e55042e0200c1c81030392072980d162045206021035559a1842810416411003000c000ca0403d420041c000005031102c1040e01d81090f800341c80d2040320344a850040c4e029004802d80784503803114001030314062100018111510000a0303c071000c10449100c000020340c42008800d43c1d290303124034800c000461150b801006484049035034141255129070305c0e44610018881c0c10350300c40e03442d540454102e18004203030540100c540d000c04440c81c030103074010407496000203024483d20380da07910000b1400c0d2286022a8030080d40141810411040c03c1c1c40c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 529636402 1250 529635152 529635163
    0x51903140310061d151303210207290a030912120606030207021c0303110c0601140603090c0904110a0b03090609030f070b04030e040906051f0f0b1b0f 66
    0x41d0b60001c2c8118050601219081c020f0901074400a803079070b001120319024140240e44203806c40b0012280c80040000410b06201c010000b1080060001070b15404102000340b5004064202d440c0c82d4500e005464000d500400c9846200100701c403d21780c036051041070030341c01400e50803809020404c44428400c00198000340345180004c5004c4100301c0c80d80c40303030301c214224012500e0080d007102d814105030713100d51540c1220f4040d45119180218500020017000289030b0071803524030016500100040c809903a0f00f9104252216040d1307101425072a190503c50780d01d0101040b95802071a010300800e003400460180410707643d81c00b4100d0f540d000d03035900c0c64640560048070b030311031180107681c00310b603000b41d000c0102d038910044641d40300d0804d44940c03a107946040703015100301e040c00703c40082000705072507601602401da030040b10001103c1c41d00310700d003040034503103540c0c0c0c4030742c5e41281c83d010302417500344240100a441850b14901e0b117564100c0200207152000d5003008001e80329060a404c01403000286 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 529637652 1250 529636402 529636409
    0x10509010c080c09040b040e030a020a030207050108221106040f051f051b010b090a0b0906012c1207090903022104090506040b130507110307051903140310 68
    0x700200511444212038068003076800e6801d8480800c2018000d01d016008500800d00003480000e455480c0b044c040d1440e4401c0480a01507003001c03205009141e01840f08000800080c2084080d510309528603024100f8002c482e01403201d0701c1031000b070900900e0f2030b103403005a0025000c4c43d41d480c0c441c00c2c0c0d6841000788e845000c0c4581007038000807100c0d480c8098107160900007030715454100340300300303501e05c4151800005080d101c2d0342e620344c403000310f5071021a80e50140503105c20004242000100f845541c200007400c450500269511035031200c40c002c4200c40401261b0215070040102c2200000c003400d402d071690306490b204045000c45c0c4a1440d81c4800d105c05d00c20f400b100c5260311200b281d00020003040d0000c2d8104101031000700a00f018603001103510a00040001a183c154000050404110881c20f1100242d80e0000c1040c4c194005846041e5441d48100560800d1015514980c1c0c400b403a201002c80e220800c25510101405007410302c01d44a0008101da86034034201e40040d0500e0041e20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 529638902 1250 529637652 529637671
    0xf0201120f14160212030402040b0d0c0906031e02030618070302090c0d05010f0605040303081e041a01051504170a0b0415061d0703110d020a051c02090a0e09070b04080105 75
    0x103c2c400d44c00001c0744a0340101903003511741190f40c2c075000c00006009040c4425000760210341d100f00050302050340080030700703400880000c24500310f04003078021500c98900c858240d150004d00c41d000d40c0d400210780ba8480003000d0420680d90500c04c1c1c1500389030151340001c0d00018491f0034000c03000380d888080c1c901080900c108000700d0781d07540781d205070070640e81c07090501092040000b440400e10420b03451750300020004100c003880000079030301d01c50701e0380840f02594003050420b083d0001c068100d208900501d001c95005503100404030064100340724601c50f100b0711000401c00c601303032098140451102260841c100604500d4141400c580c0701115080c030b09a424601240070408031281440042c480007014010b048581d40c0310703026070003000b8582d504411078030240556800c0c059980024040542140c1e00e554403030030044207003421031402680a00c111401405810381b9615000d140c542241c04000031003041c0c2d00d5481650341440790a4210326552640041c001c250b041c0150042809491042c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 529640152 1250 529638902 529638931
    0x6041b051206010e090103062003070c0c05040605130e0a14070e07020321060d020a06050c1509030a0f140712170106020615060c0601080601030b130f0201120f14 71
    0x20b500440b00c50f080003c040c1d502451160050001c94520b0b8000a07160003503180044c1000b9007038000c0c12180d04201c1c2d103800024454800b9074100b0210100e24401030005840502c9554140b00c00035145078002009007030f0640d86c52180b002110801c015042e4405d03040801c04048141c140350a42e1241d03154065485910160000f0400c0c03d07100100b01c400745503440a651583e1140e0096541d52200050302a5500681707084190015966000c02c0b04020815a00ca569841010382e52280c1440c008402c1c050f0b0704251201085030940c804000c40b100140c552604405da900071400c140d88002c1841f001d20141040890b20b0b0041240440e61150604d0701c50b00ca0620f5000706109400c403d0400340940310050b080880070484141e60400f01e056440d0009081d20f05003020802150b2a103002680300007030540c001001001804840610305070400111011a0f03500301c99920b0b4080c01503c100e20090411150140703485440016600140325a603a4210034444000c1c1c070105842103000c16074001c644020030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 529641402 1250 529640152 529640161
    0x302150a020c070e01050102031204020415061e09030f0807020a03080f07110f0f121516030b0d05030304020d0c0902071214090a2108030108030c010f05090c0906041b0512 75
    0x128459174101e0307105a0040d440d20f0010200c001d10300c032016004030380280c2c4610031002c10210203500d00000d0105a56600c820302c20a811040d000d1825404a1040c80746907042407000caa030110034a100542c105040341c4d50340900344003042600205e0b60010b4030342500030070301d120945804001000301900882004007441070718020040e040f1006195a40d00c404c80f0310340c441c600d09110345038100010303000c42a0351850a140804004803141143d1030120742001404000c0b5240e05403146108240b02500c50344407404040d0341d025a00d1202410203441303103100d6414501001504040b0b9400350201080c259100c0f40f451034020a45d03e402008000400d031100e075006020344002c0c01f40d6000e080001c5c041c50740b140c078101540c1001e5007100e01400d00d407444605820003241c00c2000a6000340b071082d00450f44c3e681d42c0070009085030640c500c1158003a00346400d00144503000182c5802c560011106c0c1c188507155800002c0040c030724041c05244018a032515000c10907080b2010308004015420046920b40e038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 529642652 1250 529641402 529641419
    0x1e050a0501290919090503091c0818030321060306060105031306090203010906020304030c050f010213090b0409060f060501181a0a0c0f0b04060c09150c0302150a020c07 74
    0x825071000c0142d5010160182262420344000c81d00011a00c140700d88620410101101340c4001640c10b45c1d003a480080c0314503003070a00c020030f80d02426007461842e80000095230343e2004d5201c2c03040c03592500d003204010483c541c2c0d030510844150300701a10100030418007408403444960801c8650340c2c440d00480c400142a54041c20440f48a004440350444085a40d640d03440000c103250102030ba01036503210002400140c00e840254020b43c0603807511405289940f40041c0f502059469091580e401407081e80c001040ca1600001520340c08000440e2104864001c2001081458000f400090404000c4411a03e00707600140a40e9000e030703140181c214030568003001c01419840344004100518071169202e2240c00040c100031406071420318001c0323046c1e40303481048142141e419148008403405100c03c1112030b00c110308040c0168102188054501100700d00c1c0541030129840501000f40c9940d8201482801084603828a00c88020900e00b0039180480081d0452039600d9902d10030000d01090545 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 529643902 1250 529642652 529642691
    0x126180d03091e060902041a03060c0c0c010309050a05060115090b2110030c08010f0b04051512100501150e091006030f020c03070515070e0a0902071e050a0501 70
    0x2900026041c04000b0000c1104080c1c9000030815150550b8170710300740005030b459004c3d0780f4412040c41c040c2c80040d040b1070101401e002e000703001030302c074180c04000c480520b07140072418040d09802400c000070102c050b800c00c0760601600350801411030240100220701d2400d600155407502c607256444080054031107445240d944124400219240a01030540fa40c09558007042039101411100d4030034111756036070f03071513005804940202ea11651522014003d81046106020b14400c04031030600c25400c01415404a8018041c052401800610720201c02e01d242081030050020306044204103642e510a82c20304400400c130b14000000d00791130885201440d05115080c0038035218031074450158074040c0154020040705442000042d000c3c00780c005401c00038800b13890214011401342120350508070b003240940c0170041a50060001580352800c00e034813400429026a18031800040c3c0c0c480c61070510851084d017075040c0c02d4080442c840791004126011407100d034440e02c07500080c400d011007410580d5411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 529645152 1250 529643902 529643921
    0x305060601111b01090b0403081e03010506090915030f01051501020708030f030604110403050d09350a0204150f140d080901111b0a090903020c0126180d03 68
    0x1540401c080c02c003c00c44102c485041441e05041c81d0304100e0f42c40c1c42c8006150410f03030040d203800b00c021036404c00c5031810800168032075600c030070341d94619810900062000e00406285500032000200000c5a44805130500a8000701c014101e03000001191880da01820044a0300e00d00440b140f040d56800f0f50000400700309407030320744000e181420001d0382c2c80b107070303d03040209031961041e1945421740074100070a000b800514003c42c007410500c0c00c0b0b10806401035110fa4098100c000c41c2c101d090019000e02200e580b00c40d991465040b600b80b0742c0686a03072408040c5070001e94010b19142c070030310344100c03920858011180714041406030716a9999840c055480c407444440d8100c04003600085c000354410b00100a00074050500d044604400703841385240c4042082e40b0040b034440f500038085146803c02c0307052b0084c05000c005201101060381c000307482d00036400003036040c4010310f2a11428aa410208007004000c90908200e50345450400c01400c1c0003030800100c03860040e000d13041d400030b200e0702510010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 529646402 1250 529645152 529645187
    0x220f1238090a0b040b01050118031214190e1002010912271811040b0912070b0d020304060501060201090506010611030d0204090603020a080a031e051908010305060601 73
    0x19a55240d120400000010050794050003000503020004000c4032600340594003c00380060150704040014001074000030100048440440c0c0410028410401d051000d000500e03211082c20781c81d64540660b4041c0382042a0740d280c41a921003ea00d500c801d40142000301200d042d1410110600d003a401c0303d515200140c41d01d004000c00d21503542c0241d00502026494034030802038a031182404500058142d002846035420000410004206901850701c0b034407028a5524903091503d2400c01d128840e410701c86014904c4490410000001445544018482100265034a1000909210080d030045808036203151a01c0c001048461052141541240e801802458140d003441c8081e40c100040c0140340a040c8000c0003103441102c1c8a001a0006002020300441c24038118030402078003108507000915103600042100021a0340302c19050481c041507202c040c4040080d2004a605101750440a052030141086030301e842c40e80100464100d90046068440c0c50311802c00440b1070350081c0c8940f040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 529647652 1250 529646402 529646483
    0x2102191107051507020402030703090b0604230c0906072a03020607030309020609030d020a0203060c0c071406070209070c050105090c03030d050a06030c0f090c090605220f12 76
    0x3803800e000000c5607070080550a0303907041113181e90006050b60300844062000940310a51001003140d45a86140c1041c1d0403034041c0140811440600b0401d8000c0c03400340000b84221001c1840c081c202011129042c40c080c050a50394001810042604804a9540b0955100145480d10b14090a400310015264018009450302a060f10304072701508601500b1780c0d001d2400c1048421907a001c01150b00d01d44003d80282c00710f442a4010142090002407c004158200704401510f00e200460030313005803104142d80f0201c1484040c0403071024050444d00070b401010a00074402c040c0d1304060542c1c80240b00d14000d100c2e603510070944d10b454441900015030181e20034010034010307400075044190700c481c1d001c10006440e0395030389801d042000c040e40300c1c8e0480c503001402804481024080d1481e40a00c9040c95007810703160500007402e074400e103044104802d00c50110030f65604401142000248414948440d04585842c000240c1ca02c1c4580c00300d800ea880c0b10759220310401d2215219018100d2002d4000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 529648902 1250 529647652 529647659
    0x115080f1f0507030605091509100f210b0705034002030a02060a03051608070c08071103010903020c040b0901031509030c0803090c010318020d0809012102191107 71
    0x1c0182c00054000d105040e2200e03804591601d076034008600c9100508503090101300940d09200310044094100000700300080010b1002102902a040c2201c14512610003205000746076080d80706561040140304071801401d02c40550b9000d40a03600420303044ca060421a1581c0c2c80720190399030016120020601210072221003202d981c0d1002e00518005401c2e81d44410069000916603400a601035010995941c24012510103914a0004400d103605007011b06050801002e00310100c0d401d0010404840081c210040168500107054450710240003840090002d160282d145c81200f19030714040c44c81e141e0205e003640f1f0b000d4039041c100da41040c601c0894010950342c4074050a4500402c1e810f100c0d5281c401c20000c1d81c484d008600c00d140490251150403261000107040d030710110f400c1010704a4040804016a450802c40c01300ea0707602c001c01070380d240e08490040c0d80c1c82d4804408068000184e244100a5000c1078004010104d05040c240640c481240026100d4424181d0340c0c4046070302450061 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 529650152 1250 529648902 529648963
    0x2307090b13050306100f30031e020c040e070f180902060a0c0b06010816030c091802071208010b070314090a14040e010c020a230115080f 60
    0x201401629940812181c40d00d910200346891819624810480c0000b6020051095041c2040001d03054510820383e40e05c00c17520119021203251005007400c0800f030810070f02018080c04406c0b144048481c565840d135010503001035214903000722060700807800d00c882d91316107880110300f003010360305200381e100266400c0443c4c2c41309042c4500880c48071070745e86800d00f50150b99980c1c080c10401d2640c0d51651707182e003c2d515101c948004082c0200e0b0500c031120381400302c8242c01200d41c0d410351140d89030004174440048004c842e4040183e2042086074440d07080d883c4202c1c0103070000c02c1071070300460319580d03030300750220003110640403d03c11043ea1301d50038000703071000901c00c01d01805039122044030541003403800000118410165844004071700d07a10140e80313006080c24007410030b140e42098020001034039080ca0103911002213440081061041e40044d204035148410b0381103440140c03100030011944040c00c00440e101f014040c00c03100f4450903482030300708800090b1075405824501c0d000c9200307d4007416003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 529651402 1250 529650152 529650157
    0x806010f020c010c0f1a090d030605040c0503040201032301060507051510150e040f0609050714090f030312040c1e0807090e0316030f1d100509060d06092307090b 71
    0x40b204241b256014000b07481400e241d09000300d00f1000900000c03240e40c10b002e0708441940c1d0003075000b9420568040002e90700036013540e03401502802c02060744646d005505100d121071440c001e0f030712500c0b43c00101d0002c1e48075000d00074452146e01250401000e04181d9212440c044910141240c002c0c0010700c14482500e029400074034407414107080d00c101e028001810b650300c000c65511980c0e5200c1d400c100030140ca01900350000c809040001d03180304001594100c0c0d104013020b441c01122309050408a43e201002100da01c0c02ca0351130354401900381480d041160468601ca0700e400000300014140d2044031303070544802210300d14070060440138540300d1268050415840740e1540da002c14001810501d074806d964440051080d40c80c008210746001025080400c401103d84100d0f25250714901e00e611441e19800030ba140c1420540d4503100748100260052207031000e12075025041c814009524030954000c242d4401c0e003c0c0b5081c1e0010709185e0403480d00e0004a55080010b0100c07503082140f01c180900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 529652652 1250 529651402 529651433
    0x1031d0703060c0c0c350a03200303010308040f0e090a0209060d0212010c030c09030215031b190201050f0c1e041505030105040c0f0831030806010f020c010c 69
    0x200b00842d0f8815072a140364802c0e0991241c102c481410f06d007851040c0300d060b444d4102e44285146017034031000f032000362540c2c1c6200140080600c5501011080c1c40941100c0f54840c20641c5001c50780e583d0b8580c6013004140d040307171240d401d10003041000030449e00c82c003034030031842040203030000c040d0803846400308010030501810741c0e03400c0501e820036071004d616845201c40c1a0700920001180060130714a005085420046e0404e040003c54131083c001641d80304008001070048844103626034071030072410050103000c1903c2070481000007402143e01c04401c000700316030f4485500200241d90311400d00c4034000b1021102c1002c0914100300300909444003525201c0840c42c490350280c20703d600e03030120560300e0b8100c038008800301c0d00102c010080303842d0a0003071008031801c6d031034410503803d42800058580d5a000d40001110501001d800603c075805494400420755010380010101d01039007000f0f0405007082d25160b0000b000c12882c820000d000080b00622610103a40740341d5004901d03100c60260043d001c0c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 529653902 1250 529652652 529652657
    0x15040807080d02180f060409050c04080d1205010605030f040212011b03151a07080c03070609030507050c0d0506150607020910150201050403170901020d0e06010501031d0703060c 78
    0xc14480456020005000107240ca450700680d14100c1114150003c0700400c00c041c0b255a840802480544404003500d045545e0714102048a032034203940f12a045c050754120101e00d2080355041d242c207591106516000c0d50a50800300074903605d481d412546403004495804160842e14003040050401200d4600000d10a800010f006d00ea1032003025550b9011075403c0703001a4403400c00340804015059040c1c0101014120951000c1d9031088249103401203040c00383c02000302090040c01c3c4041030040310342d169409202040180c5035441d02404503003180340190742620880c41061100d042609480c0260340e0004000c4c0210741d0b84095000421007400036260700f004042c0711000040e160324512600074140c94142445007410548400091a5401205d01c01c5a0402041c000403e8010399100300581c1030816840c043d640c0d03811402e029110f1031541407100e40c40e00f400d004c003030b07480480c0890583d027090f81c0034049140c240502290036210031800a04941140008000040032640602c11095160 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 529655152 1250 529653902 529653907
    0x804020a0f270f2906030f04060902211f02091f0309060204181808040909020109170105090c06040e1303110f01020703200a1b151d010c0203150408 65
    0x3940380c0c002c0d500e02520800b840b8154030600809003060084184ca16002aa40203003140760001c181c031043c42c0c016001924547d40c0e40110000d5441e8980030b0800d0031800c5071083c04030344104c50081d640344180b81c1c110602c10f0020a845183c000c1500855002003070080c00850040d6011491840b0900015110814107030b44507464000140503001400040200d929a581c0c17409040c0d00b100103560f0900c2e099082800324040941c0040c85aa055406955007034100281e094290310060f500ca080700c1d005a8406030038112080c0b81e04005400051080c001c40064403401c03070180e428461342d402540a0324100c5102d00001030320780600f0243e5070040301c0c06440c050181f0004001400e04080c141c030490340490f5000100e10081c140c11102e011664103e8540c1002e031601c40e02075950303d811116070700800349042c800c2c540300400c0580500601408880c5c492082103800d148000d4041042d00b24240021104000464201d40c06a07194140031074010f000f41c00068550740b950000040000d1045591403000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 529656402 1250 529655152 529655171
    0xb0906130b0711071809063b10140402030c0901050a06030216060606050309120301050609061b1b1f021f0920120106081009020f100804020a0f27 64
    0x10885528148150031800103414502400d2120544615284203441c10007284142421420751540c1d1303140c46902d40c100d023106181000b00940c01c00500402d01031090f07051140301d00d181c030018803009016504c01c90403602460410340901082c0c41003442115400b04894500700728240c02a0010580e080c0110400f1003480c803581d9515040351007a4100d20001580441040b03e141c004201e546d005980e00743d8001e045600d03010000f0f5052150342c8070f640c02808089060800d40da60034281e291021503120558540070270b085ca01c12004807032800e1407031290135101035007c8540361100140100d002c1580c00303003d45d40003941c50682900740b010069241541c1d240820000301d0042c000340c441804500e2003808406030404100803185541c0c200700c2c207441c3d24183c000c00641400162003074420740540e00101c1d2426160001444054650941c80d81151820300000f0301d5a52004503148101d108407401801c081d11900b540b8181c500c3d50062032485189400584400380c1801e414000b003003108400400c14640703 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 529657652 1250 529656402 529656419
    0x2c090106030c081f12020d0b151e0d0201030903140c060115110c01082e300b0a021c0603032601120f0c030b0906130b071107 55
    0x364032000009075110880c0e4207460b0300540700b40c0c008101da1582c11440341d8541401040140c503110704c0301c000100c80c80b0319045403140304c061154143c1107201e05400d03161082c05070720360100f040910752142d42840d41e980942c425000d11100c003040083d092a0b0054981d5005400422130743c00c040d41406405080d52800d07440d410000c080c441a00e502030590b07945800d96603142603054100c050184507082d1001c4a80c00f030009218001c90b5003d2a25070150b84a404200d210301d030f41034003d04400017800c05081164203046500e84201c40c17511035000c035480680c804107080d009181e1441e941045101d141503000c50040001903400800d1076000500d0300a02d0680d407601c50218141c11400e181d15840108141a04541c005071400c500c19940c5030b842c1200c51041102c1034050080706000041100c080050044400d1210640c0b03500ca040c800d9200e0300c03030070a41d000000c01c90760900d0394480c04000a81a0280c100c19004076031344041c241060303882d0000160f80c0d680c1165072030501441a498002041c0d034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 529658902 1250 529657652 529657669
    0x150a020a050c0f01060f1a121503010911090a0204031a060102010f061401080108010519020c0309120a0b060f09070c0f120f142506110304060b0907020d2c 68
    0x342a04000200e00e0310b0010403500080c65680300012404180e100c0018400c00131048035007001d4908c005810340d98030039415814254080120302d800d9803920702108104211021100d030002c90417610405103a07103103161101a80300e03a00000340312907500028400c0c8c4061400c0300a412181c140008039030b40b108c1c43d42c0b44040300c50540c840b0b09600d00481048001d0350700150072070b0141036124000d004d10326164180200040078240b4401f10b80758005046003042c03609000b0b850701042d00600e4140300700341486000e03a4070200e0f11000e81d1880d0350704000c90368528105800c034030115409800c4c3c0c2c0c0f46540b04182503807100c1000f0420390ba1140c1041e20380c0700149900d1014290002a5111000c88811150f40141014903030441d85142030410420035030706184000088034252a2481080c20202d070f24645003003d40a0204a80207404001c0103102c10000a40c01c800ae4100041e80e29003050340d24450102e9940c2c1c420103040c00407444440c5d80380b0041c286241041202c4c1c44040702000e9030b181c1c58000c5100e40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 529660152 1250 529658902 529658923
    0x60f0525060618090507061404030c0803030f0c04030b0402060a120f06180603020d0b070903081c0c18060806030a0212030306010318110d031407150e150a020a050c 72
    0x25640d002c188540143c2403000b43c08406908420040142c00d81d650540d10040703401800e050002110344101140300540c12600034640c42401240220707901c44280d95250020789400009203000b00010f080c0b01c01c030764180c40171030f40c2108994400703440765021f001c40c81c0d010b2400e100412249242c550450345090094501d51200d101c000240300b4681710045140c041c10742107620b030b214200b007020000744e17a81080c124a01c80c0c1040f0111459100c00c0d100f45c6081240b50300c009c00040012412102c000c42c4255190100c0d12841803d010a030920780c8102d4a0035809202d00c880c00500310024003450b440b420b05150b1000000d021559114525000030722028065a0440c00c03542c000410810156031600400711549043c0c01d1941c0d203200960f07903000942445000003400b52860300300b18030905118102c0c0751a400095254250350b00c480c0d08140201820101403001d420f400c1214207500901c000030a000c120584400d0302c20603840e07003200d0b00082e40c0481d5417202003142c140048000d9440601000030f40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 529661402 1250 529660152 529660163
    0x90a0902130302091e0f0a090209090a050c04050f0711011806060302040608030304150c1e11120415110a020301021201081203061503090109080a020d030e010204060f0525 75
    0x468614410064440c01c01495812050100c50961aa100e61014846e4100345000650981503864603500c0008125040700603510010031010b00903902c4001c80d104030f4250145050b604800c050701e0512003990000e4070b080842e10400400143d202d485420090901e500400000c100c072100403541882e80b40321105c4c16110306d683ca00d003c20841c9000d205030070080c00300201850861500c0c0d100d40c507005508041ca1088149c484d81006622446003e1002c601000fa58402c04801c40b201d0000380700404851200c4070900c2611080542002503800b03840441d00c0041150710030116802c003c843c1c810051251042a220f0820388070010380d030a0015094189420152003207031362400018929101d480e80700781d010160208140491030b00c442103940c210701d1284d120f01e84e4039122090090300501c0f144002400694010840b0b00700f090b0301041c20725007003503a564113204100031040719900301e00c5180701d9074021030703207078468070100c42d0040d000303050f00c0c0c180c0b030b4007051540c2c60b851045a90f00322400e00031500b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 529662652 1250 529661402 529661437
    0x103030e0d052a0d0201050f030411030109060b0414040b0615190f09060e0108070302030402030307151d0106380309210a0903061d12040e060d050a0305090a0902 71
    0x49140000d0305000c880901104c0507810007a05030000b038501c3c85a190130780c200b4140003001506101c0180701000c11031802800811060b0160b042200044c41b00c68800c034803540c01c00c030001e04000d030440d0342035000300d400c5004028152600c20812000805a002d0118800014098110161940c080048002903145c4540d00d11069100004100e06541c0c1c2105003800768031200f160150340d01c81295075000c8030300d0400694030b440700e00000349140110342004040109410b50095030400c590030901c0505500b0221012414540c20594282d5a942c020840c14031981c200021044c3d12848242c00b541580d01144418034110410a690503401104d4115a1358030030b1741401851400c0410464011103400d1076541810300701c4c00000e10418083c0f0024005584582041e40d051245000080f0012203440c1169540f805060742c0d00d0542d0441d10078840c4501582e000144241051100c0c0242c2c070398010701428010703155603401d951540202c0b049d50b40007181118080b45096051000f00030007081d412a040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 529663902 1250 529662652 529662703
    0x5040c0c060912081f0b1c09060c08090c2815050a020714060304061e0f150503061915051002010e0c010f0c201519030c080103030e0d05 60
    0x81c000080a441211580c0300c10800c03a1030428134500301010703540c1c0341c1540382d5a000d0702c7d105c51200004500b584280c0e50f00d44800d42080104551001c039010405485580c0d06580c3c82c0c9009403030314090304c0d5081d00700d0f00c1400110704a03001000e001400303c070795041d10038a0a4a03018004d8241903c0d00e0180c012800001c3ca090009804002c8280104503041080034092070a03000304005000c080d100a18290320b459201ea00000e054080c103c900c01d017450108020314079101d0f604090f10094860146c8940e820070003090508012914520400600c0382155150a800c01c42d80000c1130300040c0c1007200e050402c8085050740d10500c0b101060762141d4000301d13648050348800c900f4030580c5001c803814050302895007414503401408621280b50000d286410071416884403c5150302c540f5040395001e540c04003c0345002500801a2104640c2000da01c05410120720040d0104e072504111800420154001080082c0c410400d21030300303100c05000051440440d03030310780d4600903c0e42d0180d10900c1149032800c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 529665152 1250 529663902 529663907
    0x90f0b07120f02040f0509040c0e090a11030d050a050f0403020604180f0504020319050c030102041e06081506072a150219140a050f0a0215031005040c0c060912 70
    0x180b49490880085151a141014a504c50b00091150901410005001600740000c045110000b8601ca0304a00a01d1070121119602c51042400484030f03402c9061000803103003400900c0e14030400c00c45d00c419242400c01c3c20191801c0c0c01011044c180317000204004070058640030054001008400440300305410015044000c0e18980f0880a2506107448100000350f94000f812841c10300303c408605001c0c4906081c5a400e1440301c461050b00b66000180004e60541030b42c0304251650120042d100d051912864222044801603070503480d542d401004046551411100421940d48198842d2040310403024080005400041600d0b01401100b40300708403104102c0e41c0350381058814400380240c81810f40440201880c4c40d58060a0071030038925140d201c40b0204001814140c116048900c49084940e0065450b1080c0800300d00514072941050341902500f4152802043e05201e103070212410701c01400014480c080100d001c01c0201018180421080c1c0f068030881400350845a0181001c00d101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 529666402 1250 529665152 529665161
    0xf0c2a12030a0804110d0b15030f120403110a09150315111b0c03031603031503020303070210051308060a0506120a06110910110106090c050706090f0b0712 68
    0x10109541040140741940b0b035200c0309542d0721907440f07212983e0400c000300c042140031440c0074004160794190710501c9100d0402c00c0840310080412001c0303070101000000d41c0c80c0ca03903c00c0e1010600c146002e0000744001100300d00d040c82a0103020740350b1680240c1c1c0e900c440c010794410051481032a1849a018018001070342c54a0841019201c2c042c00340501c03001503d18035101e034040e00e01542071101440541080e05000d00c0c411f107580203049a45070341009142c05444295a0001c4021a2803c582e83c803085501c046450201c94008014508102032a02409020300758800f813541000b801b004030524148510420320080d2500000914291170702c824028200c40d0b0280a541c0f044010030507021000c0400a00e019000da070282010901071100ca207441064055942410b0f802126510341c027480540c04201c21251400d154024010b60303548031101c00849205560900003e002040004085400c41c4c101c000060312422000041c2e100302d80f00d5071010401515103400044480209100c40581400f4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 529667652 1250 529666402 529666429
    0x705011b1d060310120804051f08010503150f1f0801020408010510271e0902010815090106180f0f0501120509060103060c020307050a05160909080f0c2a 67
    0x2502c2e891030508090403503091002c4c0c460031004641c082c110a040045c0e050980700101400b5184103074560745001d2007100c203021500100c00060058000181c6442c0c00180c15000401c540120710b0f0540302c40010308040d81d0010010002c001c84000424421100221003d0082041c01c00068031181042211825500c01410407454070f85116018401401c0c544242c42d45000c420150514408561070581c02070081505000c03041071509980d80945040b680040500300c0c0300340d0750080da5a44d01c44070344200b5110540d07010341049800005100b400c2c05058008501c80c41e50018070b1407656502c0a00a00c0d81071900031906403d10210204a996000100040110700440b0217000380c0c50200300e400c1d40e6070b50521001c4c00003900c64410701e00300707030080c0300301d6110030707000400e40f00215003034101f031036a90010010030250b05090304800909002148100724981c0d6014000300d1620300510052540c5400c000740c0c000e00340c0209a010780301d01c6150303e9005000c40041c0e01c0078101ca6440c000b0040260207010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 529668902 1250 529667652 529667659
    0xd050318011b0f14120609070c12030b01030905030313051204060c110616050d0e06090303070204050402150a0906030501050604060e01081b040303020705100507030c080705011b1d 79
    0x5021641c01d6a1110000e40b0400c0318581808020f02c0424111100c0803104081030803d000050a100001044003100e84200d00030f82d0511402d4807541d0080701c80350b1041101420700592091034100c928130a400c10480806c0516000c1002030051705d84a056030301c2654494003032604e000440d401c02000740001d0240c1614146103600313007890070101a00003006a44000c1000b80782074100005a81e510041e5640d0401100c0507101d012001d1500d03aa03202d03c0041d1110218080c807401100c1850000100c506e88000078000d14240f2509500b404050711018100301d900000640251000501d504060070080015540f511203130352804a01030115007068011038000d580c10441403043c207070850542250300c1828070b01500c1a0340c40029032400b4807040c04016540c2840040c000084c0b5a00154a20a442c01100c500160a085c907005031a28460007400a000c6a0f040c88a0300c0450f0750b00c80079008060090780040341109076041c0980c03044168001c03c40104446002e0440421100c442c521401142074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 529670152 1250 529668902 529668911
    0xb090708070215040503040b040305030a020106230f120607200303040c03120c0c0f061b0c15020a050102040e191109120c060d0917030121080c0d05031801 68
    0x50710000e40324250310018a2000c406040420f040201c20400c81e40280003001c18203490b82e80b0b0b442c10340d840f40e102c5c0410350015800c082c0c002c13804503007020754080e088001805841e200c4004005010311800044042640030b824221200056401848091303c2050345513622803050104114514905540c1521024241c2c000d00c20880050301e42030008050340c2e0030a147c102d28604400c0b084401220b11880101002c45000c4001508440044980f007900c0554452048025133000007550082c0c062902402040590204014a4040d600074149855152068a02d40e01003503c9860aa0b8800da01c42600b11058404120004402446100b4002d841d400280441c40740c641c0004494041e01c52454801d1601c481d030900c0040301088040030003078010b02019120f441da0300d80f200c01095801ca00703881c04480c824006840054a500b1030f03041c3c0b1200f0792100c601c00f401d48030b50348101c040641d00310b500030820095108100020400068280700c03035a9040daa03407400240c82c000c200d00c2d0b5600c010503613040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 529671402 1250 529670152 529670161
    0x30b04020913020315090c0a0b04140f0607170f0c030a03050702060f0105010f05040e0c040602011107262206020f0a0c1505190c020a050a030f020f04110406030b090708 74
    0x440e43c0da4141d48240e55170304150701c5090010703003480c4041459942c8080e19400000c1c225249038060400c9494a90300d145010f401c013410f0112044081040c03540c40082000013800281010401c04100b50380c80040750f05007070010050054680c0400e150803010360000c1005a1410ba0600034507503c400c00d44060280c0c1e081421a28483c44810701841d4144181c491210000324400c0080d580200128074910050782400241c40070941e116009440055092410b000000800c01c02107890700c65100c2401c0c40002600008200c0031220380c00b806004560400003c540035048004000014061710510b56846140c080068501040c4090b500349640003480124082050035000104440070200707417120000040408481510034400c001c4000540c0f96581707543c1c01d03031010512516520030384684020039192002c0040302c0d901444001c091719204494180141046e18507014500380c064404036410714209010b949681080c1c016900196407143c0c49003ca01d007500c440e07500081c103400d202c0102d003030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 529672652 1250 529671402 529671409
    0xc030f04270b1f030b030d0c060c020c0109090509010f0906050709090e12070611070c060f031b12090b011806120807020d0c0510050912010b0120010f0501030b0402091302 75
    0x100d0105000d90304503030081010f516010f0b030450102030000800382c804505c001c0401400000742024142c0b003007441c1094074124140001500d4441201c1612908165032900303c044000d06801040384000395281c0303010388002101d85c0508200f040c41000041024948058010941e0200b81d0000b03940b58100394048401c08804a1101141903016030b607955a1621420f146001e041c001000e410700110000307a920902140c8400d00081c0d0b812036948681400784500102d090320107030002c0448150b003001c684003060380989620440b8401000000c181c4810f251584800c08209a1040343c00021004080035200b00c40c3c0306200142402c0e00074081e082ea201d4483c240580a0075030000c0c014205c3c1c2090b0020300c00050000d400800c802006007112036203d0705d009000303400c11401f29000d035510800c001030302c00c1d044c0260f10510301d041c1d44030160308039a4075526101064000c4000042d543c2d80c00b01480b00f001d680030f124041d60248490a610741000c0c03040c081c07240300050518800300c40d0255281f00595 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 529673902 1250 529672652 529672669
    0xc090c0412030e0a08060103020916050a081305070f0810060f120f08190815030a0b07120e0109030929030c090405070206250c06020c030f04270b 64
    0x102081e0203120145428a01520301c415440001d990281400c50002100d40c40000c5450690f4800e80300000309455426070048500000c0a200c000b00b0800d0002040c0f01d880781c64020b030b0003001000c0c43c41d000c407450313240e0750304200140e000040c150551441c01c0c408001d0410140304c0d0381d441c002c81082500e01e030006d6125400c000c0d001300070a070580c3c10075100a2042a40088080c41e400140f1250f8822000320041c40d03039003251a0180204001c3d42c00114030b010b00c1c00d0b0015210101402402c07d4114559a201000703000403e076900380808807201700c0880707006115180110b88508000178004242d4217000d440240254400420f2104100d900360100015001100990000ba0351141d100d40340c501106103580a0404131035040307032500c0200300f046035000a4040c010a099440c0410003030048015410b45a440f580c03034400f003036000d405040000c405038018010001d030501680d00304401070200741307026401035005240380d40001c03c80c01c600440407803a01103d5058168100108941800803920f9803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 529675152 1250 529673902 529673909
    0x20a081f02090a05060a02010e1203063f011d01050106090b0a030b060f1b01020a30050c120a0501060c0201030906060302040c03020c0c0604121401110d06080c090c04 73
    0x141d000714403030b10300d903c1d0030b8071503005032800500168a44d5900b141c0240200030300d0303c5600c0507200b802d1041e000c00042a04aa008600151201c00300818031441c030a5001082c8034050000c212082110900801d0700303080780c10b210038900003c41d1544e41c5034004144400d0600c07020317110342d141000420140d43c0014102c0125110708500d507440303013403a4034140c00600840d925503070054000600c0070841d0408400410b45a008030b04108030000040356454201d0103801c1403400491402038124400b03040d42010081d007132035000086a41c02030280f9640b0182e620548400311819008108840901c0104040692101c00140100901c0d8034001c2d0060590703605d060302906041c1c0e00e021100a108030354205401030754021308180300e1250b00c000028000d500840403ca40c034011050403c1aa2030640c0c200c5003120000d50140e61008020341741c0e04d0303450503954801a1903651302c0440c1c64008051a0103840ca001c0d2540000442c203140201d0642003149005103103105000520810242c400300c041680d055 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 529676258 1106 529675152 529675213
    0x9120a081201051002070e070c020f03011d1b0102070614271c0203060606030903040f060f08071b030503070509030610140102150a1e0207060603020a08 67
    0x111b51542c0600800c4400300d10100b400c142c460010943e52034001821703c042521200c000901311400b400404001d001c0940c4900300000083c00f15605600583d400442c4100131040002d4950000b40143d80c140320510b82201e0006c0320798001e03603c01c00d0780200782c0701c0701c103148044400c1480a0150528408c03c042490b1300d0242801800400c00e19902600500d06510303140200421070300020f01510713151000307020000740102c0340c031000d8004200d16102c0603604561110028803c010041c406028004004080c071098940a09080c681d107030075141082d00d81d25210411191071103071042459144c4508418000c551400b89003040841d0381481c010340d05000204016030311518030b6504c50301442400c0d00000e00ba0040c42e0000c0028500051501280380740c11b29000c4207c0e00324074002c0d6605695224240218100303030000701c0240150500900a8a03400400c004044188d802403100 = true := by decide +kernel

theorem cover : BRFrame.Cov 529496402 529676258 := by
  have h0 := BRFrame.cov_init 529496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 529496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 529496402 ≤ n) (h2 : n < 529676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
