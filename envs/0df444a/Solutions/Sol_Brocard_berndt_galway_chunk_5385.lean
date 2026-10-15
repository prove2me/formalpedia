-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5385
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:42:01.189811+00:00
-- url     : https://prove2.me/submissions/8edd8126-4db1-490c-bbaa-55396c133ec1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 968345323 ≤ n < 968525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 968346573 1250 968345323 968345327
    0x714061c0902030f2406120304080714010c0b0402040c1103120f090303011a09010512130c0807061b060f09080304061410030212160f030605010f06140307020a02030607 74
    0x40508001c0f4083e00c82c90300d484992110104100504118006400940301c0c90381802d42103242c0e0282c2115407240440240040c84a400c0005000600c8044060002203203010a6402040b070b0000c5202c0c18801741c440950006221240034507400355045a000800d00071050085036000c0c8000d00c5c4818500c000110035400a041d1a9594410f0803000d403040540c0d61501c00007030310782c007003840b610040380ea00c441d91420555048001d000d26001c10302d00305040116080030522200c4084c4c07501d019681c1d118500c0740034811146e5140d000340255030010041c091800800401e2800941c444a00300c01c200c1e250042000700c590401c0005d500ca901c0140034041c000e04013070115038410b0700c003182d0300c51a2000d0002c103594010f000314454080ca044030b010052035034080c8070860701004240d09035400b402142011481480700414040c00c040d82c0c112040a0031031425070111001a00103922820760440100041903101104429004850800680340e499110341603180016404000b58107014441c00c05c85615 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 968347823 1250 968346573 968346581
    0x9030804080f10090803130305090d060614040c05220302030a050d1e08060d030e03010e0606280605072603041205120f1b03040609030e0109080714061c 67
    0x1240b607001d0351403c400c2490700000711032104c2401400c400c8103000060711030341c6031a41c0002d51802403d0903446c00d41a00001418900041070485d1510b984641c14004013000f0700341c039440581d05513001c00c4500f1440700068864043c3c0f907035404140030f10a189411a910000804000f140d018085840003e00c40c500207440319000c03825a00015800c0d2038540ae001c07100490707800c9010381c90303ca200442c2c03108414002c03a1890a9020750a01000003d20444c40d2424070400b1004d003412005882c4900b0502c0801282020301c42c8035521292100b00410100808201448100c0300e003400c1181d41c079405403400f01d800700c0d2a610f2600710942e105051003401c021440046228510a04403c0341d6a86440015111130003528541609641e000001410a0301d0f0302e403010342c020640e4800e101104900d0002d0911035442242c048032400e441c1c01c0580200b541008005806080034200300c081c46050071909039950140f48103402c0b680003a03022400c0c0300d407914821550501410b5031042c03e2000e60800d010054 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 968349073 1250 968347823 968347843
    0x90c010c2604260a0b0408031e0405060a0c020f0c0d020a17010603050d0c03120506123304051c1b110a1e0504020d180b1e1b0a0903080408 61
    0x200c01080c0c90000e0140f0080b840401442d40001c1d091000d40b581d440720f10094000800d0520110700e20340d807240d180e000c08601c02d4480d512403401000a458443d1a000c240c409040115056510403400300481e070384041400c030040001614071007020070440c00000c0c0c0d4198554880070754042081d4245406071010742003402038a010314101d46903443c000c0000c840a032440c242c0940001c3d142070652800c1030041c2c110a40040300200305c1e0041461410501d070401000300110800c8240c0030500c403051025818070400b039007003042c000d030003030746000d44485403103c11000010030312507103400a012000d4051910701d41c04801c840311401c40824580340c070043c0302c3c17880c030a50b81c0f1800c100500010130b000c3c6040703841c2140c801564200e2000c0e1403c41400301a4020096088074a0b454070441050a1003d20385501d2450040c00820001c0c1410164091116101e40c2c07041c08544000c030400800e00b114040c120700c0030f524181c1c002e036158080c010483e2100400c1d0001401c00c83d00150014001c00700103054060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 968350323 1250 968349073 968349119
    0x9090a11010c080901080702281505010815090f07171b010f1101140703061508071d01030e0f0f010617072705010e0f090c010c2604 58
    0x5100030391001034450500301036009016000c100320040132544125201600440c45004817240d501c021000c02c89100201200801103606c031400035401d002145013003182002c0400020400ca504100f00c10751038041c101c01102c2c00380202404200301400170424082c00003184001e407a4a252213000e038010750210030000b1030f0719120780d106010410b1241d101e00c1c06440016192040d980314442019a414006509800f8595694000e1402c05100d0810428841e0410f92b6000400609141e401d01d00c42600311108808c1203101c1c820410070f2a0072411240500044901000140700e050004170060070a01010540b00d0144016a044040700041d42d607400b0780d03980e4000d02c201e1b6211002d070540b19181c031070040c80e558400c0d0f008225021300e8002c0e0520700f0801d16400c040c200420310404003615400c6c0e001c0074412224408004404034901440c941015948000d840136000280c0020f280088000015000c112505a1000d01c0e005413178a0100d94400490083e40f40d50340d62150340009140341e405050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 968351573 1250 968350323 968350343
    0x503010501080703050708060f04060b0408060604060b030106020a020d06020408010212090106080f03090409030201021b030a12050606031501020309040908070b15011d04110f180405161b0209090a 86
    0x41c0713019000300c40c49045c4d10751301c40219540790400c01500342c0c9183c0100b500030ba0380d000f0203e00c0d080030310002c00292010000810302c60808030280b204550740c0341e01c28000c04500380014405d183d80841c000000790340441d907403195100a4240303900248966805452158170004000f00302903540c84a0701e205e4103c20000308071140c0d072000c140d512011102020210380c1c100f0096509107207130540c07100d11804e0003440014100000b04200417204440311000e084aa88082084088168002c0101d00d4003000305509001c941401070104070540000b80001c000700702201c00080c11030340700b0001d54240c060000c0081c40042118204991160322041c3c0994103200b4150000d00b414861101400122106949070405c0200040030340c10b59071a14850554041d0316060303009100c201c514003414504890f070000396651311141d8404d8602d400c4440559000302e00701700c2000401c280300b9101c07c0c4980c1203410b00c110a4122580450007620700315030000e60119401c014000c04141c000f0300c42d51413a206400c005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 968352823 1250 968351573 968351581
    0xf0b220b03010b060403020402070f17030f1b0301060e01020a0b01060c110d0b130c050604090f0b0f03120d02041a09011106100303030903020f0105040b0a2703050a140a050301050108 80
    0x10700fa0f0b400c2d0a8800d0700076204000070070050805030700800c03419004420312103110301c2d02e07a216508143d100d40e0020040c0d0010007845188400034642c1078000b240d40031040542e40030724000b15180d000520940d014001d02c0090b00049900038030000609903884400600e07150384036407000e032504170030b03074400d94104110b07895046180c240604404d02c05500244c46010300d0341c47c1707030418540d659600c00484400559034400074040e02c40b84c010b8406003070303140408103102c4c3c43d0b402c0c010b04541c00d9008040c0b00c1e1003842c8810320140c90125800c0b141d4254004130a60300c1c030001d01400080e1045520001c46018090628907460780da41c009404120030903651141c3d402c00e601e10440e034507001035500440100c0c1403034081000138000e034010244540300c2e0059541c0848205a070ba8210707013046400ba54504d48000c2040100b1005101d011a089025840030b12500e01c01c5494030a00f481c83c3c10020b0034010005110402c0d64002d03004811036020030a80c06940c0c50000e000107045400a07c03841c0d01050742c04000ca = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 968354073 1250 968352823 968352829
    0x708060402014e0605090103020d02060f0c010c0809010902100f0e0a08070801050c030c0f0901110a03030510050d03200a020a0f0503060c0c1c0315080f06060916030f0b220b 76
    0x103400c030f800c0180301c6d520716400c6402304608080f440104a074401da04100c01d6540a507420041c12601200e1070001903c43c031001400780948400406d10032940e490301c101800140c0e1940241030320a00d5510748000d001d908001e0568045900144495001d8440350000030b44900c0081d04406a503110170080c005500c0e4481c00c0b040c0c601080d107038094801414400304844842e850b002d09020001450181c4000203034000060a210a11800350700098580040100150007200d403000101001d0b00c6d0040380300d54a880c01004428002124541c1a00c0b001110303560719010050540055001807010401d10b5941804101c0701c21036106460003406a08001800450b02e841942e6603400068090148212845134800c80d180f40a080c800a060780e0301050b802954845c51840080c01c01900205055809402c1403460604000c000c00d00c20500f210070030000c1441d4606040c00c2e4609400c02240000b02c24002c00c028040c0750001c3c1d5000fa0104059090050301e984034150005c2074000100041007400c1c0074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 968355323 1250 968354073 968354081
    0x6060911040f0b040b0d090302030913020903010c02210903012a030605010203090d110d0c08210304051509030c1219030b01020d0c060209030601080106030210020708060402014e 78
    0x740d174002141c10302030303500b0b503100b140c0018600901c81d2055915100b440400501e02001d16101d480030f82d035020846007001e0a092142c51103001e100c4c0010040a0034411000c0c1c03680c0180041c40b020310303002013800e030b0140d03c094004c2150581008000302c044b881c0a0a604158480403c510000900340180040c2c00d5001008581c40203101070070300f500ca25010f03120259502c3c402c440082d042220041580b0208208910706005012810081c01c0201100035804640038142400d0000741c4000300144000030301c1c00540c0d09a03808004250310410b0351516145810b5000b640d820700d015005840d240c2240240150042452600c962408915241c0b192001c5003111070140d10b2a02590040e6204402a8058001c0c120828030a01c1d016242c61500d0011038144002a8088801c0d0f82d1222410710451038000e404c4003640398944020680d241c58044602c0e550342000e08047e0500110f061a00e040742d0504150034007031000c3d0924800c0c0003411b45043c00c6101c11400f10307900c07c1e4150320601841201c007405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 968356573 1250 968355323 968355329
    0x5060a0c2a0302060304230f0c04060e060f03070306090305030708010605160318080a06061d0f01030605060d02060a210c050910180b04180b060703080406060911040f0b04 75
    0x20146003440c2c00c5909000190780080e0090302c101b0b001c001080380c5c2c0d284402c505110806030401030250b1160122000780342002008a05106a00b003c0090105000d100c8500707900c0503040302c00d160000c040d41b003c04e0400095401c060002070402c8000c0d1305140d0403800442c01651550740720106aa40d80d14121101d0082c030304105244030300d0305201d0001c40c5c421030102a0030001d1400240c0440c0e0764440b818580008034408640290b1108020000034114810310f10380000716006070821132a04281c070a8050070140001400182c0c0c0383e002c1181c50700c13407010140382194013a10099881003c441c02528030b2158500a90f40a0001d0101c0124190a0701803a0000d6546c0e49070141030800f081d04000380140e04503040c10070021600101c00c0844202005003008000d114941c50b07032a8141b817900030b0107003c000c0d441c1d151039044c01101e140340e8039000c044400c1c8a40503d49000b054a441c60001d01070041580403040700313401e00c0b003101c40600c0c0480042c400c82c1e0900516508565507a50708400d140544c0c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 968357823 1250 968356573 968356643
    0xa05010203070210021e060f010509070203070b04170c15060429030a121709070b040b0d1113080105090d0e100302040e0a020c1b03070902090a05060a0c 67
    0x2c003802d801802c3c00e115420801c01c90b401600c0c5e000c0a560700d814110916010700600d9940103d051141001c080107000340585410383e1115800d00d0102000b0390342e44070f182e40041071000154006810f01040c0802040e101c140248001e50392100c683d821a500c900100f02071700b80308000c0700414503d14051140c2c3d00d03880d0294440c0340201c5180312080c031083c946441d24a4050085440000008218094907540f0b000107483d2041e00740211408450140e000504010b2960300a480500c01e5103235803022380e0304a5054840855540048401000c0541403800c0007490b4007001054080f640b100e64903a11090700d401e0030003048142d07641c1020b6a940d040301128140841d08084c862006400c00f03101d400c45aa809040251800d561021001c105400486159101c580d0105040442c2c0f00c0510070444d840c00d10344910f5600c2444240005d444051521407440324586c001004400380d10f500801c90001c0400030a01912525002c002170305c11602c5960494444140a030b14000000303203032030b46102e004959 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 968359073 1250 968357823 968357827
    0x171009082214060f0c100524130b060d0903080603190b0103020603091606020c010e040c022e050408130b030c030606070804030516060f02120d0902010c0b0c03150a05010203 76
    0x2440c01d2001070b0f1301c85030a100e404d000030848180c0b440c00400680014071601c10b800905d40c03800b800c40c00032951031b01c0500b80d8806a8405611601e6031601c00c40741182c16850740014540e075110340003e00600c14811090807041c200380b460301c14150002a128032410f006c1e001e4450f4003500852000050310001c2c0f0040108401500500140c1080400307198044420000c59120000c2e00407000d10302210b5030b011200507800241c480c240f03540d00840c01c068508050fa030a226410031040043d440310214541030b034034000d4624280c201600340d80301314002c0c0100024100060700b01404c0192541d80325a40c001c000c240e005800241426440c800c0b40d04c16415000010700b1034507843c0404c1490b070b011480a64018400340008004074100b40074040c02c4e400c02e1a8011a41864500302a020f01480031080e41550000c0910984c442a550100c94000d00900d03000151354890348016140d1340f81c4142d000d489800e41000704080703610314030001c2d8011002000703a940c444191001300101c03001e460249070700503001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 968360323 1250 968359073 968359109
    0x30a2406110102040501051b07050d060204061704030c02090408130e01080f07050d08030c0415050913060f0611032503030b0f0a0b07060f05130c090e06011710090822 73
    0x1802403100041a510155510641d031080001e13411f0000c00bc00f40c6515900140402406400c541d070402e40110a505242052810343c4010f412030204c41000b0740660070610019003000b198108580c00c4500b5440003103219600c1b4080305103100c03002d000c3d95050b403099400241d9000000a00c0000300c0350700404002c80801e096541c0c5609800207003100c071415005020214030807081a8003d0112809a540c1940792810b86040103481c0d440349021103d103038546072082c0503112004803032a00383e0340c641c1440c08800c2d80c4031510603e944140d401c40841d070004026107240c2a000c0044490406c0d010355010300184040108110740d8a202402ca254000c003a00400c1290400e00c034090850710340282d100042901c20300039a00c0560b54101c411110403100d000c1e8500c2001441c2d0300c8003000e80365902040001307882c01c800c00b60f80d078801030046107955a284191064480000c01c81c403c20100380800030702500030701e03240070702d0340b40c0080da08145482400341c4041040c0e000c01e0004030894414110402c41003003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 968361573 1250 968360323 968360347
    0x30f030f02030f040902070b060f13020906070501020a1e050f16060f151a070c05012106080a1a240312130e0c1c02030a240611010204050105 62
    0x86061082000e42c00180716050201c0c101d10060701c0100038105001da9520840e1400c0030360407400810307003071081e40d00100c845155202e864a40d841e581c080c1d40010b03600c6114500040711402056401045036000098030080070350700c0300042400c3c1400490740c5941081e2440203480030f0195881c0c140c1c00030014003604541c01440d00b0341f414a50700178100000c100d20b103402414156201e001c401c01411000b01c2d000c1051034141e940e0b55001c544030007a0203080007003990701d02c0201c103141c1c402d00e410081c3d03003145441c4d084000020010403800e141010040b20340c0d262611503c072204501c0c103072540e50321014410050b00500215620620b0030940c003c00e489014403e00c0c0c28840160305060b010310850145200140058000740b6041c500403050b03613090761610030251070b004c0000b84100c82018043c021b150340c02d46545016480120b03081d801580b01e80e00d003001c8400415002c1c04155141080c0c10362160483d09207038242003a9184d81d52109404003550202d1402d0740308912940d80002c00402c0aa03100030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 968362823 1250 968361573 968361587
    0xd0503090a061e0e010c050109032a0206070b0a06050904060f141513110a021c030e3301091406030105011d190606110706020a03210f0e0a0c080304030f03 68
    0x910141000c00c203984c21b076100c041c00c443d02035100b1000324000c2420001c8010b0b80c00503102c13a1401c0c1e41034002e20240f8a5010500f24010000018051006d02000c26004c0946800640c0580b070050046555480c040c2000009003840e000100005440d101400710320078007030043c0a114a042c43c21100c001c1e1800418044030742c40c6029288211991a40d04805980440c8001d180141c4160300405095040c0c2c502d00c0c3d68107910202c101c00b810704d4200791261030301005c100c00c00c401c0c82c0c500314207800214560510030203d60f0703044c0401411340d10b8800403415000070f40c041208040940c1031800c0c540d48401c1032500300c903004c1c001c110b0441e2946103445681c403001c2d005145d100025a000c68030302803070f2030f907000e081d510b1a4112101140c034803040300d04c84180c10021b03480100828030051a480f0200d807805050a00ca04601d4001d9001c100042200c0035070f184c04c403880748601030008128450303030240e025071034018009003182c0d401404180001c80036000000d807070030740c0e422044500e1241c1c02594292524 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 968364073 1250 968362823 968362847
    0x17060a060c14011803080c1e0309030409050f071106011802220b0406080c0a051804020c0d030b031204080303060108041406190e0a121d0d0503090a061e 67
    0x5801ca20031070520340b500a02505150100303000b42200c1007002c0703180140105500420301244550240701998402c00702c40c43d064040000c2d0900309030b4a407140c410b840e0a45c41103400000103181400c0a1107090107403080420320500003546d50030508401500400d032551401e11842940c80c11060000c15172110039402404280110382001e24141c1d0781040c00442001d03194401071502c1000714013048040d40200800d0380c072044030000310b07150820022003e442400780480020455017842000e2800d0b8503540d04480c042186c0c5821900c0d10640c7c0c420082c054400c04200790700a020b100ca40030803d241140980d001da408002c091800c65940c00011900d0a0008000366075409103803211094404050080501540400d0009004194400b04032000d0340d0102580c0746032075004840301c2020428180003a00080510301e007801c0d40300c05c01e004149029111120341588010b0009500080020000041039016420b071070007540b40350345103002d4442403029002914610503604003401483e00c11600c003603d0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 968365323 1250 968364073 968364083
    0x4060605072117090a0210020319080406091401051609050307182007050705011d01031a030d0c02100c1e0807200406050f011709030f130617060a060c 66
    0x200090002e50381003d010251502d00c0142c22031150302003581090380b070700c001e04104c6000461a086207590359034040c0554421042c20801001301041c108403003500f00410a540200d511074465500181881c001c15040c0e8030402886501c14030030b001759003d5420a0103c0b4402805480745a00d8001c149080040e14646c900c480b41e13680320501c180900c5803146a040b600c1001e0225141d0110340360a510b0100e55400041c1400b4044003000110707000340321020a83c846c2880e001c10301c091910500c041c0001c88440d02c0b07516008654044403020740c40f0b84003080390b900840301c0f0084d40c19035003400e40e10000d5864000d081c0a1205140500b0580100440301c01d551081f00c08900d0440f454490f00d01c40c02d41d407411600c5031100300c10401000d14207030044030054081200c107098003200040003c0d2501701c2c03001e50b105a00c0028000581d11038001e0058035401144a804250f4840500000710081c000074000d98020501d2110072130201481d800040d48a000d02a01c044002414294251070201d615a41211707 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 968366573 1250 968365323 968365337
    0x1805040e120708040618030210030e010e060c09090a140103120c0c032906031b0109170d0f020616052d090f0118030b0402180f06040606050721 63
    0x70541510009000090207001501c0e1202d0412000400b40c039203a07501c440070140149014005a600e04040c03400e000e1050a0025200a400230340b40d000d002070700c0c10f00b103807400f520003045541c0500303400410f1200720840f004042940c8000c4075204840700c180348400c580b21800d0040c00003031252801e01c40e150805042c0040070720999900c00007162400d0708100c906544d11702c450480c20750240c0844c511000c501c6813034501071070040082a81c882401c412032030b44a0462011190a034010240030000c0c00c40c0d07200340c1e404007510b07084003981d6944036240c83c03000030300f0007030018001407010400341d018910040488103c80400b4000316400d0b0003520041c40c00e80402c108182e0184a41a04000c2d118003e40c0b032a901c4012010400c01c6950169942d035040c4803684030043d00c0c0c0f1840160000a8075413089203841251a1400440c01c3d80e80c034541a00f003025819070a0018024020140b180b050700700311010300007951941000c45140c051641c000301146078407a00c1d40c85400041c60f030000101d00a160400d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 968367823 1250 968366573 968366593
    0x10f02011b181e0512030307120f060b03010308030610021c050f0c1e0601062f0a140a0b0606090907080a15061d090c030f070c020a080c101805040e 65
    0x40c6003500400280d403c4084512004c02040c20401143c1c2161940d05014600314540031401805040048408400065403410005140845580094080e00034481a140c0303035038603071800a250398829a115403007140d1030208000524400035590a8121800e1070504510030303c0d080a4840b9040305180c10502502440a00b015442c10011230840b1030015020349106508240202d081c4003060f005a020400e47e9070a801c0381c943c0d055040100c0c00000818141e031a072951142030f041c4030040c40000d080700c101980d0500c2546000610500e560f005078a9480540c072100104110b5120304c00d00aa041025100041c8010303004200f0700d503200401d0800411400084448690040a035801a01c0410b4078488296011000d028400700c2c5e0072001d442000c89410180440f02050000a0040c13900e20301c1c1000007021240318100c20f9086a43c0030b005d61000740e4958105640310010300d0f0549004000b61907202446500c146040394420800754010402e060409050001420203602420001d1080744246 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 968369073 1250 968367823 968367839
    0x30f16060e0307060c111e1204030f060b04050f04060c030908030a0618111c060b0f0301060e0d020915030309031b031603020307060c0201030b04050a0b010f02011b18 73
    0x4401d8031203510001e540d03600b210340307003003400c458840d006801005003000d00c016144a0001d140171a0001c0802050a070540403644289841d00e4035030810365214010500208005809a448003064031907103080c4900c0004c05d0501045070b60841d05400ca202140002c5008200c55601c0213010480701d20b00403c0e02855174031101e8a9600c155402500681d46001c2000300b05d500b1107124141881801c0d0502c0030b151013280c1071001d402000240711103429100c00c4502600000e5200000800c204000b503a115417000d044ca5040c0d801c00d11a0b030022811003107a4162514050b0b03e00c40a1030380c014412022600d604d40601c002002130700b0016007520041007a4001590100030760306189594042c14102c18522400b850305008640403001c9407600352800600060341c010030324000303441c02482c01410752191400100c000d420714a90250b00145090300340101c02946811080b070701d120a03202d10680607001c007000c03401c84081c24003011342400034207060030115109070801c1800300a04991070000316101c00c41c0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 968370323 1250 968369073 968369081
    0x6040b091903020d2a0311070e01030609021507170c120f0901020705030607020a151e091704140904050c100908060a05010308091311070605040204050c0c030f1606 72
    0x800e03000f692180103a00d40c104e6105091509603040141402c6070200c0c8442c40303841c8949040710080a211000322045c031500302c1041003e00601c100000c20540e96075070b0400b44000d003203040b0140e0013441441c50140907644a00126510b01d94082007400b10300d008890320501c3c681000c0881c40d003c1c0a40f85d034917080c10803848042c01c2c40e071f518084003690350304880d4006071501d01c1d41c0d48000c0c0240c002200300701101d03401048500c44c150b082100aa88903101c3c540d000700410a100c07200340d52030742c034070880541004160701400c05148640392100e0130640c103202411543c042c504c82e0720201240b15103601e805081030812103422502c980d0450baa40c00e40c410004d10003c01d0a85c180c0c0006965078810803800800f044016089408050304100035410b40e01c0720f1100b84140704c2c049008480d403420148803e101e0360b00c40f005522070850702030b0b101c9155281c07000c0903160541e4180e200d00d003000e000c1028110f101c4101e40045061b00d00842c50720301d08400b034284641090164103a165801d05480b001b081c45805 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 968371573 1250 968370323 968370373
    0x30610090503330705030f060d02060406081b130501180e04080c0105060f0f040b010e0901090f0b0a060f0c1407030602220609050f03030c100209031005040506040b09 73
    0x11810507541c3c01100740040101602c514402030741094244140c040e000022681c1200111082c0032041c3c0e1410081011925031000003034100c2800030300010003070750100016000302b5488521582030520800d094049001e100c1380c401c400304a0703541c20042507000303407151401c40c000c400c0d43c0002c5a43d0b5070969030b0295021181a180c0b440300180f9500c460b88284902d50744003800700e803000d0760002480d010626544080b40d00c00c0c041e41d03840c48150704584c01105a00c11400b4001c104003095070b110b00544020302580f5140c401e8560a00344541c6607460245040f105403540d81c3d4070b600c2c407040c03103803c01c81348420680d40684040031144c0c3c0f0101441c10a022613005180104409a03654142004a8513841a02d1007030610b4800085020b02c1040e51082c1880110b500407500515142c03240400241180f003800ca01022911921b042e4880d4001382e600903280112003101a03465299004030700340d05481e0202c400a1003074020b800003800045170f41b1090f9410a0300301040351080b01100402d4018900880 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 968372823 1250 968371573 968371603
    0x6010620070f06051b070b04050402090409051f06050607150c0c12020a030e01030b03060406110d0f3306050a3f021c05070e03120726030610090503 65
    0x144001e800d0080f034041703040d01c503022000b040c8292500400c1e91140c003d1b03000d11403107982c0024540c805550342e501310065013604001547c0c01b8140000044400580c0c105906019905200d80041c070380c64107400b5985052380211104e0f140b0001003c4503002441d214841000703100710180c2c044013090b0301042240d21800a84c0041c40401d800b4100502981ca4001c070030750405050500e14849614042082c03600990702560100f001c2446020031899801031011468510340341c11101c050720069500690118125202c0703425007000c5080340000710648190030850348000c4440100522403041c0002c11090607280307403034510382510040703d03020900b0f000c0c02c40350126031154524102c0004144800d01341c0c170000c20700310f1406000900b20b440c1c44054a80006620f540c950020742014000c04404071030180050a4401e540781a007280071081e00400d1090358007100282058150460090a1001041541c0546801c5961b8001044041c1e55603020f1041001124071000407030f5203040200d2648a80c0e40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 968374073 1250 968372823 968372827
    0x130f03020303012108091905041a040e010506093111040c020712020906060c120418203108011104060512091603140f06010620070f0605 60
    0x2107454540080501c1013078030800d0030a40300f07400203900324121070350010103032815141000b000c0707210300c00b24003a58070641d006410700e01012241c01c1c0241c400075100900300e500b007060420b515081c600303d607002c94905400c00158408501c004541c6c010160311000d00248580300310102e845107841100c1e80034000c5501c4100080380060070b15140c024104040401d20041000a11300340401401d18087e140107405005841701055064407a201210b03522189030003101e100080315108406581d12601c0341d0980542021f082a0820a1900922a107081500c10142c114032080c00c061140380d100c40401c848103003444040d81048440001ba81d540150f90076030024081d0301e0500303a00d00396100702021620080f81013000b40100d64104050b501d001500107103841451f0b441d031808a107028004854007c07518400ba00010800141c02250380b8408509019907036041600c418a542c2e8900038055007020600c01c10151a00d9110540428401c2d0b8100084581155507500d10442c1d161040d002180041d0700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 968375323 1250 968374073 968374079
    0xe220c0503330c0a0f05040902130302090a0209180606120115020c04090b010e070c05030403065a09050309030d0503010e04021507060f0506120102180405130f0302030301 75
    0x541070310402c0c80c0400e000303003059524021484036460f02ca08140ba905100e0314070101c1035810f2040c0203841c06032103462002c540d42e4040200c02c00d60391049220032803041d920342c000140c20034800d00942d05040406401102c01580714441e407594090002c00d100e80140003403111050a40395000158000c00a8060081d00040400c5000f400c040e01d07401c46900950400d0940400260228051030440d54105c2011542c2d07120034804a03000300c54000f0207002448040303000700500c90b06501081c0008155428000303c00340c103d400894800301107600c00c0c8101c8940136000c8140481403280a18000b0f0451a0545015424184011101c0c10071090700c05900100703040c040c6007402c214810a0f07000500b420350440d850940305502084d00240004d02403500700b0388445040301d255007654400c42c0d100c1030601080c156003013601d00801c0700702e0b41c1031310884400100c1c0034540c80c18400ca4555840025002c61640c8006040c8005442e000e080d00560403848401c075400f241054001e070400c68482e40c0619540d500d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 968376573 1250 968375323 968375383
    0x10e0d110307140604030f03172404110319061e17071521140402011e020a0b060f0a0b0a030e0c0109030f050c0a0602160e220c0503 58
    0x940da8025440400100010010513a5140155070449501c80c215081c0c015481c60304a451000f540081074101910710705115100c0c880c690522580e28401c000100c4403400c09003040162140c0e4020f0341c100e80000c03c0450b440388908d2290ba42034940301c140c04103140743c4c0e91900c4500400d016032800100f4105103018030440403a0311a41d9184020344006050701418031043d00398504105400001f070041505035140710fa60754041c1113404c0740f01d154040003034000c0d1101c078252000f8101c0b800ca0003d00c0110041040c202c550610944a50980d401041c5c41a10740d0340340001b900001d0040750f8080408580400386550300350700d481c090190009280d4480d500e200005d0252500e07803500138440c1c0c11408000f00581d032b0000e075100c1141d8004403240d094034607500b0100d003000d401e142c006402188070342c00890100e8000501c08a0024a029002c0c583c90b520000c2102c00c01d03043d07a079400c852a800c05c1c0c009921302024043c80c0c030706000d40603c2201030764400010b0b1415007501310f082000742d020501d010041c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 968377823 1250 968376573 968376583
    0xa0203070c12120b0d020924130504110307151407021c02120102031e0a1803080610050f03040204150e24030c1003020c07170a051c020a11010e0d1103 66
    0x130410780307042c2441c0a841e130024200e038200a0600c8024105501c241610080144000030207540282c030010342600b50b000381d1400350808542c00d4442c500700312801e8200c1d080019040702103904d120300520041c0352103141100d1900004003402d00035003040c0038007000750b170390300c441510780040008a00c4002861751041c080d0429043c41e134040030340d20600400c01e04241c0385812119101c10300340c481031285d9808408034018807a19404140b0b2141c0382445004054114151a000d034404403002030f603803aa404011101d91140811100c0c135000c00344042001820030360000f90007012181e01d90041d1039181c91100d880000e08440d424048041c2004011591002180b04002d0b41025000b41006044800100e044402e40c20654003c00d5800281240809d0701884482c02820220301c00152035201005172594500c428003065401c2c0c003800303208940100642008072884002030b0050810201643c458141082004805606000180020251a40d14000b040410034800d121001000d17482800341407601c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 968379073 1250 968377823 968377841
    0xc1511070b1812060105010804210309171303170f0a03091109060907080c1b010b0f04050609281e0b040605010c080c030906030c030a0b0d0b0a0203070c1212 69
    0x202d000f2450001d00c00d801152042c1075a2081c201107200782c80764a440303130030b03100c12207000759141c2140c00108100c42e602d9040f000c911809500215449403a110290000e449104a9503203d000054000c00001ea0310300b00e1054140301150686041005003e95801e417540407100c050000383d601d1048208002050b500501c203820300303603100c41f414075200e808201d1859018005034140500b45000460b07854140c011920255400c039400c20008802c26060f44c0030707000015410348a20096803082c41141403522a03076120701001408a80592944c4000005170402c1018100d2800c401c03200190101c44c8070b018007130320100b0b10040c1d14294010030810030100c5102c0d4403250b10403424040e0801aaa80c0051840d880310b8001c4085a40c50460300006031a502c1449250303500b2190210400540d2980310380034501c2480800400d00580080c2800c001601c804454000c0503410312201203180300003198090742e8402102e080034800244642c880c046804201644076001580710500c0204405030b0340940e2201e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 968380323 1250 968379073 968379079
    0x30c15010e010f23121002120a050403090e0403090e04111002071a1c090c050316030206030c1b0a050304140108041709010909090c060801080a0c1511070b18 69
    0x449060080e4101521100700420500b0070b5120b40c8080306646080000d0320494003a0106c50104200c1e05082020307402110061258001440000d00e1402c820301660744525415640c0008103800c003111500803d0000d0016000c100301e00b003000c07446041e18006103020354041c400111101c0c40020800a24041001e58001190003605040080c004000c0c3d40817510b401100f2810341315000c0383c1c8101d28001c166640145883e042c8105c0009004c000354201c0d00755401903050380e06526071002081800120381c400250000070400014a5901d0003101070f05550300b550301201c80c8040801403007850300340c0c1e0000c281ca554000203004c11000ca5906d1088010345400e080c00001031920380c071111041080401504121400040c101c1c48076845007680c05e000d0034000c801040741048605006640794110b01400e00881c0c1e0720703070020a100c100003070141c00c8240e002401d02036060408801d0031029580c5c00101e41808840c4a200207020303824445200605003450440741c550034000e000000c030448a1030000c0c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 968381573 1250 968380323 968380349
    0xb0601020f070509060d06050f01030c0b0f0403020f0607060207110910060912080c06040521121819031e0906050d0b031e060402010e040b0d0b09030c15010e01 70
    0xd00803038080b03107000440394100e80341e0500c0e07540c04022071004151010300401e518640300c104014a46800382c060b060b01c2c007801d00000f641d5103a1000c400a40304150801004c0882404108011318008940c281c42a4015140c1810701d8030076a01c80c01642c00c8280c007100c030501f09400441c0541408480c1c25440307494000442281c80c6020800341c0114143d0207043c0007254010104814000032104881a4594040c201ca00c5450507042c10751b141d01c84110181c014071031039984800c21214100c1900d80d424080715401c01182c031a5a140c140b185100740c818107040c000d003031710303e42c2c2c007543c101e07000c90020300139111850341c00c80c0800c00345001d00000701140c06000c08040c0c00d0200a900c001501d0201104940007c0e500a00f00d0000385801d0206440c40040b000140842c540c5403804980300d8060340c401c0e00d42ca040d004110042100341c6200744030854215105043d0400443d040c3c4030407a40140304542030b20318007490f0156260800781c04103007400d109040302004128048071495458014800c83c1c032040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 968382823 1250 968381573 968381593
    0xa2a02130b04150605041205030424021c05040504090c0315090215120402010c06090c1215060501020316240b01110c0d0609020316062007032616050304030b060102 72
    0x170308140264050008594001050541000410401c9401410940c805544a820000d20004c0d01c031614400c204014090042c00303440c1008a4013000a004090b0340300e050500d4200810b21000302034038401070340c6404001030008007003040d200602c440c2c12040e4601048540301d038010b202540140411018050908020340403145114228064020b076091030620107800d00307414500c01819201e4401340c0311155400f0001001d4014580c1d207000700d84500c0f900c2d8444c41e464409401141c00324820240942c00c1000401030210500060b076054501c90b502c4940040701c4407105130400e28001d0805848145d0740c101085180d07070010a81e52216684031b0050030200c0381c91001c03456900000d68000c08081c0c94904800455038140000072503486841d0b01d11040913501e681c01801c6d201031105154100140101d88454500045002020390350080c40385002072038025252030343c48010051805014205000c0044900301c0801c000c3c9106001e403008544450440c00c00404060018010707506551040c8035403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 968384073 1250 968382823 968382827
    0x6080f150402010c0f051b040c08091518100b1801060c0807021c0302061b0f0f0307030b100c1a0610030507030f02071a0109020a2a02130b041506 64
    0x3240d1281c0e0a00e4090381585007450004080d40184000400300d0086890306004081c0c10766400b800840c088800380300b840e1380140c0551f5820000d0340c014040e074208000c2908802c800b001082d821107050b00c421147c0100604045040040d040384480703080d61101500401450a050741d110240014003a50140303514105014201c11a1010002d040c0301c004074100b4155514903101c00302840c0007402c240c03040b2406140081d2180c07803c076480681c000402401080684a44090f241409140c05a003131600c0e260407040680c9802c010590010035807603001d4955640c032071070b440d02450040754585900d00922490402044103240083c07003101c3c518002000142d556000307844e00748a40c81e040024442c1c58070030044000d0107a40c001500e00600000b40c1004002e0440c0c0d0b200510320a6211580081e40c1381c0c7c15000c164418513003500000f409020000b00e03040c49030341034064900b081540c5036026029980c08650511905403c4400c0269190122030040c2041c2c021080d13028060100146464100340f40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 968385323 1250 968384073 968384113
    0x3031003060b0301020f07060e1533030d0203030114030303060d02060a0c08191e020a0b07020a05060a0204080d030b0102060a1814070812160b1f06020106080f 70
    0x40c0845840d4a125002c40d1029411078260081501545980f2a8507081800c0504a8070f03a04030200d21071880b1040000c486208524003c4442189100341080700213130750a40d42001c021003c0000402001d06422603500700984c901c0410960055900c0e50316000c030341a40c0000c0a84094080e8004004000b250f030340d45200d01c40d00a504444883d21404100400c407840c417880c10006090303e1000812882c50b020302d17540d04101c0c10803030742d038003100580c8007a8520001030449403d43c0503a110880120000e84042100c80e40514188111100161542c503041d140c94025188054999070001d814051820f09000b0000710201034241400010b804a00003569031100804105078603545248001c44190000000d403c02a00440000007840091200342e480b00401d04c00e410841c0302c0c0710081d80940000800b81c40c03c21500e403140c0e00080100d501c407005480402450801c0d0b14118100203c11003081b051100e0240402e81d00018020b0b0402c0203541c07401ca003010b844446940203580c4840b10360b4901513 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 968386573 1250 968385323 968385329
    0xe240103050a020904061808040f0605040308090d0512030a060609050105120a0e0304170d02060f010e0c0a030b060a030603023d0e1003090c090c0e12100908120108030310 75
    0x18031840c0f25170721030600d00c00034000c0b49410100c001c51848960103001045001d0300c1540d281c004c245000584c2d464013682c240c03040c2d220041030300009200b040d03041d2074403107c6807000500070f40503100c1c4600d43d004020419030007100c1801010381d54000034080141d11555000141c402820064980080e00d020403516a8000f04500e0005850309c0708404d01f0542030098800030314690038807880b1550490a0507480740c0700c40740c8190051290000042e102c82e00810003034100d84500030f178000f558485800d0340305070b9444054110203054880c641600c2e5900d0754002012402040e960015801c0d0030351040000d102050003003507041c00703003030a0203900e1240700581c0d4144020b00724107030b45c45800b200242510f094001c41d01c0f6a50199000e982d9040c1b0b00d40541184048038480c90900101c561961065030131200120860400603080038030402040c00d00744010781e03000c5a5241215500740f1406855415500854012900320354045111560340051880d17160141500c08040d40c103600d440360104490900c548 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 968387823 1250 968386573 968386579
    0x120f01090c27080706050705060603070501090902070318030503030906061002071e0e01030c062a020609010c0204021903051302090f0709030506070f11010c0504180e010e240103050a02 81
    0x200d4000c00d09040d402c080001480040c0030b43e8401640c4050240040d0409401580e00d030054800003174082c640815079800b65a0141c490041090810011400035000a84c0c00c906002e03c9001c250814040b85825000551245004590b28a070496507142491030181c0000e0291540740710700c910b946d4010900d40e0130368110945400004e1604009240620041d510220b0700032441c400100a0140c140c442000340d0b9444d0700d40100c0c1856030f000d442410a011000401490162a02c4400503d0624010070f400c0350f05240c5104c0080c040e800140c126070001d60308502d03040480741c034000ba185e0940100340e44a0018400a41c1052071500031403c2440014540c0c90029140000181d220340500700420165030080100d400c10700c5d102c00060202030031021018082030b540442c15102440501800d40d4107695a6959810540380020022a01c5075810900d07541c00d03101d80008080c04001d00c104845d1403030403002024003400100410f040081580d02c3d5039128040d40005001065002504d420900d03415 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 968389073 1250 968387823 968387867
    0x4150512010216080307020d050702031203060f130f0c090e010e130503032409190506240a03050912091009031b0e0702160506070204060b120f01090c 66
    0x40001107009209042071088100d80900300031080c0310030803018512504a81e0210f071041141220280c070765008164000350305a001081d06000d401007403016540244000d458100c40f800303900000345114490380ca141c072100e80c3d41c55000f1541040c90207000c480c454507040c0202d185040c4440540411414002e5485d2441c4007000f0488500a60f00b02854140e0000f060329103070308102e10104044401d10b008100b003030703100c04601010f0b841c024040720b000da0740b07151500d0101d4403070440e2603019000082c181c943c06451240c1640b00f580d90080f40c814408003102c0c2499131a07844c124094101e980241250b452584214840c00e001d00d0310204944852904581083c0001950081114401059040103110540d10201071600e0201000e2400a4568000d8034400b66510321208a07601ca000c200003a60540f64102c0802c0b0504040009210603070000d4004520691034101210941d4800d0290512201c481e008200f0110000511507014080a40c01403001081c0302c8401400c0c400540c0c610b809000780 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 968390323 1250 968389073 968389099
    0x9020612071b08030106030615080f15062a01020c1009020d12210506030a1b150c031101051026010e0c031605010f1404050a0320041505 60
    0x50b004107002200003400410000001d850003800b07640080c03050308042801c00741c020607070300440c0040c105480e800e5954421680d0740d042c1031546008010b8038030240d180d15000025419180c503402042d0610600c11609003100103c0321510401d240d00b00d0002082c4d1040c050040507070f10112b00c002d980d140885004c82d11040b1030000804510b0ba4100040038842007682d010042c030f40003034115641d801003090340384040401090781c909507141103855641c1a000903c90300000b817003103000d41c0c10903007c044900c40203039107a45281b146880e075107881e000455a0300301200101680000c0300c4c2503041c107001c000e028a0030000c10300075003103020f03000e02104001d84002030070f81180c42950045040e00e01100900c1040c1444442c02c0c3c540b0a455220340c040e0040360124101455948a15012a0740603034801c88584140c1ca0b007150140d020038058401d944007040002400d503900305031040558000c4415000b510500b52008408602a43c030f400c1c00b0714200002c82104a452048007022504192154007036858 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 968391573 1250 968390323 968390327
    0x131a0a0e01270903090e130209072706081906030317070302090a0902030a061202063108100e0606011e020703050105040605040b06120c0d06111b100902061207 70
    0x815500c2c58140245801442c0060640c88500401111a1142c0a4480d41c840151000e0f1a40100380701a4111a0680c0800d03030003031017445034100f0a520b40500461000c1e40400030310581070720790b1180d00010151814062400b0301c41d4401d200e48014014204190b91555802a1008542c50640290104400000343c1914020b404541c1c41c410014824400d4548800019000750000d4411711081c5140007000b01e040401c0d078a201c894140c008001500381b9111120300b960f1030800481440c18204602c0f29a84045403084d514070250205e400a402c0d41015509074030b0440d245108050003d07800b1400303010b2282d800c40131080c84400140e00114000440e2102030345400500c0e0b200618a6217030004100910049500ca00c0c025480b8200039080d58466004026090f010101c2403003c9803c00140c2c0c151600d00310065413417061150401099107144140750550503080161081880c0400b00708001001c60207200e04c211060a5000c2044800c10079000b1810034052101400c03d03094840010504482c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 968392823 1250 968391573 968391629
    0x8100509040b01060906050f0f09040e0d08090c0109030f12021c110708150c09040b040609021b06100e150607030903050d02033402131a0a0e01 63
    0x818040d21002040c1440e18003640252024070642c000070b01201702c086142c070310030390803102c3d188840c0704894201381e41c6048085480d070203400d07543d52082c2e9803069900b00d49414400780c9011200c64990680f01c2c030b011000d5500f0300c1425040035040013110803040c40003800d0a5180da4580f81c0052000449010030b400513868050940f122001840e0100e802d07035002d039481002c034444200f001c82a40e001960b0344100c2e990302c1d000d00781d05844204c0000006001c41e40e2407000383c5600a0000e001040c7c81e602c0201040c2103445681084c1c0300c40750000340b01c06a1071190351550a0010702003000b00110704d00001070500e010501d02569810300e6040c0c0200d669030400402840c84080014440b80d91400707039280240c5858020700c01143d42d800340c00035101c0558004004e44035026101088183c40c2d0b000300c207243d40c01101350403240074041304480340c10000d27840d00030b058071580c484020005281ea2150310405d545441040071a40300b50280c03c420310040040000b00d504681c03051410708920302546040712004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 968394073 1250 968392823 968392829
    0x90f0b18120705010909200f0403020402030c1b06061e040b18100e090a1101050c01052a090d0b10150816180308130905090f0c09160810 60
    0x44042001c91a000d0840400d504048a900740c80e40991725a545a40320140d0702e600241e01c00004101c00740219181c0c800f00180ba81c4000c84041514081d04c0c0e0f80040c0032a04103545800b4036440c023103614210f0181e460384105e45400e4500c001c1c1035a10780710340021160500202c1d51048400210100344151301c1c0ca41000791809402040000c82c0001000b10801004003252907001c50f040400740012281d0b401002d9901409444000d84401d082e0b54440300588852034070050b04001d410000114400b4080c840d0078012450070303007081c03600c4c41958044160040445108207402d401040750401c503507952a43d0804007a44400c01c1545275a81c1c043e40c6003501c0c5039a0200c0c07440300c0c0322042c0e4011580c0c801c182034851500c556101c8415450080d080301c1c6075882d4079203070030500c031911000d0001c0b03120f03c0041c14804110458080c86507071a040070340280da4060396003c03000c0d0f001d98007894880a090020207404001507071201e956145c010035402400400c05003800c24480604d02143e40c406129901c9405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 968395323 1250 968394073 968394079
    0x90c0605090607150905010c0c1106090a030b1923011703120f070f0c1e080f130f09020306060f16060c0f020d05030603150a0f06080a060c090f0b18 65
    0x54013040d04030b0580500341c52001110154070740303c4040f850f01d02443d048003500c0c0e00700b00300380c032541c4003078060044991240000300c2e4050a60300740000054401c0203200d00c07810020700303101c0c2c003001c10380c0c0400252030749504450440403111444510032464848014111807100e038640307180d5081c60160754214803880100c000c17811110030800900525660305035008800c00c1d6120b402031400c2c0304048646001120004283c29240c5613806e91a01ca0b0314858055140140c104514001c03c0d00c6654080764020200a1181381425004001c0800b00c40c179500020480714609610f1840c0c0200012914070540c1c10705801110302151030049699000c50510070b03030b98440020860303550341200c09040b10f51103050350b20041c860310208100c0c0d544100242da00841e000350050400214400001030301020080c200341c1015507620304032200003483d008a8005040756800751041c4c1a05042081c2036a44010480e418829010390070082040c0d41c001311402c4030f03030700b0782c03126114000c803a0810032441044078090384c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 968396573 1250 968395323 968395343
    0x60304080a1805060f03250e12120304120c0611090f030d0e06090126011a030103330e0105090f0a0809010c0c0906060909050a090c0605090607 63
    0x1041114150007060700c29440c1c0c691a0140b0b0003101680c10510a601403107410030014002c0c81c6681c0714800142d41c00987c2c3c0b503407000c0740d00e10b101c1c003030a07100d05000004d00c00100040441c1ca42401c01c100700f02c1385400b000015284044a0b601d00b00180d21000d4802003a804c440c2c1601525240705010351040142c1c4032005025828900d144058250130030030409101ea01c404101011038900058000441411521085c00141d400e00800589403c158400c03814024039880300580c9802c007000220400740c1310089207078594107160707076901448407480034800bc01c1001c10050001c01c094810741030448090003030725603000407840000c3d16001c0c801d0300c01d03c1806040003101c03c060103041d0003081c1301d0308140080ba000c6c40000c1c0066031703030b461040e000a40840750402c0312103181d511620511106a01402c09040c103980d0b1000408210760302c0384d0048002940e080c2050240a40c18001c080d04000d0886092003900e0f00c544440d10352100740d05c140703018058002020728003912400166200582c010304400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 968397823 1250 968396573 968396581
    0x3060c0a090803040e06040c0c150b0a05040f020a09080a0b13060605030a0515060d031e020a1410140106020319020f031308010c080c07060b0105390f0c09040c050603 73
    0x1152181e019506c1d10711031820980e461081034070801480100d40d401c28510109082d00c0b0103007800170120000c0c02c5030403803408100071685403200e0040c000c41030141c1f0001030790340001c184002d111901030303040071040e0340220320b41034042842d00700c24a410401d0001e40000d5050503107003e100030201c5501003500341c000e22000105000c00450441c030000010756400900d6500c10040080110020380001c011400d1000c0444440300034050080543c031460045a6a0b082e15458060b030b003a100e83c02d60074007136101c2212100140c1310790182c0031404810b6100c44a1550415101a403240101180208000000b01070115000d10030072040710303600d082c1d00c2603942d100c00300d42510308000464040c3c44081e6092800030000c491241450910403c440d400d0070703042503030303541c3d0310405018003041c02c0d81005030a010908081c0601100703101010f05074041901d058054000350b54500c11000d00403066034022000c2900000004601002110011282c064403561940762204141e0210340105400540101c104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 968399073 1250 968397823 968397839
    0x70c030305070e2733060904060e091911040203130b010f1a04050102030a110304030c2c1510020307050a3002150406021c0501060f020c03060c0a09080304 68
    0x48a8038a450b1440c03442103544814441d031130035290070406243c5d40c4030503442c210300242c00d0a500b141c04000030031051520301d01070005002c1ea41160840304040c85c4000c10300c010014104680132070400c05501001c1d0340007141c4c0b07848100000c0414894041d90700000001c1e0319403107a07a944040e00d17902094186007540c4501191003419090300545225401c014184c0c6103001d8400c0642e030417100140e008501d0110031100854010b081603d40e03030414032042c0b002100040d040604c500207807000550310100442c0704c0d520218410444030062408460f280180704011407a83c06180d08540c2c00c1d0350303000040001c240200d02d517100d0403c0203400c0740141031000c0304101c07101403d642e441084500640c2d0812038214100d141d4150311454401590009150030580214420aa13500c207004820040c1000400008100364642d1a48440310095980c0b0043c00b001d504078594141b4051103200800341c0400c00b002283e40c421000d0440c2c411544042501840e81344034030141800740c20400702b500d407140c1d0f03a0002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 968400323 1250 968399073 968399119
    0x1c0f03180801051005240c030915090901170f1005061f2a060f05010e0a0b0f0409050f070807140621040303021e1c0203070c030305070e 60
    0xc0301804406040000400a105010b00d9020302c0303081001c0000c851912003005212506071940b4400c0004401c00410481c00700009010044143c2010703650b20310855040000c038802c0a05113080011041c01014410b40b02c8007040b03415502d9201036101400000b00d80c15203401600e44085070700e803181080e8081c0310001d46c0c1100307008d0b11080e034807110800940c01007098080b8100d89148005887e41413100c00c0d2101001c0c0e102148003840f2032446808419840d03080540e105120610046a100c100400210011f0b0380001d501c260001d104000075110100016801d80700c1403511445191100503240a01c8424003e41f0102c4041f001100c51965840580c1d84d21003806101d200000e43c801c0c4174440c517504082d401c50b40c4680c5d8030501d042d6070120140000c0282c4074041c10540406a00b4003101c40309800c00c4055140425008840700d03200c014030001b02d42174999001000c803440b8010310500400d0b80c0c020600083d0143d01d0f080200b66a0b0b5000b500f2136080c800c03040398951100c0075119038510302c82c600722 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 968401573 1250 968400323 968400347
    0x3020c0601060c0803151507050f0c010e03030d020310090504210f0e0103051503030f0c0f0f0613060f15030212010b0312280302190305010308091c0f03 67
    0x400c0e250181e0340d0700e900380c61088078208007070f000c1d1000700002550518462038481410400800603080601200000541030308a0b80c1d08680c02d51104103803040742002002078000180c000d00c1d0085248d952000400c1c0c03240900c040c4801201e4010011440715200c01c0d80c5100507200c1c3e188100100d2405081008407a80a0940400340b5408134075200d9900b4410700900c0d0788600d994950400c5454100c004400601000b007842d08625a08440540d0641e000d10003022000e8240b01500e4407421400c84050400305182801c9019074054982e041040501180855000f50000c1180b5440c2203d814140050400d10350303100d09562a14408240925003010851300342d038025181400c48000d00c140050072550454244d81d40340c5d1011009003080906080280101c4a4800d00041c504088260301c82c1504911504000817039000302d1854101803200240500750350843c0303020b02465240d500c80150a2050001c0306000c2c0034501d00c5041790042c028059080c9070790003003508803a0b030700c1802c0060564a6003d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 968402823 1250 968401573 968401597
    0xc0201020d33050d0b130212070501020c0307080601301a0a020304020d06050a0f09050a030f14030109050c040b03040309061b05060f0717090a05070f080d030e010b04020a0302 77
    0x10403440506a8480382e8205440028140441d661465140e04d201301e100100940108000000154010f0700e50409145c01c1a107140d000b4101c4905000019082c21403218140f8046c0d402800b04210003140005c4c40307030444502000c4542e079180c0c038520072035000a600c8034031b40c82942d05070080b004100c0c00b200582c100702c0c8a4811840540c443e060114140d00c400daa020f0360020f40c0036410b1000c20140c0d44501c2c4c0000448400040315155114100300303882034610f080d10103800040c490414181c1000907001607400b1072800c0c0c10041d01c1c041d11401640010b00808003501e80c0d41000542c20852402110702600d5410340f410b0b18ad152519004005039200c1c000c0e64002078181d0910001d400e0320300703001d01c100e80e8400040d1502340d079000600701003d04000e00c03034010410140c260a90040079138200314000d2403020080c100328002c0341401e0386414001c0d400400d20f030100c080c040040305004595295554801d00e004200484041000c078050640c0c0c0e030780d9992041c400160030b40195015801424418690 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 968404073 1250 968402823 968402891
    0x390a02070f0b0c070f081c091a030609010e100603050603120711012007061d0901030506160525020a210215030606070f05031c0c030515130c0201020d 66
    0x1a240300d1464201700c3c800d501d80c0340d00901150142026280030703c210f0040915102e580030b41d82d14000c91501003070b07605188900400100340022402d1405d543e42c05408044140d410908210794400310602c0e0503c109010181c2d183c001c2001d998080c0070160030349901d031200b15100c10b000e0429480b0780c9080c80349d00c4c0c0464410208600e003030b42044010340c40900c203240a0000180b03440400d0f101d000901d9818003041d25080030315200d80c1c0c3c80000031400b95014900501d007514141c2c4811313146010344c0c4080002c0c010f051040094008000a00c2c40000c41740d4200b07466010300610100e141d49155800800c2010288884000341c03001d0007140d40015070003150f5600103920b0440500e00a488180d65584e00400104440404120454a0b128855210b14100ca2604000800d0054003001500f0040c90058581c042058410707411b00491342c001c00380749a0014181480c4002440c500b601c1101c98810545884010a00a00039030507a1504510004140701c40420118440c1c10a003014030403136070320111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 968405323 1250 968404073 968404079
    0x180306250c0203030a050a02070902040303080906180606120a0b04052503150207140601090903090b0910030509190804080d080106210e0a0b390a02070f0b0c07 70
    0xc5910070690706600a40950700d4000c00c0002203e550340700b401303520150711450000180c1114a0b1004000840c003a80d81c124160414000742400d00401a00da40c0c1c3c1c03540c400c50f0344050802c000ca43d0903044801102c0e40031020106184080c1012000000608403403d40780401c400d2040110b00300807840017800840712000118140c412030708403140406800354480c00d000c0c101341c06031640105134031409140915801d0004900040c0780843c240c12414646481d0342e0104109600540301c0005001400c0c032007030500c42c152020803042600ca84024040585420124800031300a200e000e2082001c4800000d1448103414017458a510612030040640b1035003e241c000c1c240f103488403605036030f20342d40c5041e208205249900300c6240e079075074070035801a038075410303441211001c0194001c802d102d0b0541c001c140c5001080640d4814407c0143c40c49120703000c1210416810b0503134075066143c20300c0c500a803580520501280f500c5030a0b040340c1169500500c0109041c030400d009040c0380c0c0d03032140844001c5a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 968406573 1250 968405323 968405327
    0x9021908131e14030328180201141902070e090d0807050f040f140f150409020f1b031b0a0b0403032a0302300103020618030625 56
    0x591804068440c0711600e034a007441107102020b68260600841e06212482e541c1121141154810b440d0710484881100c880040c0c00b43c0024034401d00e260000080114109040c0e001124201150009041000c04000c00c012150040240d421111807000b6000a0304046040a03558135024054034085c00c2c071040000d00102000136074244003001d1945e030152580ca90100a0310140c019428209c0e00c06020702020590410b00c00c01c0320004d20040b04034110314030111040c02554040407000c54051000140c000e80903240d014110b5041703401311080144c2e0350100301018107060160740003045000103010801001840d001024000900502c8420400415204e120703030307990203171890014800d1880c88002004280a50700881c0c0f40c60b04a00e0440061101004290380c00d0031091040f80420303804a0100003600c00b541c18030704101109003802ca04092000c0342c1040c0b08005100091281d140060042020000a20a904109000f400710389150030040411080c03c1956400c1c6d2104c40c90403a54648014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 968407823 1250 968406573 968406601
    0x60916020a210e0f0a0b07080f030a1d070f150302090909031e0702100822030513090605300303040b010e0a0920041401090f150609051909021908 64
    0xc00f00a0031719001900d080e400e1405500642400c1da0f2400d010b0041302c0c840001000103504c54044040e00041000900303201d40f09007980700c1b0110600e0f500c0040140003403c0c40c050850180e51032075010000e071542030702c411030207441141742c89070b00150b1080c2131102c083c0c400009800709900d404c100340d091101c079201010280c0101580030354807554450b071040d01140229134a070340144003415609840b000c024103040499128410440000c1c10010f40346e900c8046944441c1c002e003600c99420700100b49850001104070280803014894040b01c5440049040b03202c08601c0c210321390300419251a0319003814030b249000710174415209401003400005829100703500c6140040ea074450002c2d409043c580301c00c242e401d2018200d29420a41c1c605100310f8004594000038002d0081c210049115100f10340c404040e2000d045a0100f5001540c4042c0440303500030a04c003041e600f00baa5404030a645040320420440e080b54008100a072002031913080f1030101c068609890b006a4503043d2141c0c0303480500745024 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 968409073 1250 968407823 968407849
    0x60f0e06160807030f090f14010b120a08090a0e0106030c120501081b0a122a030308043e0a1401230f0c0f0c0603060916020a210e 57
    0x5a440c0001100ea600aa00170f92035014040400a00da015660720050700c2c16004100341c0f074400410900700c104000034011020103a00c00e03a1643d284245281807141e840450040061400001045003086a1a2200054007d0422040d40300719945d540c040038000b4100b018044001804034181b2144180c0b4034001d036030403118084001e004c80c44072051400020360b4082c076510303400140c0c1e050025549020000010031180151002c081599284041003035010148000403822081d40c03c01f04082904208910350064012005c0001d06041c0180c6000e415121842000042d108808003643c0c80e022030000030180c5001d681c0c1d58541c5407120a81e24040b10740410b040d0000d600010202c010345800c01059880305d200b10301042c20305a46880310b0099400c0b14a100e04a07500c21814101c85840070003099141e008180c0f0014a14200315001c035940e020f00602c0d5100c900d51911544903864800c0100140c82904814007450300800c4005a07041803809006c6c40300040c000410f0314507945004a040007803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 968410323 1250 968409073 968409077
    0x70503010b1812070b0a090e040302060403050c010216030c050f12031501020a0501142a0313020f090405011a041a0d020604090203090601031e1a060d060f0e0616 71
    0x24001c0420060703041084900b8010b802c980001070051401804010705000744c0b81c458840c64841090400040650600b40d1012061048400a004c0441c0d00400c0d4250001d42501d0295952140c0520490183c410100041070a0203a00b07180418944e00c01c48070f840e031510940c140c540f10b41c014014203a03110039440504210314400c201240f1741d4522050031020708a0b060042d2020f081e00c40e2074403400c54850428201c0784503100e408200d00c88504030707502528502c40b103c00d00f41c640c00ba0302075441180030050812100e802102400000d42d074511060b400ac02c50014056038851038a854100d01030641b4226107680c946141d1827104051605000308110301d10014201c0c000d6044c0d200030803520094048082e07070084410000440c5050107400214803e045840040196524501d0702412465070849001d1004040e22841c030f00042081c5c00041d80c00013840c840d40560b45030040000c1980e00b100b440149a2031500795a151060310b203802003110300e1600410380b5503903a608100301c10030048540c48800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 968411573 1250 968410323 968410327
    0xd030b03010b030c2709060a0b12030f070f151506020c090402040c0302090d050714040221040302100e0a05061506030f270109050c0f0612042d0b070503010b 69
    0x41076040c0005443c03088003400042c4803540d00c0344120011041810745101e03440da0807038001c122400c0501d0027a840412015688500d01443c0107034065100d0040017032007800b2400005900701444541a5000302080e001080d91002803421f0102c0002400722034408a0f207081c01000c002101070021a00400589002e0404850755403568200001442c114001c40c0506500f8048a60b90b6116540c1d141c02d02d51140000741040390070044040000020f948445114600401ca0103000c407107080841c883c105181510342880d0f03110f9250aa00f4500c03180d81c951aa0351030300c80d00701d5100d000020005e94913030080d030588105890b51759006028090700c41e0001c2c2c0040d010800b09039102c0d00b908285610041282ea002080c082c005004c81142d142000d1110081e074603040d034402804802c2c40040c1107020110340410040141340d001c0340f40c9000301e8500041c00c3c80c410b0005818400348010b28040300c0010110160744074091407400801c008010019200c00d04200b000550060144044078143c40310178480c64 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 968412823 1250 968411573 968411593
    0xb0904020d1b11160e0a060f2d06120c09051005041d0f040f17070b07031406030c060c0a08040305060f01090506090a05130c090203060f010216060f1707020d030b03010b03 75
    0xa500c220282001b01c80315a600000a18141c3d46a02c0c0740140c100003000034a400e081d800d03404010101025480d0420380040810006103803c020110042c8200b5003000c03441d80e141d00c0041e1070740e5905030301160700400201c1c008000c0a82c005c00401c02d40d000c03c40340c03042041c47c0c0c1d51664002d40086414041d03a8403d900440d0115452483d82982c151142c450340601026100c1480c02c40d0304007007000c4400440800c248410030360140150443d44501403118003003458402c00080e91403403040441c41c068940040d07507800300d58042c044070000b180c100c0651595141c0e2850104c3c0e036001d088519468501c0603030004a10324069015141c054000185800142e460303184064008002c00391030b035920000750300c802600082d4041a1100142002100107880b464213906220002c00c490354036604540003240400ca0720701175003514030705680103483c00a55a94100340103450090b141e40c600b084c0703244c00c2c104000206500050019550340140d9040c00115005003d0600b6a0301008400340e0581242004d9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 968414073 1250 968412823 968412839
    0x324180f030a0c0f080a080703062c0702010b03120403051921030f0c0201050a0608030f07080903070819020a1a0d0b0319060506100203070503040b0904020d1b1116 72
    0x1030f03281c14004c14142d641c0030400d995001199000c00d48140106545100300002241c0600c1000c000740000a0785c2030030b4501c40801c2d0056134900c0e044100109888074081410280b01b50303c00380310300601500311100d02c007071154203080039009440304440504c18040700100d02c800c240c0411400d43e0b440b95020342182c1e558052225106518907140c4105aa40c3c16442c0500400f070080101665243e0000502410b00b40c00c000181d600e41d8200d80c142c0c4d4410010706c000203035075000303d5110540000c1c48607162075600c00028203102c241d500018880c0b02d0941904031b10260305508000c124400c8450b07507282d07581c80b4203001c0340009000c0f24140310b810a010f1402504815080b1201c60075004041e82d0a4841c00051501e40411010064845030b07540c500f000794604010456213804125400154100240c66075032550b2881903001d026031404000c60710010644650301600d0862002c80c0c414088440d8210281141480025010380051491442d14014500224005000340140c00503c18013904203291 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 968415323 1250 968414073 968414087
    0x106080c2d040603030507050706090b07020d0c0e010305031206010e0609010c020409021c0506130816150f0e060a0b0609010c020d060c0306030201110d0c0b060324180f030a 76
    0x94412298035803945076075440b4031490300554840c1d107400307403076285c141055860541150840d00510040c1281840588484000d83c0c0c501541107413800d8181c10706103060300005046034008a601c0c11540001f10400c1004000ba000c40d005440c14290207071740d8600111a0880020000790304034000300000441d07540310340500b18a80d0300103040442c400315150301103041092003003100f03090310000912030410860107210380c58000c400b00c51190f91a0345941c8840d10380d417007180721403500c3c840c20040703401c20007201802456003c10151400c1107510316404040c00905503120000760140074070380c00183d00002c0e900c40c9404861015001905041d01403005441a007449002a0b0340301548070181c0000604602644000700754aa4001c28058518800504411000b102a0843c0d4000c4d0b940d903101c0640c01500c200d4a1032f0090414105078842070003080c200b860034108820469043c2c00b0044007542d182d01c0c9070380203e40052403504107001d8100b01035221040480103480c0c58008001e041d610f180300d0390b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 968416573 1250 968415323 968415379
    0x1f0f0e34030e0c13020d0609060b09040c021c0c02090105090702150709080714090c0c0a0605042103060f060512010e0411100201050f0c030403020c10090801110c0106080c 75
    0x304451500052000160384260a1500d00d1040c4d13400040d9446c40f01d425006803402042c2d01c50341400b440303081a1854540380100c40c4168029176841c4181004c044c801c1010103402441500502480103185c88004d0446103001000c2e80505000d500000341418030034071f0544580013950140c03000b1045828a4413500101400e018100080c42802045120040c442c0c1c43c00bc2c46602440703103126003c9014031105c010001d140c040350303807000d0002c07000014010441c0c209050340003600245039a0b9a240170b02d5180c841035000d4100510150302502d965405600001c11707564801126400d0603516601110b180c0310380d0000c040399203084070042040c0704c2160342c4140c010b0f20440e080302c3c2c3d188180c00841c01201c00c865500b070041c2e440340140103540005070881c07a0080c90845445203035280c0384d20040d40d160030030b203041802000c02c06128607a8a10030303560403000e0522603000b44401d08400d508144e80c0d822160b50074044d540f0700080060030307035030008503280c4c140c802400003500385202d00d2a940e014070b0200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 968417823 1250 968416573 968416601
    0x6130b0a0f24080415020d180803190c021b0616051005060105040f0501230301090903120605091f0b0406050c1903081f0f0e3403 57
    0x10000c91141118115400070b000000e01c405440c5101e0808020200142d00c80c441c00d20401006100c04900300c2c805900240c03403a20300140c1d451000010060041c00c01941200080034207200e42420804c60100860207051a14000380c030011400007401c3c100c4035092080781c00b691081c9581c0e5a09980c0751032620310070100400403820a174a0ad2240301c1040001881141c40da000703500b140780c46100c1446250b4001d0345c00c1c03030b0040c141410302c13403050300007078072401401c4c1400080c0044510380b04a4810315042da0314101d0b02c16449581d00c503c0100500000b8808801040342161900200c1045110b68021130300000c0030b5040c161114841c113a8100300000584010b900c80c1034000c50a0b9104600520082c1043e42e00d0a81c0c83c404020100d041c250b0058003004408040082c00003c0b95202da0282e80040e15020074241241809081050244e030340c0d807105c09440e2111030001404403030000a80c0c4600c01d410202c6a00340c03421725a000001032035003a08005084001c000c08a21846a030042c00700070354007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 968419073 1250 968417823 968417839
    0x50c10060b091309060906020c071a03010b031f180b06030606090d031103071a06030a2d054c0b041d0c041a0906120102041a04080c0906130b 62
    0x1d88030b00c015a8007101b004d1b942c2540000e140e80d00380008100d82c00080041d001c20340c00c82806003080041d0307448103208907541450003001060802c00800410340808079240903584061340e0303605010801030903449440011502e061010800350400c0e80459114a100400c3e4518042000003000006031183c0800d030200006c420884507000d13401c0008207613003030040012480401c05101c116000140040c105406900310f80d0b0001c0005100915141c03030301d6501114080350759003030342882c01100c1d400b8102030880d101792040f8006500c1e143c030622807071a507207104250322900b4a0700050500b0248100b601000d01aa00b2520b41d00391059001d9464813000820200354050652904945064000d91104181c4c03c03c503001c0c4054070703007407099480001c09001c002c004000c50274000f80c84010000c01080c061070010b510001004029411600034040103540c0711a040c0e00300b222882c8036000380c0078103c5c4600c00c0d40540c440d0707031401c030180f1441003000034007050041c401442010082c001c021081d80d001610 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 968420323 1250 968419073 968419091
    0x30c021017240105092103090a060905040605030106030f0b070314040803090d08070212030402030f0d0804151103011404060e07020c0a170604030807090b0703050c10060b0913 77
    0x2003590142c1c80e280d4142000c0c0141050051070740c05a1610030b414841c0030400459103494200031440c0b1010068586030303001c01c2080b0400d0075845800e038000d0b030010018101096180d002420034060311015102008010703103e170300b8503007202c4660002420320b502020918000a0300300410a50002081c81d002c5000d491050700c03a50104400e9900700c030001e401008001d0f06004c00c1028480c02c001e0307450a0741c16410403900c003a454104000f019a982000000020b0179034808204404612000030f003118240113626500a00f0903c0a071000c54061184c05c0d0241d40102080c0105808a420b0809007851359207451903030360a003603000d48483d0300991901000548003000c140800d02c0780c074454000e81700b400300c104104013040381c0d10f401a00050301400181ca181c40c01c000380c2d132648958582803415540d1694242541d42c545240d0050040080000d1032808040d0b0003c09007000d00751101c01c4a42008040103280c00707461081c050074100b54000c0c0041c480742d1504c045480700f803e4000c00700080d2841 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 968421573 1250 968420323 968420357
    0x150b0f0c030d0c0e03012f090105070c080c21120307030e1605151303080f04150c060e060f07051c021308070e01060e010e04110a020703060b01050403030c0210 70
    0x620103443c0804244001c0025980c3c1c2002e0048441d100d80300185050f0749080001e4081c0c0c59640211201c0141c1c7c0c01003140441c5034000c80443d04115040908084419900c01203155924900d16203075000c3c05e1442d40e0700c1c0d0031500c51384240e01c1c1840640007034040c252800c6c01401007500000c022008254072800c0342103400c9000d100415008004d200c0400000e4103003004d1104c840d001d00311100300380c0020440a80c1f2256940e00c6201a46c0d4400391441e07840d00060404503860065030800b04498554160440e0350642050380301b4161440368200b80b0840c1410b2550685580c01140c9800c4c11b2010f040004001520942c0100405466603440382d00400d43c1501c260101e800c0030b48540e95440140c00309200c40c0070100700d082d0003401104800754040d818080700070a03074115103074402d06000c441c0f0200200d0f42d03142d230480300003c0000100c4a44620101500a6540030b2511082d10114900300100800f54410012182079917003680300d1410005c0c0b16030a1003802e1104550300010801c201c100c102c0030034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 968422823 1250 968421573 968421581
    0x150203161a0f07080907050a0302090403050417010b031501290d021611040605060a030b0301091401020d0608010e070506070515180d020a15150e1801150b0f0c030d 72
    0x354400c071800702c840c0740c1100d000d800c000016007043d034640d00c2100c042019a5401c131100098035415501081c060300c482c50180c03405e02803a0808140e40c2c10700303c0c5540c64102c0540c4141c24241003181110040540181071001031042070003150441d00c42d00b001007000caa054003801000c4114203410502d047d401f583c509049810481500e000751044180f000d040c0102030313840c03203e880001c4404009481c40c1030005800c602c90501c1c03e4051603120045108a9602948145001c580182508101d00d9140c18924002c0d031080c8560650640341290100f00d1860511980c0d005070000c0d8020508141080108941c50304554412600c500c1150141c03181c584c03030350060313a0154103501660000c00081c20b030348a042c602010a5841154032501091000c145811004100d200c800c1100003140c0c0f40c0c00c1030030500d01d4050f8000e035040340104400e00c0002d200300036100d071002111500800100c00110a42ca00001b10380c418401030010601c00131003402a024024440d822200c4101d0b03260811f8004104140c1d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 968424073 1250 968422823 968422831
    0xf18030804090209120706170a2a0219030e0112090506070509030a1704052e03020c0102120c0301080708011103150a03050a06060e0106030b030d030510050a090213150203161a 77
    0x600c041d1481c2c2c2054154000c0c242d0070501c50b44050100c00ac40d40944010201021100c888020f00b16581e800010700078441c51016002540031208240164180681070704e800d0510503000030107400392040035140d035205800c0d805921a026000545401804950b0380d002007103060391501400343e442d000940e95031000e8154103c04a4040e898514240400c41b10f5004000c80c0701e806240c00c1c00200301790740c0c20206681407852034100140c50320050031000380280100c0030764000c004903d0050140b40f0740740d040618100c6004108484840c2d45170705c0e03000d0aa941e584c0e4880d00c020414800b00c0c02046400d01155461040034080f080c19035603980315107140c4469010284c400d181d40c0d1509000514440d001180580300324103046c0000400340020aa640300c02c01c10b4001056620004144501c0f40c0c420300900920340100442441912a400714000f5880424071003000030051200046054000c1904050700c6580d070003550528080d140ca002c13082140010848130062040b5580c40d580900014003030007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 968425323 1250 968424073 968424077
    0x1e0e0c0409140a050606181309080a0309020415052b121d0d05210d02040b0c0d181202011403090105042a03240c0f18030804090209120706 61
    0x1600300f026a5a003111400b40a150190408004403403608070b4007884664040e209640020704640d656100340c0050035070800007480c4250005e035500e40b2a40c903401000000b03000320b8003007083c10080039a261031800710344915a04200080048816141c403c3c5400c015465072103110701c00020340350703a0741c071220208044c103402003032070300c0d0282c801c820001e01300100b52a42a5034280d1030014a4076091366502001501c0308000c3c080641ca0b903902e2aaa1082c0c40325020102015515980c44500c40c0c04550002c4128903103c0c81510204560389109140030180e100ca9800b81d984500d00f407940089040d030350148141e05004442266202d00490200114400c508003800001d80303040600d030119040c0b110b0745001c0220b603450240020880b483e4614807003280d501042d1200309100d6203802001c0d00c0c03c04919404400d141c68600b50381e55801c03d000e0180e007140c5a48190700b10780c00401c24170500c211400045d11501080c4820b003c0c3c001143d00400044c4001069040c2508000d10031601c0c16042e5040480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 968426573 1250 968425323 968425361
    0x5010903090f12030806060309100c0f080f0c1c09020a03060f0e013b150115020a050327220c1119020105130603151e0e0c0409 56
    0x42a204505441000307843c1c54200101c140b8041c0d00c3c0180030320302c0070f82441d101d0000080800d2000004101070003451030b0303403003040c03001692780000a040d20440c0c2d050000401c0020002500c3d2480080c080c0344640049040c607800c00c1101c44d8480841d814103c49464416601c0c0000c201598501d0802002988a05000300d04000d461043d41c0513941c061205284680c1007582a60340d01942aa21580c41c003c540c1c80c0700c5080f110f460900d2080d01303140c2450036041c0a00c60545107211010303804241a40c01802c6059603480b06940100d07079075000a040a089504248031034046018046a8a0b410320714401380664120320600001c0c0e0442401d020401042d014501503500e04442030045000440e09400c0040c0024004950251540e641170901a281f00700e03e40c07010110380c014000d80b140707685100c1c4400481c688444014008140000c10390000c030640407000503e48400800c038001c00e004c24800131190a24003600d8024000e0064110001048280000300c1e81110511401d10342c4815821204 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 968427823 1250 968426573 968426579
    0x7320f1309050103210c0605090c0418060615052703011503050607030207030c060906060314030306031c022d0f06010f0f08150c070f03021b01090609120204090501090309 75
    0x400c0da44003031740305101252403007401104c05400c592a146030540256000c1641d59940307240b5401c01e500c021941c8c0d4090318140c8004100001c40c01e40c0745142c0c1c4681c400700200d039101e600c064000114034543d04005001008002d11519071003d402c0000c11288603e140c494420000203401d6444211081c081380c01d28580400038004200113250300700f0114202103240c8000364400804d842c1640801801140e02d0702c680c076003001a59070008000f16044050140b9002c0c0e45070100f5101d038420380c1c040e072107486019203400d4101001481c0c10f02c9000e5540003003605900b010036004680200c1d04003001810050341c0d900c042868144900407802180ea00540794640c109201c072050300c034103031708810303420b84064000340401c404c001040358464015850f810103559520002070750510502d000200b03054031004c0083d04150f00001d507840002c621080100084107000011100021240b19150001c0c01a000400641d030b01c2c0102e0346c211a0018201040803059903c4150030340d4441101200000c184480030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 968429073 1250 968427823 968427833
    0x711010c06180b0a0b01050703110a120903050c0906060306090907050307090905010f0203090d230706060302041803020c01110f0304060e0108010902041d1510030507320f1309050103 80
    0x201c4c1e408002c01008001c000164000203000d8000c0e200001c06201d25014094940f0004218100c0700e030b540306520600e190200b01000348003e4040c4000c8a091065030a2501c40f0700d00304648034420200501031030b0540d51801304100c00305c540600000e9007400751a01c00324040d1014424140034156040c00424161130320701d452800c450710701121000c2203106009100c00c0c0da4010a41c4072842407140f0740521307200340f48412a030890078501c240b2000300c2c40014000040140c5904518200c0f4001c4400300b000d0289902640c20301001040c005005070010a40c2c505036600981c1c15461184034030040380c541116500c1030521b90b81c059001000442c06c01c16503031806681c4240f101d40901700c2140d05504191521000212054020096080991000000a43d00300d154404109810001828400c09031155400a8000d00e0217450940025a841c0c802c3e29090002401e000140030241002c4500d60b4a64001001d498014858004017481c081001a400a10951310000503200308003000645500d54545 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 968430323 1250 968429073 968429093
    0x10903032306370602070611010c0827030f03040501051f030611250c09060b0910020c060c0706020706140910090803070b27030711010c0618 62
    0x19844408010104001d0303403900411030903c0d00341c81d02c140400550720f520310700c00d48140060303d04884024140004a40364000748400444120341c81d2030503410304900b4420b0a03500480011804a40d600c0045040402c1410a01400d503400010316038962071508107030790843c0c0c00302d5800d40c200103001c0240014440b0030700c110f580100c1d1010300b03072047e601100548038502d43c0a120140429584000d010161000601140c3d4510000600300d0710407420f07a40c040f0300342c0b420202c0c180c880807140400071031490003900c62481074484001100d401c11126108204611602c030950360114090039220302000d4170381e0700c00b40102d4000740020b0b0802506010000f890038030302d07901c200704008005a4500c031640306d140440b10b07151003d6407000e0106200383d10035521404581c0c80031050340310000d40d480c2408180340d0868000c8001325507104001c91285030928449a5016140a080d00100484800a5045a540380801d001030420720b008080a8445104466109068901c610b05a0712100200910500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 968431573 1250 968430323 968430371
    0x803010e0108060121171c0f1a09040f17031902030c1b07030c080106061d10053006030606010c03090b0a020114010801021b060c0d180501090303 64
    0x34605903144c0f64805c64240c0a41c40760740040280340018000344000c1050703c0c10158001d000080d940d41411401c1140f0904503040c01c01080d1030001c1c43d600b0320040d405040b0b20034012603403c09035494054100803c0c500042c00c200d8456011848041c00210429031f2000240c0c060340300b0310380b01d162480401c210b141041d0014107000703104104001c90641140140c0e040b1440380303010445070f105210762152801200b9000503001903030b08840040c42603015049a07094512641c0d510583c082c1c0d00480c400e406290211155006001c100300329030062090000d8021402002d134559a004619149038803404001d060b0803200c0aa45400c01c12141020003203160414020328000101d83c030680c40c01400c280c0346001e0b080c0d0300342000a10000c140d10035000540c3d03182d0b5100d00c44081d56592503c0314006d44c001600340d20079111040035014011408220103104002005c01c50b41380c040d01c0d8000303400a104204100c0c100707511085448002c00c000748500003140f8030030b03240014240d51155100900c00320040c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 968432823 1250 968431573 968431589
    0x5011d0f240105071a18030c0a030f120c0804020109061d01051c0e070e073603051f060504020a02120f040e0c0703030c03020c1c090f030803010e01 65
    0x40501c140c070541c29104095a1044207000c44289400c0d000480381d9200d110b0028009003600004011058511440d480c00f4076041c803e01300d112141ca5428035120f0049a00b02400c9800040311240072034010000c000c1009554038044504500e28450082220018825000005c1c0d00d08208011035800c5030000024105900b40041c99400b200000c5d600b0200300240c090402002040b00740c403500c41c8425420380041380030740a00070311011050f02560b50f9241d2244d03082001100021519190050300030320042c0c0800302c44411000c01e4000d2034018501820001c408400f801d50000010400600292400441c00391102d0040b0b41c0403440c00301518482d4211922070780c41006100041c0d6000030710102000d80d0300201649440c0e201010031a6401a135212451404d50341080244640c0c01c000141051032090b1010460303038520f01401c408902030039505000c10b500012a00101c15541904200e41d02c14918100d540143c03a014603140c0e00b0840c2c0e000f21a92800480180940e10780100f20070302400f010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 968434073 1250 968432823 968432851
    0x30e060a06060e1e01030c031508010f0b01081e06011202040608090601082404110d0f06051f1806090c09051203070503090108190c080711060403050d0e01020d05011d 73
    0x44e541441c61003034415101e041c0740c0d80340314185a040c000c0c0c101d04071000c202d81e10383d880c0c10742e60300c6801d003c3d04061b060940a00e242058000c09580104451401030902d0240d04003030000001743c20201c0301018007543e061085503840400300180f98001000600344542d030308055800c021681c14034052042c0c1040205400280f0070030940315a41d14640f030180301b100844000354841e0704004000c1b0600707030001d07a00894112901014090344640038805188628410042641c91404070108102c558203a02020801040308001c10030700c0842e881d443c5a107101700010140c0c0d4514500c0126201d1b01e08010218210310810400e0745031092082e198190b100e0082e600c0c3c0421590b88a44070700c19119000e040c407504c407011903260089156a5500a9007001041010803458440602032400480c1d690000a4101e40300304044180411414001c42d819100d0707506000b402502440a40051814424250343c2480600720050250103558020306c0c003a103860000d1600800302c0584920000d084090001d07103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 968435323 1250 968434073 968434099
    0x102060708160e040f0f02132102010c02120105161407150225050c040513030e06210c071a13020f0a031b090c02010e0a060c030e060a06060e 62
    0x80d51a0380420303804a440d041d007426018000040090014040045100707162105080d041c1550394001d04445000d00500230416955160050310f2038801908484085018000c030001540a0082c030a05d080c401014a81091144066113085441c1110300301c40e240c0184030b0741004560488040c03400180d041d0b45003464074000303454510503082d4414404000c182d00003141c441039110720380220000108550041101e11045c20100d64481c60381500038455803600d40030445004502d410780e50004d038180c64102700e4069540070409150401005032034a8134441070340f5286444030303400703891040302454040d035107840040c1450720710450942c0c81e10645200004c24010340d40011000403c0180e0704940b42440c01060074082005036005900c000d20700d0f21b41a154c0e6008907000c607030850944031000c104022509215000300d013030f5074603001550b089810404803d00070a6030342e001820904e246003000b0a64041c01c2440070f03d00b44089600820311035903210b0501c00e10754040702529074520115004440f002d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 968436573 1250 968435323 968435341
    0x90d0306090c1b021203030a05010f0b0720120d0519110a120309060c05090102010b1e010c1103060103030c03030b0901050603010603050403020c0303040f091b0e100201020904050a0207020102060708 87
    0x74491030a88445040d20040108540e1040f90314175a12803040700f42c80d144d04108440402824080c0644004402401f10104e1290b60342c0b0700340d0702500d4001c8a1000891040c0c1121403100c8061a5010340160394041028607403c81040980c07600e00b110f03030701d0b0780d0350318411a8171310464042c0120f10810855041d400c0d0300c402d400021900350b00e076004124109041018441940100240381c4000c28540c1401126080faa4125026058420083e0000c0c00701301b81e005c0401403035550b1001c404085102e201e04802c007a5118004103e142c3e4401c1e1810901c04100500103450060242e0003140080c00c040c2821040550601910782c05c05002d0362418055410080000e5580c00140914400c141d65800010203262082104a00860000c3d0590382c1c1d454650701c000240c0f0120307000702c2e000b050800f003401e1043d400c040e0004001703294940e80c0b040030308840010454403090b010480c1003199004e01900350b0642e1640304103030280d8105240142e44d902c0c2e910019061030360003065082404034240c10418114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 968437823 1250 968436573 968436587
    0x80709060302130f15032702150d0f060302010806090c180a03060f0917040b03010e06011b03090f06140f0a0c05070e06151e0d090b0a091a04121202070b090d0306090c 73
    0x550441b0710549c03440342e039241d4107610700440f00d4041c401800d1482c9039140076060740c4040b05a078000c3c0d071002460340c2c03200c0a100100905441a10101c80200048994806603480541026000a051000056598a0b04d1054403085800612050f170740d49000c80406c0210800b0300c5205107869400c2d030520f85051400840c40c001403213038402d2000b50000040f020783c070886100e04468800303068421440d0072414020704181d400d0007030740c400f440480c001140c1540180f104191419030110174070326100700325103501e116401004040b003c2c4052004510b001400c1404101c0140c800440c11049030f00c6d0200821003060384100c46102a41d40801201c5d012078030b0f402c81c150034150075040c6503035070f20420351403070004044082001c4c1c0301c24810000d20184024680020301101d01908908184040340c0f0003c21003000213a0300146262005290b90171424018034503110325410341701700103040010030703100c2401d04503040707603114429040f02003411072840d054800e240103003035501c1c020001d4105940002c0c03c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 968439073 1250 968437823 968437901
    0x50c030c01050f130f12050c010f06150c261b0d020d080103020d03140903150f01210f0501110c0f06010803040f210f050715080709060302130f1503 65
    0x40380c8415006e40b0b1041c0104111100000500000c1007840d0f0000d48210043c0742c50702070912490400902082c049106044441a032900b001080340c5e500003030000070071240000211041940010701442e140340604100c0c140c1d00a07001d001516441c4c0b4071100083c2000c00620141040c0000800140007685461042890090341400d062600c2e012705011070000340100341c00a64148a402c001299000721015003500511060f401c0c100381d130342c80f03801c0107c07803072002e142128800440c0d103140c8021a124205a084040c000c100014040c402882e00c61840e034016004020705904c8a5440c682840c020800d450051070480007560515003060300c20843c0000c01d10030120500300c135203407115101e20b07100e44480c00c1d107a1000c00c0881c40452494801c0c1c0f512450301c25003240e90301c400b05180405018558180c4194280e41c2c800304041d00340942039000b9040304207a0a0000e0003950049031290900c440d540107401c10104062541803400001426180250b10011a01011343c48071205800361394001612 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 968440323 1250 968439073 968439083
    0x1a0907050406240207080303070210060f0e0f0a0905152d0604090804081e07080a050a060903020c100228020a0501050a0203130311150901090312050c030c01050f130f 73
    0x40001c003c00c08910300881e6401503070050100100380105260002020201e0742090482031000664030b16021014113030501c60440d104d00c1100c0021034010700c80414a60280303060400290450031907c84500c1c050550000b1a65078042e0f80620000b511140948603240313900c200501e4550140c585131551400d005008280260344940c1c8400c10450283c0544010f41504411203a0302c5080c29280400e2190404410860340034035075001c0340e21034010a0308454550888001d104418031965000300814207c03205130118003801c0c07586201951071401412041c099580245246404183d81c03080c0c0d202c01c510800d031700156142c03032080180c560300c115104a41c003d08001c1d880e000c002e0410780c1140f0880d44900c451310502b0304088100403842340e0528440c0426a103181003d54901c51098081c460001d1031404100005020000a13209060301604d0060b00d14048d41007807080c98905203940c2106c0b0604a0903511202000190021070450030752001d42c138040412050300070f032035400115405a5020345 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 968441573 1250 968440323 968440379
    0x71a13080f0409050903040501030b010507030c11040608011a130e07230603012c011212030b03030f040e0708010506040605090406170f010f0528091a0907050406 71
    0x34414107001910700900c038155061042d071178545081c036100c0c1e1041c050540800c0c035101011856500c10307010380d020360342d1680b14464907000c80e4641ca20555000340751168815103a410104040c0c9080c01108a80701c490007a003640c40180c07004100c110720780c1d2060f0780440c1c0d151156248080c4e03000140e0b0341c02c03076004030048509890214003404032852903160003504000000000240401318041b100010440c5031b40c1180460358a2090301d08011080c4a00078058507680f2080000c91301030075082c0c02031141070038002003250085001c00d0a540250115190109001c501044000200c5101e070364803001d28070381082d02c0d41c10b000000300180540d0180302c04000303011800441075103903a84428050701c03641c465510042c10f2407000d196540e803407200c0703070b40315500b0901640082035036401001d004007044014181201800d8021100300c64006c1c0c0c09a22054a4070210400f14422080044c0000d0400c4981d00381ca10f0003413000c40c80c042179940124019454060200000031008079071290182e10480085 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 968442823 1250 968441573 968441587
    0x40519080702121e0c011209020a05090702150702010c2709050705040518010501210e190302011410050111120403050a02120d0801090c0521101e03030f2003071a1308 73
    0x8101c0002c54004033381008650023440b43c0300e500082c60308801c05083d072415059540b8064120300365050060f100d40402c850001f410381c1541840111140c82218143c0704480071382d1480c00303034182d139003e46112005c41d00010b421f0119040c0380a0011180d5141100701c03845515000008108152000c0600d416424180301c0140120b01904003c410102c41d01c01c840e41041c3d06020885da850003014100e015610b04000e4003d00080c0d4510b8a02c100b82a641d0b40b560f85181070015200240e02d15250f0070300e07006000b10b40c1c607070840900282000d140500001c0641140324411301001c1a980d8800e10700990040405440c0d295200c05014155418601d003c00c000007455819aa0f82c02100800305040300d0480c04085191100c01c41140311744250422000c05c16a40c4841c0d004008242d007113203402c1c0f1701c0d80382d09001090040310342207074000c203500c0d04050101900f20300c42d5001c80c500c440101290000240b51003401482511707607405c030013800d0099030941041c40c1c16942200500c4802050038101003250 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 968444073 1250 968442823 968442829
    0x1e04170906040f03030518010c0b0601030e030d23070c0b0a021605190215120a0c2109050601050603130201140d140609070503040519080702121e0c01120902 69
    0x25800400034244403c00460b1289030103001608483c42d49210420362002481d019807188101c00d445503040302e2201c00540701c0300300440c05030806035840d1510380700400141d03a4030051440b074031086004c0c204e84d842180e1070003120886031171300c090120002c22800260300740201d11440344081e0490700d0030758016591034075100d99207050800c952018003d4001c0c2500b03900c40803040c03e1070540a81c400c640307807080c40c0c038503040c600d0701e900541e95000286040c041c0003800e83d08003580600120201030601c40b40b82c0c0900c3c1c4550040c00210714866030803980721162030081140401083d40500000c540c654114503203200b00e0780703007010100800b03810403103401c803110240d14000d012100c104601e240c0500240300c4009000c5840d502c02e80303403035004150b2800011035003840b480c01e80b40116417000150040d070411070003029034000e030100203a5003064200081c000596544100c146c89814883c003070b2070b01d4040da030a2006108d41000300445560000c0ca004951a0b910081e00d00380c1c000074001c002140200f074004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 968445323 1250 968444073 968444077
    0x8010b0a0c021509150a020d050904061e0806070f2a0b16020c030f060105101107060e040c031b0507230303090d03090c1203020f01050f1e04170906 65
    0x10790400c00300300015044200f04002001d92580c10746841413140c0200d50320841d6071042900010058008000003603519106000906071203000400100c0c013035480e505500e40d102d0b101c88040325907400000040141020a00c030503644281e050910145010001c03901905156044022034201d40c600c20480390301d6035440c0b004555058000c082c0050328644405072076400d4140c0354030303d009481940d1410040c0d1070002812001102000c000c0e00c00e5928040500802000b9038410000380260152107000348101000b00c080203200300d0391001d44a0840300103200c100c400b000b04003810103007441d0040408030b03020b00e21a0125180780c54101d5444515007062000aa0020303070f507540c03400c0e021105003941c190000265000702c1e1ba150176204007040f4050301f541254000c1d000105900d034200803c02c150303a0340c9a40551079a0280c016243c0c480c1031441e0160844a04903441507940b00000240f2842000c0300d0b510909054400048a5042c10140c841c11507554030f078092103560480000b0103080645174501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 968446573 1250 968445323 968445347
    0x206070303020d2f03060d0b1b0703020109110d050703151e061a130501140f19140c060604050403200102090117060108040303050403051303050a0b0f0708010b0a 71
    0x10400c603010142d02e800044032140030a41d4403589444d10181034551040741181c0c01601d00a00018082c20a50346249100c0802410000d42e0081801c0180d1440c4981c0010b2801e9440783e4000a08110b0074601034840c4040c00601d40e009500c5091a1400500700146a40a890b00108600d10313001d0003d111201400c01d80c004862002806a080203041030301d80c0250044c4c42d081e800145010301a1188802c4501480c0d49881080050000401581d400b0300109075401d64541d50176860034040c545800c07156800324405102c1584180d40c070110150780141c116800c07448140744549001501c03030384030355a0540984058400d0303070b0f100081410103008800009400360400c451450720310301b03011154001c0d0020900c5602141030b914211800c41c490200c0d6612868058543e8050713a02c9645044005103802003044043c800300304011161048000c92041c0110f210707600402c50000c15141420761511702415070f81c0c0a48a1344140641d031038200c1c00c410b041d03804d1100d440e516031280a008660b07150b4008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 968447823 1250 968446573 968446597
    0x806010c17160c081911060706140403030f02030730050f07030605060a120504020a0503011503141c110111040b040306150b090d0c09050711060702150103020607030302 74
    0x1030b401040004000722a00c000380600c0b00c40c00e4441c1c3d1581d076140c031303094152019035030403d4100e42a0300140110343c505440401c050807540c1006c074107581e0780d070031a000803106556060900b001c000403d40d141c084c1030030400100e0001d500798200f000c40904406401d0203010310300d10311100c1c0001703485c11002a0280d505e0040100b07004a00b0101c0d006901e20f00c1c16500c01c000242052008510b5081a004440c6000c106642d4040c40341d0640413641c00611000c0c0c4102e80c0324407241f80010b8203560034040d03260302a08070000751060600c0c40c5042071001c100b01044528541005050811024482c0e0911b01c0c1840315003403075880c03110412405801405861808501d9000101c0c02203800014100035100b900d1140400300a4801000f01c03c4050a0081c45840e20b0b01c2c00070000c00c21141041034002c90814407428000a40300d80792400301c0140c5008032240c078009104201c644014100c200910b6410015a0010f08075000001d9035098029034140400b07801640006401c404040c801c4c1d044840b00307a140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 968449073 1250 968447823 968447827
    0xc2e03022203050f062a1306050406170108030702060c0a060504050106260c04020c010f14150d03050406030902010c1b0e0a1415010c1a0603010f050402010806010c17 73
    0x98807100d0303641caa64081503c06110b00c12169109000c0080d4007030140c0d50740e00c4491006401440301d202040f1000307109042c1010240440c811407145c100804019190a4880301d0312641441030090040d28031140c1ca0380302c00180c3c0010403425101004607140c06405440c0c00e136070742d0a504107191a0031035117040148002d180100700010311806500000940b00c0790945d00c00300740403a0321442e01c0d2010f081501032072a00b05030346002013840e00340d0040c400590960000300e0141ca0342c1c4082c20880c2e40180460807440c03a080c08001c03084144010091441c1c8048814150b8000681c0b002046801280245414969a20031401c2568014240c040016900c5680160340700b424001c04d041e411050f11403c00300040c2c850204104600c00d0080c0c008103607150702c0e416400d90350a10b003008410a064002810b00075400760400204103801c20310500c54070310340711494042c142901811700311003a0044200300103181509001c0180c4c7c0c48410150001402d180c03001d400d1596080c00001e8414001b0680707850400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 968450323 1250 968449073 968449117
    0xf070c2f06070c150806030c0d1b09020d1d07060f0c02060406020a02130209030c15040305030a261b07051c0f02060f010e0c030c0909040c080c2e0302 66
    0x9810882416112032101e00501300301e002c1025126843c00b51010380d41900050303082c045504142902007256030140e4a0b02803428a80c0345070881d052003a4014084440d00001e100d0745e100b1403801086186009000c000742507018945007541c50b20f0407400f80e801000b5000e120b80d00715501ca40ca40484c41500188055078883e91142c010355211601d0000302d0280c00400844101f220061080d20b102c80e0003e0050646c2000740b03010030881282c08290910704417014000031000c114100050000380362691680604040304241511103c82210000c4100c680d04000f08861076030540c80034021082c0d800c00254448a05240042c108040313130801c0c0c5c03880c07607a20ac002a00c0e00d5020404000d0040c1c260241c40c980c1c0c960410150030b88909008085640c5481c81c08a844c03208405c000b103500420641c0d030740303051070680400500c0c0c408080e103068590041d820024011a14140100881c0c482d04440c04a02404030103c50080c1d9007600b142c1014414401e50810b560074000d80440c1e00f0703004441180504104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 968451573 1250 968450323 968450333
    0xb0904021528050904150b0301052206030f0203061f0e041a0901061809020f010c030908010e061008150c0c070e1f080307240902090f0f070c2f0607 65
    0x1200d0510450401160110f0215402d0700034090344c1c0510081f0749561f08000030301401900a0140003043c1c0700c0701906411001851240310051351084009000e458800d004043c076122000c2d000c1002c01ea407010a0305041c0d04014541802c881715440d11003107950f52414400c800b4886421003040900d81e86040015405c1c2c194004401e8401c20310320418500004c1030b03a98100d80a0004c002c2d00010040301812103980a05005040c90780703c1c1c5402d240e41522140c01a09441403208200c0507580004244907000740185280d00181820000921000c0d0b900034044e112014040d0003514000c070b00240c802000141031000740d000c0e00314880002c0550605001c041541c0404904e170f02d1103940e060002068a480220444210b960031805041c0c400141038080c9110a20702d0790355005141d9212141030040e1103c0d08098403038003600c546418140f070282409082c52500400700b00c00c015500e8000310002e08410707a1005040600c0c40904005440201c1e00e5121400903c4030f15030055010980504001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 968452823 1250 968451573 968451577
    0x22407030b130912090b0a050d0513020a03030201050910181202100e03071205091302220305060a0b1002150c040801020c070f0602010501270f020f0d0b090402152805 73
    0x4040c0e41c540c1803e5985405443e1b01e8040d804211000800070020709640c540e01d500200d0300310690a0318103905501c1903001a00000d007642c01100940d441d00700304205110f051001203490340c00ca400c24014485941c2c40b601c8500d514110052a120517840a007081906c20080009640c0c4280d40c00c0042010110b081aa0b94000c1e10084481e841c0e046011a0300b180b2480541d00108030151107011070342a8000020043d40044511008140500b0340255220758040c95190003103000c0c802420310350030100d03000c10035103e500b1b050b58050311065040c82d0b40d095000500e49039800b401072040bd003980341c0f084003030250f20035648540c1e119800072a1041c103c3d040400c41c1c1044400c2075140b9400281c2d9010141d00760361091141d00e00142550240084481601914240100c00610000344403102e03903201c001241c00c1240080c00e015408606030688030441d20842840b0038044600d20017520f0141d0000c1c40c2120002020403480401040410b01c1100c4800c0034180c1e0404420607002030800140028916 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 968454073 1250 968452823 968452853
    0x30e010b040e070e1308040e0a091505150301060302030303070e04200a09080d08160e090f1b07051e0a1e0c0b0310150e060712022407030b1309 63
    0x101c100a01048175000300c61105c1c140385900500c900c0c1000d16090007580c80d181d0081c40941c0c0e4a4071030800300c00161003012100301e43c2420410019032810080c2d1503d01c014007a46c0e1541c0260b1500340c0030300140c1d0340041541c1d0f0115452601e020b078261080046000b80446406c1c40d0422201060701940d140d04500c090980054035540d80f03901e15030307540101030745d80402c01441800701c0c03455004a420b0042c040241d1040300803c0c20b02c00000800c58001c56000c460848a00d6000e840041c14450f40c0100c03151401c00e20300124a40d20f0402d11103881d11500c40e02d00000c2032960540304032800024000030b116841113140c02c14207059680d144c16211510040140c00301315a0802c03401404503504d42414252801507400d149600540c9061000c07080d47e810092011000b440b04001992015684500040c04201d1041100010480c5203580107440c0a0300c07410790744590003081100b070135004414003103560712142034a8042030100003130b070200f295810070040503034015040100000500460004855503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 968455323 1250 968454073 968454089
    0x13080307050c031510120c0e090d03061502120309070e040506150a060806090406060510030e0106050102030403150f0612030507050c01020303061003020f090d050a0c1d040201030e010b040e07 84
    0x4801318403901c03981420200d46101240440b0002030005181880000d085035200f060400d00e0140c81d20507800284070110f40140c415401040000400da070716008810080c0490406601400070100e0080c0d00c42510b014803c410703506c080009503c088040107220b00921451000c0501c034102801c10f20789a80c070860b080b04d203650540c21a0741950400318010401c03281c840d80d6001550f125541005100400a08191806903c400002c00c00399240d249d91043c0c0c10b60354034005501200d00303101d503007034a50780d0f44a035040d034000380005c00c04606001ea48040000e0769a0000460340389103242007004001384c2c1c0000a006c40d1040e40b0000f0550007000800c0c0c80c41c0141c080b50121840078004a9503407004890f002e403c0156800da5070300450090b009072811403010b001c49800c080142001c50299050110103a480394444107004061008100416001c0c02e80050b9a0101c2480ca01c0300040303400c00904028109960303503030b181055001c20341c05035455102c003c4c4280611f2115000c0b0304d0340d4401c14060150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 968456573 1250 968455323 968455333
    0x101a0a08250f030e0718090f120c030305010b0f03010b0c01090534081b011e091805011a0c0c09010b04060306050f130510170115150c0813080307050c03 67
    0x31350303000005006000c44a03181c01d04104048458001405007008890844000310f41140c00d10004408034030042c80004640d80d02d0080700706904005055402c1a40a545180b004101c0e000d124100380b011603041d42d046501c10b030350780e80f1040d803454010214090068184d001d9071203180b0115041c26180c000071038031180300d143c411b4081c0e5107000082c0d0301446901084d501000c0303040c0108196004038100200c1c141031140282140300316825603540480810700014820701021302008441d500702401e9803028100c100705c80d40c144210f403c0c0308500e01c00071104210000c04c482d903111004000743c2d000442d0145c031328011542c0d1403c0441442d0414000d520100303040c1100480c503801d01c1403416210100c02040d03090b0804041082c040245800740030808003d90145020840010b4a82110303040c600e900000240b8459511104506060ba90000b01907101d0000e6015407607503000d1061129581c00152040e0f035450b0300000400e9840207a804100a800003040781301c1400404213250003450000da05030f40d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 968457823 1250 968456573 968456591
    0x120702210601061103120109020309011b0e04050c040b0703030603140109080304080304030201061e050f0a180b030102160606080c010c080d05041a0f101a0a08250f03 73
    0x1034680c0c011544112959000c5401001024400e001c040d00240035034096a181452004096030820704c241c00402e4880e80020034041ca040003442000c11108d080c02c13070100c3c2c0c02c030070356402001180c0e4020600c0c03140303031114040303074010242c942140c00400d1944600c0c1c0d41c0e140c0901c2c1c090003a000034401501d50b60492248018a900103010340c900e01580700c881c1c603281d903640343d5801ca082e03040500300394119961081d020848031003071000303900f61181800102038034a01e09820084903000c6444a02e004064001003044403a100a035200c00305845414007040301c0d1800c402280c0240a100b60511850b0311401c40e40c0140486680010261030881003581c2d00405050015100b02034544d000405200e801c00440c0b50701c40070f551215400030710624046221040c3c3c640130451111068a2402c10600d040e070520411030322030265240101903500460000e12005207a40480c0e00072140c00c50f0911a141002400d0480da030f8207480760790384801051001c990414400240070a4030340d9080070110b85082011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 968459073 1250 968457823 968457859
    0x1806070201060501050d1109190801060f0303120b030c130c14070201170a09060207060c020c011d150c0f03091203040b0910030e010c050307030f06051c0311120702 72
    0x1505540f010b841c1d20346007a0544801800400745c250350200003940520075150141c1d034100c03010315100c1c00c04a05050b150309000c055400c541c1550310402c036500c0074060420001c0d40104022103050640400000d82801c0c64000c2403d00101d032a0851b8881d140c0700d5540c00d070f1080d540c050405a491030361603501244c4540c190408030f1040d0100680400c2e100c3c000c0c0300c40c10380d510103400d60085401c100400d2410a40d6211f0090360001c00c01141d40340c0d00d8000801805034100820390032842c6c24a40106601102d0800b900e07544035925490b4000c4d0144bc0d111040c0003021402c80301d8010b01802141c60200b03207440406d41303d800c5a100144a040207012a04041d4000010340301a106080340d054902100070041000d902a4146124240b43e02c940d445440c0100a00c00d220484600c0e03268a0b41e00d00c1c0c81240181210201800b40303a0103482d16200b030229460b0301c00100450700c022014008050a01d0500740c40c00004003003005542d10542100e49045040c11000d0500c5520036101019149003501039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 968460323 1250 968459073 968459081
    0x60c080a06120f0b0405031201030302070e0c070f06020a230c07050d03141c090b010302132a0507050a03110c040c051c06150527010c11181806070201 66
    0x15040c920b58800500105011082d000c0c1c205e0b10500859203030980c20600141c604c6001d80c4242e0168200c01c408000880c80c40c111a940080c425030607d2400340160380302c4000050304640038000d154042041150340b07025655400c074650400a64444904500c07920024941c8520341c0c08c3c01034000d40400040e28107007d903075000401c1e40340e15002c800261201c43e4815540108030f01c1d141070300e8285146001d0142c0c40c812019101e01030078220302c8540c10341c0180042d509041300c400500a2070030703401044101e40240c8201d4001d0740c0f504900c00c89401c105040340d10b070142c0300c00500507000e200c4220701010f401c084031000040a907070684290030640e5081104692142c04000042a030421a8091042d41103544130f611882268002814a84074a4515418500380c0901804118000380141007822900300c148540d40030820504c07100c2d041000020301080f02d40030024a03606000f240e001d05a03a598020150340d49428850070003600e8984880f035280d05029102003428005c05006c43c5550380b041c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 968461573 1250 968460323 968460359
    0x60f3209030d0513080f07110319020d0213140f070c02010905010e15132d050120060c0a03051806180f030406020a02010909020306030721060c080a06 66
    0x101442c14580c4002405000d0710b001040440c000103441207960000c0c501d1805008601c046030704c001e403500898503100008040c006046407003580503021500d089103618142c1e20480f81e050b40e41940c005c1a600c0441c20190300c4180a08919052401c404010310003800079078415440c610030100c2a4440c1030051318052070050000c0c0c0003c1440340140b05550180c0c048050040f00034000c000050b680b1084012141c01a5841030136103880c4501c1005a051078824999031418400a03c40029076581070b200c0b08825107205450520004140d03540c20410b40c0d01d45555a8442981501c81341e16002c0400180340d444281800c022a141c00041000c03651540e40c00756265405100a100380c0c0c4031500b051000e0318005000c6420b61081340f01c41c030010002800544003c007516001815080e10700d200142004403985c100850b694414010002d00e5600000c4130f80c202c1c0c100401c0d11800d5080144440554000307048050700c1c2e40d0511016649a40e072101d0801d105046285c0c0070407081e5104d01c40750b1241d000c001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 968462823 1250 968461573 968461591
    0x3130b0c072612161d090f0702030f04030803040b010608060a03020114070204020c0d110f0303160309051b04150e04062403030c15021213060f32 64
    0x9200542c12540d0900c03105064800d0300301140c10806111409024400c00702c4000f40360340d00d2041c8038060075420415081d800c00004040c0040c0264101c080b6242080080c1700000c40d11543d004030300c0c118000d20841d80c2d044050030b01f8541c3d8503168184180554425a401c40d114001d840c00050b9003807141600600a1034020a9003012b2499600112a140e04012a550344500c040000302c0c0140e880c8d01c01014101c050304050100041c1c10000506400d908108015450300540304001410501100300e95009010340200303c90520002170440c001d060295005203107104502290000307012032401d5103c1c030078045a0500c0b440d81003480c12862001c00d8030900003800c0c0d8480101e000201030390090f48400442038202019070004801b02142c0a520b0392040e0045007007070311b2400c1401040c80350f034001c024199405501c0c0c5038055445c100080320040c403002e021244240070030104049a0040320b400c8004040500c641d03806401a442c4a85c038041c076855189071650000c0951440c81034480c1d1050040c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 968464073 1250 968462823 968462843
    0x905060906091513110102010b0d1104180c0608040804090606080609010503070501090e13020d0804031509210201111801030605030d08042301090303020c010c0c23030d0203130b0c07 80
    0xd5541d0002c4917a103020080c150354075180132031026140d80c090f2000c090700171100c40c0004026030040c8811665004c0c007811803900c010107002d010903000d00d040030840e8a00c0c40c0042d41c5aa940c10103186500688d042050f0303032400c110001a1144d401400c190152004948101c0541d0382d4104044ea9088a485502e0208085440400c2244101035400c1c4e807000841003080011200d03a400200e00040d640c00c02c90764140086414001c0c092200002900074100358420486145e80b52600800b6a42d844207940702d070716a22500030180c501c00c3d0000d003c0d24554012141d10b405031204d100012a80d0707885000d000a181c20400035451400183d8a40d168140752140030fa151160b450380d160121002c02c0804a4401d002c000c8060300c0000d00c01c4450860003070750b006850b8036403c910542519003030003807001081101451000032034015640011a02200e01c26101a80d03000d80c4001e00350b0041018180c40030340b021080201c0310040b1015208414070445404003d60b031250140c0c00075028101d4050044000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 968465323 1250 968464073 968464111
    0x3060302330c01090501090f0b0c032710050901061e18090c080312070e060c06010612140f01060f05030903040b0d0603061a0f1215040609050609060915 67
    0x242001400789907102c02c00420f007090303203854960035908907103811110441807040071007e00c00c8248005030001d24210030107103503041900140c010903d420031849040f1508502c0c0400d103240820022300c9180005400b4411460411701e030310300038816807180034000304c1204100050300315440815000d482000000080c040038100b00f020040440f014200c0d80740001080120f580a0b0800190942c00115541041c50307151411001348115103011825014800c1880840f10403080030400305e042d12200d1400c4120800c4903418000504030b120b0034001400c2102040c018828520300c50f1905840080e00d07100c01054502300200c0359440300715444407060300180828001000348070003e05a0341e503c1f44000c00d410f82c991b16540c1c101d80e68407100c07414848007094403202c1c50030040e502040d10a001c40e61142c03800641c80d0790700d0315081c0074010000d1042004001800300034041d448580f00f179400c2400c81e0344624010190b150ba4030002d80701e1080c0381c8030b143d04174000c424070300c81194401c091041c1d2989030260307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 968466573 1250 968465323 968465419
    0x405011d1f0210110711030304120b09100902101422031109071b030c2f0406050a0303080a0219020609060a05130f140f0c01030b0f0121140703060302 66
    0x18201c2441fa4140020170002400d021004040c405903801049501d40c242490b8150a20b0440c191143d8814507084c011440e002d6942c01d1414400310080c0e0a014199024030040c0c8401446603024903a181f6070754440011090604c41e4400003520300c500c00204082c5490400c00010402c1150000009003c1d014184000a01c4d03a011104051187c140703000301d1001030391644002901051840340c0040181020640c00340d80d0103a004c0070301410303075040020900b020049590034004d0300000d010f020641c4040341244402d81e046075a12400e1800c03102d095200e0391002900e46100382e0328100c080c030a40c40030626099492080e40e00484450744880d40030b0580d9520b9039041c0814010940d0644455000c1c0c0b210b01d07500b403003c16000705182001c0d1601c02000b85c0051308a8880d2100107000704c4201402280c9079801a0200200c9050300000d5140d4007030118104000d04041c6039241036000101c8140010b09802d0f0b040101a24030807658045244e4496110300f4104030a451800d141908452144007252 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 968467823 1250 968466573 968466593
    0x4051c050f03030703051509090316020102070806130b0a051312051905040501031409071a0c030403060902040f020a14090a03020312120c0f0405011d1f02101107 71
    0x14800c1040d140000746403801d0300e085820450340400480c0d2580200305c50920742e200301e008104402c444451003818000301d034a60f40d004040c48040e045079001e0382601507a0080084800500242088803244e1070415150f030304507004d44400711101c440784000308180811500800c0c2c0b291446409204411101e40c031034010b41e00d0742e4400c020138054100405902c101c0350b4030b25108400b0280e150147e9a0341342400060481d401f0b00d90500e045200001807180800000c1008021512129080940c8010100100302c0920840391000801d100006d800400c12026030030507446070b402120104a00b04110b442c01c002e038481c0055010000742403910103100d903c4217001030002c1c55009410741c04841d13100c1d400b00f0b16140d0364105080c01c00a010803d0201501845070391075122020038511401d0030303a0812440840e004501803e4180100c0c40c64400b0111200311300d0030041d243c01130901403140040c1044416811103660107c0050188444400e040722203805401ca000720a0000b0516000882c0c8480c2481 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 968469073 1250 968467823 968467879
    0x70809040f020304050c120c240f0a080a3218070b19020d0c03210c0f020d090506180d0501050910050105030613081612170604020405 59
    0x1d40d180c090485003126880990b03c601d10640060492440303140802c4207028002a04090300d43c4041c80013140394940740004400010350484890609403c95100e8820740503003451446903040211b101c071582940b05900700c0c054070380381d0030400602c1144c56095901c10000c92480300b04c0014035102c040a41080e0841542c0214900710700006400e80d91041410007455a000c1c108005000c11b4010044002290517201000140020700c002071031001c01174101030002001a09000101ca050310301c0c1b25056035085810040000c0402140c5401c0740d0140480c07050b001140d00520403c0c2ca1903500a005142c0302040c1c80000b04024180003843c0c005100340448580e549401c221125240070000300309018181c06003e0000c041c24404014214035812124164404d5220703911041c18040490301d08040c150b4000d4000c0a69641c40280b040c920a00c034018400091101b188007146120096005850307000300040f01420903c582c40301c00800c003e900a074013850b94030680d03404a6164000c0d80c800e506200b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 968470323 1250 968469073 968469079
    0x605090f0d0b01080102120f01050f011209060c17100f05190e04080301030210022e09050f07083a12090b070305071e0e0120010b1212070809 62
    0x80c0d8071482d500c0c41504142a80800740c3c0c1da40204901b444100c0d0003e0344d640c85070242d02400c2040d80361000003117039000792600b00350520036004680380c45429503400904005410890501ca8007070104001071400d41d021420f612a480303482d0205e01c040503c000f440d41100d07694955601041d04080811948490140302c07184e1510700c2e0440003403035180c9885000d2169019148458032507145005010000301c220744404219000311a0580002501c09883c140244500d0101c078502c00010920350001c0c1403d0001801c184200d025403403850f0000074880040e1030780c44060760500d03114000091550402658031411407008103424000030384200682c3e215080992421407081d40c4040c450340c08441688505450f0f5055520812440f19014050750307800030987d1400412031520700b0a400b46004002c2803180070400c0005540d00c403a889540e444034003415026118010650454080d40200180303504503029007400200c42100f41d8001c43c0e00d4040189840c00e19141c00d031a50769503102580100308242d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 968471573 1250 968470323 968470339
    0x50d11030409050a09110a0605071506080f0109150b06041802040b040605040812091309080d020d090203010605060705060f090a0f0515250503190221060a0605090f 72
    0x841e0310b1107004980c01060b0b0f031400081c41100900304003440d181074802580c01080e50384002c000017540035003101c949680001300200152083e22480c80a000c55a0005c0c20a1046040c1c40c0c001c148194032030034820744a01c068252240111604005072000d9500386a4403180c00e0208100243c800244920300d007008010040c81c158441c25240c2c030300c0e0403541058000031004201445114010480440114011450381f800c1c103c410700000c85554180189001494031071ba03080c4104490360080d58500f02d4416801d40d00d900085008600800018100b40d10a41c01c104000566007000d9003124100ea0708039001e402180d581444218601e40f014100c1c0d040c0303105500201000c030710010066019103100b0006403a11035012800e000b4002c10260002c0c12a1108800400760391907654590600f072400d07810000d0b120b50f1861400c2081c40c00404041002038000035003c100000f001c0c452a40b07280710002d00842c10384401092001d034107154010080030840401080403145460b245182c06158000c2c0244 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 968472823 1250 968471573 968471579
    0x150b1e1008041505041a07140409091109010605070215090117040309030503030420040b060d0c030212130b0c0c030301170307050f0601090608010b0315191406040c02010207050d110304 81
    0x2040713031421142521a20403500100b401c452510581c0c41c3c10048a107091401c07010400e9114100d80300b20f00c514105556102080c5040103030a01c0c02140d1180014030908096a450402426650061400700d1190030f04031521046011494281c0c1c8503010180d48000074100000700c4c24450400181080d414086020000000607008000451086100d04560781c56004c0d10044c814522001c102c0d203a124030b0400d80000000d0326400300b5100c5c201c00c82c080102e80d0840800c02075000b0303c5011202810800c281c400c101d8491200c9160300b100324030500382d6442d6541c620307002401e07074050b180125030107400400c0104510b000600110036131540c1502a207241c035109568007450281410000c81941d04070341e00402c040c40a6215440080a01c10020300a07107008100003030f16600c503001c0c591032011021003c580d10384d9850250b5100c40074200c60801c0503a0451040440d00782c0e046407514400d40c1014801840c0f14418025920601d80c01002801c2200080b6015105071403c031034041d16030302c0140000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 968474073 1250 968472823 968472863
    0x301030c060e03030d18021804152409021803070e0402130f02190305340c1208161409010c17040f1a13140409150b1e100804 55
    0x44003840713155010b800d0301b00f07070284103025040034460550b40c000a0a8410040450702c404801004c1142d541c0001030780c80f6440d07034203020750342c90b2201040000d411914045800d581c1580100030741714403a41030644005a0030101a650a494054510b4030305c00382c00420010b0400d80c45100e9021840c200104121608009010803071300211380707011640184525903030810b5050304ca49900840d001c0000d020343c1d4003108100c101e03802e403c2a180c0703964030a580c240007424030800d05804550f40c0120600d020840115004103810020303221082d580d0038809000d8400f038050034804000c51985840d103404c105403000117480348800f0000607694144401c1803000c0700d40300e00c0d0080c006030a0200c00c03489624109072800c10101c1e00b4054400c02c088082008400c003400c1a4041000c0740d00281d12220308a440401007070180a107400020b00b011810f11650251401302e030020740e40a603054403205201c49155001c190002103100c81c59822031501120588414070940e8995400341c01140c585e940d00340a85c5071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 968475323 1250 968474073 968474081
    0x1a011d06040b0d0902040e0c1c021f020706090603232e030507090e061b040305070b0a0e030703120c0303110c0109120207060e010e13060602030c10020301030c060e03030d 75
    0x540f480f900d66801c103520461405100d02c030800d031105002440400d1600020528a42203a110090400c5609000d102155590341c5040048911001001485096014080d5564601d07000d07240100720000404580c051003880703001a040040c0040c1d640c065200082c0f844113450150145a200720711504102d4050340040d00c612400600c84007104005145003085800c0040c00d070170414010341004403042c030382200000c0d03094104070075100c0280e40010941c001d0426128950000b0824059260005050043c5001a108003101c07500c0b034481d003400c504209a01d4034907030b000081080c0d00c80f040c50107002d4803885141c1c5030f0034420300307000a18009c000640c02e00b039000080d010b900380c0c1d10741c002c074020002d10400c3c00400341c00c180010020307142000e030f000d4144020400c0c42c1e4108010340030600d0490341c41d50344e260703004424183c0c100300f595240d010003501d0754480d0307a06150314424030b80030340d1455546100b00ca040300d170418210300d283e5051080890780210003090303c1d030f0302d44002d110710b084803c1e00c0c3c81 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 968476573 1250 968475323 968475337
    0x6150310050c0c01060b130b130509060a030b0a0504030f08040203100c110703210908060c0304030309020d14070b0a0806060f0c031c05060a05100c03020313181a011d06040b 76
    0x1aa692604007c81e5030181804450b00988690102404020000c840450f1b051040c0e80040340c410426960f208c0c00b103848012180d0024059451220901c41e0200c1c0c282c0c8107a002e0b0f0f0099030781c50000320b82035400340c456000c01d490003501036026420380213030a1119030080e2034400c0c0311700e04902c0d580d50f00c24010340f8004d195001502c44008101c805003010303591a181d0800d11a85003468076411b0710b07103c501e54072018000c1c901c00f18820008009420984039601c580c0d201a4000d048507129440341c2010214840380c2c840a2000d4403d8100c04101b010b400d81c155000e0100544d00d15419607191000c1c040715422000d62808041c206000c8400d14001c03e0021301120f80d900b14034480421030074070f00e44040c0c0e070000d051607015900100e020f029a483d21410700809240d00c4c20026403100061070b04a00e54450703400ca4050401c8001c4001c11032042c1003032015100d4203e20024811560780a05c600c09956007460302c0360200b502c0b1401e0320707207521384008003c02e40f00000f002c6508003580c030a4041c180d0750101c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 968477823 1250 968476573 968476589
    0x60a09230717010623030c130c08061c0f0f0b04080c011b0e27070905040b03010b0d241d1603020307090906090206070305030906150310050c0c0106 65
    0x1a000e005065a82d0354403100c00a00e00000e00c0614600403020031800e041402d202500281c02800c1a9940c508200d0403800c503201910180701c0c1d000d40c5068800400c13000c4481c0c4001909030300030610750310b01007180d05006240c00401014425895841a11305d00306480e00711484d084620700c5602180400711103510440c0644121079550b46600360103803c440701807154102c252030343e810310800d0310341c481001607000000b0f0300d641a403043c1d0900480454142c0c041d159410a40300002c10403030981c400304000c116402507038203009a4003403c00b05426075444441d12904100041c0f0100302090601207580c584425080c01035680c03000c200412401e1340c0b07075115048080c030001001160440030410840050b064072080e026009070950780029200d006510032055400d803a28206c00c20300005078401c00d040d9034002d2509031740b022a403601503c29042150083d0141c000e06000500364507a000c407422a00c0b80040182c10681800302888004090207410b1005e4410103001485c3c81d640309205100245c41a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 968479073 1250 968477823 968477833
    0x1a06152805120f010b0d0b010302090312090f0d120c1b0311010908030a0f0806030c0307080a0c0b07030c020d060605032407180920031e010605040305060a0923 70
    0xe80b420280000000d45080c80e90b0a101004222403103040050f2610311925170703000300f0203000850048000c1e00409100c41c5d0b00d401a20310160a11056100401030a10159a496144000c0c1003c10008608056000d41640c006140c0d1410b42c600ca100a1810140b04032000042643e448100004148035a00100c0e404054918809020342e04104072030000d1000c54000d41c0f0300f4542c01c030020300d0780300a40190400e204c00e00001c0b0b03a442d5010711002e995100d02604842c0c10781c4ea00d14589036502406001901c406100d10404100c49030090300311419960562600c1c5500380060382440018507130200f050303034819550440458680e07004d00c0031420b8030b242150620f080b80041224036520303040c090403c0003400002c1c0785e01940d82c2d614801007030442e6007030140003a18030304005c0080e256480a0000814485002007003212510790b50f001c0070884100181c1048051382c8914054889100e11300000c0d10319401200081c5403541186c02c81980240702e01910002000030040b140c182540e030714003458894000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 968480323 1250 968479073 968479087
    0x110c0307050d060f2c010b0603240333070c1e031209060e0d020105220204060306020a050408010c0f050d05100305010518010b0409120f091802071a06152805 69
    0x200b4041c7c000c1c8aa41100c00901e1400c0140008523a401c40004245004021641307180203543d041c400360f1161440700c02d142009420100306807488202c01984018030700c8460000c11305070791184000d00380060f03100a4910b4611400c40c41a40e45d680400c1007281041020461a084102d89003d0720170741911507500421070a1459040a0425880108240840e8076200800c80f60040358a1080d2046114501c2c490841040f80003180c00307014181c00240805000080300080c550b4000001c00c02c507200c181c020031034501c0400044800321010701c00ba20005200f8800c40c1c8080d40e40341c0c041500040b0207802900403e42c1c2e42d490609445044807180c50501050310f604500c01c400f80220f1441d040100c60401400080742d03610030080d0002c4c040315080043c031103100010a130242c2c0700360b005840c034044250106015100707250042c4d4483c1c3d4044484841c81070b0007400c100510090180588402450786550350403d50b83c0c6d41d0b031900b012003240f180040b0200f405000b110102c420940750f420541c0da150362021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 968481573 1250 968480323 968480411
    0x111160e1f06050d1d0d03021804020307020f0f010203010e070f120903021b03191b093803070501111207060501091b120c1e110c0307050d060f 63
    0x600c0c03103180764004420803500b40c520800880c1040d1001d15501f0010303124014444000e154036403224110340c0252002050040c0c194000600f044100e03000705c12203085101007000705081c1d000a1080c000030006e80008103d029004a100b020503030749620300078032001d40c1089d0160a86e8032949090300541c000b8007040340341e56607054075607408880580090a0003424450610100b10500101404c180f0001d0400766188400383c1c1300c43c000340011101404690070070300341320b01766048416544410f00d81501c038502a41143c5e1950f16085000100901040c51a0400546d4401c007103c064100344e00500d0500d403030003010745000d00b02645c05600d0000c1d4660500218000711404a2280d80c0005c0301c0e1014446035a90003502e006091514040202d1000b11054050b141000605030980300718400c14010701a1f20f90000358148044406000c9880392841c2d81c041c55100c401c4c60040e5030308410360410b0207011620a03005281504c8072442c001600b070900c40080c0b4200848460303da06003845010180502c1e00b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 968482823 1250 968481573 968481581
    0x230c0d0f1a01050a231c1401020c010b2704050f0f011a01020106030c0605090d0c0b0c0606010e010215180d36030f031710050111160e1f06050d 63
    0x11700b030081d846003600019002c140c0400001c180f20b11884070079820007149030b08040c5140c055507200081d010070303034200686030780030b508010380458040d031170046140303020310709492450080b8840300380c0c50603070711510b0100c2e006030000103005840c244240b4003155416001000b405000e01c1c034070400019420002c50780042c28a02d1a080c80e411603061200608c08aa00c16100000322040b40c100b8a40c0d401107a808140c01980c0b02d40040c08650760004006252141d520050840c441c0d40c40c103548c4241d44401c01510200c45010590b801039102e00100e032840c288a04201d904540020150003144c007260f4400c61910b1141c0500d0f000084c010004002404048800000030302c0e8250141d181e440b190352201d4454191600c400740c000200c0007042000c2c10302586558041007030311800c0510070700e0911044142c00c1a244109400900c5015904443ea540810001e00340c0d401e4154409040d0301e032a800070b40f031250103015040e03807459090140700314101031032000008003859201c1680303820304402414112 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 968484073 1250 968482823 968482829
    0x1308150106020303190b0303040306060504231306022223090705070f050a2f090c090a0e01080717030304030e060d0621230c0d0f1a01050a 61
    0x200510801400055000b02c00c1c1c950010710744002c44140319000c01008003403c0007108082d00340c000003801100303001c0355401000540d0801d0750184081d440c0d40e014619144600e40000c05e9000141c0003144074190101c055484050180c0005410407c02800001307200034084180b2040c0d1001110410074030049516240401a00c00d200481c0e645a2502060b03056100a0050007003160029400d01049240502420306581040c115a225501894022420000e034281300301305152031074864610140d242200a82840e010303188000940315502c4c0605503030015100e8943c0301e43c202c0004101900c0400d4154001d041d030100510342d541c58001c5801d512001c8481490190b042003040101003a04400b00d01284102600e406548415900c0071130003c0001c0d030881c030001600c8683e0308410301c2094070135100190061001c892080101d5081038420418980c56000da9004420f4601581c503081e0a00703400c09010350200d1900043c0c5560b2052011101410324158100000c018400c42c01d00000913409 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 968485323 1250 968484073 968484103
    0x50604030e01050729060a08070302060d0e010c0804140307020102070b0306031203091513031e050f0a0504140a0303080c0325020604060c08010b0409020c0c1507060b061314040e031308 81
    0x8452306180b00700e5110222070001a000c2c4100081d260341c50720030b43c1d12581d6060600c030020004070014503002481c0c8001902c00303075449480800030560803140031048542d820b505030003c02c1070310705d0322150340c499800081c80340d9490301409000102c012503060045200d903141d00f000c1e02041120340e020404112001d411100741c0413071600c5080000b41c1103003515804840000c0c141c061030017000c00441d014403a0740d0003103011050128a010505030014054000d0f91103a41e40184503007120300500420300c070107103c00381c00142c0000100e103181d10102e0095802035201ca81382c00204166550781c1c900c400c6092246401680404e04100521100b07110306084081c2d14038000c0501e5140034103208060181e030045203411640010845c200c000104545840210301419030740800ca40740c1050034003504002400e07168141405219040d610700307502110306e140c0c1c00308100042c40b4104001010801c92591310183c00981e6000c140100c9241000905024080710342055411760034210300b5402d200304000803e02c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 968486573 1250 968485323 968485339
    0x140f0a02070305090d0c0519050a1e050d080f03010f03150504020916021e011407030510030803040516080729040e040f1208060418050604030e0105072906 68
    0x195000c1c04132030004008031088035020f6600d0510520f1000917500641d07218650070485900070b00008210300846000311803150040e6603401002c01c640f4040100b00b9070020740c0310014010b514150000402c0c0d10300a40d00c1d0747c1003d20902d4801c416500a802407481e541c4620030410800040e0014010614900c403014003650a007903011800c00c1501400c0458440c2c1c03101c4051181901c20419681d00c1041c0041150805c0c12041200f4000d0503403884001c170f866070100c0002e40a6001f03005e600d02070100d84451040712032540e11040f046030006081100d0a00480c031340501460b29101908000d000e021024040043c0380060800c071007480d404a400443c0d0b40040c0b00ca8840b180c403000c0d681180c00d91306424065655901c0d056041c01b10750311008090389820800e8080095009054a204880030f40b400c00541880002814410050035001030180d400300000800182c82450b09000c0840c060400307d00308090b95513107200d00980440c1c0760f43d000c40c3d2000c81002c854806880f5980042050702c1c0d00c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 968487823 1250 968486573 968486587
    0x290405090f252f06071209050105010b130f0f0b0319021b07091e020702030106120b0603010507110d0e0f130b1806031c171f090e07050405040c0504140f0a02 69
    0xf81e12840000c1c1038409001d0080c50f40d40155485d40c0014a580d5030201c000c104030340c1c5405541d44035420070704d080e01c0364600e404008100000a070b094002514509013014501600d084038200c016440200300f400f01d01744450181d0401081e900290803901c1a10001d250b0702d10100f54a18a046ca4560001c80513504080c10950b03a445032604c03280c28209240c1c80981d4403501800400d015050562010042081e0049100e0900004403800c9024100850090101e0384805004460400d0801d0013655a43c0040540c40c5509000303a5030790020910207081c070b15111000200244015040d09001c80402d51130304544121854468036441055402c00b99500f058203005000c02d5540301608404180500000354800311280241126002405005078541103031030043c03005494081212021604c024510b040415941064019404440f42d9180100346c070743e1500c01000b014013006071080c1c41d003a403110004078040e10313540112180b191106c0346880d454140103010620312400144080503c91040c4600 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 968489073 1250 968487823 968487917
    0x2011b030e1311092b0b1b0405010f030f0b15040305151018090b24090c0d0c0c0f0c0806010f0b03040204020f0d06290405090f25 57
    0x184180ea5001d4417010303c0c0102c40405103c40c044c40740740e03503030000001040703940801c00d281c6080e40c46984040c003880d800c04100d810ba5106401640540c0d40810020b101840040f4800d911900e03004101d0003000c1038090b4000c000c40c1c2202e8200038030040480c80040d080c410302c5010410b072903002c40101d0a114103889c092012071100e083e5401101803128800b064140d000403540c1110f900c4c0f81d0001c903000a2420610b0045001443c0b5412108a80d49078401161040c03a200b1602c3c1e20410b500042d00b483d14038844072800061805986540c188000101f010010914040000803114401d144120815007400308017440c0c024164080f151140d08400c0500c42010303207005480d0850781c103032000358940b1514080c03a6014000c5042100103d49403540011b0f400349568401388002c071501c074580c540459a522000164401c0d0300840740c0000d10078001c9582d0b6134140e80580d40c081e400c1710101079109441d002c0341c84140320080c8214006011390840519407421400f0548400b00c4547c0c280450072411556 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 968490323 1250 968489073 968489077
    0x2150109020309070f06050403020f01020a0b0610020f0f0106090501050307030528080c0a0b06010921230f071715060402041a04030b010503030a0203031302011b030e1311 75
    0x10314103826000710110700c0404080107070134080d02e41c481000640c00c0d10f50348014000e4002c3d2005902c1541d01040c040c0c0305500100d5a000e5136500100c03088000d98030041400114215800503000314811410840d807141c1b41800b25950030104880080746040c54501054217940068002510940100e401007001410000e280c400500c52225003030401d03403807041000718001011501805038080080d48030900314010890300050340c480c1c02d40345980d0311580011154480b1a003c0c1802c2150b0302c42c0800d8001c2c00c409410030010b4400c02a994040200071800301d014810028040220303441100703403c0d502102030080d0400ba009244030340348a9010200c003580d40e070309003d0505900248181c0071400035201d0340c044a0150001c0b81804400207180703100c0f0b03407403a4458030040c0c810300c83da500041604d10303000c42200c410080f16401581161120030103a2241fa042003012410304c00300411350594aa43e4003094940d441c020748440702002642c40a0200480000001c20a00340c5800302012023603001e03c003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 968491573 1250 968490323 968490329
    0x10c0f020a031803021807080901200d060b04080618060f060f010c05030c0c1c050307081606060312030507360801062714010506031512010c020d021501 67
    0x14003503c0c0300d000ca0020300d110a01641000e500800d10340d1b12010740e42c440d000b510740074040642e541c43c80d560b2078250403401c9440d400ca1021b1000882002c1c1c14203e020f51f006001d0000600d60300084140d503916801c409580a50300003002504048104410240d00c1e1102050203180c2074007070040340c50448050400010700616661140d2000700801e421644200390b00860301340d10101b00c9035039940c0c64a106588650500c0381510500c0481c1400c404944504010040f02d94414001c506055443e9580c000c01d420600302001d110304003d10110104402e4005c880c0194042d190500d80c50348500b02c0201942d0f4020700e0f201c2405107103540a10344284032401c14509031008031404582503041c80064020032000d5100c00035a40c2068000300b0461411408841c80c41c0e0704044101242e103a100040301903850b090070806134042040300400150a100f402954403440c240d8100d010426018001014482c9601c24481169590700312010019010400d070348401c489800101101d080c103034444e4010b000140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 968492823 1250 968491573 968491577
    0x904020a21060f090c0201090b07120b01110601090209060d15030201090b03091e100213141017040204020c0a1101120b0d1104021303260a0e01030903021903030608010c0f020a03 78
    0x100c178401c1082c800e61221b42007ea004030301000d14240100c004004041403024040204e1030702c4c0c03601c0070542c0a9011800745169039005041d49038a8810703d64005d40192900740d4204a08010400d0a000c5e036103c0d8001054101d40b00b14490307401c1d800014013003d05504440c02991041046c8001a200090056410140c40c4859a603081c11074502500300082c02c0c10008015001084804140807860030120950301c44d148a040b121604104024201d140300e080030340400d00c0ca100ca481491042004290300c00d001810151030300804c4d1008910f8440214000d80e0b503100300b1881c0154541e48000310f200a103200043c24000c0c0400500010054000544018001c0c05c103240e01032141e84031074041e03850300702100d082d5501083d83d900300341d01d03190300c1d03014003c2903132081030b10100b44100042d05a41500300c280e5606c1089810020043d4000c05401d1000d4095209070824806c289518640c01141ca620070b0b42c0100e001c2d45086207441c00d44003400301ea030013409001d4982c42d540740c0e4001400207010742c00d8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 968494073 1250 968492823 968492831
    0xc180d0305160b0105180f1f05090103050606030c040209060904150305030c07060e04180f02180901060306060b031515090612040b0a0605060901140904020a21060f09 73
    0x10346016501482a04200010000c203014200180010000141d04945090f113a0f0124201d201d00c501000306400c40d651503441a482e004944802078100108a8074102c01340310110b03283e120301c002000000241c3c811561031740210101f110038141800f02c9540740009440a5040c07504840c0020080d0056810080c081c5681d01080d5140307407000030a4800845d00081600e5480080105007915050140215800319000c80030409030b9090074881c0072201c4c0e4403006034682e8103602e9900c84079501501c010a07070380b044d607021620140f5600c0301d071082c0c001c540340070002840174075629081b0103851003a8020b1003000d0701801008081000e01402c4014403c4c1103d030042c0a81000001c02244d004961b481500701c44003180000c800541c1c1704030640264001c6803504019903071050042d0903206a4001c4581202c018044142c655005055580007090018011404c4c02103207804642280c0113094000c00081070b00f8083c0402000c8102c03500c0c1c02218081080c0a494141000d24490307400b107106880c2038a42e5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 968495323 1250 968494073 968494099
    0x90d030b03160605040303140306100302091f080106090807030c0501030209031203010902181906080a020702150915030c07030e0f0d030e030d0906140c0c0a030303020c060c18 77
    0x2480704920280b101c1e80c41024058484000130410340190000b100400c000c800c6a0003800c900c0004c0d01d120340c034020f244160850b0202e000f03c0294124460591b00012007254400d8407003d1010101100d06160ba07440d00e09615080004048040540c00917101d9000061705002081e5890200800c3e20020700300982d6034070380c1401003480d14022640c0010507800100011442c046180c00614131000a61030210000c1088420030440801903000c403502408281d000304052070194490300c1d400b40c0b040c0001400d02c0c2840d008110135a0b9a440000105100090408860700e004a002c140d40c80060040034114500180c1c260b490b031140050280512650b80044412a42c0344910141e12718070140107035409420380d250181c181c10068002900c030340074201000d880f1a11864190b801c03900349944000f80486801525501540040c50340805c0d8004e030341b800c6843d91108003010004512a58006903501501c0c1c00b96030034104003170203102d949501003041850f60128651900c04010741140c00180503d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 968496573 1250 968495323 968495329
    0x50903060f060d021003020d06050406060f0e120d03060905150306070c02061e0307030c020f0c040f0204050604060f08010f060e0909012d050109050f0c0c03090301020729090d030b 79
    0x3c64110000d42c445860b000c2c14014651540240c912100c211600344509920740040000713950103800f40500085018003c036107200d100d10344081c40d40d1006860a018112a0320300c07a0300b011001040034001c251103460821241c4114071807141c1c4901c2c1005002040c0c070703880c40001e4444001a003038104000c1c0494074007081d0342e52902110385420a6a40189034400c80c036513040c02d01d070411030740640803900c2c00400500c3d060000c0340c440c0d000011403020708030305010307a0f081000078185848800142c07540ae0201040644401c07006102800007900c960618180409004041100c1600000032000075480200070b11508103c814070507080c100c0305280582e40d04007889004081040310500c900c504c08482d001c00305900f01c2030042c3c4101e09601440180c0c0c1300c480d2201641c0060300c80d1100200c085000841030700d06100070300402c0c0e45400030399141c04074650000303003643c20107407003555460101c0c404100354079480c0c001c40135200256140001945480c42480381c03030b410b95240c07803414140ca83d0700b0841284e0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 968497823 1250 968496573 968496589
    0x8070e0a290421141b10080907090c0302041701061707030203030a050d020904110c0d0207080d0f050708030a021902010902010c060f0608070807030b061c02011b0206030f0406050106050903060f06 86
    0x1c1303902411102d000804501280e0822188415a40640300e0701c040c450100e485101224030640d05000100221464290704070010403200500c2020180e00b07010105440700c444000400100c60354001082840c01c004e40d510041c0300c40d40058a07035910914040006860100c15220b4403182414025102c15015000001a01c10904007e512900c0d040b800d00383d83c0000700c0035000c02c0e0201821900720681e07900e4281d90360002c50045101d6a404a411418041d00c5411a28440c050360300d0108e08210740340d079590b811a007090718034149580d004158201c822411107034485411543c0c1c4001d005c414a150006400380280c00e00103851107441d030410b060728400701d810003001001c0300b01c112184166161200780d00d480007404204c801e00110700c04140e61f0301e8002000341101c0098458044400030550040d41c01ca502c0d0f03039000c49070541d50707524bc034007680c2d55101841c800d01300c0c4100040c9a150601d080c10071203030b05801010a200041c0300a481c941c60001d81c4a500050442c080c0300f1036290100010202 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 968499073 1250 968497823 968497853
    0xb1c0507140a0807120e15040813080109120507080904112a160b0a03051e041b050a1422050c190503010b030708070e0a290421 56
    0x418001848030b005540c030030500da104008550781c070030603284040c2004c1c0031b444210901d0740c2c03207502c0b9507802d01308030ba400c3c0803058100b440b40040d10300d8443c2c2000c0080d240d803929800024945d55443c038a07030a0003031031045240c401da41c0746001454030050f99282d201d98060480c0f007178011503885004800b07000300b030b5007140d2004010b45801e480000c1141c9403d11140b003881c284e040d0f10300071420b440001c1800509030b5015224641070303040c03c10000d00001c800501000344440e03441000c440b8402c662084001e2580c0c003882c0a00d0102050480f256501306034480d2680c4032078000c404143c0100700086558505036503010086914589000c400454541458a0200f44070151483c0c203041c000c84c0d002c0b120080c480c10f20300d0280100000d8650809031091300091181d1920f681042000071401c0b445a41c04130b1388031505007004050a100000410402c0b0010380287c142c0107036000c81d5203480b00421244040c882504017500e842d00d410021007440700e00591034201d1388a20006524020030621301d03c2c255034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 968500323 1250 968499073 968499107
    0xa050d091b0609060f12392007152705120f03160c18151203080a05040f120503240607031404090e060a060b03250e0a09060f0b1c0507 59
    0x7001007a510792680880305007148000c1a003100340d40f4050881e0500b40303034960202c0790262400d82c1c50080402200e1040304909420060bca130801c0f500c0b0556014551120101401e80011050a142c2030080c8044d580c0824000756002100c5103002e0035000048555400c46685488800112480c0071040400103801074000c0381c040900c0a010700b02c6503402960f4000000080801803543d9502007000500e4109001d400100954000384146005410444e005407040c4890100c00c401511030780c00483e43c1780a8107000580020501100002e40a043c0e000403a00f9180f4145c0f90074440700280f02ca2140c07640040034803a120101466051504041d5801089a0002401056200520345440300030450300b0000d40ea1a00c0004900c00005606a81c40b800c40031400218283d0444403542103141d0540c808030401030a100c445483d5211412040020b000c3e086001c2170950034000c0d0382d1517001c5140c00c10342d20408184418601c0010003100c0142a001d01100018181c03203d50003105c1d183c60301124424 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 968501573 1250 968500323 968500391
    0x923010b0a11060906091504030e06090a21020307170303160e0909010905073507080f060f07230a050d11070b011a0a050d091b0609060f12 61
    0xa429280070805d5071007400294280c5401820951014009002c10b5030f001e0006011100290302609254006200b0114000d01c1c041e000756031004114141800764040c204a0f607074800e411001c600b0304001c000c0180c900403d42482c00c0081303c904036983d0000501c1000c0c1c0400100300b00803614081c0b401250f4000e00500160640d10341071551502a200705001281e42d4484c005001445014145998443c2c1e0f400c508a03000300c1c0020801c00002100e06080c04240307004440000440c07483c10800302e02c041c460040506090710b80010391500c00c04001b442c541c18809940d1416610303034500803502403601f01414120f03481e081480c0003100c036401140030b1240e481e45024030344000c00ca5038101620703446205000b08112a03889004606803541403a11504481a081c850011100d0055001d4502260340d0f000015030b4a0450321041514182c0400d10301c00000450b00600440d580210b511003d8400707403d10980c98043c0d201c00410b448801c1400d04c5d038165995182001c400f481c95103540c0600340404d4180c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 968502823 1250 968501573 968501581
    0x10501030c06021c0905010c020f031f20070210021603030503370e011401030c03120f0905011413240c12030c0c0803010e010923010b0a1106 62
    0x40900107003030080b10094458450418400b8401c5041c1042c40c2100740d0310510014504030040d0b601c0d52050500b203900082e03049034201c49403400c1100054440b50030500d49100100600b0392401c90b0100c001c280303046440b469444451140710000c84e00304980c15a024008269006400c030301b46044024031807003200c2148400028558800051030188841d840c100340182d0413200d034011000c08110143c1040b41c100007503213210308001ea00c50700b8040d070800300114504601e90a13290300184240c208842d080c038091014420301c140b461403442d4042e07050a200c5403200900038041c00c00c00003840781e2070411404032050069107411005a40401000800f820001a00c2d60f0038810740445611884404803034035052500c1440c4145215403609802007104554111504000c4018040402d01801030240d429170203000164000d004600030449040c1150565040c064100150b51843c82c14408842034081c0d400b080b00c0080140a0440321803c90b40b503500d04040e00306845940b104584060603001d158204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 968504073 1250 968502823 968502833
    0x60606020a060506010804021f02070915170a1a0a0216060b12150c030903071b030c0905042301110a09030203070603020304051c05190f140a140706090501050103 71
    0x900c0742442258184095554640115207086044502075801042c1c40c1788100003401c80c1481c0e1140d48d03403034416103401c1c0b0f483c0e060304020782c4c8a4084150318401d000d10704000f5000b0b401c500344100710300743c40500100195078842440c0769000240b0100160311000100d111001543e0440f445c9034000c400450400200d418020000c0500464107030042030204d0840c1100c6001090803966030800c465001026110200310703121135040100340701800c0c402041020003041e52417a0525011480500403034040741103180880c40c03003601d03610003003046003064184400a19014000301c02da498010f500c6405284402600d4050800d20190b002d0707541c4001440c0c441103903c244007401340d03030081d41200c00c007079a610f10460891004440280858000028440e05c82070500c0310708804582d03d181003400d144902001c18085201401e10001240701144004031641e0005001a01d80f608803000c10305210711500c000c2d10045110007603030003210303002070003800300803681e0301181c2002d80217070003000b95603164600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 968505323 1250 968504073 968504083
    0xe0c0f09011b0609051615050d090221010f02031006180302063c041a0d02040f140d0206030703150b040e06031006060e062b020301090605060309030301030305090d06060602 76
    0x1080c1c0c5c1c14000e01c0354880b0304582c0c0380784c0001101c00308030300741c10020004607040b50340e90800402400c1386600d13000c0344809a070b00d406011f29030302114400605c0040340e880c54207084805440800b02e00d0703401402001020f03450340b000c51040750301d0390900035502c4204a1101c02c10301e00b5508000d501801c00f20341c0c24100c110480603800c115444950000c0e030b02c07646c041c601c0c00410310b1135064011100104402d003d40e910075050301542c00b94141c40182030403c54061a03040c0d803c142c100142c1007805d000c0400251051400c2e9242e0140252800d8a981d046600441c401d803000400f8001415201e40d1300c4400f05100a030010010b116440340540c40b42e880340c0c15620080c80551342e15100c3d224a0810b2042d01511f03104200c111062616482044010032041c80343c00e401500364648200031482e490015182c441c107550701d0b200e45111005940798140744950381201d840b5003106005100500800860240001c2120705403901420100d86030a051000500e500c41020070041c1818100000040d5203900068 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 968506573 1250 968505323 968505341
    0xc0c0d1103010e030319020703110105070e180709032a0315060519060e01200c210c04090c05060703180b0f19021e0601050a0e0c0f09011b06 62
    0x2440481e03107803e20160749010999100e00c2e07244056075150300c83c0440b80c0c01058168464104201682c601d007000d04d084980850303660000c1024106100e40c90701d4107200c13421516181c46403070480c41c00c0c6400020406078880c00002c00034000010a40702010007051160341c00c0701307041103440c4029200d01c0c0c406240b41e81c40160189250400c08045642c1c0342c0400c19001c1d01c81c0c441c0380c40d9000c81c0b81a41c215074070160121151b042c41600c10500740d80b04d600c1c542d03220314035901d00e000701300d0080c03d08284040310f5044090210128000210403005031004122003001d50412680031480d0400350401c2c95040c0007940c882580224002400001c158014030b07010a0701d142c0814249980d81d842d420840d0b684a012041c4810b820104039415800035441d480308050003031403040301d00b0300c0c04c06800d00001c0e41b852100d2201c41da220400420440c03400307444000c0a0617250104803407a040018241d90300780100d1007446030002c8041420200c60740704140781d0704041140001c071400e50f09181018001070542807 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 968507823 1250 968506573 968506579
    0x1020c0d06020d180201021b060f1b070e090307142b020f151303030e0303150f10090315110a03061d091f060330090302010f03020c0c0d11 61
    0x202c3c10510041000e4183c40c11580607005800b0700c0d80d001118400c1c480c000384025502840c02d00540e82c01030ac00202518001c5014981807a00b548032103002c505d403040980c0002142400b40c0100010389d2008402d8698140c0d125000b0390401281c80c241504105030088540c40000200000004003411002c10900d001203503001c0d500743c0d007214040303e82c58022814440b140500c1500105080144106800081034040d150006201054202540c215401500d41c80e10042031126000b1262602c03424a2a442a00301c5407409a0500110090b1496000307101c0901015100c81c148c503490340e41e6401c00d100294054030358540c1c03419503040284c010b0071980910080b400ea400c2000900044400220f8016907112005210802c5299512803ca0000d210f07004c030407036200c2e031002000038611606207540300f074081640185480306219110380b100a01d40001d0401050740800c0002d40d030040400c0b0b003040c0442c5009699520507080c1c2034070317010816481a40000d802d56840c824890314522002c0030050803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 968509073 1250 968507823 968507831
    0x9140d082808040c0605030702010b030a0c080c0a051f051204051c02060907050913060501030809180f0a15080d080106140c19030309120513050103060b090f01020c0d06020d 76
    0x108001c42d1945402c81d0014000b901003081407017003030f01030005980c0c8090548004681c03004002e0109007400c61005007103138443e040c00400d011844042c030448009503800c0d0f0f1403030500342c45c010000b205400070300ea4030b98410101c624003500d01c911800490701c812a207880f11509506061501c550b9660391903d80688124403500340c0d800c07880c40400c1c1140501c2000e801040c3c1c55007010204540088050080b825412240125400081403406610700850054601e82d44035202141031206418101e00d911100c408c240040116502c05080c1c1c00342c1118412100140000017400c2d000c1c0d160004ea0040001c0307100309006900c045c1d9001d824a4113031038807a070fa200801d01d01001c142c0e40a00400ca0030510f2a0030100403003901c420f40c612900c640600074640402d5059907900c0b509541070304030204100084000902048100c1d607024160f0080100303203010090107290100303400690180005203485105841e400c0c0006030700c204084c4080100041c6842919109843e00740001c0d1703c140c0700c82e1803090070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 968510323 1250 968509073 968509147
    0x201110f190e01020a03110c04060902090f0d02010219110d060b010e03070f050111031b0604030e030a0c0303030b130630110613090c0c0b06030d09140d08 68
    0x100b005800140c06043c0c004082130202a5416101980320042d0b049551081c1c08028111750395030701840d4024100d084005946e0004481400462403411002c603002c3d1a880d0320703000041c0d90001e01050b1101019007000060b0105d85050f6442ca01c1210706680e101e00b2040495080c4120b0380d0021000c0030098807140301951380e480030f250b1550800d00c151003404130300602c2080907501030806070720640303101001eaa2516401c1507025a110b10211140f822076030103d4200000c05801a88810a01c001100105203003000d903650400303204110301000f0101034607034100385495203030007110404444005c84244001501d420030f410342c00d076503607214220340310401480c0c4100048a50382e2621860700042025402c821410a000603176100810399241164040c10008a0303110a00c99a800e43d1050703035400d6419180c5050441050101070903030b500c260041c1060561698012412104a82581040c40442e400d102e000031022010b00c40060203c0b2000256840b5000b00c0314601c2001008010710442804c00e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 968511573 1250 968510323 968510327
    0x609030801080c09161103130f0e1f12031e0521060603060411121608280f020d021315140d181505040302010c1d040b010201110f19 58
    0x740a440400150140c0d001160a4502c10044c01d202c6d03d86030402c4916000450052000d14016a4000c012002d00d0704000d001d080e51b8448810340040c80700310440f01c09801401e070880407d015100c1d480c1020200c3c0340c004205400f581689078401000c06070540070070f00700380b40603205e58007100780078501048400c50b0100756103441580710b0141201a040c2821030352000709010050800003410b1188a505006005611510001d101d10646038055810101c804807400507020000c0540b0303401044a00035a244000703601e414840241c103030424030200c3d4107825440740070000e21902c0c086250075800010803e4034001d00410309011184c4038a41c0ba008500342107011900c00382150380007500d9610410600828185580088141c01e020080f10003a044035070b42c890402801c500e00898034a1b450348108018181c080c40741401791800303800c007031580816013162820034901c0001d50b184605da079102d41440c1b43c2d100358400c1543c4030300d150b61281da486000340340050640004182034030122034858000170240c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 968512823 1250 968511573 968511589
    0x131a04030510050a09050d050415080906040209190e03040302031002030702151b0c0c181003080304050f030f130f0f0e070c05160911340609030801080c 67
    0x41d03000005000614405101240509009802ca00c8015119203950b40822821b01c0410071b807203050f403540c966551510f00c00540c40301d0303661182e100b40003560042140c07880010a80c95881035044504841a0740c0d4107040b41400c04103140b1103061280307040040204008008010400c0e039000318211022600c080104005a1008a54140060b0480c1d10700c82e2242c060b101c08683c1141c8000d00c140e26190002c0c030b0703c03102d0384c11201008d44903601c4841e024085046c40071202ca00d80d901e45040078514944111000f1110003a880010001c01c4000300142c2840400c4c000300c0855003040e01a239548405180705021150011140c0020520070840f0004544108202810482d0500b0100c04000c91619403600f020713410050405041c41420300f803041c0042c0061013030a60306001d04503245200c604000d007107002c848070003101031104003081081901401d40c404180e0801c0821404e4605070700310342941c405e407801c1804401031050342000102010190840c1106040c3c6400c04100e808000c1c9900400100c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 968514073 1250 968512823 968512829
    0x3070e0705250602070c0501030e0606010f05130806100501080f15060901050904060f0f05030c060906070f0f0605010603112809031403070210050703021020131a04 72
    0x41101080070184003007840006002c021880c0c001c034101c440c6651900310130313039019003400c0f50941035905051002d9a0144600381650036280002c100e280381c2070002901d0424400c043e1810702c5008140001502c40c0ca100700c070043c041150558650b41088299006008031900030385010aa0b903100085140a03004403c0b48a4103100010309843c120040c140102d0303074410b070001d85c1008810401c1e00c03540e881d1401000001c000e21000ca410982c503110324418000c4181d00058481e4120b110182144e540e03440030f4410040c02207a0255440c8450314243c0ba205002c403e0041612015519178018441c4a91046049070801c0d181032151225004c104d040a100f06200c8078400c15003045425506181ca00800c2c140c4401420540c85141d00c980b18441951284a624011540001007050441c24030803000f143e41629401d107241890500d5402035151105103855000190f6102403130751601c89410180510710342098115a82c0c0d070070125411110380744900510720300f034030503c2601050340c00303040c00c507411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 968515323 1250 968514073 968514077
    0x10b030d020601060f030f05090708010608010b0d08160c03050a02130c081b130801060906080312010e0606070f080a091a0d021b031303032303130501090c09090203070e07 75
    0x155030b08000c0243c1d010f42e14001c5040800da0744d80030891f08030300d01e44291800ba01d000c00082802c02c1c80d1615260a48807990014886a41001d0312400704e611214074080b04198080d0309640c5460403525082e1810000001c054180c0c5101a13002050080210320414518001c0c0d4a8800d00344c240240c02c0c003902c220350380540019080c2000581d20840141d8020400032034401b5087c0b0344040f01100c444000f00c00d40000c0060307503586c0010066140c0500c5041e00400c2140040c6003000e0f1a010170302041403051007500d4007024940000b0302203545020840c0d21456002c0c004030111401c2c1e0921014030b030000b40c0340401140700e209002c542e10994181c21210f05030100c140c2c0e41341000d04242c46001e034100c001c0e082c94000e48140b1101c0c0c05a0180060190740401c003614082031031a6041c0244000188484050300b4000041c90600c000400022aa40094101160100c038001ca14015006114201018081803502d4201103400c0f0042d822071140c06000301c08541e400ca45450002c08074213400d80317407540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 968516573 1250 968515323 968515333
    0x10908030a0b0d08160f060617010e010b060f0a021908090f0109140111010e030318250e0619030b01150206060f1c08040303050a1d151c15030302010b030d02 69
    0x99074045100b0246150344911401e80241c4150747d03070101070700c1c0350780c1100044441e2003c118100d05824840c0651108040009010100107203010820600c80c0d03900909102d640064005c4206000704000508107210010200c010426428160031640010010511840c13064509190541c401c91040c405d41d600c4080c101c0c07100d0784400c01529401841030f070b8403480e952110b1084d501c0e0341042c400b41d4801e0594004041c080e840e54a05142803106400c800180f0107000381c1056000728070b1001e95020b0b00c0c40b100056009840301000698500716000d064000000c010700040300300b10500700202d0490b07480d5014001c00304901c0c442a0b0703c403203003100c20301d411070391800d446244c40c038240444106540d0700214800000c000c83e11155415031103504242d010501c00a41c1c404100d50280d101c0c40710601d8061000503041c40c0701e0014003800544083c07030220b2803010070801d44200c5510030500040c00e580b5404c001d1f00c5000c103030310441c044003848240c015519191410907681030115440401c20401e0340940 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 968517823 1250 968516573 968516587
    0x8071421130603020c0a020a182009011404090216030207061407060c090e0a06060e0a15080903130915050d020a090e01110714100c09060503090f010908030a0b0d08 72
    0x20002c5d042040c980041e0b100d14005000036842e0b05100720b020b00f4113207074407240b41880311200800f9103290a40f210880c250546200f900e042481d03082d2943d85800340b0f4403024607210f100c41c1100310b001d40c1d00010589440001ea0399080501c142442031410303c01c1d001d50b64541e0b50380f40281d40188041c0800801d0384c1003080141c00096465004800c200c000b41003d0b80c0b030a454011030f1050740d004403402000180d80d80d006102081c0c100c442c2504035041152603040e55400c0055030340098882060581c18425003c0c045004520f050065035400c541c1d80d00003010b0559240c00480c06800d040e062068011000d0f2008100790401140e409415600a400c1c080301070700c0d261842c401043c0c0110001400e5589402030301269500b14018082c0c0c1d401840c0c00402c2028881e88a03007000040d800c0303242180c1c038055a8025568100482e10202c1d81681001070701da6890402c5103040c0350050034100801c3d4a8114030801300903002d0081e41c09000100b40401502007040180000d01c3c200d514045c2244109012103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 968519073 1250 968517823 968517827
    0xc0e07090b0d150e0405121e070f240e0c031203040c05041b0807020c0901050f060408031209060903090a14040222171506010804080714211306 63
    0x1032240b030b40c40c1c4a0009207a40f004407000c4401050780c11001100e00e103403003408140b00080004024140b1103200300c91401c1b80c6100c01011300940354545103141e0030040b03560001c1c810554030714248c9940005000d12107000a2202c00c00c8a101c044480711202c0c50002c400684060000d2859000300d0f0281c028560031031210740400346504001c00c11240142d5801020455483e54004c00003e0314090344600a0031414210150035840c00410302002c42d406201403290783ea80d103000c0141100c0041c0c8645400e0341034480030504d09d1089402c40e001c0c40c40700213003080d182e4a103200120b01c1501c64105440294a401ca501512031240d105080c3e03101136040d505204041000004070f092803402000180f0741981c7c0910011442400c5012580c40f91200804204140ca040100d188201c6104054400e0480c8407c08116281000e05035a041011180c0000d0400140000301c0d500180c0104000b03441c000300c842881d13920b014031102c3d40e4461355065074800a604a50090390310300040f2080040c001d505041003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 968520323 1250 968519073 968519077
    0x20a090b040c110a0b040c090c1d090708010e0604020f0f03061c03080a05060109080a0308160e090a02070305270f04140a09021c080915070305072a060c0c0e07090b 72
    0x6c10355032011031203c0000c915041d0700c5500c2d680c142c1034035111000c04500c411400707066080c40b449801101094208071a15a005c0607550555079003582c03100c1c09803071f01d001140081c00b40701800c0c21403090000d4040180035004000d1403040104450606a82207052041001c0c4041a20014007007004100440e502c0c203050307000706034484010314158480030365402072140f914481c07040a50200300741d0b0080c0003014606c103038850384103801ca0801d003801a100501086041600400440c070680c1d001c9000300c20184604100c545814402e88100806040d0054000444c079850704114881c5103281e0034040e031070509004508441907400070400c1e560b03603180e2214026100b20803040b64404d40350304090051fa040d05480c0d140050044099030b8403561100d041c001c4041a92241580c281014061040040d52020848101c65800410400c41041c1722442c0e4441c000c0c5c820540314448440c1e103000c600d190b44034080108050060b05a403442d02e0b561031038090007003000d64a08001801000c000d10030f420702400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 968521573 1250 968520323 968520331
    0x30d0c0c0210050d06081c0c0c0b12010e060414040b04030c02060f1c020747150909070b090d05010606080108150f13020d020a090b040c110a0b 63
    0x185a050003006074001489a8203540ca00d0001c50000304290f0b03000c1c82a4401d060103071099400802c01400d4141c91181d150165030381e51420070088411100c10068031003000c0d07004040f0881001c0d01ca030400134500c1038204090103110803843d05c10f40000c0c00c62904d4003491000058003540c25015454945416a40c0c040c0100f083d4207000e1007200020041e11004010f041540c1280d41c00c58807203282c05d181e07092000c096030341400380d01c0c01802104007207200c0210602d20072043c1c42038483c56a40701c90b2502c1e81c2841900c03c5071148102c0e440722000c40c0113901d0400b031044a00316900d54000302d601c4100b1460802c2520f006180d9032000e10f090041043d4800208040c442c001c0c0381c0000226513584003403d50340d05810210000d09014010451640104400c02c0c09606440c03411005151000704906100401002100c03401d040d031900c401552201c4607250355080d009025820041d03294540040030b0232982145074000c0e8a40080710020a01c00c02c3c0400d161a03081010b400300b0f840c0c60b11068003461000e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 968522823 1250 968521573 968521577
    0xa020304200315040b0a060824071e0507020a061706150d090507030308061f03050c0c19140a0f061d15010e070e09040204110c0d0905030717030d0c 65
    0x40e5084001c51610030f00e80d2042d8800c1180001d1071400140c00800d4541651160980c2e40c042148202070284840b00e020303c10604511a00c02a55000400ca4810101030b01070032482c0a00c000d02903001d0390000080011a000f41c40103c201a6144400c0b64240102e0154201410800300410101c0c0780558600b4001c41e600214542001c91010011084401464044039168803201d820410182c1107641035070300c01c2045134005082c981010b00340f8540010310465504242d40d510014205901d442c2c1a207406452060884440741408074030309600220703402065503c2c0b200b0617a0032030300e0700c800680d5007a0307a60b00101c0039040507043e6440030046e0401d401c001c8462030b100341e00101010710810a420103020009031140e51545803442d91001504050300c050100100c000e20920030740c480d001c0c02604540d05450010300603641110955050251458090060203034840c1c09143c1c541c48000c0c80c0503a00200c0c2a180c60070750342d040810035418002140081c9030000d00c090346d03255045034170084c140c004074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 968524073 1250 968522823 968522833
    0x8071401020f0c101d031902071502010b010e040b101407020d030f0f0504150503071404080102040302130902090606071e060f0f0c0207050621040c0503060a0203042003 74
    0x8150814603000750001c0703c002c0d0300500c401c1460000d54041c90039100040011841200721070100360782c591040ca040e85a000e4244104002d0442c420407070748000f0412480e06040110041400074080c0a5040c00c042c006040f0340b0303000c02c82d40340910544030000d00c0100290001d0a40d0f940c10b44480164600c14002000f003806800c0250300e585010100aa10980c0c5e4408004683e103006456502001035200030850140400c1c812110341a910581c51340990031326540703035540c40c0c0040319010304500480100704004240064009415001f038010f6034402c4844148841002110754121060903c0c040e500441e002c2c08544141821401810440c0c098450f955080c00038514403103000c81c030503d04a51259543c80800401e82d554800c2e04001813243c0003c0c080809000d00007555036001d405910700c100400504508400b81c0c110030030b800194800c4c01452203183c5410854405c8409110351030007405a0030005854091078030031a0710459020034418066503079000b241c0f841c2e04c660a2080c0d010310a03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 968525179 1106 968524073 968524087
    0x605091b04031106310e1009020a05250b090102030f040602031e0c040303030501080d12090c05061b0106050f13020a2106090b0603040807140102 64
    0x3000c010030901c40f030741c03000904a20480d11704907260101c040215040415210703030a803101040a1003060403da807104a00300c0e200007100e4140c0101c883c070303206000d5070507242c0c05040440b100d403501c02d04040f500941c501b081c5080d056030001d0761011421540400844916095010003004003d508604008010069803e806040100701c982c000c80042c07041c8403c1d0340c40143e100342e1044103c540b07041c21000c21134194018041039000a05040c004200168000303806403e18240c1d55034503c0880e10410300c4002802451402c0300e44448481c0c0004e090707a21480605113690f07840d034010301000e00c030642250854a035a8001e5005110340c2182e070f840e07556071031000310b18560244009a80c44e0301030310040740d188032012881c17504980c1040d51046106000c1c3c0c4240b05940c0858410010f005103001001607034001203500424411007000003c0c0001d000e141003100b6280224009410054 = true := by decide +kernel

theorem cover : BRFrame.Cov 968345323 968525179 := by
  have h0 := BRFrame.cov_init 968345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 968345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 968345323 ≤ n) (h2 : n < 968525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
