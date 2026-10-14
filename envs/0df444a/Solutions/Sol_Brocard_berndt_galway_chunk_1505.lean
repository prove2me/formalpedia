-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1505
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:17:56.770574+00:00
-- url     : https://prove2.me/submissions/e329cee5-1627-4b96-8544-1518925465bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 270503597 ≤ n < 270683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 270504847 1250 270503597 270503599
    0x161d060a020601031b06052a1203060a23010c0201110a080706060e010e04060218091801060801110405040f0216080304170f0711010210110901020c0a0608070815 71
    0x6445541000c8029540c24080c88151540203030907a07601041581851280143da040351200c03841d00031000c1d0180e88440c01110f0f010b03202d1001da01c0050f4141818049140d40c210700d0404036403070382002c1003040300481c00c503480a4a291100c0241d1810340030b03100d191a48041c02420030a6400c1d4142c00140e41e40170044140010300d0069168080403c07816401421519000784010404030b52580201440841d083c010010301d003407401d00042c001195900140381600b030345040c0e031100184003404210913040959003e090750a030844482c103c0c6401b446080007d10402c0d000748451a00f07140549418441d03801500e008548a007044030744107010f070b0102c0d0303c4030000d5004111144102c2c201307134a05401c10760302100c0c9010104c24150040c48040266190800713840300007450a11580c0d91007441c2080500914198050722411100c00303c81c03440399102c071448055109955488000009050681c3e00c2c102c40d01c5540c0b400b500740000e5601503041544030082e41086c0301d90307844000144810018002c032305 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 270506097 1250 270504847 270504859
    0x903030c0f0803091605060903071205010b04050103030806030d0e0108011e2301120603081917040302060105040b01020307080f03100801110d05062706131a090f161d 73
    0x3208950f800005c0c2101c2043c80414118001074660080141c1c610940030381a50541c4180028404c0502c0c00d80760802d041d2160000040e42065070340402c042d80d100b64010303070102c0c60728800c004d0b080c00d09028204400302030b0304c1c002d0418810000003034448803040c020103052113407201115450fa5600750070200039000c41803140c50518041440d0900c0e0b00b0020032001e0008214022018443e24140148425240c2c0200384131308002c00c119000460380c11100c40c100c1001982c1001e0000a1001110b030340c029070095018100c270f5814070041c070064403289071075039046510401c40c2c032010450356000d070b03546003246000035580c07600c070204107451030b52541d0000007455180c045600c41e80301740b14004244811180358107004540da04030400942d19078520b609001d00c42d01d0210404080b0106d403805611a0740140b0542e031003900f4540324412a5011a4150720b11106001c00446601c1e1003994184c0c49100300740183c0b0140341c00c68008000a906640c01000e000e40b03400c0c00f107080c400c00a2105103004006d004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 270507347 1250 270506097 270506101
    0xb0915040804030204110a0903020d1e0c1a04180207020a05030f0106030b100b1b16030821040c0e0c07140102130504060501050a120204120f05100c0903030c0f0803 72
    0x40c06490303016201c100d124a1806103052146d0160f04151841e400c03060302e0b1102c0881c9190280702d00c40300900000c4030f01802c0b50440035078400c44042030041c0c00b4015181c42d02d10604101141072a01941c10103d40075070001d00c410001c1c07440300f00c288440000102e201581310315103403010800e80d40e0903800060b81406000d90045901e101541305004a078021910301c5407a4460b9240e0f2000020a80200701007401e081102c0b880f0a80c0ca229840c0d80010340008441c45a10b140d000c0f00340014003900100c40348031000801c2d5548402c0c03003c07880190306c141c0f0f40d001c000e41815036804610a1030b46c401c1c484004103080000d24001407950540b201c06802c203040c4001d004020441500079806030440440340074000402140301d08041c456002a00d030183c482928002c07001d981074604401c4a2000c81616808000100d498814032285481d41481041046201202460064241005800c90110701d13860301e485155030907803043c0040c0c100c9805050100180040c0d0400c215008211003000e8030b00c400000c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 270508597 1250 270507347 270507353
    0x301060312170c07081308030d0608151e0403090504020d060602010c020f0607031a0301110c120310060c03031401030c0528060806120709020904050105030a030c0b091504 75
    0x40c0c44001d112a50b518160b41000005011445009030b030b010701c2c1d03850240000c1c4001030f08100286043d2000341050b1056981d1041c0031031940c0d01c010a440c80080d141c0d1020080711404000000350224003003001200c920b1720039001c4028804031495581d03010704290200b8141400f40c0c0301207018041c0903100395500c85500058102510701441010700543c1780c101c07607000491011500e041061100405031900e501c0d030344c0d01140a051440005020741441302c2203c3c1d1940d40074415454204460190641c641e6500c502c06070410221980070300c2c40d6202001000300c0c50704001c2c0720009851807414840403524840c10100c00400441200c12581225013001005010600750707488200c80088410424008036a44500104000812807900000c0307000c600703120042c081c0b11120f90006000c0c00c0e00302d0768a0100d07e418030380704003035010160302d950010b079119060410340141805801c05600820444607640c0c0c0041455030320503c0030701480408030200e18600024005150654103802d10310106d0b0078141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 270509847 1250 270508597 270508613
    0xc06020f1906180b13150c120e011d160501180b0f0409020c0f07080d3c0f090b0703020a0213231501080702060f0c0f0a08071101050c160c0503010603 66
    0x10026540301e00c1c1d1406c403207130407000ea00803541c3d07241440d6a10703500f81d0041c0c1040c801400301e4081412040d5241d40c400218032440701c0300c501c0b4841e4040300030805c4049070740f5a08040c5442d500420b0400989918803403e603031140145800300c4010845145c0c5d16203268010540c107001e240c00203000c01d400003c0414803200002450030b06c003403400c1c0541c0e016a0740c9400c4169500c4014101c0f2012500c2c1c40c1d00c09403038900712181c017004984480600b1141013488884010603002509190001c11500040315201d541d002c01030706e01804120811514003107542e14060358518007031100138030840e01e000b526111102a070700800e41c5c986000d03084450300c0c00c1c0c8510340302150700d00700ca20942e0748150b41a1a0090343c410419107008142c141c002d814251540100700c0700b110001098010307a6401040341c0203400206000800c5440c0d0691746004c22424013107001007040f44104929501d5a041806201003c80402c0464204c0c8481c000008002089440d003524108200d5000f60382c5135203456400410f014240c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 270511097 1250 270509847 270509881
    0x70b0f070605010501051606021b031b0f070303120b030c060412050c091e0c16240e0304170a05060f01050108090f06150301180c06020f1906180b 64
    0x20708014040340c4c0e29200110345d03078001d10115564031040d0002140120700310b42d0080880018003c000840ca0000360141860f542c84181500d8108840302c0801ea00148244203004403540960050140030b40707140c03001004500d42e82e042800c0940d45a0343c5081c2c0e81d0301005a070030030b10409040542c81340c1c1c0e00c014200b1400c6050030700380c03614092212543c45034130384809014862281541452601e4400350701d982c521840007090342c0800a000c00015246030901007802465601c20110b40103c804a40e010f50114046121656211814111801c415a0002c019603041d600411150801c903d8450005481c1420300e450284c064020402800b440300542c684590503510b007a00c81c58010748034917101079510b10402c4403512003500081c000c101c44c0c00315414100c1881c40010008220340d11402c1d1910010100f10908440108a00f0380812204d80c0611541ca0700c280c82d003014000000c440c6600380190f08030224020400f540e14108191610f4003c0254105c0c107170008001d4295180085c6030140c0e00c116 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 270512347 1250 270511097 270511103
    0x151f1503141b0705120d0c030e150a150509010924060509100306081912020316080309010204030b0a0222050303340605150d0203060414070b0f07 64
    0x81020307103038000700303001003a5008850304403014000781e880c40c141c103405800c910000c44207030180380c510004034090f002c090710800d00001c4001540e001c1f41c1d10060b048030310fa10b1101400350025800b0304a00400d25600c0c070703840a1030b0038012804283e00060320035990456007150ba40907001d0030001c2903451403588582c030012910810b40c180c205080c6507240310142584500380009404014000345404c02007181200313404c00342000303d800b5844c1c5141509103031036144c01c0d0540f030480e84641c0302400700c1d001440000041d00d0002d107251014051703e00d40300390300e00031002d40034010020104947c00c43c254100c81c0103581184615807142042020100690f002410080c02c414504004e0a81f83d9a05a4142e0845100030007d42c500031a0511040c071000b41600707900104410503850540440b400121059110b120b80750014591418041454038013180e00b40341805130000010410068a0016044e0b0300300d40c00c000d0310701e1145840b0381c9842c50301710150444170041078040750b030f42080c4540c8030107000440d00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 270513597 1250 270512347 270512351
    0x6180f050c0f030114011202070503071b080c0411071a0f0c0307090e040219060905040e0102030907030803090709140a1a06160204020f2206030c02151f1503 69
    0x200c40340040c00c0742c0a128503824155408000405c50088401101c07414030754103061194568610b041d9000882c2c1280c6801d460640000514104000c002c60000f10225001801510050b0031321507519640c44003000394600640d0740e00c00403408000300005440e082ca503c4074020481d482c480301d0451586400741c0d003140403041400003151101c000002528801c0a056541440791803a00e1103a84114101400980c2c12001c0c1d80340d1200315203070a05a0b800030344460703100c898102c0d290405110032a03642c600720081992060082c001103080c00304180088a4000d081c4948030703210117080a0a00c0d20342c0d40201c00103450403082d00b9442a03d00d00c85480341c81200d03400c00002d00f417000000c1000602c2c085065015904119821004000100b030f5070300300b400900f00509101001c03c4000103684031a4840d13580c0c6040c0117404a000050403805009041c0c2031900f440740e031510704c2d4060b541e00103040d01c421090914000042503800100b0090b400d40400108000075255500c6842c3c000202942d02003000074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 270514847 1250 270513597 270513601
    0x302070b01080109120e0906040b060d060e0615070507050d0c0e010306050a0c081006050a050c100e010b0d08030402011b08070f060501080f0705090711060408041e061b0606180f05 79
    0x6c1c06a0704284c542c4102402403261a61680d04000c0184401901e290348408140100f9403e012203200b80c0000d0031000c01c0b0b100b007508204080000040c18800e601c0304800d070801c19140003c0e13001c03030039100b1078409584044e088000c1c3c0c9050030790948a0f81280c15a9000d400000050103690b41105014900f101d2080103004880c410840e18034508895084520310102c0d41040080e10840041111003468506107060145804441c1d040401001105034096210001c0c4a02c6910a10030714480001c122039140b441c1545a6458555000c0213001906010100b0305040c5228a2081d1a084041c3d0200040e0ba54441c546060168a800180b043c0c51241c035080c004586c0e2701000a20001a0351901d0003010918588010091141801805582048489005034102e0241004802c1c01984240d000d203450742d04001142948414079412200f11003502c002c208011504030180c0d42c0071a501c2e4040c5d84601c80035041000c00780610354400b4910080048140350082d003140c0c860880700700740b40c10600080d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 270516097 1250 270514847 270514883
    0x20306061b0307110d020906100e030a030e030c0414160504050d08030712020405030a1103010207021504150e09160c0b07030204030209090a1a0907050307030609030f1107090902010302070b01080109 87
    0x6965044002904031f506440410014030b8249014010707220f01d0f160000390400c8110220382000d2000d5400c0780800c5158004904624082c007440d61000001d88040140305447e007580040c0101c042c0420012100040b0700c0d445086c8560101c0b80505030251040858420b64030b0405081d9104850388000600c1c81d02d081200c0c080c0a000f01c0381103801c001c0c0104180385042c2c503510140799451030465403541d804c2007000300580740c1d408100d10b40c500c030794031440c2c545181101202a418440900070b00f0442c200d05c003041190389000640350005e00c0c441803101d59a21041c0103031a4982d0f0840098201c0c250030040104c040c0c0e06400030410707a44203842d450703001d803160f18016036245030504005084400303070f607d54500b441c00448000d43c1705c009042140d07041c940d1140842c1c28503643d900700395034036911900380354140350300000100d03288001441d2083c00e281d03140001607140c181d80e00405142688403ea03000640e882901034404040c0c1246036030809580d0340300114000e1020803c21940b01c1001d0090a0030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 270517347 1250 270516097 270516109
    0x110309100c02030306130f0906051b1303030e120106090b030c0d0c0b03090307080a0e0901050f010e01050c0f1c0305010e0c070206030a0e060703140c0405030709020306061b030711 79
    0x52001d580c00071400d5440d900204611091300e40300030f401d0700c0d580d03a172100750075105400383c0c040c2203000f240c0c00251801c0403030b030300c0e0070b00d4078030525111a210041008038608010900d84004994162a0072080c00c120400016503042210100020540c01d00d200490000001ea2088444071400c03400c40300700c0c1194a091080c6803c1812000d4900425008100030b40040310b40210f5008444c881a00c0c6004100d40d201032454000710030000001c0c810741a586200d05004170490301502045909646040701c9500080c0503c100700c605604009000c0703010003094104100b407090303401c03144055074040e0903454003c0d21040d00604e12200040d042c240006413804030480c5640c09507616142591a11a080d02401704592000e08040e00540c0c0e00c0c00e418102440510015015002556002c0b5501684148205001c0c50240680f5501c80c0100000c208035640000d10004940d82c2080141c0c580e560a00000d0450292181040b5501000e82c4c3c49140c9c401c0c040014400e051141c1c011083d010140414000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 270518597 1250 270517347 270517361
    0x702131b02070504061a09040e0604050a061a03031918060c1a010506220f0623090f010e042013091802010507020a031e0201020c1207052211030910 65
    0x290031b075005031961840308090051000c848080c0011441d10041c900d4140b800ca01258140c03020b41141d005100bc0095a015849809110049441c1741030102c80000c0c0c1c80b4819640452240c00d0304502c60303295240284c000f082600d070543d000340405d07691031030302400c81c034a40072085500c800001c0c5100f041070712180c00745069880113040281440c090001903102e44904c0b640048010040e0b010001e0080440307410b9070050003460341c5030303408190442100260f0780d402004d6182d1f4204148120301440d2282c1003500e407441402d2134006400c41c400c1003c50014250002c1c0c03c044420322860700f01c141c6070b00b0f80c02080106481c2c80090b050690314035540c0d04840340b01da4620300e85079800c155107000d5889040603001450004084040281c3d481e50754a188a44840c02d013911000c9a10500d401d541c2c06111206000800743c0312a100c01e0f60009100c0d4440100d4090076104580d10600c0340c2c4a980c050070390711020910f41c1170070402c19800c183c24202a4100b00e448001c54450440300b07210703125007402003030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 270519847 1250 270518597 270518609
    0x60301090b0417070c0f05010e0d020303030c0f0d0513021003060506030402130e0106080c0103060501020c09040204020a05121f14100e0f0301150501090e040f080702131b0207050406 80
    0x10442e440d66902c0c507004030400c980410f100706042c4280c0300441c5010046800400031114502d510600d0440090811071a14400502c100d46110048001d40c4007c02241d50001710140d41c0c030368840581c42080100e014000001e05418076240c01c1100160b08910306080e00390080f102981400d0400360124160390003800303140e40207031090000c103005040480010300381d00e03441003011035040d01100ca0305007140c81d0f6a0041c54560b00240c0050034a5030148211005040288064441850840040784e844000584000e00031640010400c0a003886002640d180449080040e1011308052103500003c00500141a51084c403007000051480001c2c06061010303400a0081c403100505850281d5202c84a018103507004081d908440c2c099035020301c01d01c1004c0c09070903017010b042c81c10103000510350a036603004198440302150038400811341845422a555900900d0180e6030707140da00c040307003241c28103141c1c0c540918241050381d051901d015141d01c2c070440f1942c0c21079030f8403980d6900b04800d031006403050b2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 270521097 1250 270519847 270519863
    0x2413050a0b070504030f0b0615040f0317071502130f03481503092006040308040806190c0e09150901180e0a0201140a0306090e011406030109 62
    0xc10015090760036069120341d5504086013081d5070394580c607010889440003200c07a4500710041000318174100440d0400365403d012081c0c03c081c1068110741e6205101d02010382281a040b203820316841e180c0c4107d842d820351050985500d0059244103034040d4000c11080c0401030850000450807207014841c690880e82c10492075024000556405101c80c1101030805090344010b0303d1000c40e2000c0380302d401082c264201d101480580c60b052400c0310f2042e0300e1581038201401d20104c4070109054680e40f0020107501c5030780ea00e244003102d001903541c0c8a5640001e0540b0070100d80000c0c04500461050f100305981c1030078030704010485001200b11001c00c03180b007010401c506119406400c040320a50f40c4411003840410b22400b01c0b100003511241c4c02d92225104600440d444607041c0400c1c040c1611980805000344001c881d190700280c8001941021006545004118100d03c0ba1080d04800001c03c0c48070020044140c244000c03c8c01b07060440004ea2019403c0c80115841d424140706240300503401c0201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 270522347 1250 270521097 270521113
    0x102010207080a12060512100506030d051c02090d0609061406130e0705030a0b1e0603100507020c0d03050301091802031209030a0501020c060601080901050712050601090305241305 79
    0x41e1340381d020514484854a60340c50011034203841d0810400d500100b554014200c403aa40700c619010303100000c100a0194020074020041683c00a01b550354404003001c00e001294000d0141000074002c8024140d0301100c20580c4509103c02c41d403003800b00500486050244900c80c94500e0000d00082e12070301c1c0c009403481c03d1844c04014a50001c0c805280d440240c4680c070703654000080c5071101041e003e95105400e8024095210450200341b6188035541491038407130316080c2c0010b919150342c90b0030308030502d48900015a2083c0709209074040c01000038070685075601ca0b810002c02c10f4009002d2040600d01c1c1c00940240300b06100e00003446194014020700500400da0702d0103a840d041442c1242e01480b420042c0c0001a50071300180c0a10f2081d42d00501e228074118000408409002c0d00c0113103580d240c0802c2c0170304035621030160740300003000700008907c0d1384a200048078000d1380c0da84090114003500c1043e1480c0100c0c04020501c0351211aa10019a100d082c2d800b480c001e10b0040c0142a50700c2245 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 270523597 1250 270522347 270522367
    0x61e020303070e120c030303040809030114250318060504060c090807150e090103050f210a0c1502040e010509180d1206030c0b0d0e062215021605010b010201020708 72
    0x41c5200e440103c0d1405d649040d0001000319296800a840c00c4411400c082400c0c00282000d202e4240010b007082604156030402c41700002e0203018a172041848a60703c41020b10300300c0d0183d000603207a811003203001d03e1100c0745030528600501c801e4a0441c1c400b400c018017142c10701d21841065040e240041f001d091501e1805154000c0514512911410300003401c80d4260f0b9950b0760480f0a00a50150010300f4482400c440d00e5070506807109001e1410360489441010911303445820b403082110326050807420701138079091010700c00d41d07081c00d42140c00d8000240410785c45040b84a10303040728002c0e110340303015031980c10392100d10484200a400d00c0d5804003204054480c882e1130b61280b0504401d400203034580e26900c80050b03041080e00315103600c40c2c0000f2040440f44403807086034152040c400c0684054144107681110100182e5290542c042402440c0c50510103260480072100758220b8046640d42d00318aa00c0050095001c2e040d02d00b946070002e012404c4d4018000c5408199000030340701d280440200c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 270524847 1250 270523597 270523609
    0x5011202030405100c090603110a080c0c2805060606070206120c07020607030e010f0e06090126011d0106020703050c0d03030902041e060f050907030b130501061e020303070e 76
    0x420540e80d510130600380c400c02845501c60808050b911b07a60301c44c074490070104080c0030b0316508007002a540108000806032260b012a00130f4100c450503c6071581c81098403006490041c00300c4801d4240c0c1c5200c02c0e40c107051b88030180b16807505440b41041d02c84503503070360003044030b54010402c01a402403810000d01c80011401e0040c00d80c0400c1200c64079003000003540109000e82c00421045011602584540c41d556070458110b90301001d05240070100301481c0f0020800b107008006c03105051007400080d1310b0840074041e03c110a81c501342e81104400c0c0d03a65020051113008000c59002200782d45c00000300d00c1502c046056415250000c00034118404140b042c030850150a50007582056500e45540380188c0c1c8a001c0d1908071609482c0000e18625031450203c2251200c1e40410617140404108200750788440008a90201c0c1c0d5003400102c1d03d98000210701c1c412140c1c07500c00303001483c01001050054214200507119440c04840140c1038108540699483c4420f03146d02000c940c00001c43d0801d03151003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 270526097 1250 270524847 270524851
    0x11403070c0c0e1905061c030e0604050405090a020f030303161d0907020f07090207020306011a160807030807090302010c0209100801020c1e0c150304020301020f0a0e01090801060501120203 83
    0x20b48040e0360364a981d0100900110000c3d240140980500d07000c2c03502c03400c10f41c002d1940056003225450344020140a082940006d1220000d060160101203880300ba0740750710581e002824007610a12880c07508030b15a0382c85040084040f486580303402d10082c06402e000050f680321b1010032401e1101c0c462545019100c00f201041d2001106118104124007502e60380c030000d0040c603031f0350010700ea180604007440d070426141d900044030b600c1c4180002d5003d88e40008600f411a600c44c141f018141f010b0300d404000c20312885881d460501c7c4114150002c002d8010010496a406661001503607121688122000c244910000c1c1c00a103a100c1c0f01e0b40540b4000020340c0c1c02a03010090903c0c4141c0c1e8030b802601b0b98004510261068000b50f40b40b20680c6100030200a454500070003405160700b010002880e00740395000e01503003d640200001e01103450035411500010140d904082d129056204028402007049e5400c5000901e4034100103820b0300140070b041c090b00c0050312209058209041c0d40d20081d040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 270527347 1250 270526097 270526103
    0xa05090a0f0602030f0c130e15060714060a180809010e120f0f1c0f02160b180a030308070c0303090204090506010e0f0c0913090203060f0a0b011403070c 67
    0x26840c00c8800550304a80011010344100380240e2245020b800382c800a500040200000751401c002d2442c0c510003400880040d00d03540a4105460385841c50104103c03500c403400d507904114005040424803200c9100d8820140c1c0c000200c4409541c0c1054050036120540c8070840314a482d542c072000042d282e103001e020490b2042c0340980042d140c079400914a000041040c00054200506a114115082c415205100c001d01d008000240805c0c90103074603080400b080000b081b58603806400305520a0140c00356100140c03942214841c0c98030501043c1d5030000c0301c02e401607a0100e603a0011814100310400441f03401d601d86041035504c441003036559040c000022020150344414240c016903c9209020030240210001c085642c145001610b0780c0c031000d00049400c6908000b001800d00102044030482e02d0305440e0281c00c0740804000801401100b000258180111300403c145030300d408940c10b1080c1c44503d800d104c8105554015610781c81125480c242c20305c410400076284c24020b090a02c15544 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 270528597 1250 270527347 270527353
    0x30f021210090b07030623101b030305220b0109020906070b0906060f01021605131b020c1302090a09020c0a080409050f070801080307030809120409150b04050105030a0509 75
    0x11465441c046890a14080ba500240081400901a41840340e44041c0a0202036410f81000959911070050840640c80381300303003000c150000309640305c0d40c901d0304185c0695605a42200152401a025160231910b0030305180b00d040500300300030841c4202d40e803c1c50f0041154900ea07400c005860300650300c041d401680100003000030000145040400910460703046002c0c1c030380380c20402c1c10800825503400703902c1d045500882c0d100881c2030301502c176041101c00440d84070720091415200300700600170a001c19001080249d07468104141c02169900700403004407281080200728821030001c90082c42010350304420003030b505209541c41175008105c0700c940c0d0b100712400c0b09840d41c0e90703440035400741c0c100d000b650b51107209000f4682d1075080c0c03168004403d400c15503110f42c1010900e5a0301d02401801408024000c0f004c9800034074240807120b81800c50b08c110329503898071900d00c0c00280c03614451311f044581068a002075440040000d45e0140e4005940b000d295481d80441da401a05010700303601c40d140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 270529847 1250 270528597 270528613
    0x323010204080d05030a060e01050a170a02040504110a0614040b0313050109050a060501080c09040807020109030c0609170f070302060a0e0402130509091216111207031704030f0212 79
    0x1900801001051100f950b4415950385002070b00081a40c22540c0111400c8200c14014803641c3d03940740580c0c050710703008031000c089014044003503440c1005000c1e01940243c0303480240800c0c090090a800355548095074003d400d04d44e5414102e4442c4103000714074000c00d0003444203101c1e5011101c0107503003204050465251041098403480e00311906803c3c12540c0c0d60024041000300166405080e00500509000d4004005000c0114041082c0284000e045020001e022011a80511b050501454000b200e4030011912035601400070303280c074000c0c4020114a4020040a4400020098072210480014220451455080c001070380c0060340740070184100411400c0080d280c61002d06501001407948403440f61602091184811024000c1d41c0540c00a610030321a108426003254035000d00c0d06500690410304c3d0410820900c040110990300100c103110f144814180003d958080d030b8010b1802c0000c3c030402c0c800d2960148180e02c40108400b01c15800b00c4003619000b145404910984000e440001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 270531097 1250 270529847 270529859
    0x61a01110c01051603090b03010803030613020f09010c020612090106180b1c1a150f03011a061608030a0509010c09080709020a03020903030a09030b100b0306090603031e070b0c040323010204 83
    0x60f802c00d2b081103440b9071002c004c1252078a000c02400d191704003441411071810454607005c01b0148180080c481c1848000d103211411034a41808031028400852500005400c190540502a1043c0d00c100c4000e200b8420441c051700c80c0c00c2c40b6144d0400401085041741c4406c182c50b0f5a004036826100707840b50004442e2810058101c0d00f007a0f807095248141c0143d01c8918032080201182840241d0390081c2c0c500300701c02965000452600a50410441c0c0070394454404c13103c0785405c5201d61320700802a04010080c8422081c8640000d40140d85180017403040780c0c2030a00c120390038012072140c0c0700298031403c010000c45805600030a0f080a40c1d144c05490440004080703880e590182005038001004848108240f022010803950030034803400026043e81d160212146580c0806441c0a108016000c08110743d95410421a00b142070800d05a104d0300d800541503080a400040007603410b52200000101d0f4480d000d02101c3c140e03035101140c0b0340e04111600c2280c0b8251000030309400690b60070000840c803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 270532347 1250 270531097 270531119
    0x12090612041b080a051603030206060906040b060d02030a0f15060305151002151f05120f0601030c080d030903050a120b090a021e04051f0c061a01110c0105160309 71
    0x3c0c0900200603d80307503d032481d203546003024107000961102010101400045e6010410f1074100d10111160300d81d68440d07174002001401d8503812264003042c00980034000110940103544125100d6008020211805a591301030b151a210300070a610000c3d03106000b020301990005070003855100900c40904400d1001c40c84001e444400740c00582d02c0040c1c1e240641188020891303128036400c0c40c55010384042d103441241c242c181d000c0c082c415005461248080c8804200050220004c01c0031210389581d01e040801d1000300354080d020482c0244014070040600a0041080840e415690545000000401202d011240c0c0c0d82c00003450340c54a40145650b5141d510b21805034168078001a0755170054900c0c8688006260f032075658101302800300b003107940d4400e85040380d160b03d000d030310a180c1266010211440030210000402040c40e21411382d51812024140c030003019402c1c0c0701c03003810504161a5036a0b40c02c0115485000503420060040052060b1250703621a0b446428085d07051503d880000c0c603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 270533597 1250 270532347 270532349
    0x10c05091c05030d02030a0c0e010e0d150c0503070f030908070f02061c0b1806100f0908060c1201060806090a020c120d0c03050609090a060b0f030a03030501050312090612041b 77
    0x80517001b2091040080d62440340040441060614118001c1c2150028000c04585603e6034411215078039641d0505c420b07080e0000614080308020070804200e800054016001900c035600018810902584030301d000788036110b04950824101420140a030303994840600d841e06040340c03c0842407041000c0030031240810007440e0742040c404105032020100740300c15120107800d41c600c060054418807000d5120794040b902060b09a207412450458007690540350b0031915440f188807440340c3c1040080d03005902004e443c00c010115034180c0d40e07903a151400c42d039050341036446542c09000180402c0c5185150b03401429100b42e1402078034544442c00c2d2540d20150030aa00b00300405803104407032001c031503041c442c641e40401c0c01c80b40400c5070f0424841c5c450307071003102c100c0c01050990344514864070359880f010400e82c4e03264000c0c01c44558010f1403030014003a00c000e03c5aa4040d1040b07204129095003c40e0a907400c48d00050003003030800a0f40c03401260000741c0030340295040b0a83d915400d10803201c54003140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 270534847 1250 270533597 270533617
    0xb1017121c0603080313141504110303070c0305150703050f070e0a12060f0e12071e020a0602010e06060a060e130603060e0609122a07090e0706020708010c05091c0503 73
    0x2401000d1b29040814031681061111981901701d443c808145404254845402641140000c0d00140054021070726600c11020b015048800c2c48400000f0010300140c51800920030a41001087d110141c0907429140c4c15140100003201c0b400024180c28815640b1004c901d10042c0520702c0300b50b0b0b07a052070b2440b1200300001d0390919280c01c0c010000e200306000e00b10038485010005d0114000101d46c0803001d00071504001c1c081074030a04450741d109401c102c0c8041440d0001c0400060303a0b65084046c1c028445500748408a000f0040000e510f4608072030000c04070b80c4107484814502c0800001c02c41250601591b00038880e0703540f1404004582c85218090b200c1d8840d00c0140440d050000b00c05103810080f5144920112080042074a8010032043d48107240c441d41e08140a180241044981002c42e550080e29071940341410801c0c0c0464001198401c44000c1d400303481c03965480f0759070142030716181c0070f0305408110100b100c80000e080c5902a0340f100480080c400da00920300785e50309410341d40402016 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 270536097 1250 270534847 270534871
    0xa03030e130234030f080a0204091406011d0108390405030f0a03050715020c010c05091809030307140c0106090605100305150603090a0b1017121c06030803 68
    0xc030545502d08140c8140f04100000c9a03002c0100c03d41c2c0043c4072907418000d00c02008981c0c8007240303200d04103406a90242459400a11020b03010044c0c2c3d01c5541720403101940043e0600c0c023a401c80c2c5224031464500ba20041e50f0382100ca0303903080b1030020401d160f00d030029900c0c40071092811010460b00c0900300c170085140b5031942c1c2c0d1480d2008262400d00c8e41c40d8409582c1d00000320810010707401504841001c2d40c02148030201c187c0500e10340c0c00034002c0105690745542040d06004036294004014485200126030002a2200940d070b50b81e41d1032011504850a0351040010074800e901441d050008100e424050900e040304200300e05003034812640c440c501e4181c995078240400c0c502080d00c02c682030481c1c80d0800040c0b40c0b803180c540180741d08646d01c500544000000c218030b140184580100250040c0f1107a22a041c0b500e510b44502c1800c4c49282c642450b0b4140d02c55808901148008200c2080540203042c2500e00418400081442d5640d05e5201d69400300000068885c1d40503620070340b101514 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 270537347 1250 270536097 270536137
    0x3150411040e100501080c040803031315091a0108030702030c0d111906031109031b0109260f060f010317040e01090b130e0703080d020f0c06010305011103060a03030e1302 75
    0x14007030100290109107c51024041403008140000689034800412000c04003001ea40d130030000280c800074141e0141c03203410001010180124000000c040ea401000300c10360503030340c48850780c1d107074020b030301e0002c2d895003000301154094034008000c49502030250000c103541441c0c81000643c80440d184480d0304140703c9480804c1040c0c0c0601c2807403d8000c20308405454010f104002940302d0318805c901c800f941000700c005d92000d0f40704000040c003401e910a00d155647c500443d141110014400b421203491040009a013224030001c20800e028a00c14000c5004903400c42d503034249903d81225580e480203006000026100181e03081c080e00919402e90001032901c00c2000b40003070104408942c050150030845448144600001e440e002c4030b411200700c0e52649100c041d8030000c1d100c1d02c40d4122100102184c41e000c13468000c46c480f4102da208a0003080051542062203100340170440d000c0c1c0e88141003030000c202003400303003000e5801400020841000910010100c4040ba081050094805415800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 270538597 1250 270537347 270537349
    0x61306021005070306120803090106080d0903050601120c030209071707090e1303210b03010c02030c160b0f090102010e0d020c010e010302040f05060912010f0f0f0203150411040e1005 80
    0x104907500020f561409000b22801d01141020402d6110001003012000100050700c1e500c084d4461809404c40c0426169212a160130003042c180141c0420350f1680258000011070140580004203900d0307000d6605030202d45142c007006022030b0001d1440040c013640070003085081c4000040305210789096200d510f669424000350410369040280305482c02600c508560010030b4005065402d441112003040c03082c002c21041d203070003034681450b44541641c00c01900454803a0040301400801c400a4100c40034030340d0412084002d41c2c3d2a1141100c040b500704500140280988002d1080d140180008a81c2e0480d100c402071600e01201036030001a000940344040c0d5603402240701d14021401d01c0c00354205401d000700348160075541d2003801c1c8600000620310b4215100c100032629a00307690b400801100c10600c5094014210005d03003030030f9041c5040300c441c3c030000107842641d004100110014a0200f8010248002030030001080445002d0a110000307080d08000b09a501c0391100c1220309000b82d1030f00c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 270539847 1250 270538597 270538601
    0x30f150a0c030c0e060c071e080609070b09040504020a121209050d020307090504111305061c03050307030903210e060c04080a08031e01171608030f090613060210 71
    0x76122410542000781005060b0b60101040300c1d400b108486030b030303078603c1d080141074036242d1680e0040203c2805950081421000d170343c6d40c40111010841581c1080d503c218144d034071030101c1e0081d03040907a810701401c4c074542825409250300038409072050310f086442e0701c120369129036001e01c1180c4480310300300c1140444d0340c045200740090006035031000c4081010303800030b9100d0032180a1501c81c140d5401c0006d05014a108036091280006000305e040740002203060340c00781c00c04541e103d000702c040c149071700c0c031040320722204202240e0540e03545800c5841e0100100d0281004036401d90400c43c02104d03180d24002035500b170a0700303100da940002510316007500d40581403581c01000c043c540300c014002006040d60205012141940c0010f80c0c1e5aa96a00050300014076000c0c030701135a149070418008140404100c1e16101803031244003c0b078002e070344d07020040c4000c0384079170040c440580c20520402c1e1400e0301c452b01422190200900007410100c100032407a072450901d901580050b031180544440d0020380e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 270541097 1250 270539847 270539861
    0x5040e0c01120c090e0408165c0301020c0106031a040b0714120f091504030f0c03200a0b010801090f0f1a010b300106030b030f150a 58
    0x14070b000d1060004140004d4010b18191080070140198800042e0030040c2e580100d800208855108100c640713180c0c1004604913004c90b02480d2107020000d0451280d0300d01c4270180481e400c0c945121001c2041b03a031004207090f1954510405080ea0998824032955800c2c0042d107000004a03000003030480c5103003442c0c901000d0341064070101604080a200206440701241e50b440b078203c2c1444009034443d00a01041031040c0c0e150250b4a03004d0005004031807412041d402c0c010007500044807981c4142c02c08990424006030340c0240070416807096440303154041c42c149210180641045c40051401030300c0310740c0c1350404c00829411a00000462010080e4906100e03000d014920004c11406070242e641030403100d80e085010300341d40c609414140c200080c100d01d184002c1d01c07001c4801c21650750745481c960b450b0024070003044044046040110155110340e0030014600b21620800002e034030303091007074006280d40700000b0f406000e20349100c85200401c020219412018940c01c0d8054504001100304a03140c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 270542347 1250 270541097 270541127
    0x60705250501021c0501030c2c01032f0a14150c0303010e100b0403061d0a03030603051c0215040303090b0c03011a03010503030306090a0e01180209070206090a12030605040e0c01 78
    0x1178100144040b640641c21079040d21089491400b10300301102d2288a00b5005d540703180c0c1841c031580e002200700601400500f0a45510070905450f1034103032205403c100c6046240103403c410880402c02041c8101654007651300f0002d0060921a0443d00c01191160f11600f6540030075403000004214080400e550103a010580f2145146a507040c4000d208c0c480c845d070b1002414007600c2d80080708200c0c00a0034064080003103074086800e0000d140c13601074050b0030325100640700c50040d5000b12900f84005c4c10910000b4040d0780c06403e032280d14104064030381d44c0183c010ba040554514010340040e80100103c0d0041002d00031140c0c50b0f6260150000342c9884105400301103200902c01082581c03000019030350001011140c0c2502e90f03558600070030080c2011071070001c01c0c0d82840300403002c1c411038017051005a0b009460080302941d0b83c10003a42d80760015079400e102684100000c0c0085034244024000c04030f0b0b03034500403407030503a94000a81607643c105242c0c2e620343c000b0241120b140d0b0304050305102e1014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 270543597 1250 270542347 270542351
    0x2041b0c0b07050a08010603020f04170d0201060509091e03090301020406170106030c140325120b06070209010b03071101060609060206090105150d150207061d010509060705250501021c 81
    0xe413005004001c3c10041c8964400e246d00441d800750900001800d480181042c0c0480080f5910010003140d5544a2015280095442d041010510f410a258007921511420707000f091402d0920072003801c1074003d160788125030300041c800200d00740c0e8207000900c000c04544d07035007401d15106540d04032040f4406902407c00d00d89040d020044042d0418100d8040c220402505074899451450140580149811050340c0d0903e10b410700700140d400000301c440079855140c00700038040000d001d000140c4900c0c4000703503020b8414001084086c074984011584041d003840c11241a41d40991441c0c00d48030a50400740207d180240d060000e03075410004039501c5000ca00080c4124144900c02400c50324004100a001e086d6051100c000d0100d0362040103450f100320001190b40d20018102100180709644034000d000250507405044c69038140503040c004ca04c01e034068801602c51050039036040c0d22078031100a414041102d81030a80001802c6070859038000e00025940315214941c206030000c0351015030411034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 270544847 1250 270543597 270543607
    0x5071b123b010f18150e03010f05070e12070b1e0304081b0c0d020105031f0b040512060c030a02090f03010f050403020705030d0509040f18110a0e0c0306040902041b0c0b0705 76
    0x2842041900044915032400c49044070000780b02141ca24000c24845031f050341c208580440038000c25845907224034065031300c3d645800c52074410008201007180c400440366022010500001101c01c000b440c800e034000c4903460340100d54500c40c0030207410490b025210f1402c045a0000c40c09540302900e4154a113207070290820202c0d001c0080d9800700340c040c02030f0400001000203048030b100f000086042c00d21000c00c25030307400d40d241801e000750790060040034002c24403c442880f00c5100051094003402000390540d003540d07100a1407030f009400400403141c2c0005441020021a2001e02c10305201c4040000c2c04202c40c6080d0030042c1c6070420031340c8414065808642c0318030700c00758810155590984125070116032142d1204032040680110250000e1a203215400002042903080051481002c1502c000d150f0b0b554468080070384020845640580c190200700140840c03419900000740180b00400000d0b0110906440c2e08108000072800d001040440340f0503c240186030141c564029a203140881c941 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 270546097 1250 270544847 270544877
    0x60f0a02030c0d27050604110102070305060109050c0d09030c032c09060a0e07052d03010501030905010f020a0c05160506070f051f05071b123b010f 65
    0x107481502d402c040d0441c0e0b1032801c0713440c1c10b807540300e80b02100f81c10b0048031455014904090380c403014140c5040ba00181d10403c2048154008100304003225042005010315a00e0304182402a000040001441c5c800030445504034410a2250b00e800034001d58903c40c00905500e00075000b800c5c039001c94001c0134140204003848401c0e001107031107910307001c0d00c3c500e505442d01d401203100c5900542000030181c0301502003000141d4000b01504030321248080380410048606041c1d80301543e80c11200412803010401440729500079003240c0044c030b214100004007081150b01860480c0c10800300800014440c03c3d01006000b03041080d001100f1071107085400342d038505070025003144540680240034a07065914001480001e0113400c3c099165128848440c01829050740c0085c00d00315038a1000c50b001c043c6d00c62008000c1800e02e0041a17000c81050f40c01d001e4008140c500d40840f01c203014814041e803602407004040d2407151250440701c2c550748000903101400142280b080c03500d0b80810805184d0341c1b0602c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 270547347 1250 270546097 270546121
    0x20105060307030c0501031a100f0810060813050a05060a05060103060b030f130c0f0e04020a080f0c060d02130f06030b0d0b010b0a030e010212060301240b0d1508060f0a0203 76
    0x112076090034001140c46c55050040b16002e200c0c0c0308c03a540060382184540301203410520b01c98240c54030b030346d07034903140c0d50351110200100705103024110010b442040003c41e507412081c0e0402c0440e0003801281c2d0003161036501e480c5466400c4507550880c40d104e03400d1001d40d5070940600005044100c40071802d61070f0003c007061254100500c01102d2a1243d41d608090054407402c080240c503492407000501c076220304c010702c1d14940540e800c0b030140400c1c000006242b007001ca28428000f80090103801000350b081c0400420307410548000081560030001c1d5041950241503580040c43c5500204181074500080603007211009800540201401c80700507002580191030207054a00c1d50030043d8a034000c0150450080c402841d02d144150f20004a41a407501051070b10fa100e003404900901615000c400e401c0c00e440400800c0740c228820000b018000e02c102540542100d854a46002034220309441a10340b1020740d035800f9400300d420640a002084040146240e4000c04080c0d0541c514101031240d018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 270548597 1250 270547347 270547349
    0xc010e060108211305090f0f0105090c031902041d04050f010e03040902180423010b091008130b0c03040b07020c150702030111040b0406080a05270304090516020105060307030c 77
    0x518081c00141144c1140483e400ea1005004050078050b0180380c410241d510782c5805403000c004890b044800001c4615094260f5485002d58071075003070558843d002940c5070900b410024a40b060b0b000e200200d22a103119602d00e102c03182a50030700300b00342060b050080c10840742c1840c520507641080d00171000110004111011205054401aa1003544540060102800c04155540036007026a1203802d0051220701da04550234403402044c40341d9860b0841217446c8114601290061906000745808602400d08203520052588201c0c44941e2507030381c1c20030b0f000300440c0c480114450101c04d00c01403045111b1525400a031500007001200403440010f036203107012414207070b6240400901070085403400e410440e00035444c000745545030387c0c5513610030381c194025009080000315075134006501e0800c01d020742c82c00b803481c0c0a03900813401d0380895040c8420050404400031440104800a01c01000b881b580d0300ca4003070040c00d009000c40075400242500c034040c02c005c1c071941c03041c1810320120f45001e80c0c4034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 270549847 1250 270548597 270548653
    0x21b060411060304080c0d0309141c0c020a050d0506040318030b01030f061415031011041a0f0c010213050f091602010f1505030c061204081c020c010e060108 69
    0x10f500c941d2149490141d83c4200303000c0354000e000d91a8200d04a07501134024030380340362061114050040f0a1000b86139245001c240d090051545d04000c681013502810031088014009441c524410361507501048003249442e40071a45680b000f03040005056002802c104078070359040040c550b41d8550303200d21a41c050b044c000500400f400c54a03020402500ea4450110540c00c40010440c524000700403441c84020881010301a000c0c104040344070342013074441d0204550542c0c1c2c105041c141091061201076513180c40c0012088020002013100c402814050241485640000750f502c0a10701b0320b0160791111a03228030301660881c1c90340c414a41d180340c41c441e40188414414800c3d4101110103e014240d030b1480381c03518520b0043d5211100f003c5003c1c5000340c450581c00c440c0070303180d182c081c41102d00c544508020318400001c00701d4001200d00340180044486201d8118410140d0b1403801d04981c0024034000a81c0e5481d02540034510b420f0040da80103201c82409006880386100b180e5440901c50202c1d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 270551097 1250 270549847 270549859
    0xe0d050d050c091c02041a03100c0207030c0b090a0f061b02040b0d050109060e03070819030b04110304140615011107090203090f0c030d0c110f090a021b060411 70
    0x20b4114461541502c076040001400d459186000000781c0b0b8885815900a03801a070524000c4c8a1b0116075000110303140201400421980910781103078001828034600e04411030040e8100000820042c011540281680712a0a41d941c1822020084440c0d050381c803940656038004804c04c1441d420100681c2d02c2c0d8045055001d0a52081c800280100700c0480030301e80c407561442003401401300540c400c292491082c082040009000140160380b40544c020041480d082009a28182091000300c17010004203401c010908404040c0010242c8100700002c41700058080100b1007070156000a000101c2c042034058007207810180f01c01c109061843c01440e041c000d804402c140c040030304210f040002c003003104045440e400d0400d000da4607450440c5001c1c40e07500c501c0b071000040c3d00d008500814804800c2d2a1640042e0701c03680c3c0c0d86140444145000e88c0489200c200080c40d07180e407030200384551401080103980e5104c0720184a2004c00c0701d805407226034089804c010000340b0445454100707090803120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 270552347 1250 270551097 270551101
    0x14130206070611300c030c0a120518010507090608060402090607020d2f0105030f09030904060b0307090614030411030a05030409060302090c1207031a060415030e0d050d05 75
    0xc080c1500c980c1e000b081c0350300020080d0791007040d81d41c2c00403d07214003102130310180f905a0205484080944018240110400201d2003a151203402008a0452401d00d42481c142502d082001c5400445a500325103401015524403d00d0a201d800d034016000d041140e186405c02400500100004003850b00a47c0d001402d0f80b140e81d22001600d01090780100a1030200200e441c5c1680741220036444100d0b4403d500c03003008400300a041c004520b041040e981c030b50440d03807050104116003034094100340c05070200300802211500e0740d0213000e0241001c006200ea890801d00700050414a06501407020007501d20450110011042c04590300b1540000e0398086101254002a04114000100900d14800018000b03206900d54000c2c4040301d0003255045542c0c0c1d01c1000034078842c401c0d206d2011810311200e00007550140258409214400d2459010108540c182c01042c825401070708038002100e02d114259885d00c2c0e15000b0b8801855041026126803811400d0241c0381d8014800c8450072241c8401c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 270553597 1250 270552347 270552353
    0x70c080114062e0e1c1401151410031d2508030d0203150d050c09060603060d0f11040f0b030706050702031203190606050a1205060a060509031006080f011413020607 72
    0xc00c2c3c2c010301c1391400b82c120891703d00d00d060b202e81d00d0f5014190001c5d5007405c9101c14000101051002240c030300c2c145000c5142c80a1082003098500858004141a524000006582a00003180e46c402c0c51f070700000c0610500c01c15142002860b03600d0800100001c2c04002d0090200100c1074400c50503000f0030240c1c0b41d40729051900c900d4030034072412581004841c040300e01842400070b001c0c1c0d10404199001030158851005000c002c1c40100c84060b006044415010700180380c031000d01200c940582400700e007484440e80010185c6000f4a40364800c82d44400c045051481d0511a40c40200140c0c02d00303500e003c00990100b03848194016180c803010401100081c500b411b1341504440704910803108205943d11410003400b20340190b030700c010000705070192503148001a841424016900103010b42c10759494000104c8040e485600319580502658a200402141c01c0c000ca2024014032009051541080301c0c44a08440c450203032170070590171950a200c07641f21110001d021305034054413056030350780702c0341 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 270554847 1250 270553597 270553609
    0x30809070b0717040b03070504030c0e1e0405120307020a0302070806090604030f0309060612060c21180206030103030201050708250c0812071808030c030f070c080114062e0e 76
    0x9446005c3c81e5074004200003005034850010010b9912480b000ca00d5941c070f03403402d0400c50388100c580000c05151500030b6941d1502240e40194000d105408982c0000250802d42109410a035808405a48070854800130180c040c051744002d00368150081103a881d10341042655118090000360900407030084c040481da110360000c40040360041c1f4144029076880d0f2043d400340b44003040a985007840c1034001e20210388230307520b00c440d43d1011281c3c594214107288000c00082801e0320151011540c0c6408800040c1c0382e20340914025802034000207070703518110002030403e00b8020489245203d0760f1095a6818217078425584c40203005140c402c24641461501c0010352189a015441c2420014100084a58096045000c02c00c00c5c2d0440003629030f66208203aa02c0c011507607041d0803600700780030482100c000c60004c2d220482c0141c00c15018903941d0781c034446c01c40f01c03007040a00302101d40f101040004d0503c207030300b002d101d03002c01d21401a20307060800424000020342d46000420404071540c2c444e0395203031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 270556097 1250 270554847 270554849
    0x30203130503031e01090c09050f0109050a0306050709060206040b01030320010e0d0e030a0c091802102318130e01020c071401030504020907080408070c0e04030809070b071704 77
    0x40781d43d00e04045844400240018a041800c1c0e0010000420054040c0c020403000f003181307890310325019007000100031500790014840d0381009501540050360303a031082c03000d40c02140200d80009290910890040c02900203802080031755219100740000600315980301030450fa01490244000201e400b1043c3e524500d0704110041e544c20710b0033500181e600407901c81803081c080d46441500c0c5011409240d201e1003072600141c0000d0040404100e240b4a40c0c1003038420406400c00c5140c0b10080c0e078000b41c001e65800c0e01840014458050305000130b81240c65031200c6051100c102800c3c0291b094807011000c21003142640104105803803a1f8003002950004480503816000940d141c00c8030548241c0c0e100da0f83e1007001244240500c058410394003910400d80101d401428412241e550b0040940300808090b108642d0000204117200110f098200c041002d40502c030309801d000d007860b0400601071540507103d003201d40c21000703007046090070341e4084070030850b446101c1d0a04c0481c400c0003c032942c055 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 270557347 1250 270556097 270556103
    0x5060304171c1a0a0602190b060f04060305030310050603040209060d060902060d0b010e18010e1509010e0406140c0306010e061b0c10020d0918021c0b0a0e04110103020313 75
    0x3d010441e1031035041200c0e62441920107681e100000d60351002c0c00c0f87c2c0c0b1400440b441103039640c80c603041d0010919402280f940140040c2c0f940300400b0754030000c03504640444d032064920f90000700c280305c0800280180c000042c1411070307040703045003810340000765042c40c00b40540384110400c40d043c0c000c01455804c809000e940044c4403a0700d030408002440007402e51103148500145129011a6591903c00c0c80c840201d0006d44c0159002c0e82401e130418601c902c0a0164103114071a2455500d003550f45003c4079002c0c2c01c0107209810241414035044003602c0c040410000381039107030700c20001c013000540c05a0358060b50900e0800103019100021075402d204050428070588074844126111002c0080d103040110403e803201d40c01450480000c9840300024160100040e40d50314080000c8c29101e00780707035070b070440305800146400c062441920340200c1c5c00f4980c1d4911500c8030181900c03440d060b00c1c0e40e00240035459010030540360136590b0309040e8803184040380c141540072021403100c801c1c4481e030403429a8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 270558597 1250 270557347 270557351
    0x807020d051c060305010c030e1617030705060712110702030c100e04022106030708070b091201020a090305010b24130e0a05190b130504050f03130f05060304171c 71
    0x5182d04000b801f13081a9105400402d0400848000b400c1002540c0e8068500702101034020901308050140c1980c0c071020700701d0840c032060003e078010642c14005140078180d03545445107007445c6000c0500a0b2045a100b55a00400906c01000540c6000c69800302b9040110b0703003200d1003006582d041e100009400c4040740c200b032010540ca4405808031118075001503003c000d00b24943e69140415658045901855489400c42130081000720820005804d100e18000d02000e80c01075130040b041c0c02c9800a0b0003940c00074582d200304105024080c441c1000d000300130740d00d903612003003603940000261174101380001b010f50380002c0e144030030310303846d103510010701075604034103901c0d007003045846000e000155102104082200440003403400284207601210201030031140b036050b207901c0010014440103205589500541303503841c40c01501803004203d116401c00d2000e45a6042c1495080200c4654029034003a4004100748000319400c0308074007502d14400c407417242d45c2e44014950700012144101c40322003024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 270559847 1250 270558597 270558599
    0x304120501090b100f060309050a020d060b090a0509070e0408310f0609030b0a09020a1203080109051b0f0c0a0b18071410020f0610150807020d051c06 66
    0x88419001049002d00800910400b51190410019403403058405c550801320040c908010381c80c084e4112440c0da5000c1c40030307902c15402c0342d008100ca4178141201150520350300e00000115140101d042c41e000104031000700401d203401c4003a9580d40b070090140c046602e80340300003e000c00610008440d08c00c2080b00399081100520340301c1c43e003a60892074800d6401c81c0810004038400c0045032030102120b80640d5100d03205031840d2140b0800c244041c000502140e1240a03c40141e100e144428000341a502070a00301da003001d007402406d010060b004100c180742414188078003242d600040e0010140b112414035600e40d22504400010b2180c040503018074012000d1000a00401040ca18810b030302041589801c102449103160300c1d0602030066024591550710b040f01c2c00e050103401521000e1560040707030041c05040c3c7c0040d10f44001100e0083d0101b03900706060140c424420700002d0100f840e82400902ca01300080d02945880007220400c040040214000c1e142141840284200f05042d2400704042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 270561097 1250 270559847 270559853
    0xc030c1c0f030f11010207170306010314040b01170c1f050c0106080606040b060313060f0209060d0e0f0f030a2109050c0108130b01122603061905031c02030412 70
    0x90703d03a00c80481c04035020789a0200080d01c103000301c603580e0303910050403407071115400d00106080c3c00180c0b00724100740d65000410611401c5400700750185000e0000c003007442d0315091407040c1700700d84804030000c50f8200034140d000310380b9140390041c0842c010660790302c5003112500e011100e6010348104810203600b4607200081148020541d07600403002520103000258081e418411140300c103841c010842c10380c1c540c1b00c40101d16941d00401900c1c1c030b4040301519024889001a82a400113681e5490b06a9206a0a1b1b0b1896003003090101c0007048902620510540b0811103803240a07450b60102072182141c1202043c4030002110700d0f44802c404020840c518441c00c210b42c0d141e92025000d400710304102c02148240300341211400c041c1d5408141501c0704c0e800d145410116581c0b10000300c90a001a881e84c2070050407450084215034440e502079030300ca2400c02d08015104000019220074186013030401c1c001e680b0003241d001a01c4c4048005034001c8502c5c004103d240d0b128645c8a2620280410520010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 270562347 1250 270561097 270561107
    0x90c09090f1f0602150903090402040810050f0705030703111201150207060e0604030f06090501020a050309010b0402040b030c03040c081606080c032208041221020c030c1c0f03 77
    0x181c00360010b003410308902c95010008004040c0900c1000d40e002100d1a908a69120602907001110303106036410320700c03000040b40aa80240c1c02c2102c20f0f402079291142c45104900c00c896103e00400d00c3c1c0c405a0500c0b40d000b901920001e0b09035000c060300c03441408148241001210b00c80948032420307888542c1e607140300d00c040103c0320412400500500400044852141e140002843d03c0105418034252660782c0e4905003204c44001211540c4d01c5456032008641c0030700c0075100c80c204d1500d54554a1505420302803c4440b4800400e01c2244103210a01810010f801502d9120810f03c5205a0b251114200325404154035401520070388140303050b40604a5081c04140212480c64507400030740d0b10703440512081c81c00b04a9002140e00b40e030404210010501d400e0b49440540540c40c1035107003030346030700303558075000340081d400e035010310440e0a81d1100080b00c0c0141c07400039003184040c1c11205040800a61160044100907200300c1c200b624140d10100c0c000c0c10300c010143d120050f031b00c00000701d20340a05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 270563597 1250 270562347 270562351
    0x21c020111070f050f0307030605010801020403020a150207050f03010e0607121a0d032a03210221090127030809070303050304150204050d0303050a060501050c0c090c09090f 76
    0x4001503081d0345140d150310000600a058075014407040f0f922504002c20f1055042d200304a89a240c8609200040850040d100b014080c261140c005690740703045005001d801041c0da4410b5187d101189407003284c01d40d012030000d0540c1c2c000c403010461096104002030140c8210703a444005406510f0500070420341190400300c10b070409100c24428084c0103184a822013118440e120780240b01c20246400092003880741d066400c0c0f0154114003510000d100720701f09024807600881c0441c070a001b0318403c45004c1c806035106180555410361901c0518100800c45420403800d50641d84920804140e10800a40020ba020482010f00c88000b00394074140851100c07001c00154003045100010840c440000302c2d003042520380644446181d61910f07640c1ba40380000f03901c02d8100c215800c1c000480c85c1d54a070101324011340e000c1d580100e0581007502201c0100c9403543e02c12414030000f08128141ca0002042421a044c4116101f1240342d80700e405401152054104040d88001c1140400000c2d100701344400d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 270564847 1250 270563597 270563599
    0xa180507090801020702130b12161818060c030204150c02040b0603070f0c030c1403030406060f0617060f0402040315060501050711040b010c0b01090c080c0f070312020403021c02 78
    0x4404a55502d1074a00302d00c14854081e4125000c03003040351101119811034100c415000c1c050349031004009801a042043d0003000800c1141e10160400c441124584c141070000c800c041e0820400703000d8815000041941c0e076000344195240c070b0b20010003d0083d03055030000c10041c6081c1003d40c0000400500c0454030810492280e45408003800782800c22105031381c802c3c0c7c0c0c1c5845001c20224500401d581080042404034108095001001d0000f0399044003150400000344c020341d2282480d00c3c0c40801d0300ea081c3c20101000701c9500041120503404412004070b09000381503405691681004202c012038134010640e00103000040000401100c02203603081d205090808110f8030342c5a0f001114144034221015000e00074880e18004907103460790100b0700080d01414000b020408580d02c01038165003d0b0b1042c0d6806543d0107070900b02030b802c65000c0b035014890314002d901d8803105821103013050140c4000a410003d4108101048562650488016680003080c28040c4401500c411660307128180c000c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 270566097 1250 270564847 270564857
    0x228060e01110604020a050607150603030804050c12030307030e030d02040b04031407060905060c0a0203060c0307020d0c0b040b06011b0803010f050105070f021c021207050907020601061b020a180507 87
    0x46502d1903004036040b4003803a401800000c2c00351401041048036000740ca42a100f0010512000c50801011302c204001140301c0d460341000f80c81c081c10041d0130301900e416814000c084404032044140004421a940079140e400d001410b10042c00210b850b500541480320000c920010303012482d182040302520480c0d106050900303070728200c0340e00c0d0358076600710b4401c50010500221060004c3d103015006008441a1442201c0104089030002440c0c02001d5842900b001d000000f032000e003540c18881ca18941d9481c2c101100c0c1c0104590301c000704031100400c06048046644c02241551703119a55050902445589500c55480142007211060b8170a108902d4521740c1b2020000785940a041921032143d041300000324070080940a02011306152107250030300602b032401f2100140c2d2240c3d24502043c0e00c1c640100b089a082c0b0040c841130400142c80b01040d940000d00420800b03034810549100c62002062202400400b440482c0d085095904100400c1c104240003180b9503101c0d0f403000388918010390314 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 270567347 1250 270566097 270566117
    0x9050a140d0c0f0206070b070e0a05031b091f060f02070608060d0201110c04060b03150103090f0609020303040504050a020d1d0d05130806090303041a0709030228060e01 74
    0xd0380e600035055501c1c0424a50301d40300b404281e6020841c00c6641c00540801c2c90042141e07140700d038507030084a805000c600c2250b01c001603407d1511100000d0300c401c2d0003c100148966a04103204140c100420388200b501900048d01d4041340800c0105174401e86402030031081c2c076040040c01608404200c5001031041030000250a44590441c0d4010074020700f110b10400c0ba5030b0011038003245041003a888031710942d00003200c60788843c86210014140c0e02600d6450381441051454084200700c0102d040504046804020545c0078901382140ca50000740003d09e9640345c40030901794095a800349600620700b004001d10208107400901e00c80300034030410000f46600400038404040c803040c40500a41c0030b0f415549080d4000c100610980c030003194098041c941c0d54000d1850140200c0325030603289c002005000c10003030482c020050328101400520081d1801d0040103118802078480688138240382030005030600c1c89051032104074407504450009154550303070080c041729058040036001071a0101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 270568597 1250 270567347 270567383
    0x60a0510021e121603030e1f060b030402060f0304060e03030a1b08091c090512160b071a0403031503031d09010b1204230105011d0907031e050109050a 66
    0x1080c10340907152400b03540c100201c1603425003c130148003100b20b040c140c2d1406100c071513200c208603d001d00050040d000355a03c407a03000c4841a56815403000030b4000e4203106000c0140d450070151140081c010301d8858480c4e417035060000c041c000000070b2030f01500000091056a42003a0010390080d1101c59208001c0e2400c104100c2d80d0032002c41304c8101740d0300720345112a078920558040c520f08800c0b91800e0a03c2c50303261030000721402c00c0159022030580c482c40c040702b0100d00c2010164001c05500c6103050030541d080e15920743c100c0082684150041d09100010308150003580907441d1940302c03040354014203440c2e01e0060071030302c68214583c06031300c500720344110389142c14400581070358802e50300ca41c10325101120b40c03810f018002d8011940d07420070028040c002404030980c2c80c2e41c4110a000414294507156040c400b001c80c0c000100d40d600c0e94001040002c40c8000396440803254030a502c031000900141403140303010134100c0300800075400c1952886c00c0c418002503090745180100c5c1d403914010005030b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 270569847 1250 270568597 270568603
    0x30207120e01120b0a0b491e05040506010801051303020a0209060117040b0601080c0703081f05041d010f0207030903030e01030626120c03040e060a0510021e 69
    0x700d40d6030014010340f0782040b8001c03140e00b10b10b10b603403006040c001d0041d459201c0034109400c8080c05424aa103000c0c0b0242a404a10928100c65008402d01000d00011202801e48500b08041c0003200701e91913903580c40072455a000c1c0c01d011185100c000300102d0400c0d290050f1110820310480380b8079802d0601081018401d58003034079183ea0b05030010808a0103c0c2d003030080c0a440101001c0c1400b03038280410b02c001000c41f07000c03480b99114002e4036080303181c5440003404200c030140c802101ca460510991000a0308201c0c242d4000000c0070000d0300241c6000307100480070384c9507000b068000e800c10030102448400c603445540c40c800c09000034000f04146d00c43d80c4040b400f92202c040d00251010400300007181c010f44a420390b5100601d004038460751541c00c440341018810200d54044c403202824041e9a840a1012600f100da00284281c80c04118400d00e43d60703070249024058840d0710000c0807802d01e1b581c3c20300007001008094a1042004401c40c4060b4480000b0607a040c0307007121000310209456408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 270571097 1250 270569847 270569867
    0x3190f0f020607200708120c0d020a080711032803030609090209040212010921020c100807111501060503010f140310020d0902040e0c150f03160c0605040303020712 72
    0x31356500070442c02002104d0100c00d00c0c2c590040030a0054440c04985070f031041c130503c5403180ea040c0c01c0c42c0e950104101036518009100c1e0000d001c540081c2407400000d5580c0c0c0c21280c1c0d00e0f1304100760500003400c40700020709149400e011640d0240d44080c04001074810030109130b800a0081d1000c101840d924800141542d1a07184000d6200364280001001441c040c01425107610062000050109a0f0340c0c547d0810850360304541e503d806000320807682564100149040850281c9201e0740740815042c000c0c0080102400140038840060070002c1c05000412051b22814041c50f507140c019650780c1005032580e4402e0091010200c01c1c0b101c040717990411000c0308848030714054001c1c0701a202c00003000000b90004e51020003903a03151000c900141e0795900950200858090103003040042860401c601e140c588202004070540c1400070700c00005403081941d43c44241d400c4195074200c0c0300b000444214040b07810041007a071418080c0701c241941503000d0140c0e1840b405401c00121484181510304200c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 270572347 1250 270571097 270571111
    0xf0209030c04053106050c0c10050714120a0c021c0309021804060b122b0203130b030717010806070e0303090a03030e0a0e0c03070305040503190f0f0206 67
    0x10141400c0703154203095020070362000c04008216901040140514155507035200b00740a2540000c140d0f2080c09503a100b03513a0415003541c80c25140c540018100764855809144a1105507076840004401c24001c1c0c100702c9072010854a040e50b500e80384040c13295020340668019010030716080340300c08070900015051042c00d8050f400c40020400002044006e80051070701260080c05500e0044001c10005001c180181e20400021402c0203480d000d00c03149141029a9010b10307400321100b180898140181e000d00c1d6030901150100c10002c040059185100310814500310000c20880001c14031440c9000d94040c00c0c40760b8403035060600091362000712003001c0c06280544d4001002046505020702e80c40d1408040150540f424000f5110026030a50950760081e00031402d5000d1b08080d0f03240842c2050301600d980c244543d07040c20f0100080c0741c14000109500f042c91703552008141030101c204240d0725003001c400100507a0340b9010200a001c45194080301e00428101610180800d0010586da803190384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 270573597 1250 270572347 270572353
    0x326010b0f030603070b07031e0e0609040209060f0403032001020a09051210020a0207050f03011a010f02010609110a1e02031905040506040b0c07090903020a060903210608010f020903 80
    0x180801d00342029074009004250300d40f0650f54005865040e10303010b000300c00d00985950026030795007503c4600c4480600111010403109900c2408550b82d1002a01d085001c240c80050325901c50401007000d921a00d04081c581c1c50b80424000304040e404040d200c1e20b042c0301122043d640c1482e0111900f0307400790100d0080410103200051002d07040400000038904244012112a02c0310481104100d0707001c1d04c1650700581082100344010f0800c00344c07640380c0140079002080580c000300703408e241d00040c00074080d0400190f0b07024200054800d401c004040c0001040400a0b0409600040c4666100c44410303008160341a4001e00c5800d440500e40ca169202500554a07005852000c20310f016078900700751050003801e00c0046403607101c05000c0c00144c440805003070b0b03a620f0820041d62600c1210352101080300d080104200000b9800300e003040110780d2003040403900600c20b00e003c2c0c17841c600711a001c000c2c00340400c403503107010207040e04a20104c5c3e20101c0200060b08180c00c04070300303034810500e030150568 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 270574847 1250 270573597 270573607
    0x3111605191505090a0c0f0f2301050a0c06050c07031403090c13020f1602041d03091c0b070206190605060301030209070e030a0302010212010f0e1302030106050d0326010b 75
    0x42d0b1150411503000c8480016104403190f2a5030305020340c11710350000d8610154407881440b0040c0b03000d2066018200340c03075030b104060030707004900d881c5031400120b40ca04105002c599851028000c0d81c00703c64680c3e0103d0180850b02c2d01120b842c49a401000040e4002103c0950601d080300380d5074102c038000c1400c48050151503030307041d081c0a489000b64a000c0b00096080000d07085007940b00000e022030390109544401709110038010003043c0c42c0e1600010350131056003190f41d000800000f040740d40a4000742e4082000407105d000821000003a21400b50105107041e003003002d81503002c14094070910042100658000454546104590413070003000c1d00254108014405442d003260115401039951030704505150412000c030303080001c00d600440c0507070b401240e08121030007030380c40b41400341032004402600c071071078070202601030381c406005c00039403021416022040d51000c4d0030a102419003d09004003100140c50300030000b141a000941d4003141c0c207100c0384184026080040d040300c80e0400038174104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 270576097 1250 270574847 270574883
    0xb12040501050a1b11030f130f0f08030a030507090509040302032101120b1815010303091a07032303010f08010e0303011d180a06020d05060904050d03020a0311160519 73
    0x2910751700b45842c0203100911142114416080051100005842c861403030301b0314158040b410003c080d0468030504d810444140700c1c0c01000400d17911460614a000308054566241c15294450141c10454001287c18100000e054000008050700c00c4110300661103800b545c441001103050038003035120900300d414502c001003416600900d410048008a800340c03080706120451510303034580c0c032005103101560010010b00d41c11840d10340080c284080086060311840a21042e01d03ca034540007000c0c0a6803c603010302440741c1660404038a50180f58055032940c481c042e880e550700341e500c203512143d030921502c03501589020013900d048440c4508202542101c8103040180d030f1b01c0040011951668017040f1031140d400c00c0100002c9680517003c0169191444e10400040c1c40c40105500d0064801c071042c48001500018200030728149440c1c0144c0741d440c0b0742c40440141c80c5c0d880d1101c1846030042102c040303070000d00691a030b4140c40755046400c808000b02544403060780303d900c0a0300c80420089a0917070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 270577347 1250 270576097 270576107
    0x61e0603060105070c09020a090e1303080609090a050106091e1a2101020a0302031005031f0c020f03072a0303050708070201030204090203041b060e06030408130b12040501050a1b 78
    0x266100310f41d1074807026101c0b81c40d103049800c0301c230031a000200c0401c000c201d40181c40c1b64040e0419186001c0c0c0d00281100c4c0c5002e005d124015118600940e4502e00141045005201080b40d0580c42002401a40d582e04d44070b40191034039443c50708004100034201c500d410003600c80d50721802601090140030161a104000786854428260b081d144110b140012102c070b420b02c020452505542c8006803a80ac0c043c03402590b00701280c01550090340712000f4031000c030810a90020003056512004500002c42c014124202030f42c00803900300c3c9120100301c2c4c8003000b21980c8044a100c0daa0120b03500d00c0c0c0da04001603540c82c1060711025000c12010841c2d43c02003050340000b005410300604000d0715107a40c5980c41c00480c3d00c21182030b42e400e2183e941315049005030781090360003000e030b81c0341000e1140e08060004d1418400544010181303100040d501000101c85040b0000a0985180c10345c2c651080c03420200032500704503811516946040c000800101440c80b0b820a801e40030120400c64071240541030715 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 270578597 1250 270577347 270577357
    0x1707020f0901060c170f09150d0c202b02071511120306010212030a09020d03021b0109032120070f14060304030c0314030c03061e0603060105 62
    0x2030400160000d01005480d000315060090010781d0783c9469003041800d25a003003c1d28942c0746100c0000c20061101c5162860741550000c602c01c840501036484070a014200038401c3c1c0da800480581014421004a60450b40d0141410a10380040c0d603413220260b01e10f51500800784055041412404040000c0c0d040c1503210381d481556401200d000e10340321100c1c89006070280f1070711030004d1090403041803810010302051f014084030604190a43c184a00080d4603003203040070400594030084001850214260003025090390041e01c1806103600906000791240c440c0303140c0090140103106854059407068804c0c8088941101c808000030301e44440003075582d034020104204118100c100e080c00d140c40001c50008824080004100d06807030010440c002105c0d07540818007003403401c20104619190041240d41c8998949460b1b4501079241c90700351440a020001030ba403081c408010044036180305002180200d4085404215921000000300c2c8410b03500f0514540001c0c1c14000708002d5409040901 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 270579847 1250 270578597 270578599
    0x1509031905070c0305010f0f0b010327020303040509040303290d06050a15080106090b010e09180307120c0b010b0903120c0106030f060207031b08040b091201021204020108090a170702 80
    0x60f4105603203407143c1d030943d50611001c1310f031565104880d00b001e08440c8070342c50f13500d4400e0809001844d030000f43c001c41207644890510002e44858215011550240201c2c0d0242100401184050a09003001002842c00240c07d400c602c812118008080017040c02034200c1c074000a0407000d0314005981c40d18050700703000d05101c41c4942c0303980c200c0c03001190354080380000c3c0900400001c1c0032807500105005440c0b0303c00d000380c144400c44400480c540c881c075442907440300e036100d0081c60018900c1912440c51040c800060f025280e80c445074504203512980c6e080503540600c14454490341c85814110031445608403080d81580b040d0b1040c02040c0348900501038400703c2d1000014410342c4c0f038a0f00d2180300e6046108440d50b6500007903010815400800441c40700c40d0004080491509559401c1a00d11a030302406103045404540c000032556148003444103402104025500e0307980d1101000701c0c1e024150f074100d0100360a040020b00700c00700099600f0b4404c1c0c00a0400b84c44c910501d0400015910440051f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 270581097 1250 270579847 270579863
    0xb0702130c020f1b010801050423150a0b04060f0e010e06120405060a05090a261902070b03152101060f150e01050a050a12050108150903190507 63
    0x100c40000818411031018a903035401a00312004504000c0c1c4c240188005186a1081c20028035041a60703c506041e054406c180d4001030218031800c5160031340e90185038803030041a8904204005242507201d200481e020076641140043d07226044010540100d00452000419154141c114a84154044016284103052a480c1d202405012074901d034070114550400411640a20003002010030400da80810003410030001c80c20f00040d050b417105140c14018210442c10030074403440301c2d0034514040d0681c040c0e0603101d54a820440c0205ca94506c2d152921000d401401c000080081100040320b11542048030b407440303000500fa0400807810000320043c103048441c0e45420302c80c2e41b0248209e40160500d1600e01c01c1d41890441000008081c4d000041d080107a9080e4100c441e03600b0105556610829007403443d11405450000c880d013420004981d01201d0504000003001c0d640030030041c1808412401e10403046d81c40e500e1003981d038400d48081c845581d00381d4008070030091061000d040394130300c50214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 270582347 1250 270581097 270581119
    0xb0711040e010c020c090112030f1d1e13062105010912020303010807081212070507021e0102100e030403020f031f0501061e0206060103050c0c01141008060906010b0702 74
    0x71403400c4800c5100600050ba0081144c1c800b949400e1400900510000140c0f0f41890761b10303600204500c4540085009000030350305682c1e10042c4100796204110400341030150b40c40e01d201c00d4280744201c00300407180140c50850780040c451800c0d002d003000303942e04503061502c000c0b0343d000c2c4110f0b19900040162450b568416405001403e08100300044414a9009549a50402090604100042d4040e80313403588184103182075881a00d01342d031100c00c1c545401074130350baa403d882a140da2190100080d841084203070340200071400c2c90380d508181d10003a401c5800d40c010003800181282c00c50011300c00a903006100800041c9013111305401071050103415104c4000b1150400250900124205c0d880540c503030340107012040e031000f241351a03100c500d140880b00030900c5a02a464180190005040544130390009580c141000102e44d421401c0710000c000304041c21079801c92420040d2900303243c0503641c0000003680d100018029005568080140003164039100d10b00d4069070003444226040080904 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 270583597 1250 270582347 270582371
    0x50a080a0305070f080601180f0308031b0304050a0303020702040b060a030c0e01020115090e010b060c01020d050c0f0703030e1c0207140f03070b030403141206040b0405091e0325030f0305010b071104 87
    0x4001001944655802c336140e007000d461540c5100000c0d25002c031075100a2041001103140060082c40740741e090704005075514800d001181c050a24980c419402c80000290b01600700e80c180d11121500303e103546d40c0c60f40100c1040c012400d0703c60ba6850680302c29201c500a104150b0503901189181c0303500c1000103030480052000c0b900903003000501c00d0851351b01003000c40340c0c500c290150650101d034043c04a40360509150805190f409840c2000d0100355840c040304114217800c2020600b0019000380c1640c41078481003009646028078010550010030040000307045062480b02d4098801e0000c0242601c10f00784000ca03100c6801c000c0080e000c01c840c1040714904c10740e429001f080440030068251034640790050520084c0c40c0e100406c1c074007491502003084803640c0d000c00c002409003504d0034071002c81654030324168514014001e00910100c01c8030000070810324501400302e41030388641c03603844207808800400d8040f98000d00c2405800d100801024001600722680f0500c040002000002c925031048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 270584847 1250 270583597 270583619
    0x10e06010b12060a0609030f0c170a020a051002030403080a050415050a03050f04080f07021305090105040c06020d0206160507060501091a1e061303050a080a0305070f08060118 77
    0x2a0000c040382400255882c20070240141e201e0b8814015100c4200181c90408000c103550703090701c4081d0043c071848880b0341c100801c0e0403191000b0490006007401c0e6003e0007105540303c00140b0412841084001d000080351308000050140311403403034016508040c0303140c4035503c0c07070f0740084c81080c2000020800480c0d10060001c070480c026603980c2e9100d03241c41c000c3c00003504491020300031401032842001007000058650f03080741c481b60840c41d50251111580d201044001c251354100010460909082140c0d035401540850702c04d03805040048451640c400f001da1700c480d080d84070500182c000c0400111130607a1020046c940740c00b80d28003245400d010303441c0c0e001125000e8001a40e0036441c2c21504070001e04542d104c1c458988100c50440c0f071595822081c440400d05a400d845c0144404103444918850b48821000115000f005940201007189040203080e40800d05d00404a803804010840c42840b6849611007250140c40307400050b02c450300190703900030b2001c005d451140d01001c1c010604007200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 270586097 1250 270584847 270584849
    0x30506060d27060f0e06061f0210110c0d05070c120314130602071d041506030203030d061a0c0604112403041e0203070b0d090218090705011b060e010e0601 68
    0x1000c000a14444620900307051721394910f2090345642c03005040c40250790b1120f07400414254100102c00102030500c03801c0e0f0400c2100c0c2a080c00e068548110baa458414203001062119184021380d03019450a060594041c0980a4040c1942c0140a400c0c002c0c0034080014402050082c14842010b24000402c020107601a03038035070340ea04151201c02c0000035010030140000d03200c1050080c040190956004a4400780148090949100d402c0d0a41c030850107072307004001460300078069035650340240c0318100c0544030741d2045d040409202108a0350f5802da0380c0a41d485002ca5401a000540799900c9108403a6124038885030f00000c608411f403840d010344000e6000d03000e000c154140e00d91809041c100c4211980c4041d50890040036480c400041c0d80100e090310540350708108041e110180c40b00004001d15503420001d4009180e41001c9007102900500c1c20710401d2590200c60150342c5481c01195840c2c8021a1021603403101da90600029009030030100069003032500004003403202d0b06040303241402c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 270587347 1250 270586097 270586103
    0x90d031206060206090d031e09052a0907030e0c0310090b1f120303060b0307050909100305030a0507030c020a0f0e07031401060e03010b030d09080c01030506060d27 72
    0x6440841500c0c80264001c5800800703040c0094000b81c5840400a80c0703801922884c0c0081507900d5841c1d201c1980401200c03000da1906000800aa0781c0500d4095a9645100c12844203801d4070b07482d02e01c52008000c008113218001030000242070300c80505c140c0c007402c000e0700d2007229405a10000c2c5502e071810040000c1101c0c120038049903400550402c0c94031104080c2070400325603084001c6071003982c4d0700081d0b50103e80421a001080340b40c070b4201180201055004403442c1c00c4004140030400782e002d0080d01c0c0c000000c542d480100d89559000c0c440a0081d440000c025030410300c8000c00307480c000c202406685010703003080c00070041d8075030000f1a0750200b84c01c05400714070f0203032050083c0041451030941c00b88281c11700b00000030180a211742900e0303051007030800b04030029a045055880179088100c0c455805022188055074400010b40051a18001c42003280300d04a55840300b90310a005082c061140070303040e079180550700345480024024030030002007080c1d15050020300d103400110481c50a40c0c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 270588597 1250 270587347 270587357
    0x5070f0b0c031b0702210708030403050706111507080703020c01090c03052404020d0204020f1801120209010e0f03070e04080304020901090c17041401020705030c0f03031911090d03 79
    0x1800b083c031942207040b001d280750342d560400d2180340c006885207844c5105600c00c10364040204a1807071505441d00e20642c101e82c105020102c0c000080290014070170065403043d45031400030028103040c10f9034840f07031060203041441c1e015001c41c2150b4040c1e503c45402c0140d80c68007620b4841106566801e54280c01c4040700c9981c0100820070038042e0030b2110400071300c0c04011050640b03500c894100d071144e03005000a4030a030b100d003c40c81c08554a0f0303812101200481c0c40d0164032202011100d0039800b00a4100902044021500c1c07401c00407144200d44140105031140700c00d03185680e06104900342400e1140f13030144540c003c041411113840050610651151036a0b641e079180c54411700c000c0d0320041c0c1c02104041c0c20b02601e0105650011403014010f0b110108803500c0fa83c803401e0014032400014100ca2940d4800604403003031010103c01061320f030030f0320300c1252043c038425071740300303582c0d101c100e40381143d81c0d030302c20020070303000310701e0f4011000c540b0303942510604180910002411581c0d0148040700451 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 270589847 1250 270588597 270588601
    0x50a0e01030b01171e010b0d060b0a0b0423040b090c2502011704050109120c061a01050403021002030403080a03060801150315020c19081c02040303090605070f0b0c03 73
    0x12281640d40d50140c2100407804d0000f400300c1000640d9283c1c918040c80340421607040440340c4420075404902e0206008159011414080c14000020700840510f90301510086a0102c1c01c600114100c41c21100181e80b910340744d8640b211070f281c04502d06c004180d407090301c50703089140d6641d0b08101c1501a00403140029906d5040322400c514699000480300703e103950740031805016070380044124050700d82a00d030001e05075840b0302d0f00c1c40c010b09010700018281d4000100202d001039000340a240d40354400c05080140700c0d030880c0d280d0454099408250700040013004203100508203105810082c801d103004403411b00351690b171a203660303030072202c2200c0000381e584004220500c1d00f400350210450030f903110f541c401c5003151a21400c0034041140c15240d1500045c03101071104040101e60480240d9001c000d0f280c0d545440c01417503940c80000e060950701c002c1020040320792100d10072641169455110600e07421f2800c101030300e0542107598243c60501440302c15101294007142d00c2c40c0700c0d41260071180e96078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 270591097 1250 270589847 270589853
    0xc07030c0f141507061d1c030b0d170705010e010c030605040b2d040f050702280b0414010c03140a230a1e0c0e09070f18050a0e0103 58
    0x100403640c03006102c0b0842d00b100489903140d46406005940d0032800155582c24a814500058804140b08000c452910702103038000d908042250b08407881203a040d9030f0641e510040840c25641c80c0700380268003407c0040a04e00058030103001401009045683c181804080d803505c0b030850f0900b841040441e51680c60a040c800c0d031602c50a005030100b02c808200c40d9901202103009c0c080c108100b10409441034200f6107941309002c141c01d010020040c41070000605800c51000a0681903070000098450200341e22100b8890507003006502c0084540c1d84901403e585a851420700040c10940c1c01c940f4a041d0b52007290000c0c004d1026030081518040740d1401e8010b04000802d20092118211624041805031404e2180c507442c400310800110031401c030340f0f4031078544000f4612880403950003040c5551380e62200180342c104412805d11307a10f54000f105800014081d00640c12124000003604c40040310490758000d16040f6403014801d5002101c03e9220000f0515036441600048041b00080c0010410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 270592347 1250 270591097 270591119
    0xe091305060c03041a040804051005130801020415030209010507061113060e030c0105070203030903062406040302150d09020907092105070b03040609240b03060411150c07030c 77
    0x294141c000503c0c501c2c15860303919042c081c0011141c108030f071490115080c03200c1c3c07509840113884c0c0140b8402c103d100810000d02964003c2c2c1030810804200ca1000940c42018402c1d1800c5840d40c145071205400301c820218000e601884610b418401c050000c80c0c00310396144142c00d0032001000341d9656504c180450703810294039030341c050000c00030046c12083d803d84021031382099030b840030b0810b56205d08440c40000e0440c016213a10035050320460080040300d0b00800d0390103282000400006244603429810b2004034030560001940010007440c1c1d0000d0700d081040244584001201c002481e4500d07980043e180e00b805980751400503400050038004429407a400c83d54098540c1448065101c040e92002e4450075075214680701c844001c80010180700007608510103481c0c2c0840c000c0145500c811108610355806003041441515040920345241400690f1501458100e0804118003c05004000d031010302d400341ca1130810000e029044032040708100f000091449010000342c0c16081c0901e80038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 270593597 1250 270592347 270592351
    0x5101103031518012d03120f120e071404140408130509060d120207120303140903070b04080d0e1002040503010b030607050315060c030a0306090609140112030e09130506 74
    0xf80150120004201d1008403ca00040d42e490a80010030045d405035140030030002d070303640040c0034a500545001d52107036101c0480b0b0300545060b103c101100140450140845540203030b0b114980e480032206004803000f20002d05607109004001080d4904242884120300e6800c0c0e8084034490000302d010503090200045900184c50b040d1107080152802400244ea404074814000e080300e201c040044161610034031121020344000c17420b000e59160b56240060081121055a212450074803020944490012017110211608914811450346440c0c0760480035034401c0d0300044460341d03136a000103500c035010b00102000d0100c00c03800584681c904400d02d800e540032821424441d4200c130041058190b041010b0f00c2d040a0300c00100c0e1142541840030550340c0c03180c3c2070442100d20000c10b52810165064110f0400d4880400003849071994400704101960001c0741e0292400700c0110050140c035110101e8521018024549401c0100e480d002182c05c046095a000388144141d540100610404008aa03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 270594847 1250 270593597 270593629
    0x30c020103230a0c0e1903150b010f03150f03110405180607080604180b1506090a140409060e071a2502010c080c030c0f0f07051011030315 61
    0x42c11030107a07030310b01000307140005080c8140c099541803542102803203031941600044010b403101000781c0c01150401e040070b00724030048800c259828402042640680207a100c02c0388181c403440310300c0e50805419409016602c20b010015a90001d00140443c9002010360085000340030111004048034107100950ba80240026080828225403c00001c400070f68258070420700c0c035101d80039496032000500505103040f411000c01b14140100380c240203040d50300d42e00460b0304810800d0814004020301205005400f040da40c0f20f901e440c010041e07680c3c1c010081e8120b11000f003001543d244a940c6800440344a519036525a6000c00c4007070280d036140f400d0b0845e803240f424501c02c1c20f080c052003090000d85040310480c140250b81c0c080b00e00440e40035884140000e039008003219110000464029903907008182d00c07030040d218181006010b403c000c5913140c851202e0301c01422105051030103100c90810450591003c0104242001101400600107540504c2440030031450443c1c00070100692000002042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 270596097 1250 270594847 270594881
    0x605030f060106020a0b100504090803090c010f122408010212090106050d060f09060c05090f01090e1b0c0106031a01051c1e0503031005090c12191107030c020103 71
    0x610103d90001754081815900c842c4c850503d6986001890381d003110b6a0200e900305091007401c10401041101540c07140050350111110441e5440045480441070402040420a0b960f04680c84c1041908880388200344a2000403480c02c8062200040303224036070024003665408104008403088030fa00c0a0f80040c0d800001303214860801c00022102c21056038003c0820b540c41000300501c85a41d0000d104141d04007d080180c4075400c40060501e40c4000001c900c00da0082540c4000ca6000302c10385070684081180b9084541e464140112100c0401c20001e1101e5005028404590b9424000d081c01f55200e08031100400020300c580001841c81a00014403d50314804441026490f03400090709490b0003801e06a038000c001c661030a20350168480152040c00004100700316000d00c607008104441302600d0100b41642d400603010040e005007140282050303040c1d40450f400c0c0c00c204510100d43c0351580e000098500600b9036041459000c50802c8012965040d0b44070195a00740c03045000801c500c40b07034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 270597347 1250 270596097 270596099
    0x10612050d140f0f07150507090f17120307090f090f0513020d0204110d060e090c0306040503041202011202030f1f180f0f0c080415360c06030605030f0601 68
    0xc683c0d00350090034800d0302c50440c00b0614030144000150200382210280390704000d1400c00d2500102202c645000d603030791890499070001440b00c1440c00c0c1e0b406840043d0050500a0001e0195840581c0050045010025480004900e103501042c6080040074030210004141c000071821205840340103054070480552940d4040268503500389841c0070703075412038000505c0100710b03404514034000d40d0000c0030214a0700d000411031a2609403402d00401080e01140c0802c0d14500c101650390204440040c4260810304c800c02c10150b40d00985249180705040207052018807030b007039804a0700100c07503444644105405010303451041b542090000b9241c110141f958a08050507540841540e903020b001c0300c1c0d980d00761120741810542c42540d055220b028240070207106114000c0c80010107031000d4402420f54010300b504c0d90403d1062003030f004c9642c000c011800000c0003403007000c446000311a21540c44141c45e00c000207804410020050202510300040c0b00781030070240343c0f030400d6034030010900758031103c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 270598597 1250 270597347 270597367
    0x50c0f0307120510120201050a03150b0912010908090616080d0203180c0109061223070f110d05030a020d0504061b08010e0a09020607140607030b100f0f02010612050d14 74
    0x40c80d400d05c0b5030203003817482c2c1d03c5100c01001c900a00340e80d81040d00240c00141c0210304492000010305803003400700c40700343d074550040b0422400c031400441e00030b140c1740342003010050700e003400700c0581886100014011a0303420262204045030f40518804005950b00000308101700100c102c030700d003440b00301000130000b0100031800a000c071040d0380074203814090101c10021449a654000b106421000600c0d49011a20348000c5088240181c0708080032914a030580c07804a48039041e40c241095545004114000d4450001e0307070700380d00107090340b0000c640800c0641d01c0814036000d0203000310f101d10070000c0c90304111903005101e07000003c83c9800304a1044010803101e480080c0541c1c2001d000c44000802c4d810030b100080703040c424210020406402091811107a01011802900c2a900b03a2014410451080100b00311503079107520a40101d801c030344064100318401c9161005546071400001001a05c403044140c00b0142c100c0c044030300d0342c440b00002d16025400304180020010340e000103824140c0c40c413 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 270599847 1250 270598597 270598619
    0x20301051201090201080c1b0a150b0114090103020f0409090b04020f0f3a05010b030c010c030c03031d0109050c1306031a13080301090902151606050c0f0307120510 72
    0x75060703402c00d0801003a0480e01d801c001340381d0b45030f030140034045410100091a01b00084080500d12000072130bd481e6035a41c45500550244420210021016142840e40030040d8001d401580c049185030200f80004258454240b0900c03204901400e809115483c2a02c100980f07250007074029401218010180c3c3c00c2601c0b02c8036140318407460350750340101c219034049000030b43c4542194101aa014680400c2091080648c0803090100301601920728070841c2d8001034a80c244654001000a102d1000030b00c0131a110390311051502c1c030030410164200391003400c03690a481401d802602d0a4001420307a980307a14100781c01300c8100d00b000606011440c0707980c84040040c584a08101000b00003140051a440c0c0e4140401c000240e015032a1616940c5a1146c03e00030f18903404102d000d1200011918070070040a42a144489407281403407420000c1542c0d414040c00020300b070040c0101050110690400b007403000b4602c2440669a09803402d1031046801059810140030356900307001d0183c0c140100030260b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 270601097 1250 270599847 270599851
    0x1517070201020901210209042a0509090106080709080124090b0306010e1e010f0509090105040503030a0b03010e01020406030209011704020f01030903050c0604080309070e0f011a12040602030105120109020108 91
    0x145e001c00b05d110b491800003010f8801c071124203901c0b600c1c20743d0130147d48900390320340d01c054014030340c0d400c24020301c0031000c1e00c0310b11440303507015070102201380100101c500c2015140da01c84100d24000500b2a9140312090030f40314403059600741080702110940340c92003405110700c010150a04140103050a96000ca9180c22040c00f80c0445541a4030010b07003940d60b5080c0560211085040910f8035603036502489034a400b06001c0d070341c861030b0710102103100c0400500030140200d0300038010314610345510740381c1c80003010a001a40c1e00741d503c0e4100c041d4117607003e101802c01014907480142c0d0b0345500034001002d8140b1500ca403034003049010103000144c1c9a0811440007584282000034006529050a5800e4019400c2030112071150400304003c00082c500954021005582102c50694484003000d4000c40c0440e540007413075510b0720042110700c0b41040c0c200032544840030303030034a02a007640210040c81401c85050302c0040d000801003215040015180141900000003000681240d0307000070f10f28040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 270602347 1250 270601097 270601127
    0x3010f03030c0507030c0b1e0304020a05010e0d06090b0f0603190b040809090a1b052b1b0503041a061c060e0f0c040b040c0504090c0203041517070201020901 69
    0x5802c003040104002000154080c6800c02e40c6032540c0350307503074211200c10361044000c44156044d40b15855026002d050a81e801603500401c40343c40719081c007004595900c0b42900303860f4440d040340031441c0403504910a1122070741c0118486060303460081c00b50f809510010b04200d000e54807007002c03a00d0502c2801240507610f54400c042d00b0094849003030810450141ca0800355128100d070701802640c146540c09403400680034054520600e00022090302c0c140100783c0c1c03c1e0b50000d8090f9801c203c1c122040260b00681a41c1c10740000e00445212188044041c1e0b0b12414001c0750001043c0418090900000b40102c072000b03d84000790b14006003c508015802845844204102e481c01e0040051980000104000003012901c10301c00c503014869607209846841400b4a01e0901c4c0011141414003500c59a1070258075100d02c0c15252200c00030007412440703c040f0841c002030101003005050304040c1001c43d6201d40e503600c45c0310201d100c110345000c00a000d42c415a81304201d10b8582d640c101c81a401d203414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 270603597 1250 270602347 270602357
    0x306040b011a1308030306030c041e05040807120f02070801050705090f12100c0e0a0b0f0708070c030b04051006080c06160c060306170601050112240b0316030203010f0303 75
    0x282c814280c280741c000c2c86000204485121000303d2030710b5000002d035120701011401c4460100c80001030100301c500400c40003060200000844408e444035401c9240c100d44940c49607450048a03417904000043c1c03034508000050401280f0035012a41041100c01400b503e20007000107003400030340074105100f006440d40c06124044100c104d00e070340f01c0001c0103035070400c88241c6800806500c6004000c0c0304050080c070100d45039003040050350a00c020322030142e81c0c02c0400e5600d4010341080d5819550001c10044840c4081041610b000621001e00c0038021031107580410407034205494074501300344001d20b800d40d5052900a0421882600080503d1414810364501da6a0540481032074455181c100c4080c026007603032200028210352643c8603d0032650078000110a5911042c12103071209020b12482d8005440c82c03000c20130302101a0701403100c6070815440c00105200c0300545252700003080d8060000c0420100800891292800711341d80c00c56041c0c5001c51856044c4400009162805d003c0942000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 270604847 1250 270603597 270603629
    0x50f0c07050907021f24240c02030304090b061b030d0e1b06130833070903030302090f031f0608010c0504030b04030504052d040c1b0c090c020c040b0306040b01 70
    0x1641b500b04161803180301400080050b21030203048100340d600d03c01a1500d40603503c3d2403d010340300f01000140168000e02440c5040c2c500710303068001d0850300500c0c42e4000001c021003c807448010b0340e840c1c4013100c82d101860316460001410802c641000f141081076400c00512440c0360b01e8540000f81942008403100d6032a04008e5800320340c1c004183d0003050841c8a1041c8682100b0300400d54261070418214600507041145100c20469000c182c80d504049102c444050002078000c2c3c0107000e10701409030505070008440f0002a140c580282032898a00c2e01c10964940304044502402000d015101c00a100710081088003c100e0310540c8070150124007454007090406101c0c60403503004210042250480760020906560051f020604040c840d400010407541a410140108071110b051912800b80320106400c000c00d070280042400c03503072000d03040342c04038041030940300b0344001d40e00030783c000c00b803401c44201448100c600d40044180300360b100208000004e11a00c0100d415990610000003a807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 270606097 1250 270604847 270604871
    0x1203120213030b1605210603010b06040312080f01140d0606030f2103060f030206070314131a030f06060c0106031707050d030608100c050f0c07050907021f 68
    0x3405002000209901c010000000b44140c0c100294000c06501ca80c0d4908841081c005403030b039104024031364513440600c002102074010320311030340380e8040400380010801d80141000114254450340044407864211845040340382d510006140d401000c8610481981d41444090108c407201c0d132500c2842810420a101d040007495009800103592203c600548440320b460b15098070b1804031910002d0600500c00070401510078011b41c2c04464036888021420790450702032104640c001103043d410300004600d031180300c200d0a4020300f81e0b50250702c0300b03001e1141450402c0000b82c2188140c980450301c14400e001c00500458455a0480c8040300c0082e941c02500101c02c0c0500600d91020f014881051840100401400f00800b09203110b0005c0d0344510189813015811a540380c01107102590100d0700030051940c02c0d500c04100c00c00312741000b50500312008000551035028402003a5580c00c450020401400c1010320f40f0303000401030001d0300b40034101041d00840112030344513000d026610381d2102618 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 270607347 1250 270606097 270606101
    0xf140d090c080102160b0c0711010f0c0506070509010e06030f0f090f0d03020a030507020105091518010608011b170a1107080a0306030b070507030818120a0305010509010f120312 78
    0x74031001c8000e54031104017825220b00700740038440540b411000324001174000042c020840340d0b4035501818489408490800444030703001c9150514007804030b40c50010000ca101001281e00c14000d560b207030f80e03548000d03000040485510340300b401c1c010704091091007c200c00c5a01c0160f4070070340000c1030040302c3d0741d01e80d0b055103003458416000386940a00e00700030001e164960004c0c108401c83e41c8090190703480d0f940080713003210021a0100d203030360802c04664280d03c1342c0c09003150f04400a013a00240204188402d203084510035030017104181c0d0348910b00c0c0c802880c100b8644492600504059501540603c20500c6c6000000d250f2001291346548503001c0c05004802e40d40d8151f00a1401d50325440740031000f5009010a010665040071030038001448070b881602100c2c8a02d6040e82d400a43d9203d945407800030490102d402a5207024815440c2c03142501038000c0c01505069540100355949031605001010038182c0180c01c2d1a00305c00c0d81072254006403101002041d40c5443d01600c0d81d042d04d610580 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 270608597 1250 270607347 270607349
    0xc060f2f030f07060204050901050a0e060d020307090c0203030f18071a0f0a080406060905091f060b0309030a0801090b010504170a0b01080a0209010504020a0e010815090709060f140d090c 82
    0x740280800d100041c00b03041d07170150040d56025201880641d80302c0080183c0c0d08424400d40441a030914000341003800c0c800030090707110f8400380840b92099100d00f6a941510744414442c00141d002004101a50b8059960380b80c1080c2c40381401410500f03810042c0d502c2d0b017120b0040c22080082800030005d00e4003401c00300c40d0401c0d40030b90000e4550701c00e10001400d100080e5015620b190901c440400c14543d513100c0c1da03001d241590010140f00000d400840320a01501c0c591741c044a40e00c070400612883e28000840c402d03074080e0051036603005a27000c0500141e4040c0c01c0000418540222a90144d0f0000101d03429510740000a030f0381c0400c1020480c0c6046440c520080c02d04101400000314101c0c00100309034482d00c01c6503062160781c2c8613030610040f030141000c804005040c02030082901d501411200e03400511a0040c0d81d15441e08002081d180b40c410b4664100003804000b00300f200a52100c1001c1101c04c142ca4200c00c407001605405030180107012a0b0704815603a000060204031081d45032074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 270609847 1250 270608597 270608617
    0x13030506070801031101170105130b0a03030302071203060b0d0f0e010c021c0503060d020904020307170c09060f03120d020706060f06180807060f0c020603040c060f2f03 74
    0x40c40c40d00d02414001c00c1c5003001e1100700c5a100c40c13030400702001d40c01451103015140c829000000560f1a00040240d007195051442c200c0e540c1e100c442e464140c5400b04506d01860180d140941d0b0760440d494007111389090f41520504247c9003140c144582050784080702d0b1112011840826a200c800a40d00f00610903408000302c02d40c42c1054140300c0c00c1d0081240681c0c0c542e011101b02e003c202116003a5001c0c4000c8815581c001c00c0740040394018907012041e150898009411600403685440c07000e8080720120304881103541c403200e20101c0500e0b02c0c681482e4844001d44007821104001c0340413983d100c280d880c02c1d03d805040410403522500680c0c2c1552070302e68000c43c0501c540350340d0341081452aa8a03028040019021100030f9444880c00c0d04c0c031400310b0b11004c0081c481245800402c45600e41001002c508000d103d682030030160342c1e502c2c0170f580542d000c0d0054224441c50004090300c04803007001131000b805102e01500b079440302d140b0039068000194194190301d0b9444006458190320400c0c0130b403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 270611097 1250 270609847 270609853
    0x303020903192604091a0a030303090605070912020d060b0a090515040504030c030c03050714010e070503010e030a080c040302030607120b010203070206040b130504180203011b0c020105130305 84
    0x451a01d522003000b0b000c400c0c0c025030166000116040e020300c0031081480280360180410041080303410310650010b2403400c4500450650005040009003140c041d551003600002d84490001041c0400d130300c1581c0e00300c001c80c180755003903074030b00f20b031001a170354450364003a1003011104410814880507401801c98054000e1102030380e141c5590409005000c26034038081c40008aa9000380b5600300344c8225802560182c8a103000706215550481c4c4e00000d900d004c03000c03c581070114400284009450002003510301c0c0000c942004200c12152410031658400b41c0319a04240d4440c0c502840441158800d40c0b0a00d490506561840d01e115450712440e40300079011300c10a820005000c0e0f01c00c0308401d5104500038203021602e5a40012662070041c06e4029503c800104001c20060090600130555080c1403a04031590320340c1c07100040c046070704108034202850404a54641145000e1095154a070420780d2080c085800084004091090f52030009061000018035640c0c068540038080e00107650040c21 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 270612347 1250 270611097 270611113
    0x1707090606020f061b07080703180906060305070c080313050f0f072103050d0b0d020d0311010b0402071a04030212040602070e06060c0607030b0d021c0c0b0a1b0303020903 75
    0x2000f0f6a81d04502d01019550040300c0100321340e6a444081680719140b60b2144600b800119165505181d00100007207003404108070200c034045d03080c044940c0c0140810354001400c2890100090181d82e8002c2c00e81c070030040600410b0000602d84415a41c1045000716501040c040e140381491034005d240041c03212612030244000300941c8005021801e561442506030002c0c3c2d0088008007040b01c0a01c0000c3c0881d50074010580700406540c400307031300e440d40100010f25103c1503801244014000d5401600015940101c0d5032011000340105410f919007134400714504801c5490308000103c0c00390000c02d071b060041c00403405041c800c0010b4a080f01c5949191940e40780e641c1d00203075540081e40700d0703250000c039810b00081091900809641c144c3d843c00028000981da0342c14101c004000c5500096030000c01100090050b80f0345030940f11303030316400f0040725a901000781841201d04801d0352200c642c0300c8003000850b80302d903030041b500000340c80d80c1000c0720039034880c0c0c3c035003a00a0701030b0f90115a018402c2d010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 270613597 1250 270612347 270612359
    0x30f02040b120411030f06071b0f050d092306030402190806150405040b15061b0303010801060906271103250201020a1b0f06051009060503060106080117070906 70
    0x6071801107108030b18103459802d80409140d16518400215071b01a0170a00009807084e0152101105090030140c00901d0214542d1b9420b14040394850180c07800d502c950901090355401c10540d501601d601c040650300b014500e400e04008942510106008030008070200b001c6481e1039000111178040c0e40c0c900142940c4801100e5990f5001325522140e0f903840c003105032014101031081c14090350700400591060f44d40d031107008404051580784e55030416000c00c06c18442298a202062101c1140030166550b9450f0448032404c5d606141c01034000300d480c0032010030014203621140d152007552100342c50680c4408080c0400207118400a002040700d002080107002c145070035081075501081c2d0040c001c0225000002c80c01c0703015001c094000b050040d003100b13500c103820040708800640700b4807000302c00c0303410b50380c800c800c0e100140c651145513590b690003880801103034040c032400381000750000d00c1d40350b26062009051030410700c15100191012082425408030034420039014051405051000d150380c1d40b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 270614847 1250 270613597 270613627
    0xe060403060905030909011e120b0402270c09040b0f030d12020f04060e030607110d140d0e0703150504030e0915180106030f0e030a030b06130f1a0903060106030f02040b 74
    0xf41c8c000303012140c452004500170a0102d880762a0310f8002101440d45e0352654288080c03a070355640403040506120601c00001c0c481540000e114964004100e91121504c46c1400180e81c180658640301c1c00300c540e003e4003551800103202803000490703e406030013000c01480d2480244501032428851640000b00841c0a642001d1511070b543c1054007142c1142d40c8680044954070348035203050b0032607002205041040d500c0743c511045c1c00c6405848407460f21060590b4181201c1280e00313850082c3d00f0281c1c0802c107000101d2078050180403481c80a02180ca0030f5580103081244050925228050000c0410160010205184440036028140100c1c55003860740380810b40d03101741301d004002420040c404d00103811038003513041c5c03145000c1d00079800d2184c0c00364141c001d04130091540b900f01e0b40512500312154190300600f0000c01e4105801100306007060a003040da1104075261040c3c1840c10801001e00362400a10307181143c11074500080c2840c403006031000030b171041c2d81c840b0300340d110301280d0590700740b41407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 270616097 1250 270614847 270614879
    0xa0305010f080102031e09031303050a030f05120601080c2b05060d022b080307050304050d0306030308061306080124050102010605030303070e040207080c1506010e06040306090503090901 82
    0x351000d16082903552803118284c5c441296504040c080c080750b4140102c900400c807640021400058074203020300301602d10a140303a42e91094600c0e51012045209040e040700c20343c06c02e500302d803800c18548402600030384003844001e04130300c0c100080c40000814031760072041950080340404d00c03080302d0b01c101e803401c4403981c082280c0b40000c00e902d8100420810704c3d1807505035a000754058018040c1501d800c00d650105444400a07054040103ca240b200140307c0314001c40c41080c0035120a5100e007421700780945406400d00541050629090051000c00d80003060316078407410490321446007000325070101001e04040c0d4000000ca47c02c040c2643e8005a50752801101d2000088030816200d41c0d0390012400c4e10001d105240e00b5030000c00c0442c28046c07284501101411000c3c2c00980f500517155203400c80c80d4410004500d1540240c0111a01d0525903050b40b0f81140702442c2142c5100c00e8040001d015204078807000b02015503075045442088824010b81325100c400030021162581d44143d1084002d40d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 270617347 1250 270616097 270616109
    0x50907110610260715020601080105060d0f0b072c0108100e0106080a06051003021c0b09070e0f0a0e0603070f060906110f0109110a050d0f0b04170a030501 68
    0x40d0708006440030707016602a9080b00c9a50f6071404000220140a220b4420991070b12945070080c00d5000c0f6030f001400b00301410f012060340c02000c140d854142c06138210b40e40904450310882d464030440d004100c40354111072240340c102c0034031512a04d0f811002e986c080c4119804c0b13141140b40b41c40310034515a80c3c4600c1800050207880d0280c55554200c140d000d0010b03d8001c0703c1246440c00010f101c0d043c0b0401070181c0c46801c031800003e00640311400034000c000b0790700140d400240c000911034144500c003c1e01402c3c161619405100a80035280080c1050000400c0d800420004100f05500d039954082601c2c92004060000d100c6552110710030070502034103c030803500074403e22000242a800c2100c61804450341d1f692185000ca06003001110303200c020f100c080b95580301c0c03039554280c0f1850030f03c200440720303124544200e050741024040c013280d405154446c43c03281c040005c4210202d0044e8550700405070344a40320f51502c0e9181d1400d03000c0000c4030341c0d0440312014082903520400341c050388128182c0748 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 270618597 1250 270617347 270617353
    0x9090102090310050c07120203120f16050a09052403010308040509220b0604060801050f0a0c020a03020a140109080406020102070c0f031e2103201e0702030705090711 73
    0x2120030f4084240d50082d07624000e8004100403500c04075110900b035500e01426441900c1c40e00040c0e03124100d0481c0192402e500d00300313025051003d11460b40790110f00e040140d06055052030304207100501405400c0c07150034061f02d03d40001d100514903180703101c0d05560401c034401e0f03200c1d41c40b42090742a9800c40d01513140160301c0703180442d240c0161042c2d02c100604408814202c048019030300c00d01c0c50745001e40300a0700161903440c00304000000b0b0007018441d8044991ba00f1203031030b01d82c0d140e0f010790f040c59840d01d043d500103018070740c0840ea000c11116031485e000080c01149480c0203007000d004002840300a082d03000b02081c0031401a9064000b021614010907801451507103070042d1250307250442c400105401c1d003508035002c80c80503402d44915041e014a17121071041180e00306000e80480e400c101c1000081e55000c50903680c80d00030801c4211400c0c80008141080844545112000340b014600e240d41c02c00402c074902196010000c2d680a40300140c06012103090138140a440d0684454007041c041c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 270619847 1250 270618597 270618613
    0x5010b010905150f12090f0d03021903020c07030f0b070909060e0a091a09030a120605030c0d050102130906030605180c240a020a14010207050a110f090901020903 71
    0x140c8104002816641c0091040a94295010b010b05451313001d005000f00f101020f1090208640c02002440e2050035400080d0525200340344a0038100155800b211050510500c050035041c0c40c6141034100e510380c1c5040040e5101194441c880ca408501d50000b02080081d41c80b00c41006401c8a210740036000d40d889400b6031540300c40a500503140c182c05480880c00d50f120002d05e40004a0300484605400346580d0301c1c84260302c104428410004445a1205a100252101c4103a50010852500d20b6405500308807807410840083e840d61540d1505901c116505220001844401c1d81251300c2e001e54043c011008517641c01030040580400e220039213045181500259400c02c10600c81c800b584005000341180111040401500e00207202c054000340828130030701b011b61220030000b40300d03548182c2c00402c1b103c0c215240481c9c501c4503541075072b041a40103025413030000e58000340c0320000d10f80c04190850504aa500802c41d000095000b03654058011014072140c0341040d40140b401c1c480903426a2102 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 270621097 1250 270619847 270619849
    0xb0406021606020c0f0d02030703080306010f03050f040f1505070903020a0b0c0622170c19051c030e0604060f0515130b010e030307120f0903080703081b0705060405010b 74
    0x140c00540b1034400507802c0055400303c01c0c40d14508402d0524402070403107a40305000e030046484e007603450300220b074007150000a00c141b03980c10032060300b1a0180c0f4903052200b45007600d440008503401800c02410001d940d40c020041010082c0a8031707490400410400451402e00c1c00180440e500384804d03030140507000c0d000302c2c0488260f421210000b03c40390042c0740076122100c5094a43c800c841003082c038140c20505400010390b1210140d6000c0d01c442c484c0350740314046824400c4c10091481042e2701c615001c01c1c0c4410002d400424100111594000503400b030030b400b03050903009040070011004481c001d0328101710412103180d1000a5030f503500c1700c040040b80e90314100c88003202c00c50400103911a004440000614506400c01a056007061411203000e90b03102c00401d10310741008004940000007040c200c42c040c1d501142e85024401246404444030745141c60700310341403080c0140601004080340c005200d0b030505d209141071480d03035922000e60319402402e1154585c80709490032544c65090142c540c804e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 270622347 1250 270621097 270621133
    0x1050106090506180d020301060b070c051306080a140a0b0403170702060907031b051804060e0a020f10031e02040314210309010b060714060a0c0917070308040b040602 73
    0x110601d14204004c01840d40100b000d440003e40007280d0640d201d0b0808125062548094200c01d44109050700c4080d0500040101e640e448482c03c0f000c01d0b241000800100350001000358450303030008504810100440101424562004405040c5c0c440503002e000415500c403401e2151207910001c0070b0f0701074a070207100301c2c0c4580d0292204842c660002c04180701280c03500c060030710401070000e0710154035581c880100d0200f0700e030751a4089080c60700204000c2444240d010350a840070210010345028082680043c0e2100c480b264071078000e4803840c090035800f5021f50b120b00c1c2d012400b0b92100b0000314944102c1030103540b2501045944200400910300e209000145da80403626071200d032943d404c2851070300c0c20125000140460720030340d250454440745031188001170007024015485442c4040102c255286089005811080340518003000099040e51040030a41903172040902d040080070384031101c51409030f082c0c0014003482c230300140004407409114002d10850b040c54003a909104003804072018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 270623597 1250 270622347 270622357
    0x3010908190f09170f07080604020a0803040e0109051e15010207060207050a1a0d050702030a080f04320f010515010801030803070f0306090e07031e15050402030c09040501050106090506 81
    0x801c403024002d2180701c101c511101380652040c0111400801040380462a049640e88039140307540041c0144429400c00c210710710040e204540045190034a000c0e1400484a41481b4510a103640c41000c2401d50542c02410045550304074158132a9003841c05800c82030b011000d14140c09881481c100141403400810480125100203004410f00c0f49082100790f40c0c16244900c03043c00c04c0e42007152200c001c074544129400f400040e801151655a1554040c024a902422400088800b1300811000030080101c56080c003c80d11202c0748103905036001280260b8801014907918000c01e541200301c0e400540c8007030310409442c265420843c59050054601b50800c1c00040c1109108000144036070b4004e00c00312105404528002584540c0c2c1e20005007100c050003402a500c3c0c2004004002b0300808803030040c42060500600c2e6801e0006a03200c01101181040e4907a0403500c1d04000b0b41955800d0256800c00e05000e0401d0503c0e24103450002d00900b424050140130030800d01c40402c141c00e148007522 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 270624847 1250 270623597 270623627
    0x31c0510030b06040504080405030a080904060b12070e1f05120a27051222090e0c130f061508090c10030518030f0408071e0e040c050301090819 63
    0x203002c0c1e8482d10309000241c9401003054514400403c00050300d610100440d046840c09006c00549130a010800c010645600d5480031084103014444042180e0856041d550408a2803e007140d44000c03d5020840d40e0702c2d4016028151101826103020b09908580100509001c0c4c1c640e03050241c0e15864240d040700c1d2540003e1402542a000f58411039110401c0140104d00601c110b80b000c0c02e84c00010210782d070091a80999540a142503034203103041502042001e070520310390038064038004400c1d259403120175441e040d00c40c1c400c071091140c01030742e40d90010850312005402441000d44076a55812075074043c80392000017900c00000510848004150589003110051148000803030750281140544405004a4041040c410609100e40700820042080d0340d1040e22264030b43c0d182c014a21308045d05540039407250003495403407030542410910404181e0b41d194002c0070440c2c940d4101411070601940003aa01907282440c1c41c01130002981c05401c084440421007200415000c600321203401900b00c0007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 270626097 1250 270624847 270624863
    0x1403030408091306150e010f08010305060c0d020c0a03020312010803090a09020a050c0a051e0c090a020a0210021201151d040507030e010207140f07080c061605031c051003 75
    0x51003915003c40061003200c010039000c1050b944401c6414101000b0f441c082000c20502280c50400356005030f0800c021202c2d03030600210561642c0c8030136441b420024071820404500003a0640c400d00c05a040d10340032000f14040f5400c03981a072030003950329405940b140100c04902c0c800011404030000407100c5000b4064013600f0020301e840801406504241c400c20f052040610564229803000c002000d0098041e900400925440e5414000b1452074065500c40745c0d00201d40071256900c0c1d10110a4100c141900c006079180c0180600300e0038450020401d00a45000048205501d503d655950f81602c0300700340310548000099406803002644180116000c0c80d06240300070083c90300c1d51141d588900c1905001c551003034101107260072a4046041210040b03c22520705c0302c0f040782009481e60a03000c100042c8551400d01c41555640e0b84c00c0405140b19901c0003400c0e040b4664107801340f81c50b659114003140c0c0c0b1104400c840c03140000466100d506100d140034000381c0314030701c0091003400f1240c206901c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 270627347 1250 270626097 270626107
    0x210f0402091b07020d060e1b0a080109030c0b04050a0804181503021f031509020c0106060302090913110915040515010e04051b030c07060b030115180e0d020a1403030408 74
    0x2441401e0b17001000940d01e80d0f9845203000900c02050051703a01250451082c41c2d82100d010703082004210158200132440c1c1c1c90440701d100080d0304804800307140340d08080210000e070b5031850440d103054484000100b0f42c031404a400540d41084010041c110003040805000c0c60030b00c000d101e07155105e0303480045d50006140000c05a0246400c2403007154030300c1841c1c0401c151445c8000034800280350380c004e41031a07500141b4000001d10a00c60300016040c1442c05610b42041f41002521459029011494030304d50307140c0d80410000d407a40b845006540c05448d428651510f0351815910036070304c0b001c00d070003941094000380e11074a050340c460409070416140d010040100034107000050100428002c071500e80701303002c00b2031a58140050751041103070070709c4e2030f03600d0b04c0b2842d240741901c11084545019038144860346007071802e9000902d0603a8552071880c0051045008080040d02101030507200c41c0c003503810114102c1da03000c24075688103401200683c0b040070703440b00183d50b42d1008881c090111501845 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 270628597 1250 270627347 270627349
    0xe030a030807050711060301060f091401050403080a2303090f0f07090213031406010602210405011116140f0102160e090319080411040b15210f0402091b0702 69
    0x600086400313117400d0441c1d1506280410020707442030300840041a08851181038107503200c0608005403c000c0c180c064120341c10030010789a070045000040151a02240d1000c01600c506003101c0c84e0300138010030000c1180880002011a88165400001c50142e141110348409000a0440800b03d03032100816800345131161060094108080c0170101c0032504600102080c8844070242e00000242d0145c2025450010040e150005115806100c10080c003103100c101e180c11815034088030401e0910414184616100c541080c40c50000365001c1000c01038082000000309500c540b1442c01a2038180c0407403a89401a83d8805502031031480300f50490344148218491803140340d4002c206003084a003811002501c0c0074800134801040000103281004100501104103240000c0f03030b0040d142006642c2500d0b0206107404900300310001744000014000110045038500c0f115541c85602c81d140311410704140038031001c101070b43d05901c030b4041c4002203660744002c00507100c402d540c2c0c00040c0d0320b03000f0a94 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 270629847 1250 270628597 270628607
    0x2060708070e030a0206040b04092018060d021b0111120a09020d0503031e0a1103131b170d020105061c050106180203090f0106080c0613080a0803070e030a030807 71
    0x6846035054001c1d01300e03031401615448040c001400317005c5246920b450a00303440c082240c1c800c028900e2010740054035107181d03460303d01c2200c00721203848445900d290075032004680ca910842c10703690112840007034603028071000e0407000507001f103d85000b44079034540c0e803035403c0705401080910342241d95194080f608101040d400a0215480580450103142c1c0d179450703c40c2190012a0341640c1c080318204000900200c0e07003201540120f02e900100901a001c42e01c86d00a40801401200c647c15034416210600210004414244402c0058244840d03114114640c0c41c0d055030a420700d691007a94450040b0700d00600456124200213400d99480749c20f034020039100d1003d41401681c1c5951b9a0b0004644d07100369119281e1001e24201c3c0242c0ea90403c602c0b401c5c50141c0300c04038594582d14140b03003400003100100350704000d09400c96005442d1000e400b61949a02401e51000780d941c41100c42c16410060280d0280d44030b402da50b00d41c24407400101c4203158440300070b1340004001410040004170514012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 270631097 1250 270629847 270629867
    0x160f14010b0a23090408070b06060f0304081e0a020706080a020702060a0c060b030114160311160309090f06061e050a082706011707080a080a0513090902100206070807 73
    0x482c010f00d81100400300414400b01041c0e40960709240e00080440c140702c14220219007041050f01d9051420341e5038401c2c3c041c60700024100030f01004002903513010960340c400d400700e203c222060055070340e010036100c06543c825852090001141c802d400003401c49056109a9282903000342856103401652202200c0e82078100c0c03812522565078180c031022544092081007025840c400b000300700c03420144400b89403e080458030004250801014030611034454043d070b000c030100680758a03600502c1e46000e0781c01c0d481c0742d0084518245460480701c42d501c4160088001c6401c5078960000c6011000104140928404415400704200300b25500255201c1c50310b00b03510402c0c0070086c0e04107031103800030102c4034010415003100503402100144030000c00c4c822141c0d41807644a005011552402c4220f5480703a000d03400140c0711403070100e10910240d001d44229004460020100400607840e00d00703007002000d07051400e0b03000e44501c03882d150340240005200e074003e05440d00c070f80342e060340c524a003101d1a14031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 270632347 1250 270631097 270631139
    0x608010908310306020301030204060e04020d11060d0203090c0118030c06051303020d050604030e030d08060f06070c06030e0c0907120908090a081c0c0b0703050c160f14010b0a 77
    0x48880c1c40a2920072900c0000c0103141305a13000b681e294903500401042d20302c81d401001d0b60410110a005c0143d5600c0e42003840301d940b0a1140b040e00005c8400a015406010340ba001c81c40c0c000420420b25031700105001e04c02005c00d8858030303040034581103c104812602e000040c061001003101b400350b10b000e000940303004100030003010000d070345950224160710a0182e0855181d805082403004040e00040e4031810306c1001c0d8024142c10190010091510401038103090286494443e0300d074050702c404c0200c4401903084421162080d6076a18010002d11100c0004030040c0a810040d19091518440d074501402c083d0742c9410840c00421604002000c00e441c046849520401100303031a512078894410081c6103e80241c00c8404d141a545846242490321010401c19408501c10003c0d1000450541081052500003150394440002c42c1162045498461007403402c0c00c4c11608010ba80044204280e00c02c0e0b69150110b490044420300381d41101544552240070030a09200259a4200300030020032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 270633597 1250 270632347 270632407
    0x10c030809030409110307030f0e0d0e0d050f0610051801050f010909050c07031205100e04030302070f080a11070f090c050708030106090e07020303061f21050106030608010908 77
    0x640c644e0b0081c12a8031002d800a0076080100401445982610410011810580c42404030a81c0f08441640300c0e40e4182e516010f01c8410740c80d01c0038940302d65000503e180e030300200720340c00c0c1e101255100740c1c1d0784021298248144a41500400e6504069120203e1100b01e1011980142d0038001080040c0c0c2c007605066041001d41c1100142c2000d050080600031090728030900d0340c130a80d0b400c0007060301008030025511203041c0b209000753700d10b248511908813075000ca01900d490300c4034503003140688a401c1014054030074464941c024400d2400c018048100b0fa61110008520000381c0c09803110348510480b070088440c208200180700315600b080901e031020f40f6000d880e0618a6440015580081e0000000a200010180f04c8541d0303110000d0b420050500046085142140c0081c4580d60b0f40480184412030291401008030b001d882507040240081a8980f405802c00d405d01c0f0045c80d092054100280c1407042c0002c0d40300041c850b1504642c1c110b0300d11843c002d801d14401d200e0002100d000b4440503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 270634847 1250 270633597 270633599
    0xa050f160801032d060c020705040b0303070f030c0512190c050c090c120f01060f18031e020909010b0406060903020105120c0405061c0c030b06030a09050708010e1507080402010c0308090304 83
    0x60600340c4903884135108100010f801410080001c3c6050349a82282d40100d1a015883c101070742c0c00000e8448140d40f01c038480e0001141441d0864000d03004100c0103055226110034188190003540c0074010070f603101810350f6111b030320148084901612030500a05160003020300001c03a4141150102d500c0054448420b1800003402c034848211081151044001061600103022a83d44000c051801007500c0c60500f03074084e4240d217250410000e904c0000c0c04003030b0f546e02805828011001620f0702c2a00189908040d15002007600d01808a080240e0300c0790b8941000810341502464154068a4043c1e56803410901050036aa500d802d0140206483c0c1c0d005100028031079544100410301109880040c41c50003285000102c00d0310744c0c468143d010306040c80000341c1c00d5202d41054070f501c00c04d14680480c00240c1c90034120b003016860f403c4044a942031644103510546e00103400030718071200010103031503a51450404c443c0310000707807002400074900d800c00f00080703846204115040130015080d60b14023 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 270636097 1250 270634847 270634913
    0x12060118030606030209010f03170702031501031524050618090103080c0709020a2f011508071a07080c1c1d0405061003090f0204050a050f16080103 65
    0x640003603441103400d2a281d030f405008600b8880c044a0040656150031060b0368155035454440550741003100c6040c45000c00d03142c1c1076607400c01c00c132005030107201c004105a50b107900b0955000128400302691060610034004e030181800404070654030307601d0b500d030f00e54076040c8000c02c40d1300d0f8801040d0403c880d5841d0140052591407103800e500131489250b6555542c454107100a05261165002e003903010700c144010b0501941044405040050501d075240c4200b01e1042550000381c440481d1550640c0303030015010303104102d265042e095410800403900200d91f60220b0040b03405031580b440b80c054000740481c9002440100c0030705552690365040c0c6105601444c0f500703c1a682c0e050300714000410007940d41040100c42040e45d660f5174000e540030300c0103250100c0898058454080b80744109650b5107100c0003802511086c03184081e500800c188000e06002403840050102522115000e2a0a0740801c0d2010402608410b890a03a511500d0183e031842d200d0b0308034801e003003000300341404903203140c0410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 270637347 1250 270636097 270636137
    0x60503032b02030403020c010809011d0709060b0301030f0807020604151701170a021009051c02030609151308121303031a03100f02040503150603010b0114120601 71
    0x20000c00c0054903a1400300341200020700c4480100c0780d060451041003408003003540452089098803081c01c0c03000c4240c441d00c40f9140148040e0f00e1001800840d1413000580f0f003000b14084007201e103109018407102d0b458095486042c8404c0c440100800350107882c2000107030303500001c0c00c85207000034417203418a41c1c0c60740c1c00c000c21001075602000107844500c101749819961130b203007400f5103981e2140394803455481191031761304c440000020344201c015030300c0031880910408095015000203481c2240c82800b14841e1104d01d000510100c0c860b000318800900440e5001070400384440410751070507002d448010140403e034402c0c0c041a1a00d200070800a054101160061405084660f120048064107400d00404945000340c0c12040142802c501c040e056400180000c860018000001424006c2c118000e000f845550311958041c050340340c0088002c1100c1c490315118045c10360091048403665030044a03060b080c042c284480c10024440400040002d000701503100206050480c002c001014040306 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 270638597 1250 270637347 270637357
    0x6112d0c0907020d1806050703030b03071a09090901050906180a1205090a0509010b0f0d150314010e0d05040b0702011403130c080d0903020904031b141b060901050d06050303 76
    0x940d00904c10580020752000035018103040c0c0c4e0740b2a0289504098004000f03120744c8402900301034440a8801c0d03569406e102e45801043c204240c811503c40c4050340061a030804070303030503100f18244c200146041d041030148610621084001d0495580d883c00d504640600e40d4400003040c4c401c7d0742e08400066910240007600607041d80340d07641c96455103010815213106981005000382501c130b0040229600c0c01054808801b440c8000c0307a203c101a0b00b151b40201741d0000d908240c088502c400009100f8040b07003102854440b54000d01c10034030680611542c80903200410400140c042008002d0b6000402c09031601520500d082c4a012130388021041d419082a035035444011a010099010480d8009100c8020501c1c0c030080d1554080205019220402e10b00c0041d0103180480002003c041c400c4103252a00f1103070950001091510303044c11224078900c0c00e803050b06480340c0b0620f500e00700d036000c000125115004055514056101004603001d07004801c085501c4d9484400108040d5018000f0b06 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 270639847 1250 270638597 270638611
    0x30403050c160503100b010206010b090f0405010b0901020615010905040f0b09010303050417160b070503120a020714030702224109030d0504030e130606112d0c09 71
    0x4001c0a06000c10542010f4511713840000e0a494004c00c0344040c0d0b0081110760454514020441d11444458049242d503104155400c2e0712902c0c040010902000070005080008000e1f0700f101d4542d030320a00b4118402c120a00ca50b030109200e05404c002c146410341091415500d20f4130046644039a44020458141c020b8004a01240011030248440350701c0c0000c0f0b01c9a09540c2c001084e4007044d41c031080780540032a000358100c3e800d0000c0c05206200c07003001143e02075103032505000c58a10b41454484002d4000c58022954000e981016405080c00081501d100d20f40050944041446008801102486400560402d2600c41480d0071b021820740110f40144002c511030010003041a10012340801e81c0035005410b17a189100071700c6104180002554944840c0f20070000d85500d0794201900e01c680d1100410358002500f8800200b55505138000c101120100d0300c0e00c16040c50303c04c07041d0340c580f0184449001e84002d20340115009400d04054000781611403000d03030700401e030308001250001004841c60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 270641097 1250 270639847 270639883
    0x14040210020304050f041d0706090503120703021f060b04030602120f090d0f0905130207140309010203180f040903090602070501020a12081009021317150705030403050c 74
    0x429810190420300500c86a403000c2c0d403900c1d0a01000449141d0340042c0380d401503517070f003014030214442004003650182c80c3d00110380109a07034130001000019240203890090280c1080c81c5a001c40c41e80a0318a41641500500700706040d5805500043c3d00c0b011008000540b0742e07c0000d1007115813401007003d903004240140e900d448850005003050805401c0c54511000da0040207045500440c15070448a52480d21549159210314100c41110f00d82d0046075220001c0901000e10040b41e60041005500c02c00f40b18a03c4004907004503140c0c0104145140941c10070004500312280c580050740e1f084800400320320032050720381e011904403001584201c001c00d51000f001d00040b82c0421605000341402d2006241748007155542075541c2c21043c0d10716043c016440c0100711002031254050001e8140d40c0001c645619600704444031155692151a0030718407540c1001c115a0400308008034080c124440240c02e40d151041c0c111101d49c0020070a404210060085440307602080c88103c000541203265 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 270642347 1250 270641097 270641101
    0x120a0e1f020c1f14070c051e030c04090822122f0102030f0306010201091505010920090603091005010608070906110d0e010c02030109060c031409060402060901090914 73
    0x50040058074912180031140d141030b0f094814a500060071008091861071284d01e990061400070092a09904403540c44000020364080848000b40c8420032501c040b012a803030300f03540d42d05110464003003000c0a00a00000c12659003500140120b0085184800284144180e510a0101494100058211030580b0360074011403d1051241c7c001c80c040313204500910320041c5001c0080d58034411615407004484000c000591244c0c000c0d8840c001041e04083c480a450141c032100d0001400309014854065182201031441d21120a50400e032598143c00e0942c64410103508000450308010100c0c4418410000740e06a1305c0d105000f0030740204450744504041d81042c0a02902903500303900107204225a500b14502c0c00c0e40c002840d1600d40205082c010004441038004840341145000b02a4040d0300f4280000d041000641c421075242c03030075980810040d1211807248008000c15034640003940d20420214001d850404000c04400030141450508240d550107600709859813521441205606402 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 270643597 1250 270642347 270642349
    0x9021b120d0621030f0309020603070810062303130c090606031404110d081b061008070503071802070b0a0902011701050a03030c0620041502120a0e1f020c 68
    0x200c0018100034003d8015500c3c2480c21203100e40e8003903101030100040d41c2ea01200144c025440300b8081900642840c0c0c2e80c0c90a100c0161041030207a40d00018903c01801c005925032160321001002c034060542c04851640b20304002c0c485400c007401442c000f0f0a44084540003c2c0100104d9005101156010800501e0f040000d422200c0800c0c003454040b49072400c03c00026400045400c0c0b18170226101014100140be01171128004c000803104e00c1780645080c12059100017500c07912400d4940d0740c0c540c0050310391011a1310b5003464800c1c9500756214110078060424074010019007401c40d18001802c00c101ca0311055a14007042d43c014490310303514050203080d9684440040100040c0300750301c0109524042c04a00600c90503c0040c3c00c00c140340110004128030b07a0400f9442550340500c0d14955100b5404081c0a58010300c03e01110b060342d1441f40300340318004204404070111091040d42006002c04040e00d4070b01040d4149603002c2c016440d960440d00345a003607441440b00b03030b07401454101c00c1c0794 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 270644847 1250 270643597 270643601
    0x3071e0807031406060a050d020402130315062402072108041409060901050f0103091106070c0e07020616050a031409070f1403030d09020319050606010801140a09021b120d 75
    0x10304200d01640506d01c0c1400161103841c50703940703a258107540040c2e644a0741200018209100c1d0401440410034041c00840c9156580021058400e01500a603603907907144c51000e0361002c2c0038160005a04031520800230404805220004240214030b01013050410b50340e100182d6100c3c0d0481c9181c030b84e0104c1a80042e04001c200c05501c4181074522812035410000094015180c0d0b9180c1030402d900c0d10401010843e048001d480070982c00381c03515031030740500d00e000540000395009032103c100d40e8000040955200044113405030310021641620141d500008903100d500c0701003444141912614140800c03044225424425001c1d540075018590405c81d144941c40d0a9034030880400c000340140b0302869402204a0340c0380c030700340400001c0c42d0301d8a102007030034032440c101499040c01c1014042d1041c0940890fa40c1c0c4242402d81c2c0e0980160380783c0d07006014090000c3c0030300350452601d02e030038407000d00d00e540200f1103400f800c42c1407002d01d100324400307614040c940b413021240003402055040e58094a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 270646097 1250 270644847 270644851
    0x1204110d1b150201020721020307020d060c0f050a0903110f060a020105090c01051c05060d0f12020d080708040b10091503021005070803041b03080408150a05010503071e0807031406 79
    0xb500c000d5290288688500c000c90700a01114120885425203220881380200120748550b44d000d441c048140006042c58070041100c00c400e280841d50384010a9000c80c414002caa0b0400d040b40c850b00861403c41d02e40b29552211101d0103a044070513183c410a00c1d07600d18010302480c11f0a6400450781e8a000e020050070209904007150500206200d150300e40140c0300f00d40040f5001d003c800041c00c0d6100c4000400c200100070000e400113100c9100c03101440305aa0004891003021303000c80364085800b00d4100c0d6405405c03a0709800246024002c81e002510300b84805802240c4082e1007480d864454003044110b070510a0404138070708503c1c43c1041141808520032004c070489041c05410050310b5292400184002400109850001d400c0000141e00580f03001024540000712292501c0c0c80316452950313404803a032075200d036050840c0020300c01030716406124140c99015026001c6076180007012900d21205c2d200d403100611402c0c5000c121221704002000c000e41c00b402502e00b42241c443d000500744500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 270647347 1250 270646097 270646139
    0xb0a060203161104020409090c03051621061103160909020304050706140f030103030e040e01050417070606080610060f020c010c0212032205030708031204110d1b 71
    0x209220500701c842c41d461000c24a00d400c08111104182c2110006000384191b40045850318940a1490240500795882e44243d0307114008a030307581e40350038200c0e02c0b26002e148202240194600c003000c2800b2507002c1c8030394403039200e0040850540b181d03040d82581a0411203070941c141e0303d84544594007030783c0003100000501c542c2e01c04501d1400e058031003c5d1245101d004400501c459a1481000c4003030340e40c200e80d05810303801c882c40d880c2d584a00e0300402c00407511540e50700c220f080258211211318103209240c0100e0b881f401c1851086070112000f002a04044070580f0340c159168000588603000380026449030303c4a83c8c105002c2d5081c510094000c100d08020b0008661207482c1c0305030681d07041401d855519070110782034004040101e4101e0710b548161410b045000703482c400255410300c1590340307401c1500c00843c142d0704c442da11444500d40c1d900441d03403050710514050000c900420045400c207412160041d00c100009001c0b9141c441a02480078410940b8800018041140b48880f110031041310f80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 270648597 1250 270647347 270647353
    0x2010302070218100e130f0c09020301030302030d0e15010302040b01030b0a090204170d14131d04030207060f270506161e080a14090310020d0506040501120605041a0a0b0a0602 77
    0x140203406d00042111110000c0003140e03485050000e01c5841c5086200914004100303540d03a44e141d10300251a034001c4150495207070b08080f448400c0c038001042c5042c14280c01052440c0580ca183c003008050415600060305060340c8055541903511038101c520040c140e045000f60361203150142405040440c03620343e0109401642100e501c165200c00c07100b00c5084a004004c0e2281c2c201030680d5036802c080e45c00101a046598441034180554447c240c0c4224041d40a552a00d95150000e4075084c0c60003540900180300c00401c0e4207145090742c5811108220042986100c41d11200880c802d50b200b4000d0048841d0580c1c88141040510072104a140080c40701c44042e407100d036940c0e8640e9001d45840c2000b031200020344100307652079031400e0310003100c80102180c0200d80c0c0300c2c440390000c1d44070050b1710030310300c0c107000015815040c81d008050403200382ca00d90201c243e140e9261800244070280c030071984100405008000c5000f006445402400f01180001d1003040000802407024400e901800030b40d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 270649847 1250 270648597 270648601
    0x12051203010e0703020904150602060907170c011803020a081b04020f07080c15070c05060c09090c0a02031608090f090106080a0e0c0d2f0a0302040902010302070218100e 74
    0xd4a8050b0300d50000c80b1400c000d41c40d420694000f9000d40071000044401c0c08403120006001540003440902030403808007a25426922041d20705c01010340380011145e81e50000f4038912081d4455180d0005000c41e14080840e01c40d10b81e070004007045144e83c030820301c941c4550710017084480d817050750f404040401c640031880c0802090a400d40fa00a24401a10002000c511340001c5c8605100d458070b800c10701d403041b260038640302001034032107052041e050358144070701400a480c44d58407008642a10f5001050350034640d03150102c02209500180c0d5000440c007050201100c0b031030990030400d01c0d9600c103a0003680c444400a081c000107200610f440c0d8400c49181c401002001e0f08480960340005484c0c01c0452200003028040d40f0b80090222000d8004000300012002d00a0008105809458110a4182c1c00e40720407610250000510b003103543c01100004100010b03d00342d4404444140306040142c20320b40640c0008103038280c0c03000d034185880000c0c0304000700c82c030f8202c0c1404042c0030121115802c80c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 270651097 1250 270649847 270649859
    0x1b06081006091208070b0408030115020c0d080307170901020a110c0d03050c0c031005040b01060f080708040c0b031905160504051203091005130b07150c050c071205120301 75
    0x10610f10940d0a404800f10520003401a00012100e0040d04842050700e9030415140c03014240d44240319a210540c101890420380e90f2020420392090800200718035859000c40c0c94020103540301509050a00009018041c42d48850850140c454044040010303140d1001d00e00240c12202101c0310025990480800710b4415a2002008800c0396014a0919210340211031101d20700301d00c03000f2a580c14490282c420705141c0064020b284164840d5060b5034050b40c0c0c400b000d40b81d80b504400540b010546000010781d010b031040924a0707001d4014100354000315502c6156959070b50003641d100180030030b82000c1020588182c007a25410103840307490032400c13140c074010040032400781c0e00405108002815607096652010029103000c240c004142c9034002d0080c00018116500500c0800640041c403c00094800300848c11b0b549080c0e08118012010051021001c00800c801810402801030520000c4000340080003108043c0c0100e002c0240c4101c03071410400d14202c1c5590550b480311004000512039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 270652347 1250 270651097 270651107
    0x91e03070b190c060f0204080303010504110705030304151506020307020427080d060306060e0a0c05120c070302011b180b0301061b081e07120c02060301140d1b06081006 74
    0x1900800b4500b00710030396024074104c805000c1c20082038005500210340840c1c011804002503040310800c1340c0c2003020703d64421585209000d074030340c0900190811f200040101300225101000d015099800164021021240c3d41212030030790401e1005a04c085040421420305200341e0b502e201c040c0d00c0d42502880420720900342c0084180006004c1702d4003107a60442e000998201c900596130002c000d10400c0e485120420b5011009c039039544009003007501740420603025408442d125020112641c5451744d81c64990b0860b0391005200310215907075101c1c020584070591240c100454800e5440c205520f10807100801e035000780360050400c0b620100010000c5a81202091000000503840404400440d060255042c01050002000c0c040c0d400c00c81c410006101008060581c85020410018040b0031022514443d125000a401c18010801031090200012440c1101c99005181340950441680d80440c41c18088040310308040c1d80c40d8003400300c190000142944043e8801c44044c105141c0b0b880201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 270653597 1250 270652347 270652387
    0x11041103161107290301080c0109091e05060f1011070e1504050712180314070c09200c0304090b060c0703060209040207050109030804050d0903050a110105091e03070b 73
    0x2c0c0b42c842c440800d080105002c1d04c1c0400094902c1107150701c943e075400c440c1391900004811540042c20108000c180c0b020f1070f206000141001440f038807461064241d8282c0240f0700907001c030781d001104d0f0011040550300d10034501240c0320310380c1d55079048140c04007400f403608150350007070207414218104010654242060410411400301c40108003904c40c460705664494650200c01101d6060010840c2d44600404031044001c0c1b0969a90003031080307501c4800118010810000c00c60405600208450780b00394000d10180c0c038248803208425003860351024290b1b0720038080b2200680002ca020424058075200c3c4031500c0c4815500c141c0b4001c1c0b128901619079141c0e000080c5416404500c091498803181e055601040d8403100801204440342000f07445c4a10440f012907840c8160007250001c1d61180c0d19a07000c8981c0007008120b48802d40d6555185a404418554100711003071017421160b03a01c0e030700d105d01c0440705400d00700e6182114409160030101c954004400c0d075a03040007401d600c1e4040389800c103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 270654847 1250 270653597 270653609
    0xb090703031e1e170108030408060c0405030607110c130912080105030a1b03080f0d1506090b0705011103130b070f0c02012303010f05030c030a0c03080711041103161107 74
    0x500c44859031141503d180c0750341041078110304c0fa0000040345580001004109441e910f03c221146a0b549041c7d907144ea01c9103001c0c86070542c00107030104a07d40d01880b02000d1881c0040151115140c13204c1c04522031400c012000c01a01c0d80b11002c24081c460a0101da071030385141840c0c0901781d0360411001c60307515240700300000c1c881c0290103407220b117042408580c03070003a50340410140e50312250070a80e41d141c1d8000c05014591285080c47c01340440030081e01390400c8074196107800b0400c5e8070b0000841d50b260481c40068642e5521050b120a07042c030181c009501c03410b07888004003508419810140080100107182605112070800042809500107858006403642440c101c0d42e0304810000c0c0e88818019034201071700701e000110002c10480044006a0159074064003100e0481c200c02d42015900d074000100940f0a8070f0031401840401d4114004100c07140c00340c0c02c0d5100159140d0081001c44081523011a1300080c00b00034071211000c8040040e401c4000c51600b07403000216414800d40382c4007184110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 270656097 1250 270654847 270654887
    0xb0d03140c0d05030406050a090302070b0a0302091512070507020a170f1e0f0601032a0b040b0310090504050c040f0f02071110050a05030613090b090703031e 69
    0x10410890044121440d01603a1025200c450402c070340068102c0d08159412074100c0d04000c001420001c5600c42d40300e4081d0144e0041c00540c0ca060507442c0c1c9688a241a0720426400704100159616401d040f18442d840020040350f994441245000035414090000c20801c0810400040540c2e02e0301002c0c002e55641c81c0094003000074506000f40350000700005030080d4081c1b400800015100c8111401300c0200060581d01c601107045c0440340c07a0f80c024000280f602002002d00d0100000021040420f0f0007114070444010b5100c1e41240300303a402907404000003902c00400c1001d5545000740780e20080144610034041410665900d50302c0392000e00c0e0b0207026503a070348401850a4a00e8201110304084007208654802690811210400070f15590f01d002d201020314900500b803091003241d00391070305039843c9030440e00d0715810403908208061a01510f0398030b40102c1004104902651030141100c28003e081d014a185800f901602c0700a03083e0441444140441c696503030030661a1200030303082600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 270657347 1250 270656097 270656117
    0x7060207090f1404060504020f0f09040b04020315181603030e0f01120e0606030d08040c0e0702030702100305150a05060703080408040f030c0603051f262d010b0d03 72
    0x54040140a0944020929800f52041c042446080c2e401580164001c2c0d03070b1207038881c10800512005040310340303000343c02082207000680031484100350725030030520013002d031790b01040c0c00c0300c154030600c5d42038030007160181d01d40b080041ca140d010055141c1c01c0800707101100d0458910345019004012403404180580207000b441c81c4d8030b0b071180c082c61520000c150810001d121001da507543e50f8010072a06603000b842342d000b4a02c4005d0207802414425039100801181c20350504555819080024060405621041c04060010303540c22441415882d080da81c00201031811120a1354020b03500c0c2c81242c040c0d14500d0051125446030400c0f50001034050402d0300841d210b510781123100c1d20035644804110790846101008211848041004441441d64148400c0d120010807043c0170740303925810030b40440c42a4003000070000d80032a48600c0750302c0d00340082c01044c2c07542160703040c02403e03520b000d50551003410503090382d004a0210034034004084001c000d0803201d1800300c0c811420240d005020b11000c610 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 270658597 1250 270657347 270657371
    0x503011803031a03030c010b04050108211303060c03050708060111280501090308090d090b0d0b030102091e030f1c0c0c03050f150c07050a02010302250f140706020709 73
    0x420070110403c0a03088a0b5540e030f80c0031170580280400d0072220701c91400e05000084c03404d03001803e85801d8145025030411540d400c01d200a680d1b01540300540442d940410020120f05a031081810189442d203010078546070ad040d0061100034020b10150600280a00320101240c0001d08000d1102070102050041492000c180e208200780000080880d07080c40ca02c0410551301c546254001c0200314100c84190150701030594800740d1030b02500d11002c0051002c0c1504c4222600320340d03003a000c082e00041c9000e82a00100c0e094114072001042c10701405a0844114181001860501e0410350046c2c10752381e4070910021751100e0580012380c10030481c08442c41c1400410303050302004551010031141110049002961102a0008a49448880c1d140050004413040d8120345190ba40107000c3d0440c003000b98010340c0250042000c60302107802900300c0f6040e0507000100c580701d4030300803074110b10350342030381c0c038007040a142038504d41c04198004174410450b0940000700f0509039a044000032818200b410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 270659847 1250 270658597 270658631
    0x22091a1c0b0a0c0813050c010302070f0b15100c02010c060b03031908010e0109180209150301060b090405090d021c030f0c0503070e01050a090506030c07020d0b10050301180303 77
    0x248001d000d10a05200780701c075542c41c40c1e200e14081016900d0340340107555200c2103070403c00d41ea900003030105d4002d2060861035604c250300821060f4070445038102c1072000d070b8a0360010180115800301d04500e40781748210080c50034240501c0c12240794941842c0c0c088699000a1030010600c0f0020300c403e48a01d40004280d03014403e442ca128a4002c040c2c4060440c10360090001c1c0003072180c6e154009000c0004601301d4094001d0302520007400811041c1c8a40681c00c1c000c10b80001407c0c0f21000190542d25a2240c0c1c00303020f4480204203440c03203141c9421162003040112440506405c4156002c0d90301001c0b55034001c02d4004115450490310400c072551840154090054001c408075294980301c5000c3c0b2031504038014600880e4140d0705c51007502500401500e80c0d1181c1c0d100000440d2682200b044035181c030100855210b030280b00c0d00c4d81445040c0e4049654000540c0d0300319101d4442c0c0c01004000e503d00c503070b004014001100240130940e03540e82d0a1182440c0007402404054444244c0d1103041d50076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 270661097 1250 270659847 270659899
    0xc19030f0224070308010506030717090c040608010608060c030402030a0201050f0906070b01080606040504230309060c0705090a1118030c030d080915090606010513030822091a 77
    0x1098010700da0340000e0b2403640b02d980001c81c11004943c00301c00100d694100b91007030b00e100b103125440300c401e001201e00c0030311003031a002480c400b45486025001841a182c1d40501c030300070110100007083c90341c20b00c204a4206440200041a40c0000b4410000944e0f00041c2c66a15a1f4081c00c12039030303070394080c101c5451900c51903001e240c1040000640b80100444480d03214101c4107140203032202615000100010703184162009455000b10f07400035403000400030788107940c40d94803004603481c0241070740104802e9040a00b0b0341e4400d4200d01000c004c107091880f6210790143d4080300400c001d8a500c18110074034005c00e840b480900c009240104000e450401c03543d5032100c001000c07034101d1045214002e05000080f40d84407564080c50741070600f004091a4807a02504000300a800123550301c5c030044480b40c2190304400a4102c85000c000042101180281144034104015002c103903240c0400310010308076580070140b943c1c0f800180c003640c00031a104d91448050226041c6440c440306595100c001080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 270662347 1250 270661097 270661129
    0x8012322031202130608090303040b04030e180f010e0106021f1a190305011b0207030f0501060b030906070e0916030e030913150e070f050c1507020d020c19030f02 71
    0x40003600c0c0760050040328013030382119550b540f06201039403000001c0b80c0760302064034001c2030b0940b80000700300000d0041e40d81200100c405807a82e070b2005446403060390104003d8816400044e98000144540e110f0715000324050010750009240d4030302c540401400c19440051482400c0d6907500f0381b030205500c0b441604030801790080c01131314000d07005030381c481404c0001d05c8100c03155840e05854400c01c03440e00d803190701141c0803134024000c104e145032580c00303030003216030000c49442d580c6510102ea050190005507015034074900080c2340900d0800e8025204010107070050b8805c86804080100c1d8035151030615115640ca46008500c00c0290004e0f9072640c00350b054040d80c80701154a00160816066021000140d01e041c07800a02c999284d043c028188020380b0400009a40c140107404034502650090000d2000c1c401141c1a8010841c803411420350141d600c07078010b0700321401d42000e075581001030200c41401100c1c0005800101c0d80220305003e5035201c001d2100424203400340c00e5540c2d1064076a800c0c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 270663597 1250 270662347 270662351
    0x150f0319122105131212061421120406020601081015061b05030a0c1502130303200601060905040c090e010618080703030302090910141315080123220312 67
    0xf45520025104071b00419000503203a28204001a40040034403c50003041c9004e040d002e04071b1540c0341008181c22180304921a2840b4042ca110303421203060001780000c280070b0380900543d506168030941441405c0440b04902420081c03007504c520101034841e000c40b012810142c07020854440403110800d034180c405421800007047d000303445d58100e000c4485680c800c0c0340310003403610041d0103d8124020600e0107400c04907007031014400a0b0046844200180301d005581211440c0d4a41403481c00c2c400741c11020001e8210007080209040c1401103600d591803901780075007100d04180c00e058030f00105100c1c1d80704000318950b2481080d40f02010318806051100c003a100300341d4407410050041c0d8410000b00b030150103c030000400541c82c02800009440d95004a082d51102860410403142c1320171042c4150141e8803202031240080d42030a000003412101c0010404080341298821614a103006070b081211180e82008982440001c10343c0501941d84d004410701c481c24203044503041c0340340d0341c1d50341614 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 270664847 1250 270663597 270663623
    0xf050a0302071502011406010e0a0807030f060b03010e1c090f080102041a0c0601060320070b09060105040c080406090c0f080a0227150f031912210513 66
    0x140d4045454800d55a16948246550180f88402c078201e03056485003410719071aa03400b00340d043d03108600d4201c171140c004210000280d200c04003d41455520343c0100c42031078446000d0401c02ca514082d4441d258400c070020031180b0000003000da151410a50b40130104162804108691401903440b00043d1140002c03141c0226111841a4002d41c880d019138198407c0d40c5400c001101d050b001150484401d16010302190b034070700a019009001d01003081410f000c1280c081d14207229400d800390229078001d45221121382003a214060800318180c100501481c00c15520140320742c0c000c00519000f0394170820000d1015441d08200b0030303a070314a4002e2401b01d4201c03000010a1180003030703000c5e200b60088680401c14290081c0006504100010031a10300000800040e0800e1078002c9002210602500085034410070f000001e05000d4115440302180801022950621031a03602e451450290f41c10080784c0c04101501c005904240d0301000b4010a40300d000007084181e0301907040070550340c001710f001454 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 270666097 1250 270664847 270664853
    0xa020d02010315080f070504050705120717070804021f0c170912071d010f05010c0213051008011d03091c020306070804030e0a03020a0603020d110315031209011b0f050a 74
    0x208800b805c0c01c0003900c958500401e05180a02c0f0301ca01a90090f100c4a10b0102511030b01d5130042002094041403010081035050510701e0034540900c01d09a980d264081c40c6401c1c410005140c0000c8080910221008421541c054008009803090b1780c00c0030001c1c0b080380c03a10301c408140307116807034003a40c0208070310340300c038604a00020708102500c84c1d00e0140040342000ea662800c82c10001d2140809818061008000301d501600c04076900600150820365940c607119142c1d401d0780c074251820720010501c0700302003089034001c1c852140603904141c40d11030311045520708241c1c2c0340034681880f4420b0050380300c074542401e84900d1074426a40c3c00b4069400714030b000507001d007510100b12420340102d040c000c003909440c0b41c002103e42c15030b0360080c8519101030a00d4001c070f0094200644005034140c0e00c80c6035114a02c0b002e006103100768912650b0310040850341082c14201060f10000e0b20a090040c040303410a40c0c1c2021910340c1701c10401c075802440d4021424a0040b04c030040c0005402c074058103100c1801c2c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 270667347 1250 270666097 270666103
    0xc030c03081c0213121505100609060c0b01060e2b0309170d051e18030d09141c150c09080705090f13120302090a060804050a020d0201031508 62
    0x10080145000500e05101041c44001d911800c00c0ca00e60400f00c411045c0100d001c40080c1c141190301804618440d8034888102e03000f1554280c1d2600ba52110490703007040202d61181005e800381140b032500250114455442e034051403818012802401001d521800c9242c44050f0640c0f00d040503d462642442c1d0b07503000581d031600d0344100980000d80400008503a20294002c03440341522810014500300580a02c1111160400c5052170f1000300c0114401c800d48034484080d041520305442c03100040b09200702010f103040c2e540c5220a00380820550304015220540350010403503074003900c8143d41c1900031507225040c441c0040d4001d004821500704400f410800d0740c003262a07040c45031540306e88a42c49070b00349a640c02c000d02c11242e10900c1c50f13002591807134040c0d10313090300148400c1007902d00c8600c983d144455190b803054000c00207503001c5542003051030701d010244010880c0341040c03401400c15480301900e5a60050010b8001e4106c42c0c00300d03007164420b9104208502c0c03134010300000a81c0f10425561 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 270668597 1250 270667347 270667357
    0x90a0603021e0108161e120509010b150a030605090106050c010c020303090a08130e130302011a0f0d021503180c0303090105031b0412080a1b03050a03090c030c0308 72
    0x30203400d142c1c03124040744264102585001405841e000c42e00c1d5500e0000c001808050300340c41d020001030004070558070191040c414030070081a00c410070400400040701c0c0468070b005026451030f81c1440150340b0300f41c81c0c4070009044020550f5056550740221001a00a0913450340940d401c032031041e000151855016002d40b2515101100038400812035100072603881c0000c1e05c0440b020b4110294140005081d04024907412501c42843c00081e66180d511010083d411112800d004c050202d042c801c00d43c0c28845c030b01c4c540c4444600310003000030010100340b60b00326080c11280500750700710300c15040d9a03c40e034034030352140c40c0c1c8440c066503807402c540d180c0c802003088a16000c0a10808265100358078010040d1048024103035190750950b03448a03440c100c211444402c1002041c0d0401001c590000e0074007582c0300c160b00420a459452600c14001084000402164100d283d852101540000e900008481003100b29107030100314550a810b000340c12607040d5100401c0071030b465100000300f1103d500501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 270669847 1250 270668597 270668599
    0x8060a0b030c010807021b0d0203030a0c0c0e0405101d1c030b0f09040204150801140609072d11030c100605010804050705130902030f01060e060402041809050c090a060302 75
    0x160700c012500c00107643c00c0b0010788450340941c100301201f940d0781c03081ca116080714050007041800b4484141c0c001c0b1381198480c18240001882d401c44603401d110f020345540004007589401c90859141c0790b100c03982c0300c80d020f28220b401c142d29207004104a60009104144c2d841b406000e030303645036944540c140ba5403800c1c0d040c45004617003041031140c03a07842c0070307040425501d00142005007913503a41d500300310007000c100090749907514030100042503002003485100104495203040d6403ca040c000100f00c210381002f40080e0030000c1e01d040c440c511390508010004212258080740040804400302134039100100c2402c0041c1f8840820004070044000900b140300e030303845590400c0041d46550044400076002c40f0301820a41c44504200700a08010703007084003118515400040005540d800a82001d2842481107a180e44600d0240700c40c0002c080d01743e40001c0200d408615052404200e084185034041385401550b40d6082c1480030f200301800040003c01d0020203100039403038241130a100030040da000903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 270671097 1250 270669847 270669853
    0x109020306360a0204060804020f030f100911090105030a06050406112d090d0b091204080619180209040503070206040605030f0a152706270204030201090509070908060a0b03 76
    0x481d40700d8280b403007102e003646e201d59203411f00b0f580c85400340403a600e00700340195014401d8040304505c282c01400401c920303947c0902c0201d4489090700303145003964203c0f0401c07407003070203490010040d030303900010b07074030080c592207803021a10f070350b072801c01c28020426004c000300c403800000380a4650b4000e0b481050407180c03c090980c420700e4881c0050401c1800b4501c0a107402c901ca0181136400b00710071484072070740301366820700311200c41c0c034000c503080560340096101c411141d0045c002d00c05880301070128100301c00104941009500d02d43e030070045165104050203070151214102041c1030140078000c444e0525005402107607074030b079a0b0900505950040750488401c841500c08945140fa66000b41c9134014013201c0c0000403d4141600c0c102c00590040034000083c586030030440d54415240252402008085004080c82d10807c2c0603503d000c0c0d0020180800034030410017400180c5c0c108095005460301541d40d140300f6a21484281c1c1c00c0429078101d10802c0c0700342c41c10018103800d2508035464052003903042e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 270672347 1250 270671097 270671101
    0x3050405340f080a0f06180f02100822020d021903020a0e0601050d0e03070f06020a030c03020408070b1c05041b06170a02030c0702060705010b0a0b0a08010902030636 73
    0x100c1e204030340da0f8042c1c840c0c0c6400c40701c00840441c8051742c94010b813034002c803c006404036044206a044066500e0300325442c01c581200101945070a9401d2407200402d420503240302d103131036401c2180760781300200f00e00e0310a900342c108001552641c050030230f145036018100810200c1c1d034250406001d22244405c911428456801044007000e01d04064081d600686510307041107030181201018010618005056120900440c804200d44070351994406004980045c0c1d508803006004096a0200c0616820700d4010071007001248000244030b0121011800399079102d0340340014112600005401446a00781803400740000d0202402103854138240100095803540c1e61200269200e0400f00c0034040300944980006a512a803030300190b0384080c3d0354049a103001050b5001400344d401024003500d1760b0f95100f0400342d182c100f407082c0d600078240d40c2040d02c0c100b16034040024100380d0140036001813550003001044040e281c0c08188d03203c2480c852002d04943c5c00c030440c080090504c103502d80314454100c5c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 270673597 1250 270672347 270672359
    0xb07080c0601152f060703050a0c020f03090d06090f08030601021b013204080c04060b0906180a0b0c150601030c0903020f03030706020a1206050402030c07030305040534 74
    0x2c88902241a52950021101d11841c40704540d06142000701024001c40c8a6120389441441154820380c031548000234181048030502084520340d1003450290f41c00343d1010f0062010010650782c260780100c8003418000c8443c64140050200c0b028000c0c1441c103d40050010800b40c075004c1c2d441000280c0c22140b155015502c0c207510070f500b07940507601107058880c02c5549400c0141d030f100c65804181d0a401d5420000b0a2400d41c2d82d40b040e800480542c00410500009140902034807009040500c1d0090900c00c8041c00500c00384240c8403a400406801c4541d00791070b8880e1741d03504008286600001d92240f0920103c1d0303031034083c4040c00391501d00c3c69500045441d0b00901c10102d80410316a070320b1234030324156030902c60900c06d02c0d03420950500c001d2048030002082c0307000402550106581c0c4e2541c0d0300d404003101094903901c0d00902d1140307005004010300440c4810a8402c07058051401080030f8541e82052030800a20600a4080004820090b010050316800180713442949544030320049540d16 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 270674847 1250 270673597 270673619
    0x50f0d110306130303050a050403050409090501060b1308010e06010b12090705180114012f030d050112030909060e0f190608070518100302041e060321030e0a03030f060b07080c0601 79
    0x12402030220722f0034071040c4500302499111000d010701c1027000042e402e85510000b500d40d0401a200500321582603800d004402e02801408644c00d81e00000740099410100c162300b5078000d090100404101900018201c644100648002000042c0907202403582610051070900824040e60f6940c00c10110050f0b05548246c4021001c01100030301140d403800c5c1c04024080c006942401440306100500c22a250300e0031030300c6039500901d490000221800920700c1c01400581c0b084d0b0044a466280940402c240c441007290705510504080211089d554bd18504155034035003138200d80b48061810b01c0208a141001400780b00f03540d0110740002e240618680500000301049130529032074103000c80100b0060809400842100d0400100d21a000022516480445030b00e82c1c405d03601e00c0b0303901c804940d40000011310308074260820b2405101c0b2070014040f01360754410840e801410103a65209600540c01141c0c00b00018102d030010300c07592034401d0b042c540400d8201e441021503600550000042000d441 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 270676097 1250 270674847 270674851
    0x3060d022b0611271810030203210a0e0d0b1503060105061c090201090312020105060f060901200708010c0804020f0105040315090507050402030103050109031107050f0d110306130303050a05 83
    0x20150840b983d400d402c040048003115040319500115075454a6060900d05d01389144501345020280c09114a140109031030b0000381e01c00000c049d0070210041c0b44180c0617a0880f5280c0d4240d0906a015546200100c1e884008140d0050280300485050080520340b400318007041c400b0071000c40344c050341c031581040000d01c07407041035408009800080d051514502d8200c26405401418224411a030302c0c1c6941d210528001d0300080141d66031000c02030309150064542c650b280e010703141141400d40307140001e8000b080d007489080c04079514152100307120104004150141044034024003c00d40769800103083e00c4015901203214070070446140030107500c9202581c0840e80c0000c1082174505581c50610000d200782001912180207054003c94251298002035000314850350000648070381d40d040013403030380d0b81d009400c14054001c0042045181c3d41e50707410a171401804c44800c0652505460030030002e00c09400c209404d4013448007001000040d542e0039401450194605002e15a1a034840c14100c0c1c5003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 270677347 1250 270676097 270676117
    0x30306150c0a03030f0609020f040f09020304080a08180f0c010e030105041109070306050d030806040b030a0201091701061505040f0801020c0a120c0b0c0301090b120303060d022b0611 80
    0x448140c02000c039200317401010010400f240000f03a80c64856804205a0b8014aa109889000001d0410813403c0070581400202003111085003541015038408540f0710910111400f0070141c000030580b0481ca2001d285001c200b0807040312003419958135019150502d24040c18003043e42040690207606041c0600341c801c80d0302100381030344280340100b003266402c0042c1c201810980d07a0000410030792160b28a0000440c002d0f00e814007503140074410002902c4907400c2c0c0500a81081f10070b000140d820110300003d070390f40c810300040000c1104620750f0040803d5400070350031024003048407071030355009001407065400e00b040d060035031902c2c1c01c0c20364240c2c0b103001c41e0046541d02c8802080c01043c2502c4145400908600e05074508150580360390620345001d80e0b0303115900200100400c1101450302c52259407040c1030b9004203680d20029190303a140d000c0200313060301900900103014115030303c1400c5520900c24001d20307070f4105030500c2c2c2020b12007103100b0310071102d5500d1711140031140c40328a0160707030100740 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 270678597 1250 270677347 270677353
    0x822081e0601151e030203010e01050d021e190b030f07110714010c0605090f010e01060303020c040f1b02010b40021918120b04170706020c030306150c 66
    0x1107483c411880c0034240e14844001c00007060821441c00154200070f8990600701d503000750f00c950421030410b01c0d80078182d022901c2405402e8640c5d005881c3c00040d003850803000e02e4451541c43c0814046004400b15080c01d802189040c40c0101d03d00241c1c00c040d6024009045a5a00d00c0e55200340c01c4e100c01d0492141c0d02400d80c0114400c00c0002d190450a2904820624140c042118141d50311000e44400342d4001c4184e4000140702c410b0043c0900c14400360702036010091000510750384000c0d454042c1e421000b80100d4544444240801c0c1642058003541c02e030300e00c00039464a01c01c000900070b1a1992049110303a1484100942140a15801a80c2d400c0c141d0002000c2e605d0325450140c030031032854200045181c091198203030840d900c641d01d02244005845e058243c0c9520b1650002c7e08140b45c00448000c03030300310b201201041da510001030384680c1c4128030010704503100010039140c0c0210940184800d000041d007007012034011000d14041c04040e11102d03400b120b06401040326000700d0100081681c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 270679847 1250 270678597 270678599
    0x40306051608190f0f1b1421060604050909100b03010506130911031204080f0d080106050d02130311030607030b0303181207030303020304170c07050105070822081e0601 74
    0x442c07540c2c0518a91301c80040006a0720124840c0202a40d400518440c40624034050301610300e1f4100184070f0b01c07000c020346210715080c1c08100000020341080640320700086410000740b042c2c0c60390b20071100907150003001d0860519041300e0b490341d42c0d01104030704035041d4101442024941814040c0a01401c0001c2041121160112208000341f404070360903240c1c620415001e50b46524248405000003813154459550781c0d092590192078080f44001800c2690700c40310f1042203c81d4080d107107505650a41c60060384d1210050030083c00b9005e080c44800180500c0d04001082101000d04032402c0b81d0f09170103481e42540e0319a4250f0443d0402070701c40b60903410030024034070103c0517916041c400c0034006000c540030000080400f8600f41c1c240e00201d004c80c0d0b0000a2006009400890100103194812101e140c40024a40180c80c0c0130244282e0b81440000300e4400c0c00c1094078015102400002284e485401050200c1c02c601c29440384900c0b005801103102002d4204400811205900050002841d0036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 270681097 1250 270679847 270679891
    0x30525120503030402010305070329100503090a080702150d020306040f0902031f090602030109020c0601080d02121c0905070915060801050607050f0d09210506070e060f040306051608 80
    0x8c0c0c2001802c2c4402c06030b5484038440340b0a203012134404c880c43c05d00c2e40c00741e118a0342e1080c01840d175458040c0c00306000040c410044c02c0980000c4c1c0d2900594800300d002d0311241148040f8110710344010980110040c0401c1c004080340081c1d02440c4600f40842d42400002130070103000c401ca40c0407a0000c0d405812003401e072004001a03103558208030400c1000050718080303d07107070072040360001c4e081681080d0700000c0f204039101d4100559405000001d000d0301d0300300520303000a90f841c1101c94041c1507040d00811b0715100806507172a242810422180244020101e0349012500d807036207401340c4940c172450a8207014140d4843c003001c00503103180d40c542030b0007a401c190070442550004241101c03d0721031003810b81d0b0f55078802e0010362450895615800e46183c02e0065841d40111428188100004271003c40c002003a000a032641d00401c0c1414603850720405c4c030001c60114826206000086500040c00004004180e80076500c0780007910391100c0071901d105000c031104101503c40c01c0240922003129105 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 270682347 1250 270681097 270681101
    0x108071e020c100c06150608010e0402010c02040e1509010537060f080c040903050f03060315070903110f0d031d091005040c0f09140102070305251205030304020103 72
    0x28480c0d940100c403001d014000002e001403400352030103400582400c203207500700019405480341c14a02c0f00603151381541032440c020300186051090181d40705940740490709590043d40c1c89068190050424400d94400c0c0e41110354481002040c2940769880e000007918005042c400e44d8019a2200f0300002a50140c01e0b5030010a9111320740d907284403855550345684882244100e1000300b04001d00c601c28240360020084c1007201006c4014000c2c0d00f08003440340025401822101e0019072594001c0e02c94440e50086450407500821404003501c4c01c1e0248149150040c5900d401c0364494164001a0b618410901c10040300c44081ca540208449400c2c400103801088107421072a44050741400b94201000020583c20b0f081c0c03401c10045000f5a02400380381054020b80100f4003641c20020725110245400800c82c2d1868860124140c01d01e1803410800e038030030b00c03401c0000d581040840707000503c1c20b25450007095403c2c2520041c52500040080e103e000e12070505901a04038026504603501c607001900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 270683453 1106 270682347 270682397
    0x170105071101060b030109020708070b0a320708091c0e2d0f030f0a051b03150c0310030f060905060a110726041502060105010807 57
    0x4013030302842140d0442c4c07c070090040c1d41e03110340c5c100f80c00e031402180b030010001403c2805020400c0400d803c4a500d50003040fa01512003981b01c2000c1d100f400c0c804512104440d82d0b01d000429090240c0b1883d548012036034140d500f92a0070300d64480503002001202008100140340d02007843c2007841c60b440c603039800c1d514200c0c0d0342e004d0f0b07076501100f42d600c4000052094404c1105030440791814016110041c00c0039045400c0d035620385c9131080d100d20342d428110f0541c40c00c01d41d03494000e103800103c000c030088061150030303000e44805c080c1e40c5907540000c080c004a11888500000010006004030341024050743e00010380c0601c520f006814500c024080c00000380c14020705800c0802000200e07006107610400322110800071034003c109004400d01c15510640001c90005080054451075086407070369079003a03071801d81c0c9400040d01c4030582500c4401c000303041c1d00000140c01502c078010340c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 270503597 270683453 := by
  have h0 := BRFrame.cov_init 270503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 270503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 270503597 ≤ n) (h2 : n < 270683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
