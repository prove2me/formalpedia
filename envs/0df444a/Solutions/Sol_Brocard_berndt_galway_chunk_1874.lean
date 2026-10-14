-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1874
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:59:29.083639+00:00
-- url     : https://prove2.me/submissions/d9295787-c6a9-4b99-860b-7a3379366184

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 336870503 ≤ n < 337050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 336871753 1250 336870503 336870509
    0x7020102030108070803070c210f05060103030e0402090d0308090a0605090d140f040b0d0e030c0604230a060b0d0f080a09090612031808030f13050a050d0308061504 72
    0x15035400001400000c0091083c580900310000046103000c40940d40c0b4401c2c0101c510807203040704004981c01840c210140170080f0040d8000455015103485800c00549868081c40118042022074417a12841d0030b1a0007595030054000b08580d80c148000c0e101680c1548004040083c1e40c01000b034500005210340c80340d280500300784802011a4005200e010b0080300180c0090301b455041071021071490142d032011182078440d01c400e900d49400b8415000c07070240416201c0f0304041c0c00086110001a203001030083c1c8034600800558203403c000310410300041076140b400810715000b08102101044c840c1d000b2400170740006e0702c40070703d00d0322a0f12000544440414103d5268500050902d00d8940c00704103000a410360310300404c111880c0c220b0b544481140d8000060600c00000e4a04080d5400403011000521302803003965600e540c551031210940d80301080f03403410921400c1010609081c20440704d4250380d0045d2881e42441455207090b00d8140000b0030b0103078030807518403025010b0351100000d0402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 336873003 1250 336871753 336871757
    0x506031609020d0b0105120106030e0c09010902030604050601030213050613030c06020f0c0102070e061c17250803010e040c03231e0d0f0e060c1c0819020d1407 70
    0x11100c504800b003055681350030800741080b01c240300e600f000da080f407483d06045849604000400b0b800fa40003046c00c1c01209004a60b0081c20500002924030894000354458035080300e040105503100d0700150100e0299581085440c400040140601d0500c20000c1042d047c4120a410101d903480e95100310500d9a85c0000c401a0000061510012000c0004104e184003d001815000381000c86003600568020aa188240c1519580e40964400c0407002101e981d045032030703108504005e400c0e210a503804441c038500f00b151201300c5a4641c48500341c110034415404032a0b01d245919041125807003000151040c0c400100421000000a080f22140104c0e0754000000c080310540c070b20398040c2000c04006994090078104685480341250100d00090300381c0b8941030140e03400000c80021104001c0d82002c080e00500001090b01e02c0040019410051306120041461503801100c030446442c1015110350b0181e03d030300540000111402c0e000740c103002001e04c8002a0702103080d041002454402e03900480 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 336874253 1250 336873003 336873007
    0x2070609201305040f05070311030f01140109150914060a080102130605030c040e09060405121608070f05240610080408220308041806080a020103050603160902 70
    0x810008810702119040d4405a061034802070340d000403078a0341c02540c00381c4001550f1400000d041080c120006085644c004003142c913066100c1c0360032480700c410056014824402c4842c101051801401801d1464180b5080c0c045070f0b91900740e0003805004035441c4403d14613095000840c841049100341100380705440080790f220300780302051103005029504a40456401006aa1010044401031108481c0700d8580300c0e0342c0390741d600040320140c020f907000440002802d4040c04021580007440900860050301600c401c40c81c020080c400c0c503c1080c003121103500d00d00e01c0d00c2000c5083c04002c2c005141c081c0007050316030b1403d0f07521142082c140080462000034801030035441e5000080c0000e90091064402400c4a91480d40c06440d1600040006001610000b200054020740d1552014600403a4001c6d00c1d1858491810a590303800078000c40c83e0604024288040002701c0c1d018203400c03221600060056259039400450191800070445601482034105035460025000717044001800c42c000010b03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 336875503 1250 336874253 336874271
    0xc030f030a0e010f0203070b07140d09050d080403081f031a0a0b03010c020c09090c040e06070e030a112707030204090609060b030f042d0320031c0609020706 69
    0x2c0d0144814210361410095540640fa03941900041110341294100030640140d50f9026030031500c1c4e9011020880c0240350102c0d14410841a54010491152051043c0d0700032803911103040390b403441d04840c0640000c01001c00308480340b1919030241c00c42c850030b450444889440303480d01d46904114206c640c00306811481000160300309446034802002040f80207010700315030b40070002d554030080c038140c510070410341e0080f4101c0c900410403202c280401074400c0c4809540c904c131054451108a5040c404910200d940d602d0074600030442400013a484010705000d45019420310108010301c1881c2c951030310381800c0710200d8840c80d04815100307480130782d000350342c90307040c20100002d441240c0d010b0410141810740901a114070b28080da070f801410b07003001045560f181d003084c005541030b09030b00d210107480010002c1c0200503c4180010300340c0c000e032142c124184040f10801c1e41500b44601d035081760303001402039141b4054450303d52040700786a0781d8040350f400d40b40c000c0030040f82d02c9504c3c00c40f182e5a03242000c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 336876753 1250 336875503 336875507
    0x5070f1b05030c0307080c120304080f06040212070303020316051e0d030f060b040510020a060510170c010f120e10052203020a0b06060708070b0a0e0d021c020c030f030a 74
    0x2d03d103145043d00503004891800303a12998a604d4400b8042c030601c50005200551b80d402c00c169001041054110348455212900e080e807604415201030380207860701d00c10141074030000503ca00403283d05600071468110b0748841c190305c084c07040e0001c440e1406142003002c0d4496031800d00002c81c940300300c0500f2400c000c004000d030803198807110748001241841402c1002c1a0510140c50450700203940c10721a9600e2120200c2c1400c150a030010300251401050010300150804002e055881103c000300c0f40c0001d8485d00d40d03441c4003980459001400d040c944a031104e00c1540e800412411010001c1002010b00c80c015091465070309000c10380302d46c2c500030001c00e10b0200e0717000c00414002d45030041400004d0b4070000e445104002014182c6010b20700400e0b00354407480c0854410b00d40014500341c030317400d5500c0c086402c00000e4840c5c00610741001850380c0c40300d40109081c5100c00daaa001405913141c1504904443d8032041240d2095005030040c14000ea1002d210b100d5140440b400607541e40c3d80c1110740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 336878003 1250 336876753 336876763
    0x71d1e0d051c170c030a0e06090c01141c151701050f0604140a0207050c04060b0a020706020c010c020405041104020705030406020105160c0b1b0c0c010e06091005070f1b0503 76
    0x104000700100c1c1c074051042000d044440d907070044c4885000300d81e030b641c0f04080d80001d03280c01480000300d80b08a00c100a94090f0108221202000036610070801074008943e4214034060050841c000c180324400a1072030f413103a54000201070b20203489a0501d680d4480b05054204441a10045165151001c01140300170850409030701c50300c200c400b0000c0e40030200700001c030310000800d01c0030354070307400103000040c420704000850120800070024802c0c591036a048400380d070071070300740304000d4030503003a0102c0e40310300104200c8041c40c0c042c2e445040101e02e43c8c080001070a805882a030310301e0802814035170a0f803150b0000740011406400219512494218020700b116402002488104d480300c0310b40300031983c00b02030703a540a90091940015a26440d02034801400c15440302c0c0c20110300080c1400907c10007181030080c0c14400d0300c41c250783c58960014051184036012100e544600d00405840103140980040e0000300c0c000c0805200344900d40d6165040038411940b021646414031030701f0402e600e0304107e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 336879253 1250 336878003 336878053
    0x1503080307050d14010b0307080a0e0d050903060a1e0b0402090d0827010807030e160e10120f0b0c07060204030b01030209060414061e0301020f03010806071d1e0d05 72
    0x1c010005503146c50700c2030400e4040506510200150100400d0440700fa07500f002c2c0612344644141c580356000181c010b001a48401c0c0e08500901400b40000e0310031086104404c141c2e40d0605e020303207100c24a120b1a10040030301000e801c1c2c2c0a82d00380325001d8913895050f4a060210f00c6414207036681c9075002e40c000c1080390070550082c81c03041d00444183c4a0b0b64040003d070707041030850901080e00c0c1408100d560512404140e6080580f010304000180c0b0800441e0340c9025000510b40d6420f0b007520341808448801c8440c0b0040d144481000144001510fa50700107030780071030740d01102410456582c0c4d075403059904c258000d484000b0781e60300510552820045054124000310790810407000c5841013554074a800070300c158400d41202540340c400081243c8014a4421300800840d52000001c2441d8595003003802107070030b04d1050b200054041c1e809521340e82c0d0400040ca0030b202501c107103001004407116201c0450004440031402411541d1100e0f9040c12415104a003d1300806501c100d0f401d001d102110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 336880503 1250 336879253 336879281
    0x105010803180d0f030e04020d020a020607030b0d170703020312010609032f1302041e0320030303040b0703020f040e07020c0901050d11030a0206040303210c0807031503080307050d 79
    0x3088010015090344c0079100060340c5418018103000c000d000240c02409554056006d41f400018540d40302d590110b40c05200702402c0d00e041003404090f030184000c40252800c020400201d00110b0b00200301940f0107004041e20a204807031510085040c4480e52050130b90140c008541359007000c1c0b080002c070028502c100c40008000e903007566000000041c41151b10403c2ca802901c1000e841001382c8156011130b009402c1c1d00800712071061149940c0782d4110342600c003d5512900302c010200002148202c080c0815100600841c2142ca55480d520740441014000c841419070030000c3c100000c04c840040c000a16000d04020454584140e02078181002070078410b100c1c0d560400180040d0350b400c0d0240c98140e400a6600245010400110740350001004010b54000d81c040303800420940e02880080d161041c400071008100d400300042004c1d12a4694550080759403030f0700041406100e503004d40207540d180d0319070400040d40e075102ca80c40c070342c001c1d95910006440024540010364590042c642c030040a2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 336881753 1250 336880503 336880519
    0xe04020d18060e011515020c150903070e010b070818362e0506161a070203070308090a0b0109240f030803070512010905011a0304050a080a11010501080318 68
    0x40440340e101105c185c0a14444c120841c1c2c0c2a1607594420014184280009800d0840450b5508440401501304d08250307403007446202c1010955079041510075040300c000c040102d0600c1c11a43d5002c8594000d540c01741920780545444049903610001803040c2400103465142c50103103000e0f10903900b201e0301403902007000f40c8101032081c40c4c40103180344001e8121145400504c4510100000c45890665100542c060b801103508090001a0b40805400e24804d50008852034140e08030100310310b60403551440903070070034420710012902030060350340d2100c0b40780240c40b504103040e910010800350a812042c50b00d80e840181015010100109405001c0b040360007120003458043c1440c41641d8a0000030010f100100105102c0c41c042d4040d1a4a0825800452815a11750046100030307d824800d142a03080390840035402c82d00681c044a0045030481d000e0403003a00103807120009a40501300401c20008440000c409070702c802c0c0b09450107001c801002c0d607030702c0c03000c414203540d048009580c5520071019 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 336883003 1250 336881753 336881771
    0x2030a0f1b031a0114031e210406020607020a0c14041e090b010506130b091f050901030f09020603180c0307030f0c09020309030d050712050f0402090a05160e04020d18060e01 76
    0x4006900380c4002c80ca03414402d80030301f510080a040c0345000d42c1c021034401110441a900d5400344002d40103031340b042d034202d071b101da41c40e0201240e13a00d180ca18040c151080c06e40050043c034140041300ba40c0b405000d4800700e50b0b40d0031000c2c490800840b0b540308510f41955001c0f04010000412055401010102d482d5401c01e0040422468003520510031a007107d88000390364580d64980342e103c02940d003501011840c0c0b075940b000c000f91180d401825010300080c500f085c03082c80780c00f480c8100140a60090855811552002000c003175200804040c03800900ca140c00d429101d980404c0050047c52140c4c01c00300c1401d959103002500c0421035009001c0d118010300c100900b4140010565440b015000e00200f03241c0c844030b009882482c032056101c84602e0030802080130903881c0d000928000c07032080d24014110764032400d01604a070001c0d00e00c00d0a91b040000c040d050f003442846068000e1600500045c90300103d025002c00b00d680145e00d4070401c4511512030014880c0b148514812064020002d210300b6103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 336884253 1250 336883003 336883009
    0x13030b040c0b03160503150315090c090103081903060f0f0e060301020c030a0f050405031024030803060d1a10032d080309010f0c030b0a09060302030a0f1b031a0114 72
    0x603030004036002c0182c0480007588400302a00401c02c007c002400741c1e0440c08411000b4101c0d880200d80f611068452100351842a0500c604418100d0f0f41202256050a8900c040c8101044480403402e08140d184c82c0003081c6201c4124040004000c0113844150545c50030190455003140208403610a9105104ca030042c04030100803980c42580740d14007403654214024080d910390150303030440c80d00b51040010a002078038450740704401300040c84910f8031020340140c00d007a07010b042c54000180780d40c2c01480400c0c0e0a040c1807103051541446600300c80c91100100c4904001c0080494020341350b01d80d904400c009220081d82044d05a10040b403078a03540851410040e16034151041c1c0c0201000000000074450903001c0d032084a200800100901480384032841c000c000e0028030800c68490701410300c00185410652160008590f400740250810310390075254420034500840301540c00148411240342010041d05a81c0007451141c84086040300500060000b0030754160010040e040c100d001800c51a6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 336885503 1250 336884253 336884281
    0xf040906020d05151c0f060213030803100e010b07030f0809010b030f010f0b01140412060b061801080105060c070b0a050f0d061d0603060412051e04030b220f0813030b040c0b03 77
    0x7e070400030140c0e0300d07071035555410100c414592010f460541c0100030320209100f020709907003c03030718803681d407940036600d07000e010781c46101c1c9000c000e0205110601901e0194010340b12198001e400c1c000001d581c1d052000400d04016a03094811040d964440f403455224462b445040c00c020000e181c00400009000502c2d207440c4618040d00d81101c0800d4846420892640c0084001c0311000c2c0c4243e440d00300d405110340e904540c0b83c2c4068003143e410b00002c5610f0030404c003070b214640350050082c0803036031420218841c65408201712a040050801c05184080000c50003403e1428a80c107001407140e28190308002c00e141d110010507010b05280050010a90700011301e0340d0480d400501c003c181c80d554150546103846044241c000f80345209141c001210444009001124011300114440395601920103002c9402c80700342c002510014031081d00031482151250b66140c5c42488510301d0881142c0c2003001c4102c1903441214603030a01300811041010710812400103050818416007036003000c0b01e8a88030743c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 336886753 1250 336885503 336885533
    0xd030e06010e09120f16060f050a230c0403080a050301091b0e10110706030b030c040506010207030b0a020c06010b07061a090601050d1d0c09090c0f040906020d05151c 73
    0x1c0d80005c070391900c4071030403403045030800d0416040c821081d82c440c0c03a10b40081c000c3c40b000c55662901d03200000e40c1101c4c2500403881001400c0d82041030301e000324044400401c101030304034800040b050001100082c46072000300b2050259450303550f00e0b0361401e038820003a2151084400c00304d04420704042160780d0000c0100c070042c4000c580d40007100f00000c40440c2e0f40e4030b03014002061441841000902e241e010750080d21074183c10b0b03050b54090182c178400d210541d002582d041d80164400d80d004c2010030f0381e4410307542e040b01000b8800361030b007441c81010b41d1410000b0381012003111000071b01c1c5c4040101522031001201d21010000800c0c0e4980f4000070041c0100500c00c40c107010000641912a0590307500c594406003401011200740c0c0d00c01d0b42259603ea0580007600e0082500c80d0114025100000380406218130080c4ac0814041c1c081c1c00703100c050190800216006a020320000815000310b028252003070401012101c0c4480c010000c203c2d0300c4500c209160401d140c0c5018000104034104018900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 336888003 1250 336886753 336886783
    0x60906050403080f1c0c02011a0306040303051803070501150e150f0301060306020c16050a0b0a030c200c0108070e06090d05120307080901050604020408031909080d030e06010e09 78
    0x200d00340401000c0c5035105e81c0d880491210112415050000c8079a400410254440c2d402001003c3c1000c103039900100c000001c855040e8842400100000d209400c500c4e444005e500c1841c90207040010315a140d45c00c900b0046600342d4444280d541d210403035440c108010400e543c6038010500b400c00d044c0801440300d214082c01000003900c40302c0651000d400c0740004507881041150344841c201041d58407080c0512007400394164003a030000b40361030202e100000342c074800c0035428030707101c84c03543c1c150014040d60355407409200132661046100d0250790361a13000a070740f40717028140c0220000001003118500800400502082062030641c0e0744821013503811001064600130480c581e941011807a12422000505180c0000020030481d540e0000740140a440400c00a0049882c1c5d541044207170302a60080c81c500707520503c01e5403c1c0301040400c0100c103d0640c10010992500d41139014100b0403107000a902107600c41440805400f820441c82d401070044103078245641c00c1c41411641c40d0402c0240d020a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 336889253 1250 336888003 336888007
    0xb0c0d0e18101a090a050d0b01150c0210020a120207060e15120c070512030c16020d05060106030222080d050c190311060a05071428170106090605040308 67
    0xd0318030044428040501594110403d6102d03080007620844d50214080c28044c880241001815050070120100a180e0005050304961701b01980a0f44038040300a46608000c1d0906400001d41c0380c1e1001c010319440c440c0d004c1d200502c0c490422001c001c01410340c24003150302072401040400c2e030043c403000050500f1640303400c00b000314049540482c02040320010790050b510084c000700c1d1400350010110725101f90160707040d540b42c0c003d603404580812146505055030070030444a000382c03060700402d00c072071004001101a1102d910359910b080c0090300700c000441e034001740c8101100d8010308520000c1c81d0101010b01d0032410a6103c50700d4690b45130343d200074454041a40907407500c061284146a1069403001144440b013410300401600c080c00d4001440c0c0103a0700422584c2003603001c0c85101d0b0440e41c07500c0000c40c141c0040b080c120390001e64503003030124803940507a1014000c90b00b0b1039407949143c0c1c2c0d0106a101c94064030610740301d041c3c4c0180103008021400f008569000400e440c202c0742c100e03000c0c031303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 336890503 1250 336889253 336889261
    0x105070e061902101401170a030203091002030c120306040f05150d02010c050f06070f0e0307151202041409010f06080f0618090a03090609030816050114010b0c0d0e18 73
    0xfa1510070700051040c00d0303504102c034000304001245402412580030243c006c0f000701321181000d44074003280e000607005030000c01c0100300605001c584180717014000c2c4122032030011400c94950810200624441d03071003c00206008062400b80100f000c0000c0d0240c08100c3d82c02e100c0312507042000c0340021a4014410844540156030140b4280c2c8040c0d89c0080640d00c3c0d00c0741ea185095181c02c4105d81600104410440d00c04042e40f18820201c1441c0028004160326820480741c1c800c4c2000c10030400b410041d20f05003805402aa030300240c0024a883c980c004180528201007280b1014143c10030786035901d00c0700d010807669034440c00040c1c001035154041c0900d9141c07a00031441c0344044011081000040c802882048440010442d80d0580250386c3c000420740c40c2c045c100c507151014400a00403500501600008503905140c85110314801d200025810225040c0480580c100760703c106001803002c905148645d809002d0280d034003140b8903150100380c025500084510080c80051500301c00c2101c005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 336891753 1250 336890503 336890507
    0xd090e0604060803040609150e030c010c0203160e0a060b09030601090513120c20062b060f06030c050715020702030703051c17130b0903041203110105070e0619 70
    0x28142c03c0050760b42c1c0303d850310000f510104207842001000150024003600451080d556404440002406401103021400044407400c3c08480241e0b418058000c0f81d04162418183c0f902c01031005280704241d9107041c10103074045440315030200040d070804110441d110781d80804c900341901d500910004445c0c88201c0020b610041040000300700320b103400800320b01075403c0000e58561920500c44080780441e0107008000031800707010400e81106060000b83c103044000300389842c10103202c0d0380184c2d4181c500982d00c03041d91a603501010000a00303800600400c2c0e454000e03034001c00300c1424840d2506055942e030304a8803280044003a141c40d8041a0b800443d5014040c882c02940c20034100c448454101c5452088200205006404070307100014249001045030040b9105403281113106091003015118084550802003001a140c0800c00010500d060043e040242140c001d6807524285514032034110f0840d00042c1c800001c2c4101800d0f02207495981100b04d4210000c9080642e41840c0c0c07030001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 336893003 1250 336891753 336891761
    0x61509030102040b070b06040b010806130b0a030803061203090d02011407020405010f2c0612150703090b07031a060a03020d09050313331b12020f0d090e0604 69
    0x4040e4503500000c0e0005042c1c1a21001d072031041e0040c0e601810360b4440c41b040100b240e0f4424001c80c0898000400501e0134984002540c030022200100441c140747d0581c0011320b00d0002d5001158181d00c08001d01059042901041c2c0495021a00841c905900207001a000400d00c0000a0410a11104210368414140141c2e6555903001c0c0051045d56113503102c03918ec204030740c010300e0000c50b00140e0003c07401c4500c81c803c0c602000c0d540b20b0403000e0344809007400544010b18440584900c0741c0c1d010800030140341500180b043d050746c2d80008140b00d051800000006000e410442050b08005107400741c8800e815004032548811160503903030b400c1c2c00406802900690482624051600c1a60810710002000074861003401c140c8400c0541c0c2c407089854403c91603401b1066030b40500b9100b00100401c1410540c04450b55800e141d03808000383e541111035071111910403240c0c00480542070002c3c03074040141c0181c8405500c0645023403244104004c1c00201c40e4855040d10310b80c0d07400400c0756500d13a980 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 336894253 1250 336893003 336893017
    0x8041b090e0a05010b190e0c042105060a05040317040c090924150b0703021509030c010c0503070507030e0f030307050610050d023601080705010e0301050c030615 71
    0x6115030038050100c079495100d0558161115404c00043c0c040c280340c0211504c140c0711011070403406c42400e01c44003140d104c4000b40fa240c12070208006c00310b20b100d0040504036038900002203000c0381110a28000341401c8000d010910303010b04003028800002d42100200e0302d04c41200500035810394039401c3c900c24020540e030019401c2c0f4a8078200c0c0c4144554820320510340300f070303100100d030790003440c80d028408413160004880562270f5050400e212500388200248080c1d406403044601843d1900403202031a001a903c01e003050780001a0007031031507001e0045142d18002424001c7c198134080703e0145c10307441691801420031000c9010601079548844240c0e43c00030014080f291180180e14245a40c1e010a40341c60100c0035034064001514034040d050841541d03070240c512040126445e9062070b540c40d200e01c103165151100c4190348800310711042c0703942c0205400e80003800100e181200250200840031440750182c1d0502c0b04211b518503031071003140d401102c107460a4006048034184c0402d240958a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 336895503 1250 336894253 336894269
    0x9050c0915011413060c050c030d03020d0f061a0a110304080d020f07050307090507050912010b0f0415060c0302070306020d0624090308031905090d03110a08041b 71
    0x100602001440041d4012103601e020b880307200c0c070111406904070250091091581da000c1500300240039542c89800b15640303a510680c11076034000c4420000a01b00004280c1050000358003290a0000c61228000d03400c95000855041004505243d00c001003618400d0b90012038680029007598032501c00e06040000d60b88803016207131030369240c5201c5512130b104074000c000148604004000e42c80c80110b81903048902c010002c11082e031505503c103002d084000d000909002041c000200203483d84c03402803950528050000840300c06150804c83c0c1c1c0483c44413002d000c0c0340703080700d840c0b60036042c0300480050300c5550601001103100c0e85070492502031590402082e0318004aa085080c1c5041c0d00300da403d59070b2010503100c65501c024040f50081000600324400510850007c00218018100443c1c01112070b00b8210140c1c1c011034035080964000b55046502a4003018032101000c0d494850103003842c0d20261614034103000000000c01641025201412080d1010414031a40c110f2448200c000d040c14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 336896753 1250 336895503 336895519
    0x1c060e060a21380c030105040c1e0c050709060620032205010f050705031801090f06170a050108030409050a0b101d014103040c0306061a030a09050c 65
    0x104500d80c110f00607004182d41d151980d1510001c0303601c030403001c2c0c490940720302524116860801000090308040094030b05106c450001e06440c0c2c01041815150318045494000e070f507483c20b280651030080a9403161803500d25088042c4459031b400041c00502c8200134254a0035080120b0b0600d0640c880d09100305481c1070f503610200b801001141030001211400d03240c1400800242c042075803a1722418030000c09075002080780700c181c0408440d0000343d145041c90300709400e6840780e03442090b02080e0740001c4003042d51034206540c400761032060381d9449504184244025454811003c1c1d0360f0180d40540501e0517107410025040ca9665400100d80704401014441e4021840201620308500140085140312412407500300c1e03075001c0d4403844003030354944c40340c030360388500911010000110300850b040c802c040400180c000e0000d40000f40d4043d60003081da1856161451a00c0c0c811034803d41d20820b00c074174500400c4454801d001041c1da030700035801c200100d00c5e040310b8503185082440070700c0302c03650000c0b007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 336898003 1250 336896753 336896783
    0x110301090c03060507091203030f0b060c030c06130201090b0f25030e030c06030a0b0a09020a080f010f0509130212010e0d0f020c03060612121c060e060a21 68
    0x941c1c2100800c0b80e0080c5010011034498203012164115140980b061540040c084d820001b4800e50103042d05520600c0000b907080001d0300010303e07a51228118005a60001c00e8051040000b8002507411030f1400c1942410900305500191400d100d0f0301c2100800e100c0403070107000b40101001101c2c24207850201180410f00e2061440c1e030200b801e24010b40011710301144050f81400d00140348415190300411080c00c44e51101000c0000e0f050350400d05801400012000403400d81a0003c0c003650700c00f81c0c40307400b50761410b500410000841603002000c4020710100410407a219103042582203403400c0d00300c07017075500b00e4004a42c460304890040100f5602c0d0000208440d80c01141404404d9581e03603031580c54134600c020480c2e4480283d2548c80e0316801c414042281d502c1e15200c2035402c108640c05071482020424070410f1641c009601500241c0d0f6604103104c407243d55840f4403070103800301c21041c2c120b50501c0404a90b00c85103c1c041d02161814810b82008981c420000150541d50300002c1c101048a03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 336899253 1250 336898003 336898013
    0x10f090909150501050402031312052209050702150a0c2607020c060405030c040506180117070e09060a1d010603030504031a190b0a09060303020a140102030702030403020d11030109 79
    0x1400c801800b9103503207004004501c3c3e14081c000c4034003a00c15500340da58908034a45903c13640200325122070701804002c0064500d84041d808044d42400490310000c0c40d9607240c00c0d014810344000606580c119000381000e252901d02404440d500b18003044030005000107059410b80e180030710820b0880030112000c1883c11400e5200102e40d205240031780c2915a200c00302011b01c0382d10302450040c0d40e071580005804018604060340301c103621440003001c0603044e10403400c00c130082e001c081e004407100903c0096103a1134088100200c0c4028900c0801390041c0e4a80040d440341c866201800003a0a1600e030072100215070a1118140910142c41e8000c000d050f66915001c0c7c680d5010348401c6406001041005a40001c140d4855200340d010113413040541c04100b885100401d0080c80050344502ea43c0c001080310b0101d40301d445d01440c8260020084000d442c18204a001c45076896180180c0c010070030450019030100031303601120381c10349419901003824a401e0500d0b040b4115142d41561818201c40309200d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 336900503 1250 336899253 336899273
    0x1e080702010908040803180906010e040216060912020c0603040803010621020c0c030606030f2104030602071101120b0a120c1d04030f02071401080a09050607080a0f0b0d02010f090909 80
    0x240380c209947e158070a20300203005010360100c070b19a020070103501d1440d005040540040450000c11281c981c0348542950341c0304104d681880041d54015049031001c01e200741c042015040c0b03000103c0302c8a0451405648181130307803205005900810060b500a0a4440c0c1d540000054442c00c0c0341040d91074504014429035200003591030b841c401e00c18140401c1c80c5080110750148401348000c0036046001390800c144410f886034903000100c804c0d08100010100b5554405003074494421810350070004070700c100042401c0d4101810f40c050920748020400c0e0307941c44501010841d0003084400c80300d02e1041c100f0800a540c2c03948440040100160404080c00f00001d40d0b521803403080d04d5900c00d508030103400320fa841d1200d0081e02c0003070b804210a102d00758017403d4025031040c0c00ca04003084009041c1d50302803d0200a6613450301160512052041046290082ca080440d51400c100804200500013580301d6510a50113414003c030f0081d500005403240000714050036000d0030510002d412498080044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 336901753 1250 336900503 336900517
    0x60b030c030a050c0301150806010b032701050a0f180b0a02070f0c05030f0a1502090a08010c0914031506040c0c0c0b0306100302040b1e0c1b101e080702010908040803 73
    0xd518150a00847d00740400d84407007625044002409960b00b400da00c07480a500140804d0340b0180c90260080840d1041d590100750f41c92424000710345802c1c104884415100341c00400d160003810102d45602c03a1210705030342d03211903030055512149501c802c072070f0500030300c5100c801809046030050341c181440070045280048a400358121001601e800304c04945998540000030081181c0d024081e185424a80282000800040075950b140e581d680fa141c1c00c65158400400110b104100c04004014044400440070071050f40039101040f0b1011032186950b50041c081031241ea50340c61240035140c8114507512496502100d068007507512120502d00c150030803074038944981310609100e88100d10900a40c0c044540c00300042d070614540345a034501d080507541420550f040c003800060107420b41000b02c040301066205810840050020900c044041c4120703501c400c0c8004440402c20280a18103050660031041c82c010b20682c583d080128098100d504010b0a0312801240104180f90040010504 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 336903003 1250 336901753 336901759
    0x22152003090c0906090f040813060e0405010b09010f03050406020702030601030b182b11060c04081002040311010c0c05040516020d0c030801062001060305030a08010b070f060b030c030a050c 83
    0xe89040701c03c000c0c614004441c0d0701d42000c100380c046142441c44400c1c550300140324140c500c2c20321044c1c1d4030500800c5da01d607219000090b03006440f0003031400c0c184076050141c29064201490a4003d20000c1c180d420b080c1000010103949100007000c4c0400c0f0340c10780303e0481d80203041c0c902030759490401c041c22120035100466191200c07601040110000074500d40c50303500703009820046441d400b030380010701007824440d030f070a10028200c0c82c0107001e814860184600c1418120310b031514181081e0600c0c0070740004003906005c0c410402880440c018102d1030700604024a442586140240f400d0200d550056003c141c110f42003505210211491a104085400380c82d402c4821000721a00100e544130b5450f51b000d8049078201d40144107885c45903a00c4e034188141e6100e0b546a034020040710900b103804d41e500548060b000406c0401c40c0d282d102049a00402051b6469410540b680e1200c60003280c1d220001000184d5903454803080340c8051210351158103000302034070800c0080d0709200d41c0383d001903292588 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 336904253 1250 336903003 336903013
    0x15080615030108120c0a0c26030c101107140703060b030a02010905060f040807080d031b050d09020a08061f0b0c0c1e12010c0201052215200309 63
    0x2a52880030203481c125440640100454141c1001e1114280d20003162028940229070007480403450403444ca030014041c41ca82820081100c650303c0007407812003801c861094200304051020480300141d04000d01c040d40da0005440703c080c1c42c240500b8441c201c0020004070084001421040010801c401120f00540041c0400401d40307003050340b0355900000085c0410303484003041c811814054040c0000005001196180603101d00a0501d840025030100f102a0701050314501525031501400784d103403103550065507070030b18521300241050007511482944903545050b600e0965036a41c828600510704141514003e08043e005048010303083d0301c80c0102c14104000c0001c15a030381804690342c3d034003a140a000d000f0780401c10409603619001280c3c15a0043c070b068080c5070f40e130394490030240318000d00000070604210710f8061309586004042c4080c1c200010b0070480d0001e205e141520100751b0118002c411404203070040c0c0000c124411440c0c2c100b54080d4800144e18a014004500500b600c0040314 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 336905503 1250 336904253 336904279
    0xb1603060b090105070b06040b060409050412030213060809210702040b030f0a06180c06020610050a1202130e1e0708160b030408090315040b060a03200406150806 71
    0x48141d104030024a40010340411170b81020607010707846950080c80c028804680c100000c8002995604582c0002408995a00c240400c0102004015264410605095060100300000348540220a04c5000305000c10384002941c210414048200c0f002080000c0c3d43c030142c04a40d055809402c01503089009500d013604040e4189000540c40108000070402800303245100d60b541c001a08400461100040c515161800043c80060002c0c000d406581d008110070300e014803040780584000c0c2d12250203041800c101b44488151490507660316070301500c0e120f020280d1040280000c1c084090344009902a2a90f4520380c81784c00420f46200c5088070086844407601e0300b048a0310703940b90b0f103414107004980303071010880f1001c030f100a1a8007138060005107082c89040c60110703007004001411304480d9841c2d14204800c000c9012065074000d0f03800d440004a0b10308513a942040000b003000c1041c105602c001e0318483d00c2c0d940307410503c0030340140848903280200c6e0342000b0b03208620070f13030361144544c00c212840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 336906753 1250 336905503 336905519
    0x5121e0a0914011d010e18070c0c090b031009020f0919060e010819020126040b01090516030b0415030b0108060106080c0702060906092e0c1a130b160306 67
    0x1081114510340303c4c211040c0d800708019100364080e200501d070000340c25403c2c0c2c02002014000c80740302c1e56198480342c81c2c45840745414040d0032056001944150716107445408191000034041c000c2c84004100041c00e032566000103044290f50358031041c1d001c00301d0b4003040888001d80e640300300d40c1041d200c41070200d20b0b1030307031003030351081400b400303040c0301580030205070203481c3d044840f944007650040c1050300351150140103540000c01c02803100c00745a09420107100801880514107401030528240402c0941031503481c4105e1454291291030405484004000b000d075030341c1d400303400c028182d151071070200b5039646405180c580c0244103103030180c05030302d00005a41c0d008400303541c0306a000346480c41c50036003194200704107500000d00050700701106004071030a40d00d68940d07500209400103c071032500c40f00c401403940744540040059041000980b1858005149031461070803c4440c10f0540e42c2d00da42d10f05290921202d41940034103c02d48200c18400d8903116113185403136160a5607020300c209600d44c0c1c14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 336908003 1250 336906753 336906767
    0x30b0a060b430803130818010f03020301060f0804020f06070b1819120e1513150e0d1a0708070806010e13020d0e030c0312010e010305121e0a091401 65
    0xb0b6500c0720320030703103060600040e2650002c55200d080e1000d02483c0c00d42c252160a44d07500040d151200c800005900400301d0340e000a910080b0f40c8442c0350035881c0d5810014000c01195841d6489001d000310500820304540e68000901c0c1c3d044809007400b510b50360f0600705003040c000d06550100d10f0440903403403124041b00100d42a42d0ba10f00c4400c814080c0e80c11590354103032028040b4902c3c0100b00210401a51554800c00c0040c0311a031049200c644520703100c084020100480d03440001c08400301540c0448a079080780c44004030b02e00c00c0307a5407000c00806040400c500e5075034800c001c802020036000c0040760303038110b4007031030203044165211095582c0d0f000c010356036052100d1207141d000901110803c25540a0b40003072010341000100892000305101040d4995089000345090030703080416001c259001d514452801401a424100c0413540745031160b1340c655410701c1c80c2c01d0444000080420603910b810503c40c1c035101c020845155185110b0100808074402ea00801d004901c140c2c41d0144070f5032007915 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 336909253 1250 336908003 336908107
    0x30f1817070b0123030a081c050118090f060207030c0b0c2a0c03060a0e1515010503131406010f08010e060622020708031816030b0a060b 60
    0x301d5072181d00b4a0301000d076139946100d034800d02c03a1440c0400c005649043c02401007191007502041e40b95090b004207401240c0750400740d030865a15040040202803002429005d00a050110010780c200d401d05220080e5580c241010b0300b007030300010760f190425131701a1043c2c0301c1500a070080030a64540d070800a0480c4070ba10500307913541c100c514910441041243c90700b030302c481c0740d07070122258400c0d5040071030b080a07002c6070445811070f50340c05c070615400c400b032014440c0104c044072030780000d1810242a107802c0f0040322007035040240100001d03600701d00c0040006051a04002e4120086000f04c001550701e00003401120b03405051060000390b15a0140a21000300d050003014090b180c0d034000a0103214000d0b2800c1045410650703000c891521910320040405601403c84181e491410b8412046500c242804c450074560140791042c1c03840b1782076000c3c2d00c19240d011075813100640722041d00030060606600700c2c002c1e000d0009035080503c0e001c8500182d14054030380040640034110b20403541e800d00c10344 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 336910503 1250 336909253 336909263
    0xe270c0a23040918050f0a0b060a080a1b170c010e01030b180606041502010b0405010f050a032a0816050114120c12041a0a05070905040b01030f181707 66
    0x2100a2003d4141900105203619a440a0081400302c40e19072074904210464a01215048281c2c2007040c040f1282c80a54070a50944808140514240403e6a11130307007440085c240f004052001036a03050b08062441c024041b01004208240c1840071282d292800b8400e201e010a4421125a80c594004d01882c4d01c0c0c50b80041400c0d0046545500055032810001c02503540440c0410010440510300c1402c01c15844480d800000c070584088203120840f44180c0000e03203051040d8108000342d59035000c0d07050a503688450112040d00003009030582c40030420f2881202c18980010205243d40000f0303e282040c101e820a400303d0966402c01510420350042480c42911420016942010007241501d90030000080c2564503202d87c052601c1c15000781507604541080102c5100040042110007198000101600030070081c02e24000c0a454000c41e4400d090159488007103c0041c2d13802a4020a1101400c1344140000140c00440b07505c80c020104040728607020480d0006146c0c14240280c45055600c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 336911753 1250 336910503 336910507
    0x6050301030615031b08010b091513060e010612140c0412050a08031303171003061e09080a110102040b031b0c150717070e270c0a23 58
    0x15032142d07005046500030020004281120000014200c00d919040001c0c409240c0b152280c10b202d0340034256903619200500c11b20b050000d000c00390000d14002004100300321030001c1d101d9950b55080016007030301c2d441030320580c2c01100000b803210f802c00140c4501583c3d0321400c02030307141540c0080c0700203c420b81d01504401030a00041c098626020442c0540034041c0e0111030031500b50396101e000a40c011242503040c04034203c1d10f6410150480d8004d07074000e02c003000c511414501440e11040014281c4009010140c8400c0341c04525031b10b162084040740d48001c401d200741e40d6682070503e00f070380c44138503503200151145074910103024046c420344003a50302c440c42007441c58840030300070003c14030034112109400c2d004000400c0c409004020342c51402c0300c104981d0345946421080a001c203c0800c004a0141007650100311000e5800041e07100001811101c104043d40070681717041c01c420a940c0300010140d8908107100101d918074000d0320440040e55501c1c031940311101c813484044032031070130320510050302 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 336913003 1250 336911753 336911759
    0x71d01060c03120c271a0a080604050a020f130602160e0f090c120c03060109090b04030f1e0206040b060301020a020706080402060d09060f0b120309091009052e06050301 74
    0x30a4001403100380ca00e182a100d0281c41c08590030b05071010517038501482d000c0102c2080f40c0104203003042c90707044a61000c0303424944005c0b4042c14086004220f988507650760780015071140201e034180d4010b91124228240c58180040802200c4079082c042c1101510485070745001c2403552039050015601c5400954045407104042e00741a0200038010f25070340d000d4210045456103403541c4a1040c3d2864100500d5199001c2c0d0600d4140350040c0c020220745420111042d000c04e4100b03001681081d41460035098401401c08216910708500103801302c2031420481c45804550b00040f81030081740a44141105034440004150803071003900d01140241e0406c010400902d80181d00982d44980003404252400450364030110846036410380031a1100d94425078603080f400300384030b6074136078240075900010710f00c1034500050b9503030042081c580c4c800c540140028284e00b08400c0d40380c0044c0350f0160b007031110341003a00c540c180c84042c0d1101901c1c1c18450907402c0b8520440c40000e1000c46080391107031407a5900f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 336914253 1250 336913003 336913037
    0x603150e06130f02030c030f030a110c0f0d020414092a180c040e041202060603010b0303030a0c0504091a120d09150216090507020c0904080d0209030f071d01060c03 72
    0x4403e080603641401100a074001070b413030520070300d010304600201465072081c02c0900500100e01504046420341c1c0283e018441c903072507552044d99141c0080f2004c85c01c24540788001000f40120f144600654034002d820b00062082c0002d0b2a000414070a0200c004071000c40ca0741900301d0b00c0d403d0b14580c49420b1508009040f00303c10900ca41000c0181285071a00c3d4441c895034407075800c242c908450303080400d540c56418a034144503468005104a0003842042d03130381c9000a64a000227020904035503075411203462414050400c0704c00130041d03000309120f50500c221100d00e01c0e4541d01056402140c18480f182c00320a0045001141c8075a05c0c1c903410040340c206040085841241c2c91384400703510400c0031400c0460300060104c0c00519a0074004980e0f840c00d00070003400c00146140141c000c120303290034403002498460640380802803980c0c0050301d9030600b000080c0b800d080104c1d9003003070b405040004554940803a1a464491a0b0545051142d90b6260300464401c1e40c07100d800b600050070240c4502c5402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 336915503 1250 336914253 336914273
    0xb01021609021303080c03031021080c010605031204030b0609010e010b030601054806010506030405120c06222f030d0806040c020303160507080403060603150e0613 72
    0x4006540d0f1070201900ea590307040003540000250202da0780301004010f80150010f411a001e41074282c01004807104d8a4404c0d8901c28408100801030301004c581142807040c05d500070001060018122175845442c480142043d92190101351019483c5500041660034a001400d0482d00f500c52540103aa1a000400e1700b56000581a81c0c10020108005038a040c00c0d400f650400d030881480c00c14903980300441c480d07001e4001036580c80300c0c0148000d2405900c030740450041d0454005030f82c881da8a580310303e440b03400e100701007840032440c0c1004218101401800600707684130f42d02c0001030803003001c5032000922000d400004000c000300c0d5030604a01b100c2440c281503068960708680340e031101a4909002904058003620101c0024840e003040000c00d03c0c1a0064005c00f43c006d0000e1440c609111070003c507041111241c0c2c03000c1c8080021090b08002c0c040c02110001c54216004120207910f9140c0700350503401c00000c042e03e25041400c0d25012010100c0c500e03000e80c211000c1410b2480c001c4d03035542416 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 336916753 1250 336915503 336915517
    0x915090302030f0706020a02010c03051017070f0807060305010602070e07030903030f02160303050c03072708071419060207140303070203100b09070c08030f0406021b030a02010b0102160902 83
    0x140024092a0561020f08010b00000c3e4030803900541c407103110401c0207013164180c44482d0f0805041c582482030514959591400b03544603100100314000001c1c916925108440e800714541c00140c1c480010313006004a01d503010303079259075810300059998801c12a600d41490065840d5040070b140418602d500a62011031101d01c03e00b8042859100303048000200e030040303e0140b106442e500b01c0c2d0400c2543c588601c0b980079611030311090440c200524002d1070044000c030070340d184044064004080c1c110036901c0200a041c402d0031a200c4075200c0b20b8a200d408000c00c01140100c02e5094070070043d80c080100fa5099075010b9000700300c0e1914000b050840107031110805c0b501800108406001f60b20144402c51002c24265804124030010074240711400e03e0003003200003085003040b4640b0000c0d03034490481c1e07006407982c103903000141c4803070401030300a2040c0689103080b002c070000030103010352020010307080400464008001113001d000040ea206e5880c013210b04603400406c401405113000b140e002c0c04034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 336918003 1250 336916753 336916757
    0x302070b03130f05030301050a0605160b0402030f19030e060c0c01140d240b07080a081801090b04020307090204050f0d0512040603091104020a021020070609060f09150903 75
    0x400c100343c40d000c41c048060b403000d69281e000000180700d603042c4421540c00034404c500e01286012541e881014002809400061048020001080542d07800b0801c5004240d2031070191184424041c4ca14030524002d061f04030b000c907420440c400300f946006401e40b0070110301800a01808006032004450000303500751a280030310001e00010b095143c040c422041c0c005015500110301c2c02d410540d01000703011640c407042e030a403400c0102c80300142c8400c3c156801d10032581000d4010b900d81f8032072030700c1030070710a402d01c03d4942ca000d0301c4200b40300005a83c035000314001c0e015209460b4868001000740c0c03241e400340a40000142800e400c1505040c1110f03c40f813402501510507204040030118065070140d4800300c000381c1c40385030403410700c0091440c0c071080500484045290400714a0069220048800031030074103a03032a901454144203104500034110425009256140d4040c070785000102003094096416a00e84500302803201c00300e12540d488260409150409055408103007400340030fa840003102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 336919253 1250 336918003 336918031
    0x605100b0a0207080717032d0315090a0b1e06070501021b0d03090f150b1003020a1106040209010b030712020307030b1903150c11060907050a060503040302070b03 71
    0x16204038200090841c81d202a40a46610752411400c20302c1c020841c1c110454803034100f00c81c84090b1100108461842000321503521401c4140c64000c81d1a4010f070300070200000000040054014000400d036104401c200e8810140742c13101c028030001c8a4001d54400c1e04443c800b01a64070000507803a86000c4071100500080c5800b56a81d5018260307000b179070320100040c04041f40425401014040b805545103145020000300c0000c0c1c80c2d01440781034a900c00340600100c0c1213907c034810800d410480c0c0c02d500c007422100c1084941c100c000c00a50100070844009415840e041520702004070340c540c010b41d0020f00442103a4205504100c1c4c590000c2c0001090141e00e140b02d5140e491540040c620604040d100029400d00e0390f010b00009004000790b462400810b840b050001841030b103d140702d0700140407400948803c20040903140d144024400010500c41c1e40100911a407001916005a503810b4403140d500503540c0d4026181c0b40802c0d01c009000d81c10410b400e0204085c0c00d0003031603200c503294030900 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 336920503 1250 336919253 336919259
    0xe03010b12010b0307080d020309011b0b0c04061103130b090112050903070209151509030c041a0f100c1104060b12010f080f10020a091701020c010b010806030604060510 74
    0x5501614424452032079075120703403500655140500004009054080150090300b500c028000d49900c07481c46410b051145c0002c5200503203251250040c0100d920541c01801070800840410040e0020321458000858907400b03e0340155010041e1040505035a461000542c1000c2c00240c894024041d51410000140ca03000b03007242c2c803401483c2c0039001c3c04000c0c50780d03111240144110114020103225540489602078000da44503445103e8200a0540c80c0a458145150005c0d090030b07180240164020300380942c0300751400e15510a01c404000c01c07202030400c0c448105c203000d144481d030000a0040380b40369111501246c2460410600c00f03400400c0001c0482d140c42041101da0070143c42503586014180062188000d02207034180074101e03810060080d5046100401e40d41d41c0c4044000052035008201d030a4024040c20701100a01154202901e400351039a0f4018000d4002d40e210b03c1b425800c0402006165000d540e485000e00c10280251001d035446485a0303004d01400f611120441400300000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 336921753 1250 336920503 336920509
    0x70504180206040e0405010c091d0703020408151801090201080408180d0605042013020d1506020d020c0603061e120105070207091a060403030f020705060d02040e0f06100e03010b 78
    0x4001620b42c0d40500e001320f04044c244582110000c0e514042800a8401c060000101c40b104a06054034940b202d1003040e40c5010048003c0c0c0142d0b440b0410030310035484030150449840040700d00c0360b108883e1445075481e001c3c1c8194240ca10980e00680460400c0000c00c0102d2080c41c014001003440c000b201c0324403034424000c141c285280007070940d402c0342e5071000d1204004a003a10700c07078505130f05520740020b1001903000a0b408110b403185e02000c3c03540010466203c5007540c2110582e20300441351103003074540e40c00001c1e4445001000c890018014060004181d10303046065030300500c00a803021598000a41c1e603e280c4100a80000364054900c0c02d500200c0042405441e210b01c8042d40a40303c40c034a0f1207002000d803038043d0105007410034117250401c0980c03152400c0d28100c9815141038085950001d8050b42000515000103402074000607180015103000d400038421500c44580800c0751340e07a1001a68011705d0306441c002e84c0158840480100c4510811703465141c00380080000640020300000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 336923003 1250 336921753 336921757
    0x61e07050f06041a091623210f07060207050f1206010f170c030d03020310181a040b130f020904150501090e15091005030a03080a11040305070504180206 67
    0x10031101024105103010700701c41104000345c1c000c151200100712036083d00038560403210b07642c09003185002194800c09500c04080065107101d0f03138090318112804200b82c4c2041c8203514400e0510003584101000004200b400207001d40441d4050380c09000f0080c2030404026050020610259108080740117104c00414203000c09402031040c0e5280340d10591620007a8240c040f41c5444400b01c94100481102d841d0703c01140d40d102c91001880d005949540f5109503603d00b4802d41c11654280013480d2006003c01b03285e5002040d084201200b01e00080304441c1000300f80d945d04807085d5000041080c1c44491401d01750808002c00038811000b5080c803502001190031185281d40d0515403000710b484c07c00555800112003006449000040310b01441c08101d24041d4240750b440303040c0524010000070340c04803070040039400684001815a240c040a90500401c070303030000da070585606890540131111a00039081124100c0f0352003005006c9881c501002c2100600e082c800212100d001c8110880040c0c1d69080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 336924253 1250 336923003 336923011
    0x80a110406033203040b04030f1e030c061a01020a060e0106050303070303061e1d25020102070c0807050a030818040204034d0301090204020c010911061e07050f06 71
    0x40c0103803803841211030141c0b0f0006901e581c4042d0010081030144400c820125000d070780c1c11a2052084917403500c0d01100c00c401018000b00c0c0103415081040806500143e20a0b00c2c80c02224248001a410b842c0f815061001080240c0981d108101c00000a03030560406103400c01c080c0c00004003159a0780200341145d0204200b180000da03070310410310281224404990f4840080c0042d09805828400745107029400d20f0002d4101c1641140000c4040c1400c0b6120344c0c1d0f0034456084c05141d1120310a02078040d4004600840e415001080040f901c010b0001e402c8003107400050158403007078556111100a0383c400884101d40664400c60000e1a07203543c0010002075200f064083c40325049618400304401c6040e03180180c070484030324406140306a8140d100c01c45100400b000d84042c0e107200c0042c2c010b00c03000900a4006d4001303d510381d820384040d0b12010083d4014411881c60140d01010424144902c00e000803e006013080c000c110780c070b0000d0203820070078403800880300d5007030001449510f0407000b2a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 336925503 1250 336924253 336924293
    0x503180f0106060f3906090807030e03102c0705060a050705071401170919050309130209060412082209061d041e06021207030b030601080a11040603 65
    0x1001503040590118005c00a0012082c801d110006058840c00007421031000c200781642100c4400340074002c00e0781c040c0458580c040e5590b43d541c0c080e03240c041c0040d040800810310034011003169124002d070b28081c50681c0c2c1d9201000300c0540c064610480180c495803c81000944203112000c527a60f12007030020009001e00e500c4407070303d407400791034020310784100c0f42c10130301102400302e0559200e40d030400001e02c01703960502d12100b240d03900d02650520340740d07a440380c45030356001c010440d07401d1040c040f0040034043e40a171207512580a003001031105a03c60102d40300e810000401c410444064074985000800d4443c40f6003a01c0c01303080006100440d140c030300404000030040c10741004404800d00c03410b40100200020301c80c504090b07120360b12440d10010405401185000004607040c50310308020040c06922080454482000304101950800c0845802011a01c1c1009109992074001025412500d1520003401d40958990718100908200c8a00d650001c3d204e800100009484041a0710b0f00380f040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 336926753 1250 336925503 336925517
    0x6020306040507111002180301050414330405212502100f0908070308040f06080f0112170304030806090703060b090f03030906040e10150503180f010606 67
    0x2910801c821641c000d00904140107501e4614010302c40e000c120b00486001c150300050700c07070040c1030b508101c1d010546035041e419440c0a00b044101b002c640c28951030208143c0445004001a40300a8074203840030100c2012081e9180608440030a80d010281c1e01038803030000e0300c0d102ca180c025404070f00d49220703070014a81c00d000b09482c100781040c04150a9805444019410300c420760740c0204080c810394201c0d0b00f0820803005096074100303029040010080040c0c1d8115800c4a035a0b040a06140c3c0240c0100307a00c60b10700d4000040d40b01c2c4268075140c000d0090b04180710040e403070003000644c05860941e00711081d04214258403120b17031400006d140301d903000741c644407558542241000510503004044e10213051034002c007404480c8031001a101c114100341d4601c1e42c00c0c07012000180c654091401e003140d11000000740800c018a58041d06405403c084c1c11882c0500d4803441c285107504090b41c10b141c00203506100151510281d40d41403c0c03103003544026150950144031500c0d00f500d000f6000b410101d220 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 336928003 1250 336926753 336926761
    0x60121141f050a0219050310030203030c010c0e03070503070b03151903060b0d0309090b120304090b03101a010525030e0f0a0302030a0201081b03010f0f0e06010c02060c0304030f060203 81
    0x100e4010b1590088800608500e4520100340b2083d605881c40d81a030100000400054021258018070b00701640e002000c580d2200040c0c003c160180c000e21811900080b8050300031f5400381000030341d44c07007550343c010040c0c0041810843c40030201e4000070440307100403408904c140321035110580350071a043d4040f000d0761002411418690b0680d03d17244003142c081c4400c2214000032a42c015403034820746e1035066000c10b5201c5110300003828100c0080c0420024040040c0c00501c0c0796030fa51000c00720200a40a849000c90854044011200e0039000110001202a80410300358800c030004c4c11130404001548404100e401659100c4003501075046000c03401c540d04001c3d0700d184c070491000c10000b04482d1881503d04680c0401d440d40d059010090511252402042d090099143c0700f510382c02c1c803030360314035281d40e911045480822107510401c0d2590142070008034009000b103141512900041c1c40c2c0d82800c0c10503909000e0b8981c001f0700f01d00340394081030002000144e401100d07010b504c1c0c050040980c070703410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 336929253 1250 336928003 336928063
    0x30b060702090757020603060f0306090c040c2d0c060f060612021e03040503071202060103020123031609090608100f06050d06090203010f060e09070806012114 70
    0x403020000b85000c04da10f803000600010200355422a039541a02c03103645986410300402c2c1c0040b0030003410759050250718100700d2030b0034001071500101035080341c00340450740000e0800d8404c51000c95145400d0026140300030341030381d500260140810380910306040c02011036100e401c12035800e2020310b681e26464210401c01035038040466000714240d41c504515001c2800080b801100e020102031070b0070300d0007000041c00d0001c00e109986d80f05400c240211940401030400079221300007408221301203000d5515800740102d9000080c502d400300f030500ca07440c6841e03104480710543e4812803d8020003c0d220340101d41118039000d68002400f800c00100304043e09100c00d0b80544403d480744200c2035207030104c201302aa440c504140c4c603040d00104001001075a0340007081c05400c2c0b02c8601400f550510320009044009041300b54801c400110035240c5035030b25440f525480700401c4c440d000ca0344000d4103608413140f212505505603d4451a41c00d400c1c00c14980b421410406070310b11100c94840b4201e04070107445 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 336930503 1250 336929253 336929357
    0x717040314101e0b0f0a0312030f021314120f030405120f0c090408040b0a08010306150602070b0a0302070c14130905030f030a0f060803031006030b0607020907 70
    0x10981d44001d00803143c000d89842c08050110303c08414044d02c902004010707484040116020500c050702c441289a100c6c1041c60340882c1c08030243c000a80f80c94a4052012030034401c0c1c9400b5042c420b81c1c8812545485d4032900032040c004043c592062a0003c603074240300c0e0800980c00300300c5046020b0350701d0701c0c0307050200445c0d05c011081c040c0303031600722482c0c40d00d183c4008160340d25020b20440b888140303600e86081540460285d40c100b4254050700043c03204070540c00c5034010341202d114100500480700701481944000507103118140c05680114424895017803080007034080081c6500d00181007031059103444540c603045038421040310445c50800017007410140c07990041c0b0103115000b4082d2903102c0da240d030707074074422080b003040a0800480410a00340030768020001070111000203001d2242c0b10003026031031364400d4548005071a107240c0009080c0d0f010303000d60400c2d084018070300d90828500d6000e001004030f0003840801048540004101d0b01d140d9030b06940e0403035050384400f10003038901c014075035408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 336931753 1250 336930503 336930523
    0xf0c0207081509032b09060f0515090f0a090206070f170c0d03051b120121030210020901030e0a03091d090a0f02030709140a060608010810020717040314 67
    0x3040e500401c00c000c0b00000022030302e5042c5051094205500020100040e841c49020400c00243c1446d52030303c00e00c5083d40260b10f84015130501007119490304c140140b0841103110883e90040340660000d043e400b5041e4215a000301c40c00300c08a46070500340d002031141d0380885011210703190b0080320f007401c0c042c001c0b9024203008101d00e500d919080d018500c4941d25010148414205070700c41000410354088014020b8003041c0003511913440c2c8440503429000c0080900620040e6660303030004400026000140e0002e5035015005031551040607200d40010354403e8403001d041c19110300d03511070896020400144403500961381c01800c281490144110b0907010107440f01c800140dc4184800828045100074102c1e0340f01000d001400d9003480824101066980000c08a62600e1035007000082078a5031580301e200c3d40741003003110381d8030b503e02035941003828019841c00d0780c003925060482900b540d00038100140111104200d801107080c1d03045d000c0d1b00c6a0002c0b200c0e03a10503001d1102a403020403410080e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 336933003 1250 336931753 336931783
    0x21b120a0c0b07020a1403031b041208130b040308180301020301050a2105060702030408070504050115050f040506070809030d02060403140706060f030501200313080d0f0c020708 78
    0x150010815006100300e8a184010744190300c41000f05221038020003440401a520102c09800d14400b076108039141d401c12204900307100020002c00c0d440c2814601102c0940d010f00150015011154490200d69084500700c0f64000c5c581160211781000d80002a200843c41121407540d10340e41141403408001c51004000d0181c3c0c01030005100c5a5600d003d144150f0b185541c031005650281c1c065115055103a202c081d1050140c102403022560f4044024816998508219080c0940c0c0c2c400b4813007114424414140d040d0501140e10200c00e20030030040040c2c058000070141416150070000d03290b076101200803100c28900041000b52818240b054101001c013038005007620389050b4801400010a007203805075041c4c000100301c810080c45a008202400d13401415401c015268600b8500800003404600000c0c0c0d240c0100e424070b196034a0489100b859112800341030514903030f4804a82d600401030821500352200052054000036100300341000b0070715401020094030304106907040000004419032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 336934253 1250 336933003 336933007
    0x70b0a1d030606060c01021306180509040c0605031305030c060109050a230c07050604111234031a0402150a0804020910080d0f08060a060c02040b040f021b12 69
    0x8403665001c0785641d0301c10350540c2c40c182c1c1c804007400268024860700207408180007103100f01040142d8046451020204441e10700d80500741c4400801241c4d550440740284a0302030480c003845000e100d440516008160b111f0744002c070312400c0c0d41e41d81c1182c01c090351000050303000800400110f4814003406400080c604410403180c1c50200e032003034008040e03801d0940808030400125a4065500c3e00302d07820150800140d6046013080e15203400214095201240310755051011034204040229004452182244440104000e01240c001150f203040b00c02440a50080d040040840c0e11002c041c14049241c412a180600d0f291042004140d410100341901003800d001c2041002e400084030b542181d01190248078070764401c076803c00070140b20340101d11107004103100710824039041117400072502070940b61641295101001d100c0c1e0002144102d2000840300c2d2600c030090300f86540510780b1041c000d0000f0a0440341e4409840c240ea0110341040d80c40c101d803001681c0500404d20407402d801140e295124 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 336935503 1250 336934253 336934307
    0x8060a05030604030e012f0c010e100c0203100c0e100504080709240b18040b0a03060c03150618151e0e0319021c15020c030c070b0a 58
    0xa82c1d10311000b0402003c3c01141000004541c0c05029040141d0313011800c80c160b001702403644009925007005441030203120303803911071f100f079070003105848034006016201130300021150300c046414040d40e00051380c03d805110180b6118884074000d0000e00040303a01c0b401c0e900303800c000a00c001c08425084120411006100a020900d0003040b1002101c01090004c10407144060081e1402022a0103d801400c500d1500049440c04c0c10040c4c000d8103030710b03c000b00c100d00c0400284000d03100109031a541c49103102e141403000540d40d80c00001902140d160014070030440c048490112038964000030085100019001860058981c0314800741a03400d07602000f20b00c151034090b00c0120342041c0710450040c00e40010310110b11401300c100b1304110050454040403c0d840c0ca812a00c0c1c2d4589081e80240c3c1003500f00458401d01c0401500c0c0c0d0b90380280f0001307000916040c10002900056846c8000b40002c0103500c2900710200560000303001160782d9142e8810f150038026040e03022881c03100c04403102d4170b1400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 336936753 1250 336935503 336935509
    0x709031b0e0c0706020f0313020a0e010803041703090a0e0105030d0e210a080a03020702040c0309240905341a0a05120906190b0f10050913020a08060a05 67
    0x250403200c1c07441d0303041c0c80f00428035000d0701034080d00313001c49405200442004522913844002c4c801960003a212044000c0c0c032006c0407482d80d03600740540e09056008010411540c03102c075290000072a155001d07281070410480009a0030405984003510b2040b095005121528040c4841d0300007404070b00705051008440400726446a0046c900081122002041d00031001028042c440400d035101e2100c41d540c04150340042e009400c8200301b0b81c02185404c0b94408410b00920031038204541000c3c4030707440c840201a2920045203000b02258040340c89030101000500104854083c81c010741792704403000f1041c40210015903012008400c1c007000b48020810611500b40f001d040000b58900b0615503c00182c0000ea03154401c0c00c81c0e203083d604440c410080c0302c000c080346080c01500ca200c801916001c030040c020060340c612626050340001025101e265501e01501d030001400724500341076040c09200000030b04015040700104505030340008070301c0e2895900000e0310342d100b40d08950814100d8141004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 336938003 1250 336936753 336936779
    0x31b020a03091202040e10020403060c09120609021309080d150506270a03030e040e0d0e0915300601060917160618050a05062b050709031b 61
    0x1080c1c044903c02c460380066494681181841e00241c408a4404d00e0240c3d00010081d4018401030f074400345050032410100e442070100c08101d40340718100345031400e20394480d0b40051038620f02c01ca901c0100c032888602520740d14000c041d1b0060142507050f8840144000000c141e50403450400200303450b002080c050340d66588103540342da1440021550464245814104031840100e07206584400078400000c201a07002509c8030b000801568180401d2890055aa40d90328403014000302050f1642c9980b425410240c0040d50300203116200c20100700c111030086407040c0c5c5103001e0240303200c40d1030100e1507104007c00440c01038805150000c2c0000d42c94240e00501124082c00760140d004448045040355250801c1b0143c20758401e1281d064000da03807040068040c200600800f480c500100344005103c1c9000b0401c401210009028285810001221256040000f8840142e01c206c104c146c042902414400d4510500458403030022072070650400d58a881c94048140c0404101c50710240030140758484 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 336939253 1250 336938003 336938009
    0x20d17060d030f02071a042909060a0302040e0f0103120203030705090f120f100b03061603050613060f06080105062107020f15070809030a0504030f0201050d0c031b020a0309 76
    0x600b400d030644180c5000c0381070811603400700600c6c0034000211700041104400600480d008004503003202903c0c01c801f8030000000e0240c8401c0140140031118041c00c00900510403a48035103001440c1540302c03285240401001e1311151440c0440d00014810040302201c582d031080c49a00040d800c503d0b2400000308944610321a25003e445803660140d02500d5100c144000e419503013082e162003d041108880c0d640038991030a035035003800c0c002030b4106820041010f5015200c3c0105055a208002c9400c0c0c0c00340c2005081140c001141503a82c4044184501c0744002624210740b20740b40281c5019001807500e00181c00851203140c0400054890600b0700140c64080c024010f41e40c0321668482d03005904010080d03840b401280102d0141000c4141c00c043c03490301c02c0109444101d01a103408414a44e24080e015907103010071000c2009101040c0350a402022161052408500d08001c006a2400b42d034004650640441e449a04021000040030381071444100e070741c40100604038054030010481d0032248 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 336940503 1250 336939253 336939257
    0x11030403051209060c03030a1b0e0d060903021501030501020d0c0306060507020f0301021605100c0903030f05090a1205010b090f090c060706020c010c11240a0e010b10020d17060d03 79
    0x12035210544600d4243ca1750084c2020550fa12407500640020141c140f247c440c54400c1000c50040c5500340c0109a0300c400c0392809429400c225110341d5940001707044640c815000e610480c1c003507a0410b14003040186c040c6101740000b5880e14104201d00c0240d44485007400c0516040001c01c0c170020790301400342c6940580484820381464003c1000c04c0c028410102484854103024100400380f00b00021800e107080703100013081142c203403000d9045036650244d000040000e140000d145095a200b0009070411050062201020300c1d641c0e8000c0025281c0214116481e944441441e0300520b003900e082940f007010344045a80c1031130014401c6484121040c81d00c0d10072607010495030140050340d410b64079486e800400803c039125048401400381d681c1d201e07041016100d2981005a55200c0d10303001c403440ca14039011900103031503004c1401c0c00340c034028200300c42c3e81d0369034070200c50a581c0d140d98400302c10440b0340142600a410000080030380c41c1003100d84070704aa8403411700c0540d07204c00d00c4200b5915098 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 336941753 1250 336940503 336940507
    0xd0e0f01050715020d150801092f1003050a0b010c1101050703020a0611031b1206010c05100f27050309151608030a0c021b01050f07081603110304030512 67
    0x383c5000d46a403060150700740072180c400320300d64001e0219175000c0c2c08507844a070900101c040e580c0da60036081c0c9000d0079000301100302d2240d5510b241741d03070315100e0030130056224622450312282402050911440050860001c3c0d100e8003070102c020b2581c030640810130400c0c0780640c444112502c6422048001c000d6240c1040700008403c0245842402103d4504e07a00a00503c84100301d121200031541069418540c00080850046455048541111440c1d6413148250706aa601e10005541641c8001d8083e01c0d10300a030904407000d285c00d882080c036000488030001500707040055503e01d018071500380c50545882c0305200c3d800410700000503511311310707011103207003090b401c1510b41703191603000710055110710316404a1500c0400c405a0091441640c031188200410b0380c90032401c0741c1d124054039244981d105080801c0301d5a51080e801001c1c101500c0341c456150950325540c252465000007001c48102002d110b0300000c05074000e14050b410741d5050015800e090446c0c81c0e064462001d189140c1900c7c00c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 336943003 1250 336941753 336941767
    0x51206010501050c0115081c0512130606030203010f050f0c040501090b0d091506062607082809050c06070b0a09030e0a030f0605092e0b0907110d0e0f0105 68
    0x8250051500c95404000c8031038007c2c4c1ea002c18503950702400361500c42c070b95007216900300039512403019100034043e0090b00a41c551500740030380d40401c5042c501901d01d0381d129035020001d0f89003401604200c420247c000260ba143c031996000b40c40340080d0070762010182c2040704000c181c0c1e0111040c015940030309007680da201c91000c0440010200058020105c081214480403481e0550380b00c0d604a03400c644401a810f000d0404446072844001d80b1007207100400d10105044070320485c07946a02c0285c0301045401018854484c05402403103103280c0303c400340c44241d5602003140074441c6c1e050b046402d82d64503080840d01d50342c003003501c0c07001010440c3c2c131903640344200f040c5881410100b81140b07002c0c001d0081070340c40782401c4449096510303043c0da10030f0400c0c0200e102d104001841030080c002201d03892118000724029101c480720700d04c3c05000d619444003148201039035114a0940916490384400c544001d00140460900130600120300910140001d41381c09900e803a00602100d41c02487c0c550340d0703070203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 336944253 1250 336943003 336943027
    0x40f0f0503061b0307051629183f04090b040917030601120e0a140a02010203040303081b1b19030e01030b010c0c0b1216020d08070c06050c090312090a0506070212010f020d0605120601050105 83
    0xc1172b40450b6030b07010709060218500050903000340141c50720680c0c18820341310408184000e580b0162801000045c0c01e20101070750a18000c00743d500300c101490032085841d103c142c0d20381a500c099284500f02d401407154503080244400c0384c0000c66540c0c0000c1c1041c000c450300083c2d2240594070010342481804000191160281d40c1d0300070070120880d0351142c895110f101c02d500300c050340781c1c40b01c5014440c200d50101c480190144024941e58180c0d50760303404045803001140509841401c8505000d44031a81d040018403d082000c0605018000311b80c0f80c0c1d02c0182d424001d1400030307240345d40071003061803600460380d0f01040038a03640c0e58a0900c091740d51140d0780e0440384060704220140c0194038010034003815601c1000141941c0700c0c1201110031194002c150a1001c0c426464407540c441201003041142d0b08205000e07000207800200722418000500c0714150a403443c40000181d01540040d200d42d4030419441580054502640c461520040c40400386a40c0d40e03060140710305002011549442c104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 336945503 1250 336944253 336944323
    0x90e1302010912150b220c140d240803090402030613020705010e060717151203030106080a050f0403051e040f0f0503061b030705162918 60
    0xd443e5600078980c0c0490031310a2088011101200403941010031007186486c01d0766880850001550140610b2500702015000425070700043c2010701c00942065200804400d010b4140c0381111310001c114560300c0c400031010222642000c1d492102410824002110000240c91410384103403070040c0d803900c0d03071000151450b1b0490490308080d400015203404011703041d00650020500b401c21940d10792038154003a10003206090a12182c61500e4000078400403c10402042250020b0401c40c000b03405280c03642d0465109800400205540c201030102242061081540c04004040f10420300e0401d0340c0d00034800c6c0305076030b07018070442c0c1c07020b111140ca100c0e58000c0354002d080680314283e4241ea40c4103c0441201c1c10300c00d80d40709000e00000101d170703034050101044060300c000030b081d4516070352480144e4890308007a41c03040c8905a040005c100241c2811443d0760109041d00b030760400b01c422560f00c8030b0501ca004180b06010b007001c5031030b8400c50380000750f81917050340d0302540c495803215540007182d115 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 336946753 1250 336945503 336945509
    0x4030b0403200138010c0c030203030a09080c0d02010f0c0c0e0a0606080f01060e0105070510020d2a0906030b060d110c070e04050d050c011404050705010e01090e13020109 75
    0x2d802191402850039505600000342d42e101d640302c001c3e01c51034a458500445600350030103200d04084000424a640c4101c82e6448003900c6080c12041c0903071241c000c00d165401c07a07031416000c5040070320140034420303041003202c0141c0c00c119603200b09018030b030340001c200850881403001400389040041c8200b10300c2c035040601404030b61008241070301d01086c04501400d20741c8542c102083c0b14a000c101004050610b1606036045500e071041c0c0c600c80680115025070020360300351828000da150119640c51540020101d40038800000300c0c11031800c00c0c20307030240802940d20444010020080c1c2c11000e0700144244200d076014200080c07101070501c046410b0784180581a240d0920300390300d0040769494400a40251a01d8504980c56251100300140c1d00e54410380f00604680d019000d09080d00c0c0c480e10007401c0501d041400814200310515968450000c02d0710221040d82209105203d5540d000d404461810303000d28ac001c407801d2034000c004040d0003000c0d00350300d880c04010400c4019a4000d01003c001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 336948003 1250 336946753 336946787
    0xa050a1b03120c0903080f1608030709210309060e01030207050a0506101508040f0309031e0516060905060a020c130222271107051509010c0504030b0403 67
    0xd51141c40c004090b500340c00c0000604514094400d03200c2e6110300d81c0c420943c1d502030895490002c00010f15240d0350410180107881d40d208001803000100f03070002a500641e8181c483c00c2100b42403505040e0510b41c9002c01001c0c158040e000500401d6108001d2000c450190600c2081002010b004902074418224090160f124510540d410031400050071b51160f80041c0350b42c02e540b500c50702540b0b07450250103c000002800f6001140200306c2800907640468441c0c100114880d40d81d650303d500d2013a001c861450002c107050b03010402d01809101a4140c0c03080452091901c50a00038054000c520380d008d001e00464021513200c0a043c001c02039880c14038401001c284582030408105000381d400a01d1850042d180d05052050a100f40300317030003058600842030301c12452000c1500c1642e01c0a00c01c564813403a9200c8990000d001e49020042802e40e000d60040c2580344201e4541e8507460b070380175007500c400743e140c800000000c4d5804030603a03044c0c0794441c90b001d40544840c22301725a144800040c104e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 336949253 1250 336948003 336948047
    0x31d01060b09030d02070b07080d020405120c030105070806032805071e09110f0309070e0109320f0a0e06070c0212010b1c06181101110706050a050a 65
    0x261a16944002c0c014904089003110059600051300701c3c2c6518491159000c0c241c03043c080140094841030160070154111500141460341d160000b0380e03950b580c10380d0341e00980c0001d84c220049003402e004090b4851382070f04002d280380c01c10001107565500340c40510346c42408010340e007001013031152041030342050300300302101d1900361102d010014135501c810000d08030301c6241c140000d400c81c00f8041c0318455207450010605161140440520310382c0700818240c401d0085000218481480b1a00d290203400c0c03a141c0040d00c071040300142002c0080724646c5e54002c8030309101e05c00320707240008480da521003110b244510a90312030680340340281008030362082081c000c0314200841d80c3da10000300711100c0c1c000c5805078a00c0714250041400c0b01ca00a0295030080c0034007011b40f0034800480c07d0450304603c02d540c00189241c80155240000c6038400c82102c1e02e00808203140c000d5a880b000c040e0031005070001505d807031460000c001c0c0c4a0b1103440c0da41004e00c480420180200c0340201c22030300d04044020a101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 336950503 1250 336949253 336949259
    0xa050f27060a0f08100914010f02030612072412060e040204050c0307080a02130b04120b010b03010803090d1a09011e02040f090b040209130b18060f01031d0106 70
    0x58020041110780c14050801ca54002611046440620003100e40c0c500180c1141d46081d0340f4040507000f03103407080e42d05d007080028882c1250400d206940340c0c034004010050300c904065003002085082d01108903030740c0c0d10800f0103001d514043e148403081c5450b080080e030717180810118181d42603c8070002e90b200c00c0c0e24000000900070701c2d0030a000d12541c4202c608000340d907204a12010280001c0e20796000107a02c0f20005039058145070b000700301c9046200c2070842007544d0340000702c5072036001d50454081100d0400050041000c500e0f00180500121030781117085604000c800b40e6a8050303840d20512424400b11a4002d101291030f601801039668404075400d4581440d40502901c006100046c2402c01030b00d503e00a01ca05100366015a1101113980368a18075101040d800381c90640000c0b54445e600f00481940d42d910f0003008403010b4260500810030000c007000f04015148003a101907004150941004116500c140a04000190900303001446030303100c299141d580c00b40301603042c20b00e48c45c1c81408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 336951753 1250 336950503 336950569
    0x6060f0a140f100309060b0d0b0708040203031e07120905010503070e0a090e0303040309090e0a080d1814100507081603090506090a171201030b0a020f04060e1009050a050f 75
    0x217100c1003400703040c00303002d525911418003a070207004200c00b9010400301000305203d039101d0000650480e000074120b81c14100413846440400c1e40380001d8a0b840403000410380304210b9001407a0012009504140d002149441c00207032061000400800030401d11103145000d42d40c07202402c1c0c014060384003007040110310440f4800d5407903200303840c1500881e903500340000341c1d42f0071030040f001c0424260300a0071080c0c0440d035131071581e604071f0522101c0c180e1b05c1e00e130098261064603107a4480d6a004101c03850b07207050f480c0710250410f000b60348490283e80c28501081306c8070741c01c03c0f40c4d607802101c20303841e000008901440880040c00310510042c501d010744000d0180b101c0c00002e402e03183d540a10462100c0d9200610b643c40ca0f8400c01c14180090f065041c01040818030a18245a105490840251505107040308c03003101c0d54003a82040b0040303000c40f0182c0b583d84c141044007101c0008c49040c0a40e09a09140008204d01d4261043c2d80c414490a0301c2e014003515020050220501243c52040400d9401481 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 336953003 1250 336951753 336951761
    0x313050312040c0320061c140702030406080703060f060f02030c0a0c05030c0f030a1e0c0b03070f0206070c02040b040b040203090706110a030906230c010e06060f0a140f1003 76
    0x2c117a5203492503021074142801d90b00021811200000c0003d45451100c204100c43c54281d101c40c02a519542c0d08a140d441c0318000781a0b00c60441a40038507612818580c02600040015050302c04140c6030100c2032140c2c100d02d144040c180d9480e0f090802c03481030440f000b21b1841c480c10500840e01e0044c0c1c501c0d0b000300026100c520703081c1c800c02c50940b403a8200080610528100340707140c956140d807090103007401042c95071054200b00c03400c1616a00c840000d640f00c031003181100b503111084400700041006a91075004081e0110090346101512081c10289401440300d1300012003e440355544140b1020142c0c0c503684404501d1b480034100350f4403490030411441d1101c205118030350214041c0600c80c001c40748082000e50b200707a0315443d1080c1082c140b20007101e0039a0400d40c8244038403040d6416100619201001d441d011f8400310000c07402840b0400c0c41810414090181400b030395170003e01034180c2e90b43d41000c400b81d4041904107e0940c845000052140e91842d9440350405070718800e070703c0000e43c0350304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 336954253 1250 336953003 336953009
    0x8030a0f02070819150b120303060109120f02100e030709090507080607050f0c010609110a0e01051c05060418050607090518040f0215160311070602030313050312040c 73
    0x2d503550203035514901501e6030452a8030706560100040e041c80041c2ca14102e90340401403c0703400207282c01020000c1076140d02030a01035602a4408010041550382c000d0801000d0005500420200b03421a80d032080f2203560400c00034401c0d4460300382407083d10301c1250344124428000b82102c003a07039030b194600300050070401000e90b107030f01030920301213000103000272824080c0b00c1503540c403031501c0718800c5d03943e00942048400210070b5403200c60015403809580600a1028200b10740701da43c1e2004104054000c8040c01e83e0181403080c280314218078605500750001c402841c94001040c5036030745500280c005d0821b080e0a6450f0822a02020188000024014851b429a40742d84113215210b0007000600807a28001e0396411054600050005a40760b4070147e90b188003411004400c207807100c0341c0680b034001801d0719803481003401101082c10342c0401c1d98003020740070f48050a449070801c90000d44902c4010a1100101001c030309100400a080003191450040c4080d540b000e403d2a10380004088030600c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 336955503 1250 336954253 336954257
    0x3090210170f0106050a05070f05100204051f0806061b0f0102041802031902160b0906100b13150203070503040303080106080115021506010504031a0103054308030a0f 73
    0x40005206480e03040c2c045816941661515070070702203141011601607100078000c507011413200b03554100280e0f04009591420110b1000075031240d0412007480100381c7c15440e220241610445180aa540c00c6402c81e41c0080080d240d03140d440b051080104904e00621020f44091f100300c40c1c0149002c0f60640c05001500c040c0070000c81d10140c0c6404a03010384c00140c0b001e907901034074210030070320b03410044c0d005001802603e148071101c8200350b10b40f03441100c2c0c2281c03803b207030b6002202001510036030500301d00040c0015a820324100200200c0c038600c82d0307800d8002e40025445040303106c24494020000d5a8003958090304032951aa247d2170f00a000f003200b849002c0201b1440d4001103681d20544180e0700078044181d0007083c4200d09000c42c451a254080e0809050190400003c0082103084480f20518040d107282c400381545140b801074a0070034048811011510076980380405000d040450a80d42d9009a43c0095a0300044541c140307a50700940c4516080e110008560705c80340e40140c03400c05c003d4919 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 336956753 1250 336955503 336955547
    0x90a0323030f0a0e0108041203200d15060201061d0c040810020a02160803030a15050a03110a1d070f022a0307062f0c0a060801090b030a0b0c070303090210 68
    0x600055a0309a01620300a01c611000d51610120038801d42c040c1c480300780c102c0c13640e0340000c0c64044528ad00d0b503c040d0021348034684603c00d108000e106d07084400000c4c40d6602c000c00c401c504d007120780440000c0c005c060280c022100e2020460800c00c98050f40d01805032441641c2c01c11034600038182c001d40c02402070030090701072018010903001d02c07035060004079100030015501e103a82d2415040018003002e45601c0d07401070021070109250b00d4050003003020750f01c951301490711a4040350400100320700036031109074a646c00741682c4007506403800125421607180d003041800118110320a90420305603546890a400c0a5511484035035001040710404c0c00c0c095080c1e4080f40d80f42d00e0f0403240ca20b2506910041c00008480c0a070719140c80559038103056000030207131440090000d000458000607a44102d0005280000500c4504440d12603129140d00c224014044542aa901c100310007000900d000b04c43e003800705100b000c0c1402070308011029940102000b0380c1c3c248050000e055100941410701d165104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 336958003 1250 336956753 336956777
    0x10b0d150510260402300601062a02010207030f05010f0504080910030b06091e04060306020318070f06050a030207050708210408060f0606040f0f1505090a0323030f0a 73
    0x26010703100c1c0c0610307000b9002103400750405069840c070700904829110381b5001c1e040c1d03800388104c05000080c041d000319500c2003811140000019072410f19a0020034030422103d00f0040142e0300000c108003201d5002094000d800d0a81c1000d0303004203812015180000e00389000c100c108036031a4010440b840045815040030903080c00202c04482c085914a40c00000410009520385801151800013507a4841d03180e810580140104041c2c599580c41240c1c070365000b10034003000540400300303c600801c03410010440f00d490440120a441c0140c4114000c0c010b00007041d020f494420340440308140c6e080300484020a07a40c18540ba03a44240f05c0f40c08103441d02c0740b81d600042078841c2d0220f50456038684000c1c035081d205e140001400302c0d40905004c1d400107040200041c002c400b901954020b201460003100c80070b24000c8000210502c0f074017208204401003020000c6a90707507400200940e900040c5003503240c1e45100407914400664040d00040344800304181040402c0e0400420903012a0b61385c90141c050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 336959253 1250 336958003 336958067
    0x180c02030a120e0a06090c03171201060302091c030c030e0402070c090b0102390a0602061308043c05010507030503060316080a0c0e010b0d150510 64
    0x10340700d03545001698010403582125030b41c0d00402c01040c0d0880c20354000003031a540341011208400011104030b10350807010000d10841c21180856819184038040ca40b03200301140b028803020502450090560104800380d45894101a03142140303006009038030214010b09001d04010390000c800c40c00510405d02550540c00c142c000d48001540c44102c40089a0070030004802920b03207140014114820701e024418003420366070681c00c00444054184401120f0001340c0c1c105454414501d600509644000304403240c1c0c00101540e2001c0303e06500060030607540760198161085138410092903074086101180f201907241078121651101c602d400c0c0006815030850300d100c1581c07040e1070214400b4000400070902403001940c0c03080000f000e90b45c0541030504404850041c94110310381c10350284036401c041000300c040341409403100c0400d8580b00d40c175201501400e0f114130b0851a90841c0c0340c01c1900b102c20104420440501001040b40c1400c400064009243d160002695000143c10144240b1007030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 336960503 1250 336959253 336959257
    0xc09190c030e0c01050c0a1a0f090a0b0601080907090221010906120b130501050c070501140615130305030301060c1223030402030a05060403080a060e0c0702090702100204180c0203 79
    0x40d9040141c5112103c40c8019141ea800c03044032004503006606245e80080c91004820760840d03120740980c4568200081d5110001d400107003031140741d60195240e040811045004c50798468000d03e07010309255201c18246041a40c80c0c1d1003152000d00201d0a440c43c40d0310b0380c52544128140a101040c260387e00c1c00d18005070b98051282444505540e00760102103100c0c000d4440d4001704d0398000241c0c0d504c495483d1421a00c04030750410701101d000c02d48600f006428000c010101344001641ca8080c20b0840004481200c00740500759101400110300340d101034034001001c0110782081c1981d8072076a58000103032070001002d0b401c55042c9844508400031a000782c03060036402c0349a440e652080d41d1199543c0d02030340d1010700140ea052007110090300c00a00d00300462440783d4800c0d078480704c203030810701c0005040d5035940c0c00014840c41c1250820298901c0320381503c1045804942e03041071a210320b14260308200c9081d8120a00a00009010954051205030301d88481c010480c10402404804402c91f201c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 336961753 1250 336960503 336960521
    0x51806010b070b0c07140a02040606170105010e040f0509150112030801180f09030f08010801020f030c07020415030305041d09210d060608061005030601020d030c020c09190c03 77
    0x81c8014444100401c260103160395120449103102460310314903448020103d56070105501c007942c0102d06000860803e8004c240080000341028140c0c42003c0349108245001402101d04020420004124568543d00220f030144913500041206040c0301403075980301c8070540406c206801503030000103030034240c1003855103201c0d802d0b544602050f420280c1d210010107851421071006c540764081a0b805807050701c40d03070201e070384039403646801514603c4014180e07610503070268986900c103001c80a40d010fa480116030f408800f24485070b030b07115400d1001a0040c044000a045450722604000c41016001b4008000303440350b401c264001030005038660315a45608a038800f406801000000c190702c0d2001840e20901a20b124441d410f103021072061a04490700d80e07107d00001030101d81404054203200e0b0501603030000c5850120710714544400080d50b0780003905044d0301007581d07900002c850390f8400e0040303101c002d20007444a011410200e84080084000e07031045071503140340400c42c43f0f01034024481d04c81c503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 336963003 1250 336961753 336961769
    0x5010b0304051507021203070f09060e220e0708030418020310030305090a090f0903140a080705280507150b01021e1c03020c06130c09021b010e0105180601 68
    0x12040d581c0c040c0c0301c003400c00901201306520a496030344400d100b4010240d8030510b40c0e0b41d40d0508218003200001c11402036503011001f0300c400744000c407086495151007a0303000da8000407503845c441541a0b01200511051003a205203000e5440b020403c000044001c0045032a0100d017040d40800c14408a8100d20003950960780e280041101080043c0c0110090000100014803001c405aa1542c0c150143c0300e40080c284485c0da44c0302c03500380070184c019002d04c5d81002004841030a0400e480c0c409001948090045818460049404505200ba0761083d11640c1c040140900c10900c0062001c1c005402800d812110714000c0b000d024240c070480d100b050f4958405900429038019820b0090040050032440c40d0b4041c0030340c040c1582090052007009400c2009a580180c1d039080c0401802d0804801808004000c0031041c10100480d500042c071100341c0f15059001030782c0d8460038100140204a2545071480c0f5400c110000c0b030741443c190b106038800c4601e07071601082e11204070006911407400740180b0007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 336964253 1250 336963003 336963013
    0x106140a0c05030d0510061205100b0705031b0615030109030e010807020f0109050a2303041401171008010b010207050303030f07110604050106030302010f0218013504050105010b030405 81
    0x40c40d80e101d00604204a80184142ca103800341c4064100b090b900121190b210b1002c1d02d40b070801c9003550100151101c0c0030300d800d00700128101800c4003c04989144218100043c012030b1010a1150a00c111003080d5a00032f0300050010800300c0503501d030042254064560b0f580703000100707144e0038103000c1c1b016a00d40c15030360b040440c400c40005503240c0001810540441c480c040741c8c040665024420000103034000d000031300541002d071800da101b07031f8021041c00e0384512203490b084d1700da5200001960140c8598120b80b40060301d1410040b919141c01201c16460b00e6080d80601c100c540754020f407901600c11b248024048a034003000160781c0d44625200e140c0d00f40c0d0003040003c9144c0e4500c54099081407261820100d401e880540562030894107075000c3da066507443d001001019024840c4002920981303030f045d0b00780200b007a048440e54031014043c034180460710100300740010a4542e00680000c1e84000020700f981a200300c00410f5800701ea084500350710300800881c14503040d40a0360312480e403060080c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 336965503 1250 336964253 336964267
    0xf14091602060f190f020909090129041b050316030b010c020411040302030a03111006030305090d170406030207021c1106280302031e0c032a040e010806010614 70
    0x20343c0d101e00003040b590030859106200c1c0303080e040307a002e95410b2048140015840d1961041000202ca001034040f90132a03240a800d034412a04072080c0d040b5000c5041a0407400640d01408070340074000c0f40d5031021914150303540740081603805c60099070160350013001002c0c809800e12003e9003158114100340e40821402c0a10100600e06900481110003500f01014140f07560f96022a15080120008a02107280480c1154640e5030030842d030340b0b40084103501406031a00c2d689001d004c510404410314008c801c840c00680600c100c0c081b00250306410401c80558403591004010000d400c1050100d1190600842d2724001d04940030b0071846668120300d0080c0d0400d01c00c0c04005290b0b0110014101c440c000c101703500300b13080c0006100d0070090100d40f805030780c91803d25140a420021180c5401080746844103104000503080290390b4481c0440c1220f581991100c01541c0803401d400317258000029001902290743e81c15070321010b0480e041902150410f0b40c030f9010580d9408100c10286403045c105000003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 336966753 1250 336965503 336965521
    0x2100509030415110d081b1c05151e0a0602030324010c06050f040627080a031d010219080702030f0304020a030209040f140c0a031106040f1409160206 66
    0x7000d0030b03a9590070300701e00c0c11401000d2603040c111145105c0c80410038000c10400c040c007441411039215103031040c0981c50241d10031410118081c1203440321000e01d40e074000140d02e0001419a607480c200d00102a01160303000c203034200c0541507001690500407038504400151a5000005480c045d80b00100380c24140e01e240f09030003004904152406040000801100010a049100300c0d0b0003440340007411142864942080d80a59200048a01400080d2100b0b880803c44c15404030300402c1e8041c0c401a510030203a01d048001d030003550b1038a11511303003190b68600c00720b205600410303002e00600316400c3d000703c1250050f500040100c4894016030400c10510b0304401c03061004590007403000f080c07940791544940120f2000c4000312000c4540c91201403144040c8074081d241030081c00020380c0207103c034803074500109170b403603003d44070081500c1440f4202d40703481d03550607060750041e200c0c4008491000d50b03030300c0f4180e1101038490500d40c0900d94007000300b00c029040010711706481c08036400074003154880d80fa072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 336968003 1250 336966753 336966779
    0x1050d030203121305010b0105040303052d2106010207050a090c030f0507030905060c0f0d050a0e0a120311090904350715020301120f0314030412021005090304 70
    0x11400c40c0000c02c41c2d40140580030101d54040c4100207000501040c1610703029003180d52501f581414020140000c00002c0c1e0300c00d04440000200c0341010451085015900707032303891030081110040440100d4044003000c107403802c0d0303030f07210031605c215096a80b548801641c0711240ca014140e04402c075580107018050054000c07110b80c200358640008d2040c0310410072421110242e4070940081c1d12aa03900060060402c01a0741220122801074600b88101d000f8000034483e000c1808241503c2d07600166070806140d00141c1210328280c02d44130f0b100324620302000580300b072042900209207010f9260040fa0303160001d0b2899104058460320082c1c4440c0c03103030007140d0090b01c2e0101071000c0c14688c003155106404080300765841c0d0642c200b529050241f90404041c9040c00030030558038418001080700050b070000f00c8041c541c11401b030350740210789802c0489001c842006401c2ea19a0004184010840350450740c911044e5260f082c0c1d8840b40d00121154107580080c0e81300090b660060100b0b02c010354017020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 336969253 1250 336968003 336968029
    0xd081608060d26090907020c030304061b060f06030c06031a042c0102250c0e1b03010e0613020c251a0a03060f08030d0c0e09040609060b0307030b0105 66
    0x80f04841c4031040714440c0b50280351003501480007030004559401581400404c65401a8480c00580141040390340480d503a402140b00e9101003203e4101000e02d103141c9044c0e51214650800402d1180700400602d0703401410f554801103e01c10400d03a00010720510034490240d041007410541485003054804000103000748010f45a8400d007008102d11051801c1c96114288a58940025032900217190a4408100d483c4130040c000c17200440300c1e2400034005110070801d4826400700b0034615101c1c1c10010000081015841d450340c40c001001140b00100c07103104078805c01048840560321070765403200348140d020340300b1805529841810358054410402280d0001003501c100c40c035144560b641071001c40c102d0400441100360380001100344203139a05010320005444034015a5410915181107d030b174a10810201c880d1213a915120907010300e06c10305d11b003100da10b00142441a6030606007019001841003820458640e40740c0440c5880a00303021079910110394008842c052503078a00414001110301c004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 336970503 1250 336969253 336969263
    0x50102030c0a030327060f0506030a020105030c0c16030c05090c090618010e04021602030606060a170a020f0c030306010206010e0c0708071e050a030e03120a05180a080d081608060d 79
    0x40e04001482998010041841c01200c021851880c007019040c12250b0113409c40303010350850868240580d801c40c04407500411000d885a40d134081d503603407a509040803108100e844c13000c1e000b800000e00244030615030540f01e04481c1140580c803504c1400045108095000707401030028410740080d42e5201210489584040c10000290341d8910300150803684507014804000740313811080c0041d802c00f00b00240e8484025561039280550342040079004880203180100b5001200000a00959494050303d000c032007005502501c0f0310020a4040d220380040b910346006100f20000011010f451150307580c05050030344026450300031292608281c0d607001720010b840074144180141c22085030200e0014005000f0405442d200030b02e0300e00101410070a03d030240c86980000000e040c5110f08908664003000b25040440e81c881c000d403003902d00401c00b09550b03507122004000000300f607100810b0184683d41c05a41d8141550380e0610b0750400c2500303030031420000650030300003c1e40d603003481e104a02c901070243c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 336971753 1250 336970503 336970541
    0x6300609060f08010f050402090c0a02070b0a0804031b080f07020a17030301031202030309030d0b0310050c0408190f0f0f050307230a02180705131509050102030c0a0303 74
    0xd03405182964040da20100c010802c0c25000c00081c082071165024451801c0401e02450800d40c00107103000c20301034102344030342600140a001e124004c0100c60700801c403240074903896a060003000343c2600070444083d004960b032010000010080c2d000e01900c07195000301c20305c8c1001d022a440c0e940c1900302800498101035910400703d0b0500e8004191180668010002e6035650305510707107444e801010105280565006109104200001005841e4101c111340f100040707500710040007030316108101d1040100d841c50881801124040800140140c40010045034141d19608241059141013640d0150100c650404484006800c9000318003407940201c19228030b00c0c1094407a107055602c5a01d00325400c45030400741070020102007a0701c00740e034070710711020708040c0186030041501100c0160009106080c80340000303991a01a0003a690114203410001c041d00d42c503803034201940030400c1120b10118000034800282584004100c0d5100e121a9000d0b03d007400840d601640a4842005404e20848603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 336973003 1250 336971753 336971759
    0x9050601090203190501090f0c0215040f0206090607050a0c0f050102100507050c1c1b080304240c020601081e1906090807030201050703060f12080c0109020a0602030310063006 77
    0x43c001c5e2800f9041c040c03000650980304002000448a459026806542002e41d2121060a21001243d44190001034900d41c140b100d01c0000c1082c0b00f410a800e078001804160ba03014007034002511581c85202e40102d0074420307101c4000086c1910188651401a84420307288007018072550000b680100180c10028184401031001d40d04200600030030342d659003003030881540b00d19809181c4502160643c5020024a0001c0c0c80381d4000c0d120007030004d44100e54918034401c2c12501c2040350500030a074030300100b01c00700c10307000000d4440307000f07115007c1d00e441212010401010035019411281221a00615020187c141250412028200190341c095a118140302c0800c0c0704074000c0c04007520a900000316480d082c00d020301101c025401840c00303007500c0d2605002e064001581c40000c2a0499486916880e14040e9140500800300c0001e410442c44200011504d800101a500031002101c1e081c2115490310301c12940a44a0081c02200204185d401125116180b04d801c400901c820030218055407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 336974253 1250 336973003 336973051
    0x6020d1b09152a031d0f010f030c02151807051503070c030504051003052505270d060e0f03090906010e0d060c0806180606040515070c0902120105030109050601090203 73
    0x42400050300030407407580e5154550703a41c17080307015000b007030850701c44010880c4000000c01d0814814800001d01d6540c40c01c40040038020000e540f41c1d42862880200d40b4949400c0c0103030702c1c0301c1c0040704101601c101d030000b040c14034001807141c05410450101a04540e41c40c40100d4070048007010a0f0280a410800840e15444403d20404059003030784000c20a0f04107200012803003002840c10303c14008c54452039208042e402402c0303801e504c40407c0c00c000071094000201035201012540150311500c0481c811081010b0b0350032955031200044141c0340c0e0048640d14a82c0c491003010103080c2d2154880e00061029030040e401c2505248020301403055480b5a9511502120460084200441e18140811100349040045030f0280780c1c100f03044005609081002c60070700e001c1c1f401402d00c80c0c41328548800c1d4500302e44058451640d0008018160186d5030741e0002c000f5800b2076600101e42c411400013058038181401142c054682c05401404960320307054001000b90806020b4500985a000c4903010341d40c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 336975503 1250 336974253 336974327
    0x60f1c0b0717070c05121b030c0a0203120c1906111209070f1809060e070b030109050a11030402120102130b04080607020c0108040f020a0306020d1b0915 67
    0x2407690310ba0301c5031185003001201c2040da00070891000c210812601c0000128042a0a034003c04c5850105803299007030164032212044405100c02180b0020503145400c42c000249050186c1c000e4050307648200d03001c80c5804c403034410342904060315800487c48840c6d920327600c01c80c01d43c00c5004000c000b42588101d0740030350707956009082d1000d0f5001d50806000035020140210b400a0001840c0410038a140c50000d4000801d900115160075070382d01034a40c24000c058201c02d5802e14200241c0741c1e4962580c0084080d60030030b0140c01d98a034074000c000b1308007111504c1400b4403031032400107043c1142e0340c607030030030602c1500c031080c122540d5000d00030a80031164036001c02d0042c1403102c01c51900c56060085040c90b183c40104807204560111091801070b981110340c1c2d42d082078000c0c0400b0703181c4010f800071510f0203809074401001c081c8009100b540c520116401115420300d00954280c901c5034a24044815040f58024200f511440c25011100036004143e003250000204000030001c9140e20704900da00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 336976753 1250 336975503 336975511
    0x70b0f04031b0318261b04150f0f080c0103060b04090504060b06040f0503012933030114090114130605030102040303081609060c061a03070303022103060f1c0b 70
    0x8040341201e60041c2080b494203101640103800201a0702000c1c0c0300003102d606c8030080050240b60386032801c4040849004403400070703100321030203c014142d07140c000b4808a48144544000da000c0e15a1000c41584a0300503171084940d28021282481d080c550750100424016108485983d62114440226203508002d0b200400303001140310304d0240380106150030348410268806043d4940170402d0303024083d41c21070840e0401c050710380c5203000d1b91012010031195015050391840810780c60480c50840d001e400154140c0d1004003030400b86603020030501c10406428080c40b0009420040d4900c01d9003030440183d0561004a403020448603625804a400caa010740c1003030303000480715030822a040304014200300001d0114a0f03d1003d65180c05002020b5072004c0300010104c41c0c945081504051501812406502c40142a10341255036854080d6984440710056107088111010700ca980c0b82c60102540e114400c007030400d41e6400118020001e07001d410070800030958501b0f00140c804561030712141c0307100b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 336978003 1250 336976753 336976769
    0x21605010e1e030301090903170103060605180f0a33050a15020c0609040f0c120c140403020d06060f06030603021e010c030c110d08070b0f04031b0318 66
    0x2600c0d6020710000d04000e01580c61100403902031258600351040001228111089240001a05800e918084400726000c40d01066054003100001c424040564007100071554111070310480e43c142c074990780c01c04a4040300d81108201610f030000302040b0b05900100c036012094420340d20000c42c030001c100e40301c82c100d124010807003402078824400d034149460300a0290010782e401994101d44c410000f03603112009843e4502401e80400cac8a407054680741c10940c1107408480c810701c6003140b0014020302c2800c0e41c10319918064201103018503000d01602c0f4800c0104071441416242c98116020301200390403101046a000c1c3d605d01000400f1807503511984058001c03070b58003040451960042243c02c44021000c41c04d104959030300d00740640e07080640700701c4007545400c22480e40890b038100040e4141044134040d4106030149000390070000a5001000700034411030030388005880d96103c050102108036070080c04610406d4010007075524120032400007a01c079207003402c882441c000300060107112030341c40260 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 336979253 1250 336978003 336978011
    0x30c0e220e010e03180406050d0503030615041202090402060403050105190b01020102120105120726060112121107051e1002060f011e03021008010e1006050304060b01020102160501 79
    0x10404006009010025042600034081c0e800c034501910349034407404c40014004aa9501021410b850b19000707c0020140102507207000855403c200351640c0c011100c0600c03038000550500341108090054609a68805010700c100b01000d03428881111b2010308140e90001d01031000100058090280c544212007003a440c03c20746151000c502d059801204400d81507900521485603550402c0c3c0b41c0604440c822076000c142c83c842201c05504000003038011101d0300040c0c500d1015010740340c0c18000c6c2344881010131038100d0703079848202c1c605011a01a00814900c2c49406025105208150480100c0c0e0000181e41c06076584400003070110340340e0030352031142c0e1020000040e03180c6000000070668072224009840c4034940304030b804031a2001401003a00401301c4007941d10240141c1705800300595406803070070140807070803c0e0250100109104820403500540f002516174603030510040701301d421a444190954445554240c090400800038034119035080c08010500d0403031983e22003802e801500001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 336980503 1250 336979253 336979309
    0xc060507030c0f0f0c0801020f0d0b01030b10050307110609030717120f06090c0c07030213020921120a0509010e151306020c031906020a03090b09011406010806010c03030c0e 76
    0x20007981550310046c2d0030792041c0003400788844800b0031150a03a0050303d00094144000340142d0007072010000007500700f280c90301c04046481d003050007140911484e84651500c24a50b0501075030340c1d002100d102446130000d11401000460050490688c0000c1007026410f280308074080d90302e0316104070b801500fa04c02817018082c0e40c0c1004224150410200e100151500004c40141541d0b040b080c80028010101c1081c80c00e08000154180d070304800c0002c1000b8000c10700a20b4282071081601041001d0340240381640c00345500d840101d411f0103115856032400e00561000540d400c0d20315480903034020a520302c020601c6080c40c002800388045103a006021542400c178000c1c0360a40441501e4043d90041c484a17040c5141d16841d0510183e000c040581d45403000a0200d01074003020b03078010084503120041c01b450352070640110b002c00d14040c504640c2c60b65003000465400c0d0b000d460722400306a40210480100744a41c0000c4088082c0b810701090740710030203021800b190b00184a800f00c0c801c060581c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 336981753 1250 336980503 336980513
    0x4200301091401031a181005011505190c050c130c0201051006090e09031201061e0f0801030b0901060308030c0408070807050604150e030a080a030c09030c060507030c0f0f 75
    0xc0d442e000401056400b00b90f045988280650169003103001040082c41d0000300412036444146c21401036840607940450204800300028100a000700410400f00c20b20060a8500c180260f8040060404480140810010040e510032100e0038003074070107000ea1406056151940d40440645c442c61000000315140c1182000382100d1024058a410b4003064108009680d444002c42c41524a09201c41d01aa151200310914621514007405800342d0408000240244c004500741ca0f8494060a48510590507000450300d001000518001154141e0014400b00c0c0c014020301da4007260f0712000044054907070316480c000c1d801c1150056581040040d0a01c201c800c1841601c3c000e00210300146a6030307042a001a140c1d002d41d0290099482d1468104a082c910503040c507880d408024090341c5000c412402e12950a0344090f02c1c140201c1e05100d08510400d12920440c401c903a00920725000d15402c1c5242101d041d80414015010420401c1c1940c020402c1c4100504410740b05084400d0422014909 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 336983003 1250 336981753 336981761
    0x26010c09031e03080a0b010302120115090e24040e010f0e010c0c1104150b0f04061106040312180209010e0402010908030a0c030c031202030f0109060915050402090420030109 76
    0x1200c107081c2200e1a074002a07040024203400c030f5606031010403001c0340c6c01e00481c000e01910b00280c100c0250031000040e41c8040410300320317403c01655500e0400a48404100d1061700080c0c0314800c40340c000c2441814440b18021135405050401030010440e800d482c1d03007407803c0d01c030b0448400e41c000350340b0350320702c2500402481362200d240f8060a180c014403003a522100c291040c007241090140707032628440e066205050034090058050280e4994480c1c0220703a0030309190300203008483c0412a000d140c0000b040d00041c09922440c0c1c10b5a809450041c4000e028002c1c3c034061415511200c0740e2031f840ca006a50b078424490103413074018400001454075000060408441e40e000000a40017000204072981c0c0c40b100007159550541402c8111602c00d10b021a981445480382c6482e00388040148124020484107090494a034058140191500c5070400c1c3d081340c2c10141401c0411100c8102000702d400c1c150064120ba14005100295800c0c2000d500c040039031603048268202000080140280d040d107100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 336984253 1250 336983003 336983033
    0x31b030f090d1b020f06070b0705090910031112010f09030309060c0c031e09120f05010506010e1e0d060204060804050d1706120f010e0a050c030607020726010c0903 72
    0x500301142c030300c1c1c1a4298801034064400a40210300a030b1502181c6d0700c0d004200c49a82c1e9002041401c98907000c02d0081c482d81122010f036108035501400308900c0c501102005080d00d811080041080c00702500300801c8507025a0503101039502c840c41d141814015120f1104030a021341c0707001c50a05400e01d8070750119401c807804882880b02c0e103075880022903400520180000003440241501711010b46054440c2070720342e4811404112a06194420071459041000006101d04000d110301d84403070005440c112580301c092600100401d1464594035012046d8105280015020000f40d1403151524000e07603000d50451408100448103203c101b000c1003000c001c0b484914a40032400b49018030343c112111402814561150500c4d03040018036140c1400340b482c10781c3e4150020041d60002c00d038075580381c07c081c2070300b0303038280c002c23144103244a0401140480c072602c21607018003e26414889402900c001c081701c440032100101422000041007403249506110003a1590b440440c61031070000442d00740c01c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 336985503 1250 336984253 336984257
    0x90e01020f2a1009050c030c061c1409010204080f01020f12041112011e0b0604030f0f05061005130b011e2d0305090f0a08031b030f090d 60
    0x402079101d00c0000007510303801618901d544821002003180d0340c18441250070789400034056a81031140000312503000c40405413040c2d0a549008030b41c03008142e02c030907000c10290780155080200c08a0481882c05800d048140c000000502c5004c0c4c0d035940200701412590000c0e5a98001014000300340c040116a0301d49601e20005d5142002010000c2828003416604688003107a48000c5010001071b03001c0000b40c0304024000700d840d45c41640740e00f40030b040350030303013103c0e80c04142458074a41c0649409640c0d000040079003d949071628540d5000400c414402040d80c48501003010203002034014800c0c18000c040002080a40d9401d0808010b008010440d624040a01d080000b03102c076600610f6140a4100c080c00742149803a1550080e80c4260039400041e250307103204288081e00d030014100114071800389503030401c02540d58052480c8c2c0c6031407000c803c8030f49900030f01c5842e00041d0000b00655201c80442c1241a1100212001c5110b980040d15006070022061007000001001002440380d454076034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 336986753 1250 336985503 336985507
    0xa050a0b0405060a030b1e09070f0c140f03030406020c151e090705041415090f160e0a150e090c0a230307020a1e02010503060909010b0a0b04090e0102 66
    0x1002506144120b00c00d560155002142c0c8568842c080d601c007171001c0b40b0141c4455a940c041070031061924400c40c142500c10780c0240081001107208203800e0510250310b03240d6281111981e12011020130016103500c2042c8204944032018400030710146024074412840980c40c0c020440140c1d04201da80303008500d800f501101002254074070b1240c0049001140403840c900c640716050404e0500b1040e800c116080340c28911862403858040700c85500ca10f508124078005210f0711410486100e02c10f5822002010294001c5030400c041e48660307600310070403800c00e0303060f408000c000309003800c4003640310346e140418030100c035001030f0f41000f41c00f6079400b03003162000090324103815114424040c0c05100410042144a10204045c2960341241621000d640494030781c641181c009540d402c2c2d240b0100d030203082c21548003500600d601a101c4680c0da0585429042d96904020f102c03c02c40010702602040d0740301d10790915551607201c0c0400103000780c007001035651810440786000b503c180c1c3e1a01c641d1a841 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 336988003 1250 336986753 336986759
    0x210c0108040f080304110303030907030519020315070c0b0f0708090a030f0309050a0203070312020f0a0c0e06010c060608030417160506030405071707060f030902030601030303021b19020a050a 84
    0x280c0b0b51100d42d580d2286045031a80c480742000f00702c106001e080560548000000e000620000003810f1088074450000c54141e404408441c1c0398112280000a400d9442220798900d040e1148942c05ea0100c5e1503d840c402d40b40e1107495000303801e40182c81400c04281140c0130320642c140d1212030168043e504000800c2c0042c040d5600030300568080c0d807001c0c1015610303862201040020b02440c0a016001011958480c0c1c903810700c480d00000100c005000340c400e04c602c000c0002d0011528000ca50b400103011012946800b6104241c050014940b90420901c0000a00050114071500300074020768001152110f0416103c680755071504540401c960b4040c4002ca01e89041141e8a0415204190780703460320b903100e5280030b610b04030321600500c580036410301091511000009050088507020303035400c500c00c01e0b0050305601315891450081d42580000005102080c0250002c200c699004c10351070141803400c0a009050010034846903810390100e01d2100e056142c181d0300f110145c80c0440344601c0c076a117 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 336989253 1250 336988003 336988013
    0xf030b0f13050702030f03090102040509011203020604030302340b0c090609040908190e01120911311a030102250804031e02130506030c0402070809210c010804 70
    0x2101c800c0e1944550345850001d100d142c824130903501e1948400210fa51a8142006c00074040c0d08140980d50080310703904000182d450214143c000c106800d0f030003400311074413036490440181d444034200c01140029101d10141340c80d01800b00740d030003c005085140c020b02d050700c0c0504030141c001d00047d8a80c101809549200e0381ea100c222007614008a41c006140c01c0203113030140341405080303030141c4440e0b542c6507000d0b003140c0c02c030412a280c0c0381d090380c50740d10a15100f03406d0811101585805068211400c0d8a4116810300d03140511940c650740c03040044184a8059030740304a4145001c0700d088944589a44640e01100452501514002c900075810041c0705259025040c0b607079191440540c2d8110403c500740a296400c40c1c0c06150000307508405030054400b840150001d04a080b4021324881100024040c0903109884c0101d20081c041c100788800001000040d4100210540314170318100302040309561404142e2a82c02a42064180034480347c0c0074050170b040510302081e05024480301084002a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 336990503 1250 336989253 336989269
    0xa021002090a0513060308040f24050304030c0201020c1018090207050c0112140f1e040314130b04140a1205030405061605010e030919081c02031303030f030b0f 70
    0x1d0f0054400b425072000d5843e07140c01809080d84050600307000040e0110b2582140a421001d82e511400501c03440541c800c50947d80e00350010041c40020014404100000e21070750039401d07186d005204541d0100743c40000562400c203002d02c400c1c045800080c00620f00008100002d004040716a01141090031940310181c5030b141c440104c904009940e0f5900c141c503051540002c080c00d00303040d40c0f9402480e203072001c03120707801c002c2ea07100541c600e0342c50303404051800100741c0d10720550b4140d981d8803400e002039075505a00d40144443c10406a110300e0040b03005d86041c805040142600c3e07044601041026050025402c0701d60860302011110407130402c04250000308a9040392000e44800b0b98454140c154051401d00096004107954242520407090b07107400405050006007c51703400300c2c0b900b0b0240060202031107501c12080180c00c200707000c1031040c480081140d0b0f00b0315a40180e0385898580b01d80380292090941003100407688200c0451b0340e040d03161054001c01c50040d1360301c06200300c03c1c2000031a01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 336991753 1250 336990503 336990509
    0x30c0706050919060e09060d150b1c060c09080715081503010f0506040f0b01090902071115190807020c040b190f0905090601062c0a0b0a021002090a 65
    0x200030300107004a025207910351811441c2d9070700360b1010305158584000a200c042400c6170644243c03c0704005c110146041401c1440d00c13030f4000d403030f21842c51000d8802c60103070001c0081c17590b101c10041c0318040080d52907441403005510030300c400182600c0c040c0780039000d548250041a0298412003061011028910351503141c010a410514590382e2030b003c6090340102d494010a405509012041e40c0c10084c540104d030040c0421641400707400d420001413070481d96094241c80c0064243c130ba08100c450066401800b00c9405000060ba11074041804940c2d14004a03011300d040d10000241003c901d65580c285550000d00c0f442d1680043c101424025039446440010600c1139685d0300d900d00c1c50303554500d801d845206035000102c00c40c59a0700445000c0e83c40a20030300f20007606100016012030340100c0d46905a40c4103840e10849080c0700141c1c480c100b401d540c40706900c2024201d1203000f0303990b0001884000d251018000f942c908144c04000e00700068401504600d9005124510076540c4007501d00e01a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 336993003 1250 336991753 336991757
    0x1c200307050a0c170a170c09030a02040902040f06080a06050703061a0a0201090b0a0c1404030b0103030c0c08060a0b040e0601080d0c0302031201080313062613021207090e030c0706 79
    0x9a02120b040c0b0012110840101c41c04e460400210b01d00000d80004140009015070b00d580c010342d6070303000ba0601d050710405102c0e55058100025580052403d0b91158504500142c000501c400c009500c100c200d07140c1e030708003018581c050511030081203000d000d220b81c0b00360a8903081c00018680b1102d442004000070620443d85408074421907210b100354461082c99402408180f0281000031030300004004407481d80c400030f0100050482540000790440302244e500007403c00190f8a551400c4400841e01070040711401500d1000007000c000030400203000c1d100501000990101102c2008122942d040700c003221600301c0c00040001c04008a0310200155031810005010b814610f0100d08610a4504000401107003e00100d48040004090078000c0c00c010801c052064840400340c031540049011004041d185903402503105103110922a003100e1403000702c035022021980002d01c0084080443c0c20700d9401044108407404460003107408407605078018524101b0110540764691215002e0641 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 336994253 1250 336993003 336993017
    0xd0c0e0a021639060219050c01050a020f03030406060608010510080103020405070e0a0815100b0307180504020d050f100b180f0907110606101706061c200307050a 71
    0x10314841c40d2480f0900c0740e010030503e00c006407045403441c43c1c156224001c10005114480142d614a1425801c804c40d40c2c0d003180003400701c440b401c401121142d002c0c0d01030008501400c0d4007054241001c002850160307101d50070202d941401c0c2072008020f000160b015034407078508406060102c9410003c041e0550742c0564020400d070b43c0b441800d80b0482e0f02c1030b154070381080411400240f01e401c0403031003107034808240c1c85107001c030b0300e8171803c0c01f1400b800350164103103038031040000c40d00361400f54248a8030103180c008a50303202550395000074100d03008800b0360f522f10740d241e030300f000b00b0300840521503a4440d0603c0580d86905040110184403400b402e022110001040c248092042e524440c08243c42c030b038020071810852404041c0200004000b100a0310103116100105480d13103018102403039034040999034410442c040301e41c0d00886c1407000d0b2080e500440100042800c400524030b80c0104200ea0020115400c0f61580c440c000c180c0409a007151803079424401d00c0480e90380541114001002458212 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 336995503 1250 336994253 336994283
    0x6080c01030b0d060c14120a0509161202040609050c0306040b150a0503060406080a031205061f082e0e0a060e06120705130b03010b010807200a020d0c0e0a0216 70
    0x80c480c101d00105004400e100850308007046001c2c034080c0e2340714883c06c8100b4003075901c441c0360b22030f075074640900c0c003849240d0301c1d60090148404401110008500050000c9800d96030b0300030308001c4950682c1c20444e1508004208010f50815000d10f6500600682c0c80000142d03408082c4001e07405902041c404108001002c0780640e500d6401c250040d01d2424207845100c426032030041c22420104441c2c400c001d041c80000383c01b03842c04001901322140c4003810203e04034040481150b48030720040040e03c3e072011f40201ca40c49041c40060005108556100c854003407070500300c68030034408005000882d4241844003c1c8284032243c681184c0041c01a2456100410b003403041c90304003802038000a80001c9110031524030f15840740c101000f0010142c0c001c1117008030304401151107850895041c008614110b141d4040651034213003030340041da08081690782410b01640081c0d0081c031100000e40d41c209045105000721407540d00441d8015540a404600c1d004a028072420740511407a4040c00082d100c0701c0030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 336996753 1250 336995503 336995507
    0x308060a031e02011e0e120120030a1d0f07080105060f040902180f040c06020d080402190f0e0403030e0d020d08060105090d06141b0421050f0106080c01030b0d060c 72
    0x11044c0d48000703036a41101c140c0001801006c4c920394481040c031801900c402086503031818803076860008421800181d00000c2c800ca035001c0740c4e00251070141a43c3e55035000038180c000c0c10550981148039103010b44414900408011b15100d410380104802ea49004240200b135035440e0301596400070292030110304035415000040d02202c060b030210402100c08803c0000c610f030444180340c42070f8071540743c0d520001e480d124201e0b5141695170354403011510600100c1d0140ca810003508184c0c0d4201424603a031162201e40050450301c586d0311130842c4503a072100384420590540141c640d1225104000d0980340007005000b55248580c080d0103092010b802c01092203a445101111002d45010781444002540c624048005054a1118040d1160400c02242040c410100d03014030604160601c542014280350755507100040c2c248501034584d04030f11040c000581d081c0405a6070341d8090000081140c90a0019030a04403900c00711030404d45403040504099480c504c08044043d040304002410030300b01401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 336998003 1250 336996753 336996767
    0x80f010c0c020d1a100602190b070315090c05090a06020a05030406120f0e0c090109230a0f0e150609010b030106030e2a03070b0711090405011509090308060a031e0201 73
    0x1010882400c50200580f050000240c841111a16821a075486c0058848c40d2880c0d492032100418508405000c00c1c9003d101e5045100303402260950660519039401d800350880d44451410004200e0105c1c6000c05450404854002801d40780090042c081080d40c40545074401d602515040c08400c9e514404160f00780e61103035450b0b030b002d41c60800c8000442503400741d0b220180d2035001d100300310a0001080e13001450249100081180b4900c506211620420a050303400081240070300c25615050794400c050030780115104002210003919010b41010b40c1c449031a1030003460300780103811900040180300500011241140c02c98940000c000761040340701d504003140164155030903029207072141108480344e4003401103250100c04a425640e6641109040fa000e60480941410305481080c0c0e46401c201c1c0d0001c0d0b0080c480c900010b4400200f40c4c525110f880305400c104031150381d0b031990307408050308003d4681e049030342100c45280c182d1270340d079502c0100085115021404a0640d031b1060459014041c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 336999253 1250 336998003 336998033
    0x308060a1a0a0c230d020c09070c051c1701120201050906031815070e030a1a04020310091506060804051b0315010b030a0b0a0b0d05070e03030d0501080f010c0c020d 72
    0x2c5040c12030130030744400042c0454210f44200940280d0546074543c50000641124005014002440c40d5590000c10b4074450504041903c242c061125034100501070040c00b270354414455100c0e900220142c030380c0e140344000141c12107510034200d00f46144c09170781c00c001076400c042e60480303602e80e40380c1e05d1501d05134144000c14801c010768840c01560f8101c2e4808000c60621440a5980c1c411000c2000c03010556503480002010707100d504a40404601e4030081030f402903200d800981250b51000d0b10800110844a40032400e82c3d45c440c50307010070b28051070280282d400a003030601d08a2081e0030a074585584894150303c0a160074688200d050751581c42c14000368003240c52550a0080541e940c00c000c10703866104803614a10b6524016000d40c45240001045040e00c6103036800d139052a105a1401008080c007400704402d004200e0400c00d0142d40400c004c08990030100300218442d450a080c3e9450b0400c0c1d00031106003a414000c49100c019807081041000c0e03078049840c2c41181d80d01d41007010104070568 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 337000503 1250 336999253 336999263
    0x9020d030c030e0103180b0c0912030403051507080f040c09020a1e1b080306030316061b08090a020f06070231020f0406080a11030a090308060a1a0a0c 66
    0x801106054001c040101c1c1075001e03448903207070f0405600c011011184201a0007981c01e104c0f00e100d0000c1024074840740e0340245444026450405841e0000310602d26100c41810990302c0041d0038402c1000c18082c419261032061081309280c248180051300c0b51100522031088420108001804c2c40800c82184d002040320103011955920752440062070040000280c0020f80031a0580d8500503106400144000c408040012070030540359880702059800906a00c1e8144414072841074400f6200c0d5a55132650300c955000507421010b4003100b031040307404041410500550901f044501d1501103003004039554101c5544025950f12000100703540200f95000e5008003580c2040381d18003080301602c4c403072942101c00d0b41461140300045401603110702800000059000c0c4403c00c1250300070b503042a08000c1e049004100b404400c46c900c105038008540f031030100350b00d901c1c52100b81600f1070400d6400034015181d9000c91400c144d034011403200705801301885504006201041c982c0310700e0b8010900741d400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 337001753 1250 337000503 337000519
    0x105030402040c0918090b0f0708040b1003240b0a080c060c010f060905071209020604060e03031902031c060503070b1e0d1e051006110a0803010f1d09120d0902 70
    0xb900c05da00811203070500322003007034450f4081040c90224260403440740c00780341e480961543d00d65032009000000a400d8030560b050744072000c400100003000c640c81c10104506c40e281d01003400303000003080d205144083d60044640f540184124900803541110b0701c00d007a100e1594681e142985d50340102181d06101c3c0d016440e122021429a40c076401147c000c00503071f41c9035450304c0c040f112500100d41c400180294064000c100800000d4050090000e10030700060a40382040180d211240070103070041d07202d60058000050000c825500216038014004034100e003046110309090200c0e43d01c100c54058401300220106030582600300b1300301c040b000c0e000e01b0500c51341c48060154610b00a05920382c220180c6007030104015201d00001d01c2400d20604a1022003060117203030a00c01d0395100001c1e9040149030042c689404041100e00d40118001c04405003940c0314185803440c0e280a00c180c1c620344421160b548418400100790000d15402c0e081410090180c0d55111085000b000b400d02940c000d4001c40c0e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 337003003 1250 337001753 337001789
    0x90e1e0a0303050136020403080a020c091e0109110405061201061416020108060111190b0c0703351905090f071703160803071d0105030402040c09 64
    0x4041000302640344261402c0c09142d0301d907514039000c003d810b1860308001003501e010401c14048902c03030a07a5140f040f02d005181685036201c0301d0300ca0303105c6504000581e1103011440a1414130030308a96000e00381d0351051603040001d085400714081c041c811300070421b403201d41501b100c507040801c031030041200901c00d40e0341e455a19020380c0042c400344100d1000c42c0024240441d001039100c1100c0c440c5c40080f104181000d003c1c0d00550f43c02d01d001e030031181000700a0720305040c00542001000103000d1601c1c10030302042c80c1072520141c1c48000400401c1c0c18038040c088040000d8005000900004041030510003a400307c10781c041c1c0e0300c82003260301c00501c14144240000a42034180d21040f0300500c040500580d80e914180a40e0f03500001d407200116800094100003200040c000c0007000310316101030f203250074440380b00b00400d4802d0a405a80c00c01000080c000415040400003007003004082c1b039000314170036590001c0c1c41408010000703070103562144440700c2030511417003854010f4204803040e00c4072644 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 337004253 1250 337003003 337003063
    0xc0a0b10051f090f050609060703022d0f01141611010504060506030c0102010c140d021b0c0102060a050403023d0507090e01080d110f1903120c09090e 66
    0x2c003028907401050b68084003250011003440f240080e17403806440f03140b40000c0b0b070080c0425035028020950850091014040301d4085800448402d4202c0740c400c4200c0c001c070354502504100740b11407a050283c3c50220000801078030000340300e62100c060700d0031070010b611449003038440580c0c2c3c1c000ca40065103007604100030421541e016a000742c00a40440310103044110046e801c866003000c1c0900410940d00600d210031900701d00a000000c24040f002d420900310052118103142c20350082203598101c00c000c0f440550b0304000c55a030101d1031b4402400542060746000e901c0e120b10a520f0b40f20010750491342402542a1419080188680301202c05940d5040c0b071440010034041d600200007a00e22030300065004000c184c00c2e4182d0b030072140904a001210314040d5400e00841c4c4480080740202405680400c4c802d000700c1520103e50550341e02021054036005041e94107200448400d00d19288115a040e0b0344403000b402601c034184000944040c1844508cc40d0a6040500345d8030400c0f0f074180b14892407 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 337005503 1250 337004253 337004299
    0x102070309050f09240a090504022806200f06071404030302030f160f0501060609150509010e011b08131502030d0f1e1b050c0a0b1005 59
    0x980030759600003401d500c4500f00301c04058a0894940d00c160584042402c000458291280310f03000c0703602402403540d400b4080340c41c01c07002d81d006078541c90303880c002c000550038811084812040701e0440e10f400c580404800f04000481c43c0504002c10440380703ca1100903002113003202d403150503041202c40e0001c135603140079501c64080320050005821000058200030040c01034406603641900518141a6200c200500503040401d00701c0010070403909450100d034a0b0350b44007022902540020911070300700741003e010aa0168040e09415011403c1440e1980d807150503200040024038001035100070000c012074259200480f440880300d0408690010030407908000c180c07826051031403d5050341d82d8a1140540800d1110810242c0c100300400546840c05900c140055014483c002070900c0c100b030348000310f200070340780c04171607140d604e0f0203d401c60340c502c04501500c42090300d000e42c600380d0340000054943d900340320300610f00c06801002c1703010643d1128070714024100190a02810b001401c821002030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 337006753 1250 337005503 337005517
    0x304120c031a1501141b10020c0d090b070c03020d031103030c040504140f1f1d01081b010e040f021207080f09010b062b050c0d0c08060a030605070c060e0102 69
    0x190744105860450350141d0307201c2070040e031140c11403800c064846002a544030503190b51846c01d070080c40e0707006c90742601600c0908004202040100700d0001e6001c0050803003a200d803c1000c24610500c100e2001403580510f00d4181d9074180c8425111103603a24040d110302002d01c0e1180b00d540800300c2041440300052020f401200d4007140c05100710130240d020032580c41010344000c480866242e0009240512040d00309100da1015580d00c108030f555201d004401441c070038607815020f0040c00040190340801c005040c0e9117414100145950107031000042c00d803804d0420303c0c42c01652a100f5034604805558140c45c000d21000c915011607207086240140000340444003011102c02160200d00300329414803800e20140000752442d880d00204d400d4407070003085003600c071111980380342e0080b1036030020500400e03018100c2454519103540031501e400703080d01c030452051030800018008200c40750741d5000510045030f400c140001826202c65804071105800aa805064a805c1052030011550154020644 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 337008003 1250 337006753 337006771
    0xd11011e0810210f03050708070515180d0f0201060306020c0606011b080403020913022206080f03090d030302070b01030308040c0509070f030518120301030605180304120c031a 77
    0x222a450303207031003c000101c03e203124050000040010700040c0c0301070300004a00d4004d0420398184001d998440312540e020711001c55140d000b20100c0038401c100c00c900245c1000b014900c1c1610050006009030391500d483c10b03950f00700b01d5840c03001d4048500070760104c006190440010755961a0401d18256034100c01e030b0b001400144014095031500c8196810070440503807200d401440e01e45503408008103940050305030701c003802090b980c450040e900c0c0c0204503000042d642c1c500108500403c5006d0458117150720681198020040400300c44c0c81c00b004a521441045901c1a01a203c60034200c000380100740001301507000042c004000e16400c01183c9102d1449000002001e60320351060105400003035880130045100c0e404004041406900310b1a4030441c070440e14500c03140b40c0c00f0034900d0031130b807103911680d422400401070050003a2802440d034001e041c52000d001c030f4040009420f64910891040e9080300111044902c00c0001514589000f580c0007220f45040d01b801300354003c8407070f13020703204005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 337009253 1250 337008003 337008031
    0xa060213050a12030c0303020f030906060108060405062407060c05041a070f0f050f0d050715060b03040206031005060d0e010c2c01120c02010606090f050d11011e08 72
    0x600d4030b844285801501d00d0a803254502c203400c0d540a56160b20208403c4003419003e1085002c4481c07440041c41c0709041d104001c0c940d600342140013400080000e02800d00a40c00c0404100960b01c2e00407051220301e19407a010480e03411740f1020340445000c0c03070800900c490709042d040308859034044094000d5480031f0009100c80307540c402c0340f0159845070703900092040010305525400302300f444105605c1c00c0d001d8002c2c1c4036051202801542800301044820000c1600030445e142400b400030300002403242840c00401c10b03982854401d022502005000038812440040020070461403100c00400822024180303c1d180c02c3d841ca4400c014003c0341044080e290b1030110654080c910544c14100b21032103550b45102c1c2c2c041429406c1008100342a480d0b8180100306280b000c0000c800d219240b0200f03403a40c00003c8041c185900200f0b002c56552080450007480d8105101c540d0b680040d000249602c015038868940c43c00e001a1200031422201502c0d000b0741c8000c2c101441c0d0000c2e2000d1143d9030190307040d2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 337010503 1250 337009253 337009259
    0xb04090b010f1203020c041d01050c03071206211e03020a0b0a051006050c0c09180601051f0c020a08030d0c030e0307051002030a0603021905041a030c0d02120a060213 73
    0x141c5220015201130b0059000d00c1809100d41071643c4641d03210607101039192240c0424081440c25110203035003000803080000100420303e075010990040e64401d0040c203110007132508400e10b040701b096804600c1c000d82e58404000411092200010b00080b1000d151444444c00f41006521070b81c0c201425901c1c2c201c03501c00200c507560584503040c030602050b8400c24095050032005c48094114240745191440340f15001c40103559004450f80c840c0c2501e048585042509a40340c0707040540c180d2080f0b028109000e2040c041c0081e286105000e400c1903d04244082920b00009840c41c1880d070020b17070395002c0022a0592030000340c010051020080d10300703100c448041c43d0101d6070b80c07080100c090802e40120041001c003007001c0d00107640040c0d81c24004201c4903103036000543d00f0050f8001c2c100d144480380d0003c108a04250145202001620075451119080e403c0860f8407405040c804522461051602c40c0c00c55803200201c406101013a01200c82450051078904025400580300c2540043c00700400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 337011753 1250 337010503 337010519
    0xf0303051215031b030115090902100507030f05070501090804090c030501060e060403150605040509160f05090a0504060603080a0201020a1b030207290a0c02040b01091a0d0b04090b010f 81
    0x2d0342c00d1030025006182850071099502103610740005020760554035048242c0a110244043c140038108501d00007440c0d5440707204005030040768000e00300c14403c081c00b00302c010030b401084c1c1100000702402c28964540359460310a005010301c410060940001280c0841d4580e0242c2c840d6409860644040101c0d03602c0b94001c0e2201d0300341c880d5440d4401e02c20801130000580c58142c40007114004000455060f07106e80001c0c06a0b0400c4681400e9a800741c8501040c41401c005180e00526100d03410440c0c0c681001c0104002c0c0100610040c10700342c840000c40c0c1080182d80c8a100199041aa1182c8406680030003c0c042d501815602000a1a088458500b00e81540501400350f034540c00910a2501c2c00d4400344400300d03407401a809540030204174029040281000b84000c90a650320600104190320410044a102101850400c00e0b401c809000c010007050384140300c0300c4030903281c9450726211f00c8810058410000550307000350420012408005a804006041c2c0d2080c8190800c496101c1060b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 337013003 1250 337011753 337011781
    0x1706010f05040902061603110d110d0c0201020c040510051825111c171515071721070c0b060f1e0307090218090606040f03030512 57
    0x5984503a4049440400c05494540e101e00c40c41840540500e04041c240b85c0341c2c0e50007030502c40080e0042403c844020041c0d04040c050007a0b07a100c942044600c0d042c042c01090f60b6601556040300511030001c90b42d0303003035a000700300d4102c0003c0700034014041d502d845001440c00008034485c590091488440e40f01c5040e0304206002d104040d1761344a0301040d0f000000d007040703004a21801000388005020400300d0a4000e105590101440044010055698100082c07020502d60b401280e01d01c90300c0e05001303c03500e000d100321a895500b29140700034484000745119951152780c0c0002c1a05600b00c502954030807040018084401d0001101410500100090640b0a0b030444a040008100184010000351a1255285c0086000d031000c4611498000868040c10b00403000d2081c11208040c2c0b94098501003140c1006005114025070510604407004414503e01c41c0b40d56114152020010300e09440c0c2034103840c000d224800740709052543d24103003d0007592241070921101140c6d24001050500080c2c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 337014253 1250 337013003 337013009
    0x2010f0201020f070b0c0405030a06020a090e01120f0501020421050d050906030406050c040b03070c05060702030c0a030509240a090906051005031503060108010b01171612060b0a0306170601 83
    0x40c03d50726114095607140050300d070041102c444284280000306041e2405c2006080301c5120b4000140c0e111719a010162140909030b02450b00c030301d0480b0050004800003004100d9155110015050350022441c2c440e001e4000c64010345152407480c840445002000c164030440ca0b402542a1181a00094400c40e03003485080170303803900704104001140010f00319610031035101c0c031144403460809444074014440c1d070b84107035008000500e441a0600c2408011700560346c10850740c0c00110300c0d0041c2c00d40500c0c1c5a00100c5009003e2240100d80b00300036440c1d4000f9000000341c0700843c540c900040e00c108015035000403c0210020310712190201e42d014051207408107440e8010204a0181040c034012505030b4802042490502e501c0c442d401c0c0b00d924104209030107004c013640041222008270000415102c40c201180c11298000c2c0b06025036044000d003443c0089a86140c024081800704040c1c070054403455200862440d000201d0440c403540c968480d109440c100032145203030400c158400d03661828280 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 337015503 1250 337014253 337014277
    0x51005011103042402010f020f071e0213090f050d0c1208090c120a02120303011503090819091d0f060103090515060f130b030d0f080c030712021602010f020102 70
    0x554a00807001c00c4d540380398840145c400440c0180001148800341e0b0800003030b0920078035000c2600300400c1801c04200c80f03030000080d81e0381d41d14401a00082d4141801034445024290b80b400c4900c24000c01540101c03090384c024040300c032104034032013004240b841704040a617801d2a002019031121807080d2a0b043c05107200800a0410b10301c00b800f00070200c040401029aa8400d00c08460700589030f111202c090760400601440e02c0790701d80412900161003100500d420986424191400180e085040c5c1d4031803003014803418651807004038146c41c0d48245400c000c04a0b40b250144c441e4192041e50401c1c465000048640d0b45600e0784001501911040400102240c100d160398403e403905c10896264001401020321101301e0008004c1008850358002c140c01c5503440c3c141c02c45090a041090300401c0b00b180c54180d81c08100034200500d8004060022001010008040794419218400c1c249801203c01d400315030f65540c0402078980c2c03c106d404200d010501c1010518812030040c17080d02d60401d440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 337016753 1250 337015503 337015529
    0x6010c030f08220303140a18080c01060512010b01031505090a0b03030d060b040f140904110628080c04080c010c0213050405060a0b0402042d0905100501110304 70
    0x4001950011801000003000c0c14030940c2c0400c02104100c50803243d07501a440004a5540030f42c01d000c1d1a600003410740c205103040c40941d43c9141e514840c14948941c10541507070711042001c4d281c2c1c5c0580b0b8260311081c6e100b07041d10340426103240194817540d51410262400c001d82d8203000070503080c1400034400c0750350004e200700000700f4410307440c0c0052140e0500101940d141032180b0b0031b28012215030743c01c0212421004241440000c2c3c000103110040c0103049032104000030354800086203910020300003000d05d64101c0b05060709807148000d98102240700d061020102c003409248500c094030411000000070740700000f2a0b030b51955101200e0503901620041c0034032541000054982042400007282c01000130300300869102c0302d520071107000e188504040d01c010b0400c40303840340503150444141e034443c074410802046002e1041031142c5612004540c1050481c5094092444903034055202500b00b600341410403290b4a02c402190050f2030090303ca50300c181140e00f03030580d0741e40164001c90440106c0c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 337018003 1250 337016753 337016777
    0x604060801090608061902070309080d02030d1a0319030302070206181c08031302060d02040e0718050901060327030f11150432031b010b0108010e0a0b03061e06010c03 73
    0x280303400078046d05000b814070300340d51366482f401946841c43c0c101c08480103130004140d10103083c0060041b50152000e050031000f140c1030328000640c50f04600b20f03001200b110464014420540240c068550380d82c0c0080800e511620111000000e13001840c0d006031050408410301e0100610740c80200c1d00c550f4000354000d095640d0315000c4030141e981c0050990784003006000d003504581c0c0b9400184042c050301d45c140e610740c2c2055140500000c8c1411184c80b000c00300d411003070180b5214079207454112004c0c0c3c600810358026005010241042e0307045000301807000321000310140764014a002400100582d42c40d00403c0107850481d071101240c2a133698080c01d00c3c40442c01184107140300c211040801d0100e03200c50441d0782c01d1107030150681d1851000390340000c10324140c3c040d00352292505140c1058000c0c880c50305903c00091030365405000741c0c101101d94901095a04286601400c0154030140807038506041000340081c07142e10308034241c04100300c0c1c08001903c41d4420100b00380f080f5416180c080840c20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 337019253 1250 337018003 337018051
    0x2d061407140c070320040e030a1d0d120c0201020c180604090311150114010309051e03090604030503090418170306030a0f0f05010c1b061109060406080109060806 71
    0x32180944468902c104400400400e801038001c0c9115045c4800392080500b400003131100740c90140750300900c541c00c00d104020400c0e0704580324040c0c0c140e110340d45801c900f420000207951901b0680014200c0704144d4800e525850b0011240030155000340c084412443d003150402070714040e00b80d0740180c1c04031800007003415801d00b50007422103c4d00c40d0030f007640c0608a600e42c15242003448107036140e84900c814010403201c3e00c41d01c48080b18034001c0c40c013484840310a0f155540d13200e48000344c02104c42c030402030403803503800248141c901c4880c0040c01540d83da42d82c0e04082d80e407500f1180c1c500d482075180205c01c641012000403400100b40d803140224440e03058580c2d074410960401000550140607003100e00c0c0009034040d01c1c50a00074898041001c034103c69080581c2120041e00740141071001d60040440582c68501c0050c8840c0d501c0003010442d03180c03411207140203005810580d50400030100e40491101e4005040605aa05011041160b591b4603c101c6030b441c0e0003640c448113060340c1c80c009130055107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 337020503 1250 337019253 337019257
    0x6040e0706030513020d0c090506010e0a03020d020f060a09050406050d21140409021b1501140d0602040902040302180c090f0f100f0f020f0601060c2d06140714 70
    0x6013200256000560031707004030316031441c10035040392642042078050106111510909030400401e10f048501c152115010612600d814040a0720500341401c0e14411545e5140d585505500b02502080d180d008a00016000f040b4500829204600b403c1020900d81001c0c07200713a140b10b4100d006444101c5045500301e0552122110510400500341c45001500018400a200501001e0401a0303501440420b4078226441c010559440e0b410414007820099083d00710103044d0b4100d008031410381080c0c800002d4a4296000004010500210300040c64072407541c0a8002c403802566400a0481441840701c2050000c0b500b042890105010b000120309098841e0943c4600140c9401443e811010005290048003c8002d0021b81d0141e40d50340303001c1d442001307840b4507089070008222034840e4a0803240c0702c1c00d05000700400c0040103802c000030700c080c1180303c031100302c2046c1c41c0d103402000188001c0b41825001c20144d40c0c2e1401c001070845a0f181e46124035114038000d0340c4401404001d140b400c0e06c19 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 337021753 1250 337020503 337020511
    0x40b041406120f0304030b130f052103090d08090f060f040c0807061b02010c0614180a030e06161a07090e06100c060b15090405070c050303040b060301090c06020d030506040e07060305 80
    0x15201c24100d80c0004480c03082402c4041c0c01040282f081c0c1c10011115803a41c00c211421042550040c400d2081c1c3c140c000802c0b25800029003410901c81c0e560f140300e9031800044414401c2c46224043c00e2002505204141501079805500f243c03005649602c02e460341c45210f80300d003c4c009080003030104640c0e2254030b400403400d40705142c40d03404540b081d1a864180c0d56a60104c9050311005410b0054608154440c2c026442c02480901040341e01520081e05a1042204090244e140026200141d04681107000c10003a8000314180300b91a07052030603101044112503030004070701c1104010075030441c10020103100303a0004207210b408140c5160f0440c2c5540c0c91540c00c4039490340303580085a4694511900d80b08000d10042e6568640780c513103042006489026103220305002c1012450008a0700102c00c40c1c0c1d105401000c110015140c41c0046030041c01c071444050015a844400850900e9000c284248080c41c0c65505200944454007040119000c591040b01907078814082000414080c0c3c12030360384 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 337023003 1250 337021753 337021771
    0x110412020a260d09050a0306020d0f18050105071d0f042018040501050102070608041505040303020c010b01080106050a0c1104060303050408070801020405010518040b041406120f0304030b 82
    0x14590702d00c80b1070121444448204215080070340c00c9654240c0030041e41c2118081403602076010740c50180400d4015110340400b819080d00000d080c1d0f00c805881e0010070107911034ad40c0402003081404c588492901907e80100c410b0f500307100208100c284645001800344651810f500f000054450800c941c50301050101600507460f01800604801c03a9600181c058240403d03050780e4070503a1440b1159000c18000003442540b90000611259a0014900c01960b05504065055840c0e9041080d6600500c0d683c03820114204410002050f5068001e0311281000500034440c1054040066600e05024000c020000700b0070710007008518400e10740401045d02900c036500700026036201040503203a054105070003003940000c0800052030104500301c000e10307607003000f14181030900c40000d00b03a100d8001c89803403900c1d440e00e40d0784045d6215482496103e200403c01c0041144491811161400854126100d0490b511105110240c08180544070040300320265207000d05603900d400304440080c0400e01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 337024253 1250 337023003 337023019
    0x5010f020c100905010e0406080312060a0b03040f1401141f030203060f0417030705070303020a030b0301180b0921071a010608251704080f04090605031011041202 71
    0x5000d0b1501c0c4101521220281c0d0340002d05410700001410122403601140d001e1032800b05d081001280100c16a03206c180a15880c40712920340d0b0700003501410707240d081060309010010500080000d80e10100102900c64203d480e61105000b00380d41c00ca606942084201c6059040040c50880c01c460f83d10305551940f9420680c1c2940f01d8011034588042240d000340380c10910350a0209001075a840354104c010b450b801c6514501c0c225000a10b07070302a03840c004090540100d96015480c0c029089080d0745000030b0300030050204049400d100110143c0d20555880c20014089000c0306004a840102103490706040c401e080c00b2084d01060b81c1d40400801d031400d014401201c0c80a1700c1e03031045c060083c100384c4d441c142541403074100c84900f0f120407003104085100816254070741c01d40240c1d21190b440034403182c05d525680c0b1802e041d1018482e65842e90480d083c009004075010015501407416140c1c1a02264040c0c48604001c404480140140e804c9408007400100524500704178000509803024100305 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 337025503 1250 337024253 337024273
    0x1202090412030e0f011a04090302070b070c09050a020d060f050117090a02040513050601060201091e0c27060801050f060d05030c0111041d01180c0e06210708090705010f02 75
    0x503003032010342d082c1c02c9a1030351517981d10042d41004c0800f204506c98100c43c1013210300040c0d640651f030b5945601c510380a0303110100f020003d022700c0d540e245c00200814442404607107001a00c81c0002c1d40300c0c1504500c2645000804036100304102101020740380181c40e0004501560206882e80d0100181440080e200b900c010300c0041c1c945014003400b6001030003a40e02d502107a07250560501c00140c000c0002c41e03152400c500086440c040030086060a0440224946030355818038090501042d00080d48541c4540504081c40fa0380c00d1445031420605041000000d840f0b00149081e40e00c19078100c0027818641c00803510078174142250300110743c403510440741361075001d1942c2400d440750740b5030b40110300c4004902046280c9481158400c020115a4190090360410b80a44280c8400384810030030196140000d9a8a50250f0700341489a88000e00460b125940304402c2280804c404a00225002e07201c13011804403801103a00d14083c180200107060520308000044485900022050045114001c012 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 337026753 1250 337025503 337025531
    0x80f040c06182313020715020901050c0114010512070807050111070909080304020f030d02120a09080709090c0f140103090602040b030f220807110a0302030d02030a0306120209041203 80
    0x21281c68010070700300c4030120040c410044140385401541c411240100305840002c0e98064aa580d0390007c94001a140c24002d0300480d218000e5000303440c400c5d840c10070300200428900c00c0e180e040310300c110741d403207040703944641d245481743c030380d07114a44040e1300104061045600400e140300030100c00c1400c454545940d800303488143e5002c050161440e1400100340b10079030900d04c21105200d007081d0020154541d40a100079903402d242c0764a841145004107400d000d661080441c1740c02494008100d981490b00d41e07404074020040701408642555003650300041d0040601108030071a030b61001040008034130140198050080f00100304da00d50342c00c02020400c100da15000e507008609031030041805103044403042c1c0c0940c0003c2c01c05c00b882200201800c0000311880129805150f0041c2d51031040748a11000c241500c005d600020f5142c0900c400040e45c150303002000e4016610b007a40e0034480746a0740e141280710000c2411020390030202c4200040d0200b9500780c9d58030b807003898518001560520380940 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 337028003 1250 337026753 337026779
    0x151f08060301110f180303091e0406090c02030f0c0c090702010c0e01031e0b060d020a0f020606010801031a070207150201020d0b09010e01060f020a0206030f07080f040c0618 76
    0x5000114215400303200c440d08003442400c83c01108401810320b0110031407402c612078014401e5070401c4640756035401c81d480c0c80074016104420310142c010185500d2005403d5100010081841e0003107141810000755114103005110801100b40c000c1d600c1c0c800052181103655000070105891072040107000541c5440d0004034911075407296000240c8011410001013001d803481c41d05504050908075105d4140000802c4801484460600010004d00c035401003105d60044d4449030043d81e00c003103a40490590055240e5441354500c0d82600c0a5035150801903c0319003082c00007400e000c000b5903082054a91610740f281d005921801220101651151500005424a5201c100617500454000c0d01c803501707800360b00704040f801c0b00e020302c182d814001c0d84030782c81505228007030401c940d6900c4c1c094918024005954441c0d0054161541ea02e840c005214014100780ea40a00041c86c5ca800240380003408140c1030f018035032042001640a2400790110340f03280b203624072800405013244000550030402e01c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 337029253 1250 337028003 337028059
    0x50a0f030b101e03110a0c0201020a050d11060919020d020409050f0f010605091e07050f0c070f08010905060703051f03050d0e03070308070305070f021207030b091515 73
    0x10381c480b00c20402c185164030f4840c0007800502030504261100355500800780035211801d2991510030440186400100e160840f140700c00b030440d01403058074800266110300a8444001c82c101161034646840582c9943d41205054490090000f20300d41001845c1c1500e413000460300040002c14401c0050701c900703042c030200380441d002c0340e4400f60b000400c021003800303184014501202ca0302c02510f01402107040c0110001d0070041c0030209000001d844500420030343e81a00351401c00562641440d43c00565544410700a009031400100000684c0c6801400740115080e84030300a4000360715a69419009008040c15074001c45000c82480e1107422202c0c002803000b14091001008800c0c0742c1c00c2e01500c10704460720450b000e604028801e00c04145140100c80ca041d52500d0107aa45035400c0c1001d040161249400a52243c03400c5050f5903100000aa0841600e00400d6100f10725299000000d55070b1070001411408003061100007115404d02e409110700499019105040100c0c00041d60090810a42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 337030503 1250 337029253 337029257
    0x6050c07060e0f16121211031c050604050705070f03020705040c020c09150d14030d0c0507171309023007022514041104090603021e01050a0f030b10 65
    0x8a1081c0d01c0c210400181c1140004881e1142c0c2c4d40f41007102640301900c8242000c0c080c22100c203c3c42848070721403081140011010001e881c1c42d0311061440d01d17102c2c529880b030010300368103150208140d481e142c802c0340d0240c10b5523102c0928041003a651002051f0b0217200c1603056010740b00d030010785603e443c058002c00c816a507014000b0795580b04104240703414098404001d941c1c8660001c1e1654071140101513915802544d6124001007400403180f85104512601d1400b505180d5200500358218018018951003955644441c4401c0d81100c5454021515001c1c0d090009000400a44800c2d500405505130f4010030707480c2c10b030104903928041081081201014509403000c001d806541800340190600d040310703000c0c0321640a0b080301c0c9820394450080615504140b02c1c100c01c0c0303940f44da10450b40074203200d541e00c0d1104d42e5078032a407004107880d00c003e80c0561054412100400390401c3c03103840b01d6405071602c034140b4002010440790350750900310020a0507036a6003010910ba69400508510314019 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 337031753 1250 337030503 337030513
    0x6050301050118140112150612060c030e060c0d0e100603050d0f080c030f070513031b0b0c0d0302161703160302090a1a0d0e03041d1306050c07060e 65
    0x5001000100d031001e10713190051105920040c800400c401e40c5c002c000a800c00d0009104061760440c46008005585c0540407848540c00d0100c1004190781020380d0681c501c0c0c504001c50240f007401c090715580c003101d1604e5203600811144140a11070f6200440403e0458101c550f1032000c0d01c200e001f2102143c0040ea010360150304c1f40c0000d25401380c00c10302e0012403840d1041190500c42c481400030300000d0071054a503541440000c0a0500c070780152880421403d11640c1c00aaa03400c01542d0b8100351030b0303036191a055034107021801c039590780c040f1408501228010074001d802918101d0080d000400c100e10500068080e90002c0f03030140300400480800144c415540f4145107814191156540f843e54003458010700c440503559440c0c0202e0320441d5600000c041280c0780c4810803640500c6248400e10100f840e10001041415002020f0001e4510140d15104c000a83c03911035528ac0804849014440c1940d041d5031b8009051a040320350000b07980380fa11030502c0311941d9842c050752244410b03612a9480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 337033003 1250 337031753 337031789
    0x40222020912071e0b040e19051501020106060504061713050d02060f0a0e060f0c0903070306050103020a0506120a0c1205010b18150708030c0706061d09060c07030c02010201060503010501 82
    0x5183c00d00b41c1c3c0151611012107804d0b20346151074040e80114495070500c0f860b92800145803e2a01800502c0f100c4050801c0000d482c0207405151052840d005043c01986040804210b40d0300506c00c50341035032595221748140724142c12181c40c10400041903c40c400c0782103a041030014030100209003051140d03030058201843c182051720213402005098480c420306121a10489040c085070041c5c201c1400344a81c101e81d55141c51040341c503c102d0300095050310654030300005018803944107a059a10031503401046541c1c90080080301d000d02c0340041440c180f060046103891409030f101414000c4581001c040c2254026000310841d482640301460300714000443c0d0700d02070381c0b507403444107005c404070f92142822469250303000c007038020100002c10307110002010401040541d4156035405520008c00e01480352207d0141a60140d140c00c0c10804044040c003052115030301243c280d1107031030306584160a040145d141152a0a030000b402d9065550710703107000c41c540e02c003801003a01811101072424001c1d80703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 337034253 1250 337033003 337033019
    0x50f0d050301141c08070f08040f050405090a0c26030a080105012601050d150908040510020601050102150408070b0a0e0d020a0b06060906160609030f030504022202091207 75
    0xc0c2c00400301e8420b98582e80003c815904508132038a05640010315a03845451034604030801112056018080d07000c08540041c0c7d0712505c012203400d690f010340b030620103501e07480c400c80da8681105000030700420501c1400d1100c000344a2000740300c94440b03004408500785865080c2c0c00e5500070507004001484180042c040c55030000d2030b50341e0422007450840743c903084e811140d454403407040c040c40d449804138448890a028600300901c0000c81c9980041040c1040383c03034540300547c040d100e02030003a13a61000c04250a8001b24015040351030607009007032a10903a40180c144840010022075540c50305104102c08540c0500c0312a1080d96402800a09512545080e80c030b8003a048841000319403000030b01c0c800041b80e003020f0740d4104206450598841c920200025071600900345c0001d182482290308100b030221a03001010494003944443d0680048500d00720700b6110208d801135080003400040045001000307602c12a50382e000840142051305038000104c4003284e503d200d4619500c0b00c982400154 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 337035503 1250 337034253 337034279
    0x30f150303090306070f020f0f03071a0906010612090b040f05070f0b19030605030d0201020405130e031b01150e0f0901050702120d0902310b030a0204020304050f0d050301 75
    0x140210300850925603007400190356800000e00c00006c0100b40d0220403102402040780c0385180d500e12042d03994a402c0070000c5540d90f080f0030020344455080d01c4102c0c504203084001036001e14201e00c09070029030b00740380c410b40c2c0311045c02d07900c08041030b42c4e1100540454032406a8502440c846c4007455810b1400c0c0c01c0c040c0c40c20400e6003140b9003504800c8001c00110b00d564044415030566070800c1c0d28482a034840a400812082d880306400d40140708003e1103141d030642c000c01c140c0c0d40c00c441219260b15202e84403012503440700c110582d00c1c0d20030010480c142544c400c105c85036400050001c500315a006c0883c130041c116a0303010341c0841ea458070600401144400c2c4040d480000340d0b00030052442d028600a5842c0054001d00c00409000601e004105a05420488c440358018141020b002c4d4400030700c400c0d503110b5003896460161a00f030303500c03080c00080c052100000c05c010002c3c105011079808220095101030000c45117441101da038006114002d012240070000d035a00d43d1a100d600d4060511001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 337036753 1250 337035503 337035541
    0x702030c01030b01050d110c010207030216090c08060910050a14030f0a1e0f060c11100c05030615040e0f091005010f060503040302010b0a1e1406120601050d02030f 72
    0x2160410452602c01d99119007a01d170501d0481741e000c50300c4847c941c0d0344610340c42900c950f29100d50000508030140741e0000360600c00e0540c401441d0800580c2d44110a0846924124040005000d071000c12018039000752840d07042060f000901e1041980c0750001421900c45502c906840f0908060b441c902d4a002d11910100b09003c201402c8071100315502c0344034900c094034032003040104001103081032080707005081548950000042010110454000c1c041c0710302000c20f0074543c0b280c0864019055818010f10b02c4030001601e4190864540d002000b00c001114a020110f40b01c060000041c0c3d07003960004d070b5000312030046864800f401e00c00101403e080502103031103d1981403800403c00e0120b0125072401b1070b501d03403409507207a0f00d880c13034100c0c00350211004165202d4108031011038500c0f000c00f05103882c803c540300700c1550150748040031043c0011038140d5541c40081840012000041c0000090340f1100500d8014509028011000200d8000792804e814105010307081000300003100f1032008203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 337038003 1250 337036753 337036757
    0xc060e040b1c150c0c021c0b0c0d15090506180c090915030f0d080a060b030c0a18030305030615030c090103152c010f0501090603020c0a080f0702030c01 67
    0xa07400003004140c00078030440390709401035400a070701e5092100049036807820009048061044070030600e0010018200c03040180c0c4100400a2240094030f401d810445100da44a0340c02c4042c1e03550f03d01000e4490b00014032411055031581c008000307007801c0c06001d1020300300001001400d4104101807003640c8003400040c13120002d54006011040141c201a01e05031720040307443c24065520011100003c1e81e50416641d00340c49964281d40320302e000882c1190709002955150001a034030102c0c42002d980f100e202c0e00d0704d030400c20000300e0201034130a002000481c0341e23820400354032010f50185203840c208940c02980099400710500101d0300e064510300350424121a032071400c50400d4a12200f5034070550f045641403507a54455511909241d0340390a00402d107801849c00c240301c00300c0300d4203e1201d100001d01c142c48070040c00410031f8441001d040d42690f1040e903441c902075041c044140d001b1740c8003420545103807042d4401c04001884a070010401c04508420480e00c9012601c18580b52010512140341 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 337039253 1250 337038003 337038011
    0x504150e0c0f031f0905012c010f061b170a0306150806011206081b01020c0405040c030228060e01170712020a09031a100608060604090203060303160c060e04 69
    0x290703181c900b605807900103c900403d440081e100d00712021035820b555104000481c149000040d40300d00c40066031056040c44080c03103086d48081600350a1081c0c00b4081c1c1c40d200310007a07005201c080d210741985005100c3c0030505420112641d241c2e003031080760780f4500081e5840002942600607a16010f083c0041a1410f040344540011200240403544000e0065041114003078084002039140e804c94030007840a00300351148020f054034426407008242da1080c3c003612855041e04100d00f4244213840c401c80d088041501990300f90743c204060b01708801c0c10307421039100070007800c040305240c0a0048007c2900c4c2d00e90b0460101282c0000d48540940300103214100641c0b8204084241c01c8203540c094600d40d4080140e0b030703c2c1000c1040d02d85180700e400140901c14103008000340500140308080c050034100e181081d0725540c9440480e0400c0b401c0300c005800c400240020070220b078554015541240d00102500d0501032099041940441034040c26075180100000c10000c0c0b6420140343d2120f000240c901340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 337040503 1250 337039253 337039267
    0x9050102070209042604180f150f050118051f090914100e060907050f16080d110403050a02010e0a120b190b1e0402070c080105090c040b030d08040c0504150e0c 70
    0x3d0403100e00194460fa4907a40e1200c2100c0701c0342d000741d50b18106102c11880c002d403215886c0c01018410700bd414045090707100071480e5078103184518012110003d00326515002d64460800f000c4440023040c40510440c00c20210700b034040c1d800382051120b030041d100106807608a10040c9000b155900000c0060240e07000c1c040c5940341c44910340d83c4007000707040c05655000083c00240c0944627151400f59910354800c00081085103402c014980e8584460b42031140c2c0c2c07001c1000e82c0583c8503a10009045500c802407184c019402035400c0141040c0003404a1007080e0303264030310201d001ca8040100c2e94244000c0c1000500c1e140d800e044540303480c00020400c015110305c000f041c2007924076016042c44d40c0c41c8101c254001d683e141c04031360302981d001070f500c54030a0780c50045ca4080e04081d00c00c50214004e000a411083c2040d20900b080000b000300208021312040000751030142000d00165002c076000400460340d51611700809000909083e07849800300c1c500f2052000003803029140d9030341c0040401c107803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 337041753 1250 337040503 337040519
    0x27041409060601320403020a0b0c0a060f06090e010e06010f060e010c050c0307061805060a0804060b0103060302060a0203070203070b0f031b070c0b040302090a09021309050102070209042604 83
    0x500e074008003c1c00d00000c5501e0001500340c40b00c0480e039107481c0e00f21051000e21044c0001c48080c0044920a40e01c2161550300c42c01c0b440c05500913200740c0d02541e40f200201e0804169290001801040c1b44800000e00320f07200c51b402e40669007c5980c808440e03460b01e90a894441007041f03218010100c3e90741115080703080c004024601d0204040c280d040000004900040c00f50070701c84012080801011075440d207030f480002a24040c00c00303403284500d0301c145400180341c2c100101110003a04460f038900503107a455030f40d240c4c0140702c0001c44504060f5500004401a10356400a1402c05c01a800858444806104152816a10790820b041040c410320152450100c90025260400f0108109140c0c2014055410f0050f0040d60009000c0084a07040011500201e10080095034000c0d1411111541c5500c0804246e40000b0b90003900103000d2800c01c291504142c1c4500600c600c1103001501d448101e0300003078a07110081c1c40a564881104000d8860204540c00a0441e5510300000b903003000e140c810340c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 337043003 1250 337041753 337041763
    0x7050a0504090606051906081e0601050c0f06011e0504021e0c0f100f1413110109030206030c0a080f0c160f12020f0c0609060f09040227041409 63
    0x55500442c2c03a4800070081000ca500980050701c1c0240080170000880091a01525034a21502c404901c1303038404681100b10f100400c0001e80081c1b181440d040e02c40100440b49540b01c0001010321340680301040c0716640c4180130070341c0200114058903a16006041c12202100542e50010b07101350710411480f2142c1c0daa5540b8141d003c03c16490540e21210400c0d40d160824400c2c0d0440c42c180c2c0904021002502c840d68050031214400d104100480383e41c0070007000e11101c0556569116035016a416000140e080e010700484007070624040f50540d982c4d40c0840c1c00d5410540b428030130501c0103e8001d022580c000045540000c050115103180e0600481d8281544640b040c160002a200390490080c0000301da0a00840365000440900790b42c14000000e49895800785506e049000d403118182c0c9500e00507054602e9000000d0200d03142c041440d0f10202c80c0d61000f50956007103070302801140c0c0f21040c15070030401070400e1118905400100c1100b0081200d181140c17101d22262901c0c18408c1850340061 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 337044253 1250 337043003 337043009
    0x103060f05190b030a05041506050112050a060b0a05041502060708041106090d080304020a0b1309240e010608070c0b010b070501110d15050d03050324030303040c1707050a 75
    0x2581d00401200c400e54604000d40303e801149807001c00000781300244100d50300940c802c90082c0303080103003500b45224400940700180b080780d00048080c1001043c440c282c1d4009500503d24180020389103031348103800c45807a00060700707078004100003080c208100850721030708000f040018030141100c2e1410040141510401420243c840116845054942c4c1c0b50002101d08811000b400c14000c80b82a14102d45146c0c811a000ca0107400c20b400c00040089400050b54600000502e06110090030800c00b0750050800c00d41410300b0300c0c0440002a10f120303202ca0a480030b02220b100c128443d60608102030229180601351008001d010180280890040c0361001d042d5a80b51084c3c03a507490035400c2c41405407202603040e000a20000074203c10201c5560f10007103050071000210980c0301d60b04e00403c011100e07245405408990304100051444002d2210000000032007070100000c2d8149502081c6540c00c03c0300c1c2211500c0e2810002d110b41d5188003001d1015614140043c60fa041c1828081100050288 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 337045503 1250 337044253 337044259
    0x1050106023307110a08031021020619030b13020703020f03030c040303080901150e070912050601030f080f03010b04050108090307020d061d160306050c0304031710031e05010b0103060f05 82
    0x100c138001c841c003404030001700c0350001d803d15200d0420355040c0e4040340061280400e611400c0f2000c68030141c002e0150003100340c000300114140068072042d002401c18841c1030104040d40c030010141316566000c19410118001d9000507159000c03854003914000e1049010243c0e64000e1080003620000038040b00c0c01d4035858a004d180a4880e65141405404956008410b104482070081601d80d0300011083c03080c503080c0d0307030107038610340c0c420000000b4820081c01034120707000300c0c0c014400719500c6114454030713a1044030b40b07514166a11900c40c00d160000e130032006425030002010046503a0004c4525003140000300618a451040d9002604203039481000504603500d80b4202c446002c900f8543c0000c0190709420b5407445e4a0070301e4414144c10b1140400c0300c08502c3c1c5804203d0340c400103c192407149626844902c10043c03843c2501941850040000f0340c0c8000140c804000038900103920045d01640040c80d80707500000307203800703403c4d40d80f000f4006040615002003000030102d40b402e03100440b44d081d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 337046753 1250 337045503 337045517
    0x8012103050c010504030e150a051603090815060a0b0406121505060f0d05011d07050711120f0606030d1d0a120308100e04080a0509010c020301050106023307 69
    0x985415201c030b000e4090b9010465180030304000c10316070800000c0e20907078030484010000c076142c0924480c030760240c1e1416900085080c060041c6c10b5502e5900c520b01a4000d041c94010076590740910b80ca0144043c00310240030324010288122810b111230300c48054491a11802c0c1454104038004245101075110307003d0807901c5501100c0c503607412030b0004018003800741c00c0039078031060005900d0155000c0707100c55420314036110002079550b2070703030390203580089901c407034002c0381d481d42841181d45400140064a00740e100c021006810358884a044143d00360000150030a0b03a004507009080140003403000f0701039001129100145a400324a41c2414540c418403104450500d0011584010146d0440350540e00c2d00303000e100602d9040100da500c90082d03030007032000c000d8451103802107682e801d0b40c00403c95101848580d070313145d00a030090154490180b601c1c7d02072050b03540002c0e0941d80d080c1d0207403025801100310700b404403808403441c0302641c00c0e444507400141881e0202d0b00301c1c454000c05035001c00c500c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 337048003 1250 337046753 337046819
    0x50a06050909041a10030b0c0f1c0f06140f0103090305091c060239030301030609020f090a1b08040f03080403020f070e18010c02060708090708010e0a030e010801 71
    0x340c244200f1488000c019041300300e1505030444c40c0c1312002c41c0010b0b01c0ea0b25070800018042034144041318400149201c580c1c0c14480c80207070b00d52100000b1389000711560744610110b810134280e4030861005000d108081c0d80c0540301c0b031042c00421403198004604040c01e1481c00da0109400408a5040300c105540c0130403410b10101d54480c1c4aa01d10200802c41400011212038000b020300001e44d54124408400c001c511f07000d80280642e038448120825190800c0c001000440c2240d0b100000890018000c081d06007200c80010348138420844a800d2002ea8074403d462090241d0340324a41c001101e41000074071401c06440d400c65007071988400a0402c511440040c003014404e00122116890020444035580e450300a07501240d0001c903080403103440c0188030103400340b205004001800f9004c2d005000c0d5525070380c03001c480d940703002040c030402807080705000201680244211a42ca0742120060f0106802c1880d00501d10a0207901c81d904000e2404010300c00800c2030034401a07004041d140300e40340422 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 337049253 1250 337048003 337048013
    0x80307170d0209040905030a08010501080709060503060f0d050601150c050c060c0f0d030c020d050f18010302160c0e0108060f0f040f12050306031011041415041e050a0605090904 78
    0x82520842600142001d41700001c01c940080907200c64180b03610b400c50107a0321500111940a8111908000540f40354400c11417039001e0b1005540010016080445848401000c01c141c070b884002c0485103944203000400900d8264181005030340510710b440b401c405215142c4030f41d41d00039010510f00c1240b0001d60401030200c1000404c1024000400f940c044040b1100060b0007010545440300260103241c0420039194420b008859031502c03201d01c2c0d6070600791031442c0d06d5120f00350703903042c1818554204403001208800128400c0c0a0340309014542c2058140ac046511140e03060740a02c0c4558000700c10b012000b03080c41100d40e1f201c4503054240c10340d035032141004000ca401401018010030904c4000c00c02003a0b07c03000a40c40b9141c01e41c11203480c0b041001801c422034603042c01c1008180d4051006011a210520350403241e040010031946010903120080384469000341c1c844806000413001c02e0800a84644480f001050704882034424903160000141c034910894801501c02c0c0800000a002c0003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 337050359 1106 337049253 337049257
    0x1309200f09010e062d15040303091a04030c0605071e0b0c070311031303020a0b070201020c0f060d0e01020c01061a091908060a090606080307170d02 65
    0x40c1c601145043c100d000940321590007900c8600680d01d2510112503c120700c04002c0728030485c0310000742000218510034072030401c104c00c140710801c00300e50001c810008031884a8074140000060300c4100709107203d07503007000700502849500450856849030180003110300c1401c00802c00d0070603903044540407401c58402040c0416040008040704035144c042d0000c2846420080503007034516500f40c0c04c5400c2200c14041c0804e00032820415403800008007401080d103007117203603e05006500001c0d1911201080c541c050609030a40000f00d4960b242103e038030600c9200308204101c15890b0b854041d50242d08103004942c20020081022103813510b2807420040320540303d91602d8400421300000c2c206032489044030640b18840011180f20034000c0900c00c01100c0000121100540b8160701165100d4200c075403a03130b0051080c0c100086000c0a00f0111444501003240c80e1a5080e8201c000381c = true := by decide +kernel

theorem cover : BRFrame.Cov 336870503 337050359 := by
  have h0 := BRFrame.cov_init 336870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 336870503 ≤ n) (h2 : n < 337050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
