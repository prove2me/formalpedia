-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1848
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:53:37.980781+00:00
-- url     : https://prove2.me/submissions/c4401cce-0b4a-4454-913c-7943b46e6cb8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 332194244 ≤ n < 332374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 332195494 1250 332194244 332194253
    0x2010204080d0306080114041109060103060825060809070e0a090f060213050901050f040f09050d09060930020a08030f0d1103010e0103020d03231c050c03130201020a 73
    0x80800b0448000643c0752201000301007001d02503406240c0044902c17840f40d09007961102849010408298003d01d0044002040c81e8020303440b5000400c000400d0f00c050f000f5840900f115920703040c2e8400c002401c8041c01141c6036204a4030f152103420003a00906480d420070344d00340407604009018a05641d01c1e010048006043c0d0310880f40c026214890158440c400561090003201050300301078080c2000e80d004220319964000d045a0900e41542e001400c1041c1a071040082d140040c8050182e2044030a43e008460b444070451040301c1c0a651000b809a840c2d00f45414003410b214070400460014009680031140f0003240801d80740c0c8001c080507841551b071800c85040d50042800c035801e010700841d120000716402d01070500f00c280b0700d6059915541c14011554071710041800007034051038440b00400d04042c020342d0b1440074400c0d0740c603a5503481c81410084488079440404141640390500c000c0c1140c3c00418040c8502650608516904540d104a0081142850024260b0442c42111650b50106 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 332196744 1250 332195494 332195503
    0x90d060921051e070f2604090c11010b150f0f07050616020a0807020f0f1003020a020c0f030604030c021519030b040903020604020112090b0906090d081e100503030a030906051b04090207030201020408 87
    0x10088440007040c1e4120600c8080d001040350418449075334104100449103641322841c44c003503401e1140a07151120600807805405001d901011600e5030000107208040c000000365581c4035614401c090021000440ba040340c544001c203000515481d020b02c5010010710b4001104d100039070b0050312071981c8864450018920007003130921000860790000d00360300300907030500510003101416500000f200001001080e540c1000410113001c000c0266071010842d611481c0d416040000381510301d80b00c0040c5114651184c0c451701540d800701c1d103043d08034001800c1c0383c0200141e458268025180c10756a40c0c0040d03400100103645012003d55442c20140007170080704034140510780d518001c0540d4986111220b140040008001c814088890108550068154203c2d100449031400d082c0580e1107402c4500c1040d02d25400c6150303d4000494080030507030381503000c54019070003544140301a4807070418810014000340d424000c0030000f00f20070f02101c0803540041c8429807091000624159844581c1400c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 332197994 1250 332196744 332196749
    0xa0321030b190303020f0a020612150d050606130b0904120201020c031b25092703030b01030501050415090207021801150206010803090d060921051e070f2604 69
    0x804031004060042c145e0400402c0202c10000008201d203000b00d0700051007074001c07284202400081d0380700261400412039841d0361002d0000d001c0701c0c07480002cac0c07520b2510f83d117041741c11501840d818071181a00c2105801400c06c0280013034051080b81c1c07119112520903440c07580590080d50b408101d17404d0310340802c000038142841110b0ba003041406000d030344541816044401d26240ca80c3d20442d9100e4102c40e041e00c3c01c12030f031082030006001200716001e20000e0b202585903560b22071000e54239a00345500740d0007400960200760f80800851b0f88a40801048130720280203000f40541c1303080705014005645e40102a024002002c41340d00481e041c080108101d001d8001c0d000c2004269022214242c040101502502c44500654101419a00407071040e07801ca08001d0419925142080240f0415417002d03058004030019402c0c480800d900040d10550210b81481480045510b00e0650036110205031111954486032031100d0303c00710b880e503201c03e0000b45548090140c04600c481404021203008100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 332199244 1250 332197994 332198029
    0x1d150d020c01140601020c09090a08190305160e06130f0b0901020d0f021209040213080d12020c1011040803072103140f0717040813050a0321030b 64
    0x3912400c04100c5803e5951250032035440d198102c00380041c40e078021400e0b07005100107856030302e0b1665841404602d801c2c0c0d804005410035500240600b6020201904258907407035035101400b0030345803646405034903551045114000341c5484140110784c640303000141064940441602d201035210b94000180f00400d80c02200070500001b0742515958060101207403d10f154140030740c9000d8141c901940b20780d00c0c00c140401c0e18400048140351071341c03964143d64076503000703031301c041c0c800741e00c5094a681e5000040b80c1c1c0400304190308481c980e02c004038003c82c3c074118004c0c2c4c003810601350784c42029005000c8070700b103040c0f000c101404003180c088400c1028003401402a00d01d16032403020751403038950b90520400d181080600344144c48403403510418420750842e01540b01d40030076595900d000c584641041c00041410300071002400b0a011003440500b1000c0c0c4a00e480742201c0b952841000040500b0744001084100703844908842201151aa141000b0450901284402a800c002230000a07143c41218 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 332200494 1250 332199244 332199247
    0x4021003050c0c070b0a08071b030806041409010e1603030e1005040b0f040608010b0301061b1e0b04061a0307090209150318060c0f07110a1a03041208071d150d02 71
    0x2d40d12603001000070740001050400d80c2c0180308504052031600d140c9d50b80901070103c5c00780030400e40d031581e9105189a5030314241d03a2485c1d061009a0754082e00c06904800704511a02102c20801c445402c010710880340c0c0350700c1c1d09160503807072810300441c1e00607400c080c01070040600c00003449404850041000312480281d480d5501c1c2410409000b040060b0000c1060401c11b01c010300c10741d034100b0085012034000622030b54640c0c200e4980b00307600300480004460450b91400251080101265046000c0c51107041e0500461500c0d081c1103020805060055a165100480c10004075006500814080101400318a0b8083c26807504c80440c0e4400c0e16040381a000d51a0407441c1d1103014000a40c004881c13000003868600050a01b9009005140340a0a06c450f2410805a155541041c2c04010442c1030074289218215021016032600b08841c159644103400301c0c000902481031601c10301c194a20388954419401c10361b04001e4ac01001c91615400100ca00d070444540d104034806030079410325101015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 332201744 1250 332200494 332200507
    0xf02150406080106030b0f01120b1c05100b210f15041b0506040603020d0b04050109020c0706080c07060e15010f0f091e050402011704030806010f050304021003050c0c070b 75
    0x902c0004164030810070075182c144601000d6680c0c102030030380d520091070328240c5000303940a900014041180c5007584210450341d4a10412b040100301c440380b601810646000560341900700080d01c031140c0ea4940e100302c42c60f200f41c050204c00c0c01020719003406107003112110040500f02500c1e1141c1403c180d10611000001c00c0200804a1019400c86107040301c00319615140c18046501801039014a0080c5a004110202800030540c000030341900011310601080d651a442d0f44025807021740c02c144c080c001c0800209a480c02804800d00a8070701c407070424941003523522010024803000e869a9101c0c007450901201031103000c00d15078060000c00219201d890b14113050380c10b60301141e0b4424140c80e414550200c0001c020301319541105903240e003010911750341d03600c0100d030104100c0035402403681101082c881816400040c86204601c2038035070500041c20343d40185c2d81404111002035005001c9022070052503c2508030b203802600e03c00c0503a042242209807182040e0003074200501c03071070340070648 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 332202994 1250 332201744 332201747
    0x2032d060901120c05210303040b0423070302040513061d0105090c1c03090308041205010b09041e0311070305030304110a08330103080c06070f0f0c0f02150406 70
    0x50320b00501c00048404140801c0d81d13180c10a112840c400c9910400c03128655120f03a110074100a01c1402d00031056030355a14051514541144042c0e4041e00c0f00002e061281c1444540303101134aa28504450060038800d00d1171f07003040060500100414031075071500311500c001401c68054402001c0d5500310048425064400c15821a1401020b03e00749900410030100181c5440c1264840c0c0d2101940c03045450082e420141e80c46529507200070008400054000f47e480540211810304900c11402482071321070200c200b00071004d00381c4000d0304a68030a10015540c5406a00d8808000d1003810b001414401a001e0141469440e070b20948090b00300000304010440b020840d08074850040b00c085501c0ca08140202c0d035112140a666010078000d0040000120014400310701188110041e91a4541c0c5a103896400c80c0c018080580c654030441c40881d8031103014800000c465042995402800440c1c5401207820b4440e08801f950328400e81c252040140e110207440142c48401d80620503036842c5080b40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 332204244 1250 332202994 332203009
    0x20702060307260105010c1401060b12010303030c091a18040509160812190504051c02130501060806040b1201090303052505040905060316080609160b04050402032d06 73
    0x640c0f40c01841c81001448144c0e0030605030201c41c0e8000000f50303641101000e030f41d0300500701c50704031000441d03000c15030711740c01940c02c0320690591b482554140282c002e141016140c40c8480d019000c0b0012070180c04041486c1c000703002c0c0c100d08845001c0c1e845103038070701c50100d07044440070f46110605400054802c0b01d4164048050001071488100409010800c0220040711780682e40b000c003054045070000707000b1148500c040c1d81c0a040024000240c00c000c0d1101203203e10781d00728040b4041c40c411583c018a024581c0309450488600d40c494036041c0d40c074642044000c014400e90b40741c0c0824508040403000700e00744210302c1281d1103924000307881e0030132070b1004002e0841c0c510781c40c07140f02e040544510010b07400400d0701d040f00c4145002041a807a09070001e420104910101501d14542c5500055104400501c0314094200c1209072001c0742e4440c83e24500900e01e03800b40140c2d28000300000c10050030541d00541e88401d100c0d0300710410b080c1c0362001c0e00000028a00c0c849942040f002805001c1c40c1050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 332205494 1250 332204244 332204297
    0x20a0611220311150c1b1003050f010902160803010f0806010b0c0a0f2d0b070e0f0d0204090b101802090319050304050d150c020c0a09020904020702060307 68
    0x1c007140040d031550740c45581e01d550b0816424015842c90b5004000811910700740ca200480c420107558800420503000e500c4d00e590b4509030b41c40b503101d90b806540024001d100d034500441d60006454116824150320030041c0d8400481d04a40802564140d00440c210030040c41c060f0543c1c000c0301c85080e02d031160366481c2c148180c100c0301c80001d042003050421000010b8065209901c255200407241803030800c9081c01e03503208610388150354010400f01c6400614008142c100b4072a0180003a162100d4600b00c40c44080b41004a03006458a1116901d43c90300380c2440d10a248005d10201301d40c1c0c0e081d916900da29a0135201070440c50000c00d410b000c0c0b01ca090100399441003041c0d034114100380300382002039a50315100f9000001010710a07051720a11001b030040710050000540104100c861620740081d00000c00c5500e40c0071070340781180301400c061010802d0742000e84001c000882d002c0c100030008000754400b00f0440c1c0d10a07420041c1c1d40040e125140614030a208a8440200540c4900400383c21114540c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 332206744 1250 332205494 332205547
    0x4020405060301170703080a0807080702060114010809010608071701140f010b09030708060c04051c0f08181309060f05040b220f050d021e03031303020a0611 69
    0x140400d10060700c9601c00e403411540c00c08901c81c03024082c11041824a44181c0010302107000000d43d1900b0647c00c42c48540c050002d40e6030f26804c60365448002c0703840741800c0c080c040c0c0c04608001511259803050301a00c0d04a2103007400040e02503607840c41245400c40799030181506014218446400031000c1c452040c14420012841c1580d2038110070003500c4800501034070300071950200c0e1500051b00d04020a6000d01030729002c5aa09051540502069410522410f8819165102c0d88113408540030040c5041661000340e85000d136100c6d0361407a03610707001103955022402c0b00182d01c2000355101942c0018807020108000345001860400100703896005800501007410f00c000e00001130740c00c1c0f03807456000d1428000490401c0c01d01503c5070b00034900310000703070480820f0201d0100f408808521104400100c0e0200c44859520101c90a01c11410340040401c0c0d400500015285450500048902d58401d10540d1402c1240d0307581d2a040f900081103200141c140481e900214001d24249010310103000b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 332207994 1250 332206744 332206747
    0x30f0302030709050d0f02030615030d020c06191403040c060e060703090504023001081c1215030609031806031404020f0a0e090c010f0e010e010e2710050402 69
    0x120240a034400b80c481c8500805854103201700f0f0000c41c0101444d1254003c09580c56420101c00012440c07064488040c424010030100034601c0b0300014007605548006000c0034103008800881006050040ca040804c0c4542c80115058452080d4010740c803c901c00c00c6802202810480002d200350690000c00307009800c02c102c002d005c660007c1c1320608948c000c4401507580c40304150b8030700030084611001d47c0100740380c4c8540d2400e01b204e260100c1c1030f1980481218a241081003189000c0203041c00030b01c0c04917460020350b20040c80b01e0b800c80e04508a59400341500305a070307559480101c0e10349400c15000611034a900014580c0d55402d10802019140b50501201512340e00d602c502500160000b803280d424108807203919102e420215000f03200081580b15507182c000d58964648481e040e20358000741110454400c20741c01081b1601c1c2c03650040c1e417003852000d03180c1c00645e440004610603503884007419550300c900500c01c02c8170004080d4199480701a40c201815103100c841d007241c1046215070b00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 332209244 1250 332207994 332208001
    0xf1503120703094b0f15020d080f090a0b090a12020d050a1b05010c0c030314010f05040f0b03100605010801050a1512060e01060c02090a0501150e03010b120a030f030203 74
    0x381c060412251a440c0c0195550f5980e0229210044c2c2e84007914201e46400b1a13880000d10105840901c000c58100d00c105040540c80e40c00101c0e2245130703011611000c240e40c000460f075009448440c3d164010f11607000c88813410415129450b000604850550325584007410707013800c1000c15500d46d6030500090006143c045201000500070340a00d1301402c0400c8181d03846180c02c99070302c0c0c1144908a0300100200b04c140301c4400c0003000701c1c0c00014190040790415105640f4000f481c001ca40c100c50361141100021802c003410800034280008203a902a600c0d0018403415590520010780d11012007040001c0c410303e00320014109481c141d0010344241c100c504200b0111203070541144290a2901c3e1101004014603000002003910360094115100d80a0000c904290001e000c050242c2c02110600d103241c3c2ca14103034070103442090040134001d0000e001400c1c000303402003149240c0c0032001400800c0c080c031650301150592207602840030b5a5071000d85610700b8990000c0d0301a0400b076081c51309614610303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 332210494 1250 332209244 332209289
    0x71d06210c0f030a0f0303060f06020c030d0f0c0b09010b0f03010504050a14070906061d0402160219050d08041508010305070b0307110f0105180a05060f150312070309 73
    0x34044030350714001c0c0310380c24240c500340c0d4041c003948044a174002d86650b490400750900600a01c100e02035028081c4001d0300214845000040b08002c0f460014000d01504440600803951414811361a4043c411182e1504000410403840c0302d1044401d0400000c40306411810050b000c500101807a010341d02d0311003803001007000880c030500b0701034104401000384007a82008500e0600c581d840320250710725200c00401c030a50b02c040c04000420710300000d4241c04892004100491058202e007511140102406000500300405411000004a02250b59240d514000305a45d900c0c0340004848a2000140501240490009003480c50180b4601307650a036055503100e80d0358203141d01410b114904c0200005a0480c801c62110888180010a075000401c10b5034002e8041e10701540d100c00b00000084020307036100c034006480d26000d44c1060081c4600d844400c0078600104002d030404d2160b0060400f002c09545040110100502c404424503a8801050900034000b5002d5041121000d444540002d5242c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 332211744 1250 332210494 332210503
    0x3090a052514060f16020306061507110112060b0712080c0a120219020a0215182707120f06061707030f0c05070201180f0b0c071d0621 59
    0x15102c4034180d2010040742e40000300c25000d407030440e481c00c180008000c14814405d21710786040034800d50440c1c01544658003080780801c00c0000400030300714107100c1200480c4040c4803800c400d0b00c06043c1480080348100e01c1005848a981120801c0e580c00110300c82009080d41c0c80a0001c0070f146410019410000d4842d44507104203030700c28040185a107140000c0e01c00581c1105e1004a00048004044140b007a0103515401010011b074810a005034080000c03003600d201b07c600d9840702515509403815118100b0440340e541c09484c448041c03107981d0f8101c02001d9850200e00600b059200c6124007000740d20068280c4201690460199040410821803540c014500010501603480c140130301e942d03424803c9000b8101c00100101860912a80c040b165410a00a0141600030b03a24a40a400390590401c400c050a2203040890903442c0d50801c0038400403005031515070107010644040c2c9a6450158000e00c21401043d0080c210840a2111525000802030040c0c6500740d1445103200404c010035454 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 332212994 1250 332211744 332211749
    0x9030b1815010501051c1107060f0c0f090611030d020a050423010507031215030804091104080c0d020303120108060709090903080424020f0705010501051503070c150203090a0525 78
    0x11326090700d040115400183c0250145800038900c7e16190700d09820240083c0c02c101c400c004010745402d410901c80d0744254121410103e09485484032180760540480700c21400250300691800180402903a1610301d00007455948885e03074519440c0e0307040049103051680c0c0100040b2200c1003139444210300e0798018080d07444446d010f040880700420b81d1845440a44401030480003c0102008007104003e81d42c40580155a0490030400c1700207103181000d1528425801850310541c010301c100b40c0d052078400c1040c8101c3d4030107000e40b82008200407012400032000c0c4c124201d19001082044071482d4440c842e00300804580909006d11a016100600910005040a401694814004000001840100f0703d07040c1070000304540d074002105002c0c03080c0c0c2107030000b15001c0d4213120000825107807907004804051002c030049490b41d10746400c00d45502c80d150b002141c00241d00d10030b444100985101841c420896103014000c0c80c041890032906145440d24601c840840d01c80e07041c100b100003c9060001e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 332214244 1250 332212994 332213017
    0x6120412170a02161401050f061912050c0a060201050702190b1504110f031801060503060c0a03090b0903030a0609020c0733050c060c0712080709030b181501050105 72
    0x2130300c510056401c0c281201e4400c003d07201c103903a4994a900910305500c194881c0310211000300b2240c803540c003002902001d2841203c40d20040758024409070f80c02584160f04c0c140b041c4204c0781940c01c6e0344080f403983c081035800000940d54910401a8598050040c0c0c4100741c03414095a1681c03501d940c916440c0c1c0300180542040b607218911040c0325441d150300001030040e284c0b0000c0d48070b80070300322600030a40c000c4440c078840901c00c640c00c07017000c03205000c0c4a0588500030050562961011411800740c0c202507200010180c4400c200130118403854010307401416038101840e960302d400014001550402d90005090742d10400c009803280030081505001c0d20451882c00c80700c500c141d03d4018070310104c00040a03d13041c4000200034060b03040b0f4018103215100100340c8040da56520b20340d070014002d900c2c01601450407400c0c0e840d2020301c141c1310183e00c46098244103844a859403075500d0b09031070455020b140389040302800032110340200002e500e0001e00420304102581031100003841405549100c51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 332215494 1250 332214244 332214247
    0x40b0a0e011401170c06030108030c120a050a1d0612161106060d05100515180702030d0e01140408090111070302030c060c030f07081309050f16090506120412170a02 72
    0x10004d06050144c032841050007450140c07656184c220064995000f10600140c030300c105c0340c0c0c0c84001c00d8440305507050004140c03120781c02c002c0054000d491210070080c00180c0c110f420280713506155a448054850000014070b00c206501d01041c0e40d481304690702a00e03409005400c0461a5170700c4d00007030b2480c1d2041040d905070f1894519490300c03074500200c01110307440702c030308040801000c80540c12411501c4a0103c03850740340000008040c550a4009588181c01600200034191718036116400211002c46c800000040340c004d500c158900d0b0036000d58040f181c00d0000501c40040d50b81c0320300410703041010030014100c0b2500d15800a542c683c2854080b500440d00810b103402200400d000b40d42c011100c0348043d0345c0c4c44840b407030924080d81c00100003044000456001103848411407003035520420308a0344c0d4903000d4a071b14964415941080340070000304041c146c40480c1a07128180a0a080481040100a0380c01e003480c16811420456000382d00b00200b108c42414818a1350400507001320f107038107006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 332216744 1250 332215494 332215529
    0xc06070e041103010305060f060a0b0405060a0903120e150c0c09071707090806100501050a111908040306050714032a120907050307080d120212040b0a0e011401 70
    0x20340a800082d400c80702602c0c002c03000000340400840d4462280a04000a5100341c3d01c0d0810030030040f01d04d0041030403842051106000c1070400c4801010380c2002030a1198a5a54a0361500c2801030801450400182c0106c88440750f8200041d0110704130081414403411300e04c0c80380c0100c4ea12070382c5100c42c42c4200c11806c040340300c0c1401109500300b01401440700161074a07000078068040d03061380c816510288210030000b110301c4a0700701c246040c2c480503500e943c076181910804076000e890940b420100c5004000812289040940a802046201e00e0100b031300c41c4e14600307020b001c5400062100d0180840e6661040b5520103550031a60311200c0c504030445400148200310145040c41160803200e01c01c00107403a9840700c0070481040c42440010200d03800c0c03540300c1c0b0a1640b03c80661045081c03551103000e100c0c880c140589031055614002510040c10042c6025039070024000544050714800c51030301c01d011300f002030b40c0101076848480400900806c0d910091250707445405205188010340340300d120 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 332217994 1250 332216744 332216749
    0x80a0b130b040e01092018010e041a13230604020d0807170306030d0c0203070b0d0e010603030c050f121806120403030b03070614030f180d0e04050c0c06070e 69
    0x285840700c50b0b0030020886151580750280110b110b81d2080d5074001148065411b582c81c00b80c09640c034100807040240c83c00d134070304414191b08403070190084807038541210740d4040c0409481c0505100746a901090840c1a80e541045840e042c010b1001c0d2804040045101820240010700290801e506440102e030703429890403ca038542c021020010308580401d0518101c040c840006503000700b0301102944c0c0041c0c4020400c0d00c404011500007034040d013024104100d1580340300084d014035003540001240c03201d080c500045c00c64400e40c0003200810402c07052002803080400c96030420000c60b1008040c07a5034041509400c0740200d03a40c0011240a41c4010310640e2660f2040d02e281040b00a180c4401d0705040c680076010b00a03040c03062f0b00a00c0381c4000003030228030801850310100500e104161a40c0c59903146521341c01340007061405590540c030700352007032520100107030190051656a21242d14050b0720070001650b5011f000708403800000e2013a01320820b00850010b81145090502021a4101401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 332219244 1250 332217994 332218001
    0xc071e0b0304030c0c08030c0604060b030106090908070605010e0708041b0b03180c040207020105070b04030905030a061b0507050d0c020a0f0b0405040e0604051c0c0f12080a0b130b04 80
    0x8600c462004401c0c08105a0403428200401d0f2180ca02031800945408000746c0c0c7c1e000d4880c4030300043c2c0c098008600450708951051181e203402030300114040343c4604400040d2a21414101d4a01600252081c10f202c2d032132103514094801d0039136100a5040010009040050180020300500202444020303078140c500022030081c0802e404207600d91415840808803400c054042c9481c40c000d6001d0416035151600c211000154161140ca00f0144580c0350701005d103000500c12418084100004945950204201d5034450700c2540c011900301c8145418031100566004010280481032205074000391000c20210800c0856290416201a040c000207507844080d07840040c002c0c048000200d10078142c0c00013081518015101031058542c294803040d40c0c0c040480740500303183c002a1000e0062070203444c40ba0001041ca28003e0007850313090311100ca06062012085800310009902c8054903134000480c6540009030ba0780c20041d020395040403c0d0003440da056541d0580d031b6180010310203555682e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 332220494 1250 332219244 332219249
    0x7230c0a0b0a0c12060506121f121a0601121e020d020405030c0316150201061a030402040b030c010f0f0c0804080718020702030706050c0c03010507020d0f02030c071e 73
    0x2003030003800e003200444028403520302d2000005929080c0340d89406018005d0804898026202e5440c040480c441e0700e009840142c0540c000b41d010041ba01e03489400a0108005411510754000310b0322502e2421502101c0c0320b0511403404460302040184c41c2ea08140c4100c603941500001284141224001c0090f1581c1040350500341c42c40810150034101c813507400350007614000d40488405800c44001c0581d2b405e0100704000c0700c04401071080c408907031480003800d280140c0c2c4c0004240b942d200e000242074801c124210088404000c4100002c1d481d203801840e6030380030251301504003407600c40002441c06540840c0070045c00090099250507500c00d40303042c04519006000b00d41c032f0300d881d45165a01d461881c42640a1140440c0a1009120007842258500c0e0703070060050208a19243e01901d07941c021260018250042803200802c03038800380111071082074540d000c1c0c283c14020f80c0d4040c003011004031404045500910400c480a200000c6107410350b0110104460418a00c10901951005a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 332221744 1250 332220494 332220503
    0x6060705010905030d06080309060406030209130f0f05181b030732090c0403060b0d0812160e21070f0b09130e030a080a1506020703060507230c0a 64
    0xc0030b6101484004809000c01a500c000d0521030b55660b080382c65500d0007040300d20b075404801000304101d120300a500801c00542c0180c00f050406111050300c6085440440950710303150740ba41544100c40f45c0900c25107a0011204050010103840c0c03404080c2c0e60750456202805035108280080101c0d5020000e4500070702028041d00f0405040000e0b541d146069810103120303800c07603032101c180280380101220f44200155800306042510b103840e04c0300502141922290403005a02c500004a03108130010038864220f4550b00c90123007042150407903900b110a15200800c44500b409661907542d010700d000c445841705607000c00a9028092503400d00d00359900000ba410040c45c4000b03842c2030701c3c20107420802e40032624a080441481c1c10f010540d1400401010300d81c001b04a0140b00b140111090740d0170003841c40c0001800701c99202e407100040c029800100150740011307800c00c1004854003d656010b60649091081c0004042c0444060480183d240101b544045000c0e82807080400030b040496400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 332222994 1250 332221744 332221751
    0x605100c0f0212010f23040b0712060b18090601030204120b0a020d1b020d020610060f180f090f1401060507050a150605011107030c0b070311030a3c05030606070501 72
    0x24039548001807095051b095880900c0c0c9807500300324551130045030710403604440a0b580590301e2010450328000200341c85421070381e4808001c20202602070152020400c00c400c107642801c60034080001211005100c24100750040005008110081052040c01c40e0f000710401029142c0d080040c019000700c020880070031b4074204c00480b840c9a10044001800c0341502030383d14603500d241080381c40300e20840e05001690204402001030f00d21411042038100c0762460140c42900c4400450b50810b00654000312440f5584403080c010300a243c03081c6942c89020040800200d01c6e982c4452200c194144170341400d000300402c60205002c030601221600543c40000024610844401c0400030841400b495001030500080c03040c0507100041c800c1f0a40c1e03001528036032560b01d000c070011095480500c3c128104440c0203c4068111000c101030540c1071055101c241000d44168900d0816100341d903400b403101c400e8140d04d6411003001c101d0000c40080145810f0f9500d5880202040980c81143c0000f0465844d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 332224244 1250 332222994 332223011
    0x108031903024e04140c09070201020408151b070317092116060b060409020d0501080f070b091e0306190e0d021c020f0f06040201030605100c0f021201 66
    0x7005041e0380000301e400c3e00882c1003400444901034803d006005680294100000c54041550401c140c0f106400850468034500416004103007955026140140540c1d008101400003040500060700c0f00000600070207203601d4031003514801000e040641d50200c6200151601c1414440c48038031622a244154034055030070040d24180d5500f0008003080354111301c01d801450b030891420100d41070f1046e0350000346c9640155407260301c010007507603030060b900410800c0001003004160010b03154042c80c2650014207907140803003150400001ca40503188030380002e00180451120712080e6851a5016030b00c041c100c8002d800142c0d100702c40300d901e8a0f894403510f070402c00b54000c81800c80081005840313050000b13104400005079280090074030340b0b0158014580c00c2c011842c5030100d00c440952244121000407540b821410f00b05000850480842d401c680d00f00000d6503014090303940102030503111254517250b0900014006600c2400041114141090310419961166184200c84440c90020003d500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 332225494 1250 332224244 332224297
    0x6070503070611071505190c12060506040608180109020612090c0103020313020f0d020409140606100f0c2303070201200d26010b0301030203060f010803190302 70
    0x41111404039580703800e0014a580c044150b80a480044d42d0011040e010808594070031005454000c2c0002051040c1c0c45614003c40306a000d001c140d603410340c4541f031001540500150543d81c46070030a500684040000300120340d841410b00e64840e156012210448141041c01d03405880200400f0b58003100c0071410089040300842c240740242c0a810807504800d00e00310041d0264007045400601055602c007480303016007400440450403142c000d00755040000181e001078101d40c00444207a0751300c003015400103101c3c0402c10000340c01810807108080d600206100050002c8104a40e4104200340480702c07408100414042043d040910141c6110741921146c5586e0b4a030828141680085c0f0318207101c1d034688606544051140111001034001020000e03420b0354907010701039030b0100c00e5045403451364002d0001903d0f41d0107842000c09940c0e4035455801050320700b00000d45007921884060004003c00c190000864402400140da074180c04082e440e000e400900454110000c42d410407c201c13411803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 332226744 1250 332225494 332225497
    0x120403080301140307210507030c15080f101211030a11010e270403120c17221211060a0e0706020609070b1602041a03070909081c0b06070503 62
    0x2e4500c1c0d0551180f000e603030020182c0d00d00e020302c10b21541005803003145441c19120180d9906544c0540215561103039a40c0d200a03461582d58000e0355208414503000c2c81031903206048640208448100480d9800c080320700140c1e0416074404c48465810a5800d4010080007403240b040c0c4840080540ba0390b80c8160070501d104841840403c1d000810001000c14149800c807104401c02c105500f441c03c03c04c88640162100400103407040e82400280030303501610302d00d1030050380b015445a60f6003032060707802c25801c2c403c03030030001c0c244481060804c01c141411800406402d85855000ba08181c0c8003070021074181c88182800015240344c1c002d0301d00300040400280c005011054980046403400e42d0f075800104e03120403054400d564a60043e41c81040801e144101400c01c0c2a0440c403143c3e0b10010540c005000c0300c06505220110000404050f811031400b4010b01c40200300141c02440912711a80e038100303d0744203200301101c08107c000411700302c0c10400e80c4414401c2d5405803042b580c030301c0a030030020b941e13 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 332227994 1250 332226744 332226749
    0x9040f14150316062106050a09020702030106060903050a0b0a0b180619061e12140a05090606030a0605041a010803190e06030109180b1905100617040302120403080301 73
    0x2a2080340c803201d080c2500d4800d00f600f150000d90b1058401080b44030341c80c04403d4114810249a5200da10100301a40c80707008175401051003032401603561402c0d1041c1402d48541da8007242c00d00c804c030403080010400c045541070160b80c0c042c0d07948480742e0342c1045d100b00070710304907000503000b0408424000a240350b003000e56015060465002c5882c8032624500341062196000d0300c070000700c3c052030403280e03c89459440340b209883c2d82040c0d81c2283d2070002060031600c2c140400682070740e003c010303c032044000e4030465401c145800c0c050070051801002090f6030781210b690041c0203968581c002402d0003a00c002c4030a0700b418012020840b542c2d6500d22036a25049a001508104403c0c1403a00c001da000b507400f03171310440006e443c05003540c0c078004c8400700510a0100da1181803405000c010001414607140c540315040c01d4114400394640c41c5440380441e00001c201e4000388c003c9101c2406034a400100c0503e1074070740a540c0c7c440d0390383d41c0c0c68100d040c000d5010105000380c001090100c00c00101c03002a505 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 332229244 1250 332227994 332227999
    0x71511090a0b0901050922090825030813060905030703030c080f011d07020f0d0f0e0103060815091501060824280b16050d090b09040f1415 61
    0x2081c2c507214001d62038410390306402d01091040080e5891401e01182c0406100711440740c00070040414034100341540c010600071242a80000350140100d04042c4482e0704840702601800c890300d041d0b65010308448000b510000005c0700075410300d401c1001076000490b141c2c0c3d1180590b5120355441c074001d000341c40c407052040d010860742c2c0005044503c800703030481e0480300300311180c44494108040c940155400a06075a0441c0034500c803400100c14100007641c00140c15136607456000c0801100200000c14840c01c007130402d810041308000d00c0800003510411001a515090050707194148040d2410f19006e074030350b6800844400003d011504041801e1280c40801980c5800005071403c010b4250040b03003e55038000c0300c00c4628010305e24600c000c6543d8111055403003803500d485015000d01500030051101941065040c01c008120307041c800d4000340d154500b0802c0300e080c109070f007800087c002c0407080d5002d44c0d901c86641703120b01104d030041c0110118005000c0a1400c00c100d00c002030003c0140902d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 332230494 1250 332229244 332229259
    0x5060c150112170d2301060f03020c060a0b01180605070606140108131401090534060c020d06020a120c091a030a0b0a0f0603050603010b01050f07151109 67
    0x1501002038414540703450380000c04071400400d10381c8803c1150030080070b01202e00d030781c3c030b114107107040000240030208141c42c59046000e6150010041043c1c1c900300304802094014404051806030005049410200784071000c2441a54600103c6401c5403155036040e48214000f0b001413029000070040c400e09000304000d0100c50f44a01d2640082451545514005142030b8005000c950520954400041c0300312107002c81141c521400b1400c3d01c0c814801a82d054002d0307949100b400038440048003004005502a08100c01200000040b5214905c2030900340082032004108541d6480c0e00c50158944c0804219107404c50345030000c140011032103182050703034900008030303406900a4420340116840114038040504071103044400a03080038001307035409a01d43d40200419039a030103c202c050040445101030700d900c0d00d5001429500302901c030074002d0b4500440c101059a0100846255503801280243d441c14145130202901406a10042045207440380008902c0c1c00100245020803040b00c925 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 332231744 1250 332230494 332230499
    0x910110d0f201b060a0e0c04060302030a0201050307030f1503060b0f030c120a020603090102130e0105010e01110f01091b05010318060b0a09141b0705060a050c0405060c1501 76
    0x204540b441502d524038900500d2044080d03801010007403c0201141c9441506944481c0015141041c01c0c4c41c1ca8680c80c5c0c07901440c04036482d040041040781001201c007804a40d10b99000300b901c80d040000023a0401c94008002071623a4082e170020b000316136072400204440c0a03000e4264070420b40c40d0100301c80c428100f05041030b02d46040045110514001006080380c5c401c24010454405504c0d80e03100094001c8031449009644e4940296214a601e8000581d462004440c801c103200300a0304003a4a41c1014001403107541d034131a211650041d002e0901d207902c0440151100c1c0b1f0125001035485043d0700300800d03d030070003041d2050301d507040d051010500072894480b0019820b031111140c10044030b8449040c1074000c203189801c00b6050b0b04014002000c46a1100c643d00c041c0c2d0301000400c0019080102800003210707602030b0130b08030303510080390081c00d000c400d680b841e84840700546141c0303400740c8400200f040e2030703c0070b82260020070300140b03210b03076908040b0302c6130340c550410007190201152544c000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 332232994 1250 332231744 332231771
    0x2010809030a0905010806030a05030304060b180408070201361e1802160c143a020a05060d050906180d0c030221070203010e0f070302090910110d 64
    0x7541d1102c0e0310354032180d0742c40e030410004440301e1100910540e858072450b150840030410600095004170b00410300072500020351014803510511401510003c0700c108010071011613003800548030490384c2480c180640f02c0020a1200341d0740c4071410200c4007a190140c100f415403107a0506003048038500314102c03c001e09800f4002c8041c4040b0700c1108509a0784010728007500d84550300030070b04040484404001d000e4262214110100d558000c898034040b55002d0011602c1d182605100d03120340c420540c81c0b004500c03110390040c0d4100c4510880000e81c40f02e41d0108640e070304013081002c0c0201410058445005504117800361601703030303541446405442c021a0540b800c603440407001e4040403004045088903d0001c540740d6911080540860042c4062440e107681500038103111400b48410744c2c1d44842e9030740109401c540301141c40200c16400300c503010152203008240795044940460b040c0200e5641ea03200c00781054110048040114074180060406943e030700080c0c5100114103404000d54252000c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 332234244 1250 332232994 332232997
    0xc06050706110903070b0715181a040f030302090a0503030c0c0906031203010b0706020f0406050a170f160e0607080406020d0c0203030418020c0d020d020c1c06050903070c060207030201080903 84
    0x1e02e415400001040c001e61b0011002400c2191003409070040c10301c003200e2180101c0d550541004030190044550505100d4014641000302090a000306030360305090355142c41d0f8031040a0300509054021600040980d245501c08005000240a50b9603c0840d450055190440c454115215119520101d10b141c140042e41048018100303907840d03d0741c0d090000c0a100d681007000100d078082d03003c101000c107031106600074000030400e5440b070380d8903491a0800500180d10020f44440d401c0c0402c01000341894080800c10b410000034541840783c40e0841500f201c080907980400741d000480050600c0030064450300034402c84059900b074a60740c0c403624500311303160000c3c840042e41c198000e203c140442ea403080020541010881d80061420300408007039410565900c241b40c003d45c00c508117000704103405002c140d4100c8030440d803080044049515412845121100c0600071958072400141c490720200211802260003021004c4510f84c0c0303000c001d42d00c0c0560301040740013840c103101141002c00c0000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 332235494 1250 332234244 332234257
    0xf020306100806061303080304031d0a18060b040f0f05030f03030a0c0c050607090806070f050d02032710110c1b0f060a030b03010c0912120c0c0605070611 68
    0x10304091031441d501c0e10454030b10b01d014103815031048040207400607403000001900002d504c210012600d900e07040c1405806c44603034103040300c1c803c210f580e0b2012a5940e0444201c0c103640b900403071002502c4072050090011300d040d8000380e041140005000c118006102d0002e01254890905803042640760b1041c15103a070a51040507c05900c24008501d089059400c50000082145090007113020a40c03241480e003203003030340c00d0808103540c0c16040c81454424400039511162600301850b401801c03000c001c00038800c0c4d00c42a041c082e070120110301c0044114903d909d64070740c140080360040d048895036a8440000b992161082e0345031121750400c0308012410798030070f00615005032080c0390b0070414009580740a2101c050340070410304100c0b183d40e40c440010340012101643c00203900e8040c40145400c440030100038106100ac02103040000c0346e07000e112800c209a022580c2c2c0c0034a400b0ba10240d60f0512b8034071340180704a5400b0000309000340c3c854058100c082c02094140812840d401011850b4070900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 332236744 1250 332235494 332235499
    0x50f0c03030301092d050a1b0c08030a0b0d1209060c020a0509100504022a06060306180c0a0e041b0b0307050702012c130203090c010305090c0307031101030f020306 72
    0xb40010003c031203a5504c0103001410140304292404d4900d2400710075403441002000420b85e440043c81000034182c49409945102d02c0401e580c8039902c0719014250f0100030302c0c0200b00300c030000001002600c4981050725284006410380c442880c40d458042515100d001c52000069010100000c1c481d11800c0e541030a9034000d051540304900304818071009110003006502210b000c1c51000506443d070788024902c2846107070196041913080d960006c0c00303c0581c03010800c00c0d80424240030304e5660100300300790801544141045c0010140c01f245090040e0651a180e1103800c0107000121030400300c00c100d101d688262401080611910b8401c401e4491500828480034401e000098002d070141000f8241d00340141031410f11444020041c840ca01c141848505900107804c0985c145400e080ea12001454416002541145010311405d03950381814981c840c1055210404103d107581d05010710060100050f0035165625140d080c500900c1c0c00c80041540003d10300b07440e252007080705109590251380300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 332237994 1250 332236744 332236747
    0xa0209090a0b310b04020705030921060702070e0c07050a0303020d060b0301030f0209010815060114070b16020c03150105040b04060b0c0705010e0f0f21030412050f0c0303 75
    0x3003010a60040164000b410b410104606044000c4580e94000c0350003042411202c1201006403010001038030380c0640c0b01401039005201080026030301100361003103118203540e42c40e418103400704643c43d45209940130b6210760080c5802c0c82a1142e02203140c0098908440d0360101d00e0300c0761940300b0301a1203a1070003d040b0750421200000064441c0e001440100744071900418019101d0081440b5076100f81c0c41169030001d461701080841c2405440d4030700401c05c0c800030300107030a0070403a90110080020940c03810405d6520101d4500b214003807d80d0b00842c2c000c000340ca480e10f400c2c00e0714a4994038001211000d449000301c2c0210307501d0000394104d145603c00810f20741c20792900701440081d001c0d040c00290b110f42c54079400310303c1c814110050f280c1c0746448001407000350f02d060700140074000c458103698050900c60240c50700540320702c00324005001068841880d0f51025002c66048071061040b9400d150000040000340001140030103008607000f403043d40c2d01d0684003022180d407844070000070b0b50103800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 332239244 1250 332237994 332238001
    0x140c030403030504150e0327011d0a0314030a09051c031404151d04110313050f03220509010303020d1b02040f020324280306050106080405060a020909 66
    0xc03e42219070024480c580381280e90a00e001100c00b070b202589aa0001c3d54404a51006c0e10307400d041c81244c0c01c0300761201012501c525400003c00d00950f002c0e5100842109002146158a0b0300703000200440d080990f004c0101e03180902c841e00e0358020441d42c030006180f507001182d10314207080c0070440c8408000280060151998083c0c4010509840070307007050009100002c1c018482d88800401e5100d25030340d0021002e10794042019083c4010b914034003c42c81c0c8003125030011010380840744c10aa8107034841c1c84a54041c949180340c1a80d01020f480c841c040882d50750b00d0070f05500c01110026400d04110070b03190362200240604030400b480090010f90040711141255401240d1010143d046143d10452031812600890b095610b0414140780550f4004104030080ca01c4007400c1c0b100d02003c0807007208210703050000a078110013510302602c2034641002d1a010505411307154500550380588180081c3d0b81d6164050813800c4102c0d0156100d0241000150411001d882101e481850051841d9100c1c4c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 332240494 1250 332239244 332239247
    0x11040e010b03030316021222090618020309160906060207080a110103050405030d0524100e01050f0405150d0b0307030f11181303030b0301060f090902030102040f09020c01140c030403 80
    0xe10130245d09501440b8085c8001c41107540040c107288050214028210300c02c41c413211030b07581c2954402c180242ca0400f0034410458480b0740610002060000544c43c0c0d1500944107040088001d12010b01003100200090900002e4104500f1190b198080e201d013a070343c80301d4664944943c60401400510b0391345005076158007a90000c0d030498004ca040382c0c20041484140d0b411030b2001e0301c0d4590903205140118111088000200c82c030160186c52803540000d983c4000381811070707044401d50505c41c0105103040031007481001d44004200091044031041082c010240c001d0b4084204070701d41d24140000c00030070b4200005d410040f04e0f440000741b1485500c5031280181c0c050889101540710241500030030950b000803010b540540c461130840409048a4913010f8101c40c0503c0c07240c0d02030790502008000500d41c2610751400c45d21119000f0518031820b06c0020300900c11a08480200c202c50741011034417100c1c940c050941e400540008000001c2400c00980b4040c104030b81c5502400c00800000b00040d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 332241744 1250 332240494 332240521
    0x2010605031002211803030a02070c1d240307030b0a0f020702060a03020d02090a060f080a200702030109290919150b030d11150610110309040911040e010b030303 71
    0x5642c2031000c5c1064403d4036505404c5500c245c0c0c075840f8a9801003080c40a102d00600e40800801e4142c4503083e2880c514401112142001400d48030824a5581a1550200100b681707590b00c05004060b520240d4030f9162107000400700350780320000540b13811446250300140740b08850806400070089800c1151015085020354081c18403008066002c2c4255001fa41f240c01c124005040700744ca5a652003241c0d10b5008106036001442441ca6600703000e100f4504c41c401100404c0541940034215946400030b00100340503003610078000300000c0b0200c0c2c000d92031090082884508054900d0000d1558036400c50865442100b06804424032403549d0011001551081141ca180107138503602044803c10340300001d003404020090350000c03411094005445e401c06100a001c1d40c91b00b1082109241451008590954098140441840728400f141c005c3c01d50300b003058460f403450051060110401a1410310501e400c1c45d06814080d1b42410016281c445040c0a100890000079005604540d140001800c56 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 332242994 1250 332241744 332241751
    0x60a0509040303090204020d090201080f07050301050f010908070e010503060c04030c0e061c05061603060305070312140f041409040f0308130602070501022206020c010f031b0201060503100221 84
    0x601d13a8440c80000142c54900160402e080c0320440054070f0703480c5000140424000420f0340700401c580400304810b083c0c2007419a41529800c1d542c54108160080c0143c031040403d410001c054443e02e200000c8840034090002c2c1602d000b5001e031412394442c502c242d15640204d000050841c0700342030052042949102e0303650760001004100204040c1d15409801072070785600c00646241c0c0103181000b500e000007516464088003103290410000e440c41d1038050316642140801401c2e4201010200e405900c1900d040c10b00c01c4a403885c0e65a910b444030030701a85903120748a0002c803013100103d101c0c001e140200d149032060341c100c600100702a00b04d5500300d550520003016034104007211f42c0900d011807600d10140021500c0b45c4001655944101c2100410740d400350100458130400304414011541d012949109080081c28045610f80d01d440c001d901410300510b00a00200340221038910295054100c00c0c2119400d801fa100c1c40800648010107a21a03030984950342000d41c07045c85604508c1160042c0d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 332244244 1250 332242994 332242997
    0x215010311010917010b0a06090e06040203070507082b05160f05040b1c0e0a0c060e04140f0610020606060901140d0603030503010f05010503010e0a0b0301090203070807030c0905060a05090403 84
    0x310f054071211001042241c0e0940c903030b0243e5503643d40000a05025450b040035100c1c03400c0501d941441d00060b68007442c80100050700440d008008210041d002d41c00369840c00d64040f4045071605907585c811403002c000c400d001070700003540c1609d000028085105140c01904002100744802d01c1c9072800341c400c0b0940c01c8419041203410040011440c0100c000341c64402082016203102d078481c0c5003510140c0d10864600071043e0401c50302e0b00005885501c500d0304580983c00e100d124000703040000750040c140850003001c0d084807a81001018803501600c0d038400e110072511444840313100c11080b030f07071740d0700c05c440c12038010108000d603050300d6000c1c03210303000e00314441c040080c60712518030000404d071002507004a01140c1c0200c010310203201c0201005010308000e281250a640c540100841c240002400b030380700c1680e850350a900b007614290400b029058025081760360141d0347e000104e039031320814801580d04040c0040c001c00c5001060041a009100041c2001d1240f820f000801407640400f500450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 332245494 1250 332244244 332244257
    0x120a0c0518030f070f0f15080622050415290d06020c030c0a050d0c0b010504020c0102120c09180c1b0f16050109080625020127060c021501031101 64
    0x40310b02c001000000040c01500c801c00c1c80e15403604140e1a044152038000d03d101a071f40b600b0101109901c480200d9002d24201c0300c020101091052007a800720b034500384518024140741c00c00080c410380781c2a905120140078410402490032a04400c4400000c0391505004903001e481c00c44186005075424a400c3c1c09800700524003040b40d001c80d40b940e844106890341540118254006101c0180042d81d032000641c10321065958050340e50500003813050140340c0c410f03540458440c452620940c113803040220150714034550741c02c0890010105030170205220b44288a503e0305054048201d1003041d01818403100c1c61410041010300501091004108000d02c0b4400c1005601c440b03c006c0010702203651981c950303040c0c82400c040004011000f1500101d078558005000c4c01800039510f02c40c0d000c00c010480341c1071402081204c0890240086690122580d418020080e40509210321000c4806104480c1080781c4c13000c000d0141d0302d542220255040b211881c4004002003040250b0a12030f41c0707014507080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 332246744 1250 332245494 332245513
    0x21b01020403110a0f0e0609040c09020c06012607090203040515040b1911070f05030904022109070b0f0a031104080105240a0501181a120a0c051803 65
    0x542260050303401a5540c850035142d2183d41c0c18540e490307002034681419200601c42c20462609100c0d480a0309071030081800e48001014441d044c0c1c0030304007615660760255561f001045481e591104280101e010100c8030f40300b0001014240003100c891502e0f030f42c010302a810719001700200250002441030f03a45005482601100d0b481c104d403402c2c4142d1081d011b400f114205410008070144034100783c010954980208128000f00b80300c1a98000c5901140d100704088141c03030240e0450107080f580c5500300707001107042080c03500501c42c440c8131410042150072003699070310500e565903100d40c810916440c10410140030717440c064200900a00885003008980800f0b0f800a26105500940c00000165903642c103000c09684000c2c0d040c6902451240780c5408031201c440042c000701000e22441d410302c102e004480c241e0940300000c12000300b030026001308076070444c0c0c4040321041d0711103992030601600710b1002030202400751190320f041601e00d95450303091454103a600c00d07014075104c020075030520664121 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 332247994 1250 332246744 332246797
    0x1120908030702030301090b0109140f150d0f0f05010f050111010603050d0309020906010206090607051305090901060303090e19050901090f14010b0102340b0c0303070e0603091002 79
    0x19402142e076680159960740c502210a8107c41e80c046120781000b8007650b00300104000103468801c006400c86000e011103002e48002900320703001408002c0c1602d8081506c14460760700b94403443d09040071020522001c2021b2550340c0c00c8030340034002c0724003a001000b01403250394810343e0154007103000c0000004005459454083c0b810201c0f955403000651520313080811810280c0500c0e410074401c0c00142583d06081400644071000101a42c0402030f0119080c40a40e550410602c002c1501031310301405070400b004068044d00841c04140c002c24241c107000074000411101c440e116441100400080280002d6414040c04018041c984d0944d00c42d1680e0010414802c40601103a02c01ca00784030401c1c408911a900f51401e014400303041d9000741c2010b00502803607010401c800910410142e039840305014810250781c078103401c070070340003400807500e0740003284004015805182c554488030032140c0000100850742c4400c4483d070180360400d040e294420350780e03a00035100c03c01d89401541076038495000c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 332249244 1250 332247994 332247997
    0x309020604121b14010c120504090603050c030f120a0509120d1106060303040501020a120309080c06101a16290f06030316030e01050f0d050f180a0201120908 69
    0x8080e908400640c88106288680b00010f90061400d01c0c00d40312540700d8440040d20b00b503030b0310780003800e00c108100348103441c80e11400880d009000e83d1601080107a889050940e680c9500101c100d010b88108a82c41505500c0095040007100081b104136150100c0500200c6094000030b40058100000380c041e00b20b1107205004143c4900e6440d0360302241d00845c08c2c502468084081c1000340650803c0100340a0760364080361115481d500b1403000321007452900c1040f002041424409801c400c00070071580b6252001091440c080d800d50403803078102c1c1d61500e0303410382006180e0b501292507407020030940c00e042c003505184042503400f0305041401c1981030f40c0810081ca0b030880c041d000f10031204040000c0c816030314600d02d17080744090b0021410100c018451150409141d20064103100c2c403180702c4081d503807180e07040368030182800060310b03254500404400c2c0508003d40b05690040302c1007000404800b402013954a21380300d800010000c0300c80a40043d9105403440c0307400b18210392100101c0d0003084c0d0040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 332250494 1250 332249244 332249279
    0x1006231f02030c01110c070303050702060712050304030809060105010903030f18060203040302090f010b0412150f06090b181f0504090c0519080a0605070302121618150309020604 78
    0x3000342d565207200000720742c01c58035070101c0015156421b0200458010000401340c0c01e507a81420b000ba52143c15000090301801440801003240b0500d0700d80e584d0312a0b001d4080c41c0554442d465418207521000840f903181d8509014107800a0300450040020074801c2103000b082e050b440c00c0c0451108880c1c0c1c0c0d40d0003004680e810041c0543d10000c1c0420440c180500500d510542c201da000c0c03603950501e4000c08081c491132041344200011180d081051042d46121110004007a400c1040b04980e4038448402030205031181c01402450a4103822540c204050844074880402660340140d9940226040c050300360072580280c8540380740c20100fa59110ba02c5031011841c050301c540b090b503610b440d04214282004505d04610707800d0170101045058400948076808641c4100c01040c21b5443c920102e00038050240940301d84400407081c482000304641508404581c556200c2d840c03403031700100c0c0614919403481507001c040c071000614400f1500c243d1140e00200c0c401001645013035078030721505031800c041d403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 332251744 1250 332250494 332250497
    0x80d050f120c19050408030405060901121415031903030e0c1c05121801050d180c050f031204140d0209191a01020303070e0406080706090302031006231f 67
    0x54440400d15008004001941c3e00d1501d82e103054141805941ca0740940c1c032845000d0140442e613101941c0c0103030000c041c14005050200b00700d907001d000d0300358003003819500c400080094041000360b1f4107001c64159418a8004208440d48920b99400c40090688043c0c03003d0b1809040c81c0d89142e40d41d182809080d0300c183c0c81d01b40ea0a46400d042c02420401c5140c819041c6000c1003000c405100030603810000f8030034090a010352030303040340c42404003d400d40d071001103a03003040c40240e801000078403901241a03960603140312001c00005014540c1e80d45c07030340428050703040081c0420019420320b466505020130024128081d42c0107245d01081e030742041034802114038003000103c040500f600344260300c9071840a0350016250301010f00081c3d00c07480701800703e104201e807080d0344c002d058a603600003070014124001244d140581c2c545000f05507181601040303209008140e0701c50030303c485900818041d0394100b228144c00581000c29080c2001c4d14681c1d01e030300306042032803114800c4142d01c8051000d500740d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 332252994 1250 332251744 332251747
    0x3270118020a0f06020a06020d060b030a09051b010c0b0910090302031b0304050d03051308030412060b0a0815040f060204260a0305090d05010906090f0b01090501080d050f120c 77
    0x240c8100101551a0340280441d41d403203e00c100003040c1d00144d5001d43d40c1d00503400607650001d1b01d00076030140800d600a103058600000a00c610982d807a8403446401e0b01860603910791030512400680b100c0134980116001a01c4411441c0220740703210703003e58200f078000084580b0340050204101c141c4031034001c25405600301042c00b0402d071413a00300070500047c14a020b980f4003814680050f45603160a9000b808000000c100303500880031544c080f07806030101000f240e450342d5640540d149101e500b003c0884205d802c00500c00d11608040645800340d94401014182c20082101c0703200304220020b0056a50281d0740070784101086007032008101401c031181a21049a040c0409400c00c21035041d041c0d1001c6d0300140800780820341c0308003900c2c00c0d01012101742c080b0700c10a082c0180902030352540500403d08e0005501e04103c03004c10a01421071241c0d0b4007040303603a0f071100b03c4000c40301c0900c10319145400800200f01c40da40309200800c601c07a203580c3c0807410420500082450300300111903000c5100030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 332254244 1250 332252994 332253041
    0x601091503120306080d02070819050c130609060f03050703080715090609020108060904020f1e1509010311070f02042c01090b0603160b030c2814070206032701 70
    0x9106d603e40024650009199081c58068a65524952100355403000300188a0b09001c00c1000c1c08a05001c0030300401c0c000105c2000755501c002031140b0311800316044e290000000e00d07140402d2100381126040b00c003500000e491038503031038450f40c4000002c503030115801d481048012598400c1900260050310000351b40c01040c80027500041020385036030311481b011010040180c0c4d803680d481c01c82001c1038a4050805003404054100c106041b13903050f511801c564280701030101088040e204540c0241d800703015000a19003403550134854100c024082c42214187c403000b42c10140c214080000c49201441e85203103000d02020300100716900c0b040b07801e9459440b50b5081c008403401e4190410800c03806803154001c030036004410300d078941c81a210303200001300c00603d8440e284815216015403120700800c2007404100380b105480112101c074000300e545501807903d41e01000c0c0c1581c88240c5c0c0500817619640320485840d2403ca0f0341c022001c0c20305c40080c3e078942071810030f0003802c5004440d14000c034084003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 332255494 1250 332254244 332254259
    0xd020c011826010b060d02031506090a0303050a2001020a02150621120304050d18030b070507050f030a05120105100203030408070f0c030b090607020d020601091503120306 75
    0x8450003141d441680d030038140940e103074181a8040d0030500444504024000d460100d025000c0424915440a0003045880c030780092034004520403010142044146503a000420207580148603034290402e41c541c00510000703024000030310010a4a0030080f1710030302d04c013001102c8030010a016207103a9401150260f82c060701081800d0521703104450614040c9440ca0207e400c00249034801c14400c04490100c2c00001030602c8021340c14900781004994034602400e00319900ca022201a000207842c105003001000b101404650a0700e5102041d100284c64121049481e60420310056030503024041e1440e0018000700018051200d20f43c0b5020307107480300100201c66003a016445103001d40e180040c3c0c145959070200c100d80d40558010b4070a138451249041511610640fa4030051010001810201c2030051001ca00340c42001d41508a81c03081d550000100d85580148060102583c8130800611400c10700381c04c40707110b000058040c02c9049603241c1340c50790f8100040740c1800209036907460900004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 332256744 1250 332255494 332255507
    0xb041a07020c0303340f030f03110d09030509030d110c0a0f0b1308030c100f09031e021002030f04030e150405061c09060e0712020f04020d0e0d020c01 66
    0x4550000d00b00200c203110210380c5920441c2c00040b400511104d04000120050003030040b101d2881c0000014007001340303010703606094104070950204000060000c65140702c0c0c003a03040041c5040603d181804200c19250001e444107040031824440c051000001d244c404114098041c002da580741041d080c0c2c01c1400c141003021558100c0e0150334041d43c00d2041e02c840c8100301b0100e85104403826030b10541e00d41c01e020f000ba0300b41c002e41018000051100c60141000501d115540d095a0041250807000703e0200122513620700c004011603611500340346003c0030140c07203101d03104860041d241c50261007500072080740e0046071a000b540c01c01da820311050607800b0015a03080d210950300c503141401403846011160140e4416203204050016421098660a585407588d102d01d840040c84107031554a0301801828107000b030241e031071081040000c1c03401c0d50352548142454003c0c00f07002e031005a1805110195110708101080705496014042e0840c008214a00041c0d01035800703081c60303251000004050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 332257994 1250 332256744 332256751
    0x40317010515071103030c070306020403020306150f220204030c03140d02120a0e0406032f0a05090a0209030a08030a05010f06050a0e030a05121c09030807050310030b041a 75
    0x180981450702e0060300340d10822100c4158025140b040d010020700e0000c0e01d144503009040d4960b004100780002086003d0b0040c20a50f031003102a00d50580e14a8885504405c20342441c1ea84800c03c00000c1096080204003401c1e4444460a51581031440c90f520700180da0003a402101ca98440000400030311880307040304024144140701520325441c50090082d69480c0100090003070b0100001c405039810701602035a9141e82020b44180038041ea41e04000300c00314044001d0f403038601c416681124501c5c1c0f68654075003814400401d118801ca09006c14040d02c450024170017070341c8560821030720580350b0301001014042392040f94107075940d10703244c0f0404040c0d40060b40441004150000c0c00e020042d0482e068400b21541c030314044100c00e4a00c00000d14081c06034501a1642c01000b4000151440b52001170016200866120305070400c0050250201c8800c1600031300021f0008c800304180718400c0340215000324041a03860021502c83d10b9180c001c0106980c12a003c0c50310f400850542d683d50707490540e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 332259244 1250 332257994 332257999
    0x3010807082109120309030d0905040b0a0501020d0302250b07120b03120c01090b070f090b030103020901030219030501020c0105100905060d02060f0f0304080a0305061c060c050903060403170105 85
    0x361400c481902030329405041001c41c40f0b4240d141054071458405c000399904040010300303c84240d00d604101804068450150314055420101c01c0d00c00750600b84a05000c642047e40241140c882d02d08048000390410b07040c510b511440409e244003548002c2420800c0b10317010b07454000c511b00308407102511030101d840170005014240018102035650106415031003039402c00740325035240d00480349180108030705140242042d404806000c402ea502503034802c1e042a26880d1269815214100400a4042444000e61000c08040140f00504008100100161008400c100d1468980d1354403400d982205030020204da544000b08030022014000050050540e10001c1115060031000710302a0b19030314802a010b504001140c1c1c6503005443d00316225003a01001d443e849080c28a04101154080d0050000007401c240226020349420340d03204a20200545100386071500d00d0f580c1e4805030048911382c0e011b1240620078040c040d1418812148031b03600c01c1c0c1d1086109400d6074010082c060041c0c10150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 332260494 1250 332259244 332259283
    0x60e150a0b1c021603090f0b040305100c05211e04020d060b01230405040f050906041203090f0b16030615051b03040608180604020a0e04170301080708 66
    0x200c520305400842e1501c91041d100e080c0450828a0110041c0c414180b0703448442c0c526a40321024594864a80750540703046c1d250442d034141e40c1d19250f0a40b4011404054255003211110001d0b0401da5401070105540c0390504a051400d042120703e04045850489800881d0b807104100c0040c45420001c4100031a0024100b00c80c101364001c03448107108100700800d12544c0380c1104d00c0e280e000704540018802c41040c5c40300000c024980f5004160800e00c204c5000790704000c0b02d40034032000c9024aa100324960002840c080c0e40b50740310405000d460405101c00e140d80d80c400c00000c103040601a40030b180c0a079924100741d08055100086c04500344030792004162600005003c3d00c018214800d0035100180f404503140d03004854100c640c005208942c1d0300911001400154454101c580c10780720380307104110280e003441841402c07178a640c8102d400a6010801c2c410502c1001c0c2001011174001e401032103907a08150702c40f40f446401d68000e80001840d40e110f56001c0200010410a40310701e40255800301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 332261744 1250 332260494 332260499
    0x9050108030a0507060f140a0605030f0102160b040c032010091412010b040603050a0b010816030b0403120504030306050f04021201050616151505032a010210060e150a 73
    0x80c00c500460a000300b280d42c641c01c4042040d00d01c0d400c079085420000c10087d5680c01c01906000040c0103a00c2818024010a40d29240c540018403d50b0f030070781a190f001d00d440645590b80c1c000c0765000200121200c0c4507010003c800b0640c251041d000907000c065251484072004400c000c3c40640c044105030401801110520001d0800002c0121070041030b50500d904120750302520303001d8500400c0084c0c0140c5000d400100780300c80055a40b03922400f030091581d182c0d0300c2d40c4645448402008032440701d01d1a83c01c041001400b0034441551186c068078042c040e0b10b840c01218001ea8006413026000261500070030f025503d085038602803030040403030f804c6190000d044003418019034144261840340c0000b240d0070801107081c180341004154011200c03188115551501001496054100c0b82c1030040d400002c1900c1c10002007820720410349170f0290280c1a00c800c0009404202034103880d0441c09004001182107400d4015800900303100c02c16a101440c0404c120250326140ac410584a070310b0000b0304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 332262994 1250 332261744 332261747
    0x201050709171f0b090c070c050a03050606101b050c0907031a100504030f060501140a050102062406160b060f0d0611090d050f0105090309060a03150e01060909050108030a 75
    0xa12a85a0341d5404041e030512403550f1030020140188490342205101c0e04114151824000802000c0d119807643c0b154103803900305000441441c0c1c080202182e10040105076203103421582140c1d00e2000c5c1c0b6000c524041342c40c1c8030070010402004100d0709035204800211851500e5400941d00c0310701d61034200006058807520401e0104050802c1c2d01030b00141900307806080c801c40440c0d01460300460851905805441c00d4001070909220f5650305079002c0060030924900b400c45034048a20507401010613803142e072865110a2203998150951940d544a1040581c6403e0040c1c0f0f8070500072050321040f000c1e14107020b041c40c01d0040c85030748a2010b00043c49020f5403101050350030316800c0030700001c41d0007048101500d144075030014130342d010b013900c45010104400000d00400b0b07034005000174800c54882c036510550324001c6d2901507500040c244103103101c4500c242d03c40021091020034914040307503030340b032000c1c110032083c1c0003803000441d1000d041c0140541400750702d0042020340d009600d40340c2d40850 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 332264244 1250 332262994 332263003
    0x50109030e120d11100c0f0f0306030201050a05090f1c05010b04230a0e070b090f100e0609130e0106051e030a060f0e0115060207170312061906020105070917 69
    0x100d505011010f201d144c8a03840410205150400348603080104080d081806443c0c140c0c5101203200140301c00d0b0080045912a000da1070440b541a1205818840d65504c01d444a4201054054101c8826405100307642d0f120306248445642017a010080d106042c1440350035103540042640c09541001444019544209041000000c03041001c2070a074660a90580241214056404191080140124145140d01c3c001c0800090071904411303003051010030710460414102d240004506004a42c3e102400d104004064000d00100411400c000300e002c0c0e0000c44007c82103940c807603903503420244050300301070160800e02c1d1990040f07030404500c940c001941c1c0d4905100020311154807407508003840696030f0000b444034001403009002042000445803851141e912601005100d107401c00a02020340c03000708013001e080b04d4065860035621180c17034010780002600140d00048000b12000035034900c0150349010f02402d40c008145400c10580c011b245600a4018401c2c0c00444140300070400e00006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 332265494 1250 332264244 332264263
    0x504240510060804030c0501050c0a2714030109020d0b09071a0901030c030603150507080c070c12020307180207020a05061206040e120c0102091203040b0708030c070f050109030e12 79
    0x1408000b0f0340d56605d801c07034082c0e041d080003e02e03e40c2007906106110b800d610260548480554407011318102a07035108032000b031450240800c04203401c00a0100031220710708a00c0c464800780001c15080020303404140c43c0641d44c44141c072140b8041c82403060404040c00740500501e00c0d95140386140301c180b410301c00703039204000d0054141561089042c030002e01a4104400a6400c02c803900e0031009042800c00c05080110340000010710110001001240c8217030985142d190025500303032416050645401109002c07941c166454132841d400040c80b40c0400019244107400450056210706e914418041000d00e0798000703d128003000d10150b0303001a607a2200507800003040310049a44403905034440c0c00d25456104640e58644001041550702005400801c9180c00c26141c2c003840200c0d181d070640e101d0040b40070300d0421000811541008c9101203001e07603004a1003415080c84c200f581e640741c14005000c580211b520365150700b5035100340f640081060180c0402581c490300c503004180c0980e51a4040d04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 332266744 1250 332265494 332265497
    0x50303041202040906050403020303060a1e090218101206050102030a171b0307110f030f0304030f0509040912030b0406030c05010507080c0d0c0c06030e03120c0706050424051006 78
    0x203940c0041556101e4010140f04c54000d40c00f04010b091908000b5140c0d40300311072103030190300712540004010084403151181c8510481c5101f40c140c0c10180b120b0007a40c05009098620312154000c3d0145135030329118041e42d030400d521101409112400b910058900e00d1340420705640041c0402100b96800655144603501c483c203682e040c0d80c1c2c410010310814282d421034443d004802104106a0715040000800d903040b180e82161584d00c409907a07656070388a11141c0310100841070002c180000d000340040c4055060b1400c00e1810615813002160441d103540f08240d60500020550f0b60304190503129903800c40e4002c0d00c0900690307045840e042484001440b601e410814006001d82c1804140f00681c2c50b10210340d003d48082d400c0e6090010000b001482042e20312519000000500034041c1c03061698821080002e181072086c010204144a5002812504510310401c10740d00064101e101d414441d502ca1041c0c000002500c0207619400020548804121849c0c40c040c0804400b52429600449406 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 332267994 1250 332266744 332266769
    0x1504060b010216030b01050a050d11211002030103170901020714040207060515030d0f080a0c2706020f0c0303030f04030e13020c011b0f112d1605030304 67
    0x210004030720f800700c1c40802941d481251a804010051a440603038100c5408417001100f1a449a003000034400030b8a82c003c1110306032140c00203071411f0920030714140700c007070007070b480354010354200580d0904910503507143c8100d0b40000140200311ba810071044e4640c944204c045d0525820100203507440c0d82e2800303800c010741e050407036243e000e90313954040301c6072950302030f00502960030910000b0b6000d8070f081c800c8500c00c0c01550104000944207502c25a800d2440740e4a8074059161080c1240041c424405064108840c15500802012010340801000000b200c00e03071b002d0500d8001c00a042c0140c4c0b80710650360b6088800e0a244c1b507130300001603079002201c005100c035182d03d4901d801d880000f20b400b05a50489181011030340f000000794040c0425484481c020301c010300807072450074096685090100302050031074005841c01881440800300390101d010444940c81481d17085060f070700740d20041d40c1109409000c42100e00b44024401080091344107003c56403418200b000083c2c4034082c0e0301407109510300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 332269244 1250 332267994 332268011
    0xd090e07030f06270509060c040b030c0f07050c01170702120306040b0a06090f120803040f03022b1707020d0f0306051009060329010f030f06081509150406 68
    0x2c442d8004802040104035407148103a800410002d5030342804101040713180b500001502484000c9085071040380c1c202c40c142e203000e0504c5400c0016410140040d403c0e030304c041c4242c41c0c98078012001000d210b030180d0300400c00c10300114001041c2d80c240c0719482d03e00c04400000d0000d44d40e0006420342501d4001404e4545a64030341d0042402030036041c0846034070104039240001c034590005125000c0d0323054000364915860300c0b0344c0120b0011400c3c800c000c01c141c0c01000003c02007401c008000313990324441e02c155240c0d440103d108944c280c00074082940b016116954001c5510341200702c0b940400011409201140f0300010041e407600050300e010018004032004800d001c1c0e100340e11410190600404d00c0b81d071f2a036000c2006004500c0d84c003079400440c1c9419801040c4032100701c2c02445004440c48400c059008060044980b044691038800625032a95552840002036000340c17406404440018030354080d6003a005417003018050002c0d01d040d040701000d407842040c2c100c492903010707401c4040440d5441e03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 332270494 1250 332269244 332269271
    0x60206060f0d02030703230a030c020603070201290f0102010504050325060f0f0e01200a0908150603120307021506180f180115090908120108010e0d090e0703 69
    0x3078811000031340c180121301000c0200f00210220034950000b031500e513165080e40b00d0b07032940c3d9209100d4010303000c10401c40c1d480006240060056901070054800403ca5184d8403101c5140c00d442600054605600340b0550745440c2884030030301c0c54401c1c0910082c0b0480c1010344030030340c0303034070450312840d900d1282d2220807460581c10010005080e03512440c00c100101c500c882d1040144140e40f4030008903400c00120801144050182d0765007090b104040106450402c000c680541d84030506220903c81c14100c0002e5a01c3d05004214064441d01d50030403d80c40e0410405081408400b465500c0413424410f01c140603500050100750030001040524040e00c81000048552503030010010f09505243c040000890040c100301d07001d04605014800342140032000d640c2600c0c0340000d4013084e15580d02080151510642041310400d0180039000d01c0c14540c0c0c01310580c42e4200b60407070b0110b61b448507034245d0f090504101802c1c100901e45001580581010300f08050004090030500815842e09802c102c02da = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 332271744 1250 332270494 332270509
    0x1312030e060304111806060a08071101060906090b0109080d0c0312051314030a0f0e06040f0e041403040b03010b03250207181812050d02030c09090a06060206060f 71
    0x100c4000d0101d0703280d03d000d107002d02c0c000c46000c0540e4020001035803405007600d10140d1a07805000020440341c02d14000800459109400038884420017241c51841140c0c04028410040036117002c0754042038550070207050000b500e4003203900710304000c204c403800c010b5104085180104000f4510f8010544021414110385014070311044850f568074007014003110004407903080204a22a6110038031070b0f6010382125171071340a104034103804a281865200700143c0700d110050b4560000600031820691a00050400c031501d5800c0189407050031000d21041c0007045056500000b034610003940381c2802c008407031456000601c00e8003942c3c080032002c107095151810000d2840c1045801010400809a100a5980c1d5691107085021400c42880003440500360250001ca90085500000c07549529600c030003c0c07200200c200c2c0c04001d414441020f40440303a000950240003404882a12005101e04010b94000c0c081c3c000d02140340b40c180c04010f101c6c3c003c903203264843e070102c03001d640658100000c241d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 332272994 1250 332271744 332271767
    0x3030f020c130606080601020606011b140307030f091e0e04020607020301050c211b0a1e0309060e0a020f06030a02070503190f0f0c06020f0913060602060606131203 72
    0x8140000d0104003030900d6015000321032440d614005c86072958001a600c0340d40c2516620300240c200c4c1c04010b40300002c4141704214900c070b42c1d40526240031043c0c000e030454020580440010725050b8070203c4e441d42c024910800362000c1000d6290f100c0907413020f03c0401c4801e10800008031b440c4800a070542d90344000ba941e0310342e000340090200d0b160408511000d940000b030b4038418000d0f4104d0501800c422001c003d480f91406940c10350f8070900500c1509000c4e04414101d90800041d0000c60352503841c40c2003842c08a02c101e81b004a4101d41900c3c2504c15a4401402c848590307010000c8400540d03540740d011641d102d82074841c0b1759a03845d80946040640f00c0c8038030103050703840b00040410320344401130240002e0f4841992245088141500101c400e014031041c0100001e5417443c0c0080800d2095009004c0b42c0104510035103041d5004c0081032180300c04038000324031541e84820401c0b50603018400706601520407100580740c084000544105900c441c09528205c0d540841b0741c1c4105401240802c90 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 332274244 1250 332272994 332272999
    0x30a1a271b0607080d09050d0e18090a02031506150a1e0201060f08031305030102090d0b07091d07021c091a0403022e0203070b0708040318290405060403030f020c 71
    0x30745d0004500b00001403e280c84007140c80303100702070b0707403040c818490f078820401d80b1401011445200464461904102406007202c007190140310f03020401a42e0411110b11a0f11607001b0305400ca190030420441408000505040c441ca010170008000310703807006903c50b64000c242d110604d0002000012030040c2442d42040421042200001c00e142c0e000001a01c0030700d100c4100d41c5c101e16240c0c01403600b070f40500701005070492048051180060359140386140d2103041c071300d081140381d603451200001c2c2241c022000031205132114184012164180100c1144076810a1060210003071440000c1412406225901484641c0802400c0015454003203e0003941c0060282100c0a11405160740504029207001d01c0101e901d1542c020b69400072013a5181c0039004200c0c3c2015541d100400d443c0910010422000c105001d040c03203804640041c080000f90142100d0042d0711030900405400c000380c4004840455281030100b0021641d44d14111010707240d240c0307000d19209854420592400d04006d0782d066 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 332275494 1250 332274244 332274247
    0x7090204090f0e07062102070503030712051e071101110a02060603100e0c0402030612010504030302030a0f09110105071703010b0a0e010c150506030a1a271b060708 72
    0x800c6100e5412048204104810803c040140342d2042c2c2c1d5103070310b5841903001051605840002494501940080002803e600507241038081e90710281154001c40351030012030b03040c200d5101c0d144014800c0d59801190140d140c4090800d13506040d4008000034614002c1240000914660034020b4204410f5a061045110340700c54106030003a4441b10116541800ba104d1040c0320a6122024000e424404407003c020f0001d0400900a003c065032008140f5034005100b41c401c03004030308091251b144241d019550045e240e0400098100541f404c81504480040c1072200f5100030448041060000c203109080166807a07000b8034094901c0320079109542c0c50b00401200011b68042e07501c00510307c00c58181c1e584040307100c01030010740e1054140040580a0422900403090300122a4820354104800508840d8819999a034404803681d0760051400324405000a11900745010a080201200c107010f0038014a001a90f10b15601e850300814541442e500d500123040c903455000c200ca401c16001060103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 332276744 1250 332275494 332275499
    0x170c0a050c010e030d0f030c0c050f0a110a030b0604052d0712050c0306010c080408101d0712060b1906201b13060e1918030c1407090204 60
    0x129198441070041d0741c04100c0300c00c90700642d454045144841d076105034648220120301044114000c0c600301000c0c50030701c000714078114003050b81049640c00030019500100b10280c0c0901d0100e85d0b17144480d460340d0140d25000070038000601041c00c0315a03c11419900000ca6581e0074205a641c110034440045865050071400490042c803102ca15200e22710030340b40c92203c1e0030400d02c1e4504840d011070f00741041d00c105101140709584100c0380d1055240c0224521030400e0340b240c000604120074010300c1e501c1d061390b030900860101000203503100054840c002502001d40361103e0400c842d14550340080540e941d9204200580d82d030500c00c4160000303101c03407140010380c4588003e0150720b443c100010000e1300c210b203209030b640c00019150051028100701c1400305842c0200f0b201418004e044400c8480f5100c510129110f44082c1c080d0b88154190f05a0400143e44110403030201d40c000805402000c40c0c1d0442030f404290059540f140a42d80700c0c2070307038298000e84002ca904003060f0782c01c075100c000e0000500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 332277994 1250 332276744 332276753
    0x306050403110c030601030308070e0a09050a0209040605040506030703080319020d0b09100305120c070801050a020901140f0f0706020904360c170304030804060c0308061804170c0a 79
    0x100c1040c94800811241e612400c0f10400d40d42d1002480020000741e85040000c84692054074400c107046009042c4c2d00480e502c410000003516000c40c1c034824010760200e4030000a10303240c000c1000404080d14100f02c641400c3d00400e4a0301007500001c2d1642c02c000000c00c0c0e020321441076000b240005c0300342c21501c850a03040c1080c003400f070540c00c06201e8516180424002c07401c112014044980c07090060440c0c46505c1d159603010b41103044619881e0003010030020f10079400713000761842980b0700b15005940e0500c81d00050b0040000c40e5120194007010300041314041c440e170040303510400b00d2290780c9131510031502c1e200c40648a01c2902940080c2400e00000c1c000d0420003502d01c101d100d00d50120b02084040860780368050814101078140e09406004100c0080a4507540102120759000ea0386410f8894031405080d41c1326030701090004104404140c28540e0081e5140e411940440d000080101d0a0144040840002e000a0440e556085860328841c11030b0081b19442215981174903031002079400c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 332279244 1250 332277994 332278007
    0x3130e040b15010c03031113150201060602190f1e0b0901060b0a05090909070803040b070506010e01140415090e15130b010e0405150103060b12010b03030d0203060a0306050403 77
    0x30201d55201e4040d01103841e10400904a602901c81070303403520840318071038500b20050f149404c064408018100f00c0104104042c50846006d0401e003500a000380d011083c0c000c0c2103566035800102190050348280f40c0d07a05901035160085500b041101c030400344d0750b00301800340c14803001c0340c00000315148010341c082015002c41144545004002001242e5030f40c402285035100303400d00300700090010448064645040080785401c502e0100458001c0743c0c903010310510795841a00709200c4240046051010004c0421545016111218400b500e5500d00360003016003040140c80309200700e803034a01030341c50442c8901141000301030b56601480303e0130700a0405070b1980007080e0200d03141c11940000582e4202144400c41915502100382006a844c0004404078907202030403c0320940203154039554246281002d940c069801000c000600001c140b081011407505070300300d103038035074108070f09404a59008810703510105c3d80408003584e00d680e10000034184484036040200103614100521081c1a030015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 332280494 1250 332279244 332279251
    0x2e0c0806101409010c06090803040b0412030911100e040203070917121b0307060504140c0d050715020705030f03092404090c030209090114031002070c0b030903130e 72
    0x100c60300d06105400c1400c403800b184a02103211000002c001e0b508035540310318030400c0082d000b00b10008103008a0380ea19402a481a60207070f076400300c820300303202c24000b0555158214100c603060400c00341606944050f0341c44101d02113030307214030307808022000402d00400da48a40c010b0300605c11940da04e040e030000b603c00005030050091118014200114070b038000a854000c50302c0d500851f60803e102e80702c1b50b0700300c000201a80c4105002c107010b00c500040082c02003a002d41d2080b1a00071180c107580720880e01c0d01101c01561131240c1c04807d0480c002c00e60200b401015101103d000c0500b107041c0d4601a440d110059101c1074151040200d00d0840c6030010002c2c043e0100304807004840c2c407145400c5007010142841a41c50000d0b01003208000c40301503a4881d81c42003545007400360500138505c001601c0c41009034005030340c4191a2442222510341403048100212003c0021401c0c4020754840c1d021381440c50003104140080000890a45c41040040da04044440000070034007907181d60340f01f014a6400c0c4e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 332281744 1250 332280494 332280499
    0xf041506021c0e030705040c0c060903050712020c0108040b0703060e0f0f010f060504060c2f03070824090f03030405030a02100b010e0411040801060b04080f030403052e0c0806 77
    0x40301c032652064898581041a4800100281050381c02e1404020080c400380231400203120000310311400250060103900308a40c02031b10f4080d25156103060541031543c40c100f00e402150003001601782c4981c2c00405032500305070030101624a507540c81c00300358001d20454100460f850b82c541c1c200003d54141400243c8034ac86809200c5407140d0fa543c040d156003050b68050040880d40a100a108451040401a0320356010b00a0a02d15070219081d40f8000400303c1d400c1d244910003040e20380018141000000c000f000c81c2c10042c0315100c400f0307001c00e50495a543c054030001040c0008104182070404c00b1001451060b001e40341d50b41400d2a04596070b41c0081e20480150061a610310080c0c2842d00c0b62120400c0c040e1200da0403201158100710041c40c00340c444641503541404042107400c42441514091300e5801d40e0b866881b4140f07207000d40780c400c1c011041c00315603100700014000103c0208a080515020744200c05081501a2186e0034010242203804070071031408a01110481d030000b00140141da05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 332282994 1250 332281744 332281783
    0xb040522060b0d1a040b1f0e06070f0b0c0301120b040c091e0b0105040501120c1101020d0209030705040b0f150f19080717011a13060e1302030f01050f04150602 70
    0x1030350511003540c1d00e06242c242e07c00008442c00c55000ba60905500440001c0e1070802c07030440541000030a03a8106400a0f40c0f07401d1035412580c00c0140f9007240d40d1301310b25840c0b15030342550b24020340c41e02c0548903070800a04800000740402c0c2003014143d2840c0140a544e40d05100c1801c107030b442102e00388420240344030b5031410200c101e030055015004840aa41c01a9074550b036071415102c082000c0c04282e140c48040004c01c40860081840c284003402e03401d0f000e1038025030b840d1421010103140c4410350300464421890400c28000c1541e400000e014048030560341007444403a00f280e041617a0040b007460303007907111700000d07224220899084694018600c503169444181c070759240446480940301c03d800d505400721b00041c03101c2503032228140384100816501d1490403406010364400c60905500c46c6000c20343d401d85a030454513082c0c40b21150400b40740b03021819460004000700d54464180f048500034012110301405503200d6411a0101c14000c03114010b14550f1044001d50300c010350391081c90340414 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 332284244 1250 332282994 332283041
    0x30302071523010b03070f020c031f1d0a020d0f060e0309090a020c07170c060c030d0e0a03021005060117040c0302041a0901140307080601090c02070b040522060b0d 72
    0x489100b040e06840d08850402e043d079440389820307188035150b081d038802548a07901c001812070b40c04001c105000030007032104803003d040c0c0440f00000e4803031850196404e09080403404c05041000545190307083e80454040601241604140845071039a02002c0c250909009440c00c03001e10000042c41080000c0d03c50b0003083d030303030321011904038001c12602040c0e41c0c01202d000c100d545c807015107180b60a442a02610260411300d4009040b907030100d4a50400d5810200b0900000c10461048441003084240a882c4d1503041d0b85e030003916007051143c0c0009440d030314004541207900c111440d800a01034000c049007035082c81e003080902c0344154402248268101300281c2e40700c143c02540d941c14088050041c41443c0d082c82240a0502d861315440e54240c801c4000c0011401e40403c8820300034000b48000040b105001c1200a00b0f12405400190040e5400c000810690305c5d4200740f16034603030316150240d003070b1416010381d8405042e180d400982c11107400700e09525682260780c0046100b18600074107014010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 332285494 1250 332284244 332284301
    0x180b0a020d0815120304050d060603020a08030a02060f221103060604060513050402030a0501020406090e0609010303050a031503080a020102041701060b03060d031119062003060d0303020715 83
    0x6400321441409044555580783c058100490b20000380e002c4401541c0c1066280e60204404000c0b041c401e54081e41ca03100c0400030f43c2000c8454101400c1183c0c0030b103203442c10418000e507403117a024120304c0003002440000340f0f00729004020805d03119032110810007840c40a0074580f2445d00c04001c1c89119001e080081401d80ca0948100021140702078682d0101148020350000203200003403050f60180140f5005200041c030030710080c8090081c640b1008a940c0c10100c040200842c000c0c03100c0c1c00740000364014000b0a411405075209105140340125509850480c921a560641e5000506c104004106581e07a06d8042d0042c0060303c6400c0c1c00c88180f40c0c0c900464900340c3d8424030508203454803c001298650400c00c0c81c8252207402401d1410f40b041507036440914045003590300400220855070400c2c1006828002c801c0c0b8012186e2050328440d40700c44800025200250130b051146104101c403008142c0250151689113410103000303408172510141780e802030000d0b076600300f15588803800e095183e103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 332286744 1250 332285494 332285507
    0xc030a2319030c2c19033005030411062206030b04090f060c1707030b01030b030309100e01020a0b0a060303020f071211040b0607030c0506010602011103040210180b0a020d 75
    0x10604031040c40e03400380c8044c6115040c144154403941104064100c14018800074003448010761180d6200350b886c90004003648003040b00064541c1c0302040365600c5051712030f40403042e60b1308260462842c540e17480e0040c0005043e44640240050400c03042046072000d5200940d4a800300c409036103042c01094400810402254500300340141103844403800c2c3e8001c12802c0c3c0c0802c81c51421414104000c020044007000c0300d00e0200c80e850006030700c0c2c0310400f8032541d1501860052020680085060030b001c0c00010b00141102080380c82000002801507405a10800074a50b000760003003441088ca041c50400d85000c0c04d91800207a01500c2401c1002c0e2103001c00096540440c3c640f8803624100c401982d031358441000c0e000d502240e000340c440031001403a5a40c440104455881b0352214160846036181041c2003801c164012815649044861481c1e0406101101d1740030b50b040340c80307071142c2019240030707074100060301e42d000c02030b5115103404202c2107600401441581983e40803a02c442e2031408048454 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 332287994 1250 332286744 332286767
    0xb22051e210f0306010e1e03010c03020408030a0c0302010f0905150117030d0b150309010c120516030e030d0e0d020f3c0d1805060c030a2319030c 64
    0x1c1c441008146407040000d0050740e04054145071200e1741c18515000107103480381c09541160924003405540c01c480c0f030300f40b0440d90b80002c0c6040641c00c00d864180d0860300c9008180508c01441440b04140c400c240c800e62194801c40c41e13444080029a0305410700c591341d10700d802159152401d0810001c210010107030046100110704400a501c5d204507000900f002d402504d43d119040001200100351a22922000d10310074041d80000040c075001180c0010082829142c821500c0c1e49001d040c810210580d140480f0086500c0c1000b2902011400300c1ca4070350702c222141ca4800034038010a0319201240414484a990b16036800c5900c40500020003e072115880c560460000d0142d64559106428124120740a1055240210108810280300382e040941c40b41ca088001140c0ca0010020329500d804c3e035001501040d030f4802c2c1084c182601c42685c4c0c0c803903660804e0600030750100b614241c84031800f9164070794046201c01602c42c0d0310207003c042c07441d070160401404a0b00700b00080084074801d1885500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 332289244 1250 332287994 332288053
    0x501030b1518010e04270c03020a09020c160302060d1e0203070504080610050109050f0d12050c0f010603050303060f06160506040204050a090210030c14130806070503040b22051e 78
    0x1e246c1e0300310084000c03480031001c46020048800c00000b50f07594990010003013a5000c40542c1d95010381e000a0b06120884558101501148bc2c0600140c0c030f07070170151501d0500741000040d508040d40c034400b60001c0d10405500e00c0300c0c00001005105580800500101d0b480340f8101c078000d86800d28030030f10048aa004082c0000c2c600300c0200070520b400c04003901001c00281c60618840b50a17200c000641d108400e08101103180003802c0141d0b07020421004a40507400d07402041841d0961355a240c4a02c00030300200d109401180309002c26030f5410040340ca810811041e075500c003018030320b000790b181c0310100c400340d00c11441c080002d02442e8160103040300d61540100201d40c40c6d02c0c9003c0030340040c09007240510800911001141290784c13048010441203003000c030a080b07224a440b8209113071101c020403a81c2040000d0003444002817089171030b50341004008190031a80c4848002c007800081d85240041d245125546019a402c0d00e01e00e031040b60803060340203a0f4000c102040080017480b800396600b10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 332290494 1250 332289244 332289281
    0x2160305120f090d03030c0e040c080114061603030501180b032a030d090807090c020d0309050c060301091a120a060f1b0801090e070605040501030b1518010e04 70
    0x4008400c0c68000d000301a0b0340b01d220303403c2c4003803100402e0718641c20311004c4021a640710000c00c5001d0b00f007000b585000c0c0c41102d082c04641e0b21110001c01c403100c10322440520100707484030844941c1d105010f50f80350b86e0140502107110515420001c000c1c0500f84550b11a81c60007107001580054207000d664040b010150003004c441e0300500d4101010119503410030094000c070000d1140f160307020711080f5600d55083c0e0355500082e0810141c0c3e814681142e10200b4054a81090400940d40100302050303a00e907241000106d10866080c00c0d401d2003c0c0d50581c543c040350000000c03d0749482540065000e0075001442403d00843d8828000090406030306040710341e108071904800110142c102001d081b00c14000800d181040310810308441d0200744501010810f5100188107030509481810b000c2f2042400402c042c0d864240042c200784228080c0f503041545800c4010059103d01c405100c80a004c0700d0f403295100d000348290f410400c5c0403001e45001a41c02e81c03281c3c00900e09400380d0b0480d40c0001c40c090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 332291744 1250 332290494 332290513
    0x9060306060804030c140106120b0a0b010903020603180d030c1808060604020c070306090b04031d090c07050c0a151710090c090e0a020d0c0c050a240e0d02160305 71
    0x9917124803211404603400e007130b06620044492003e00480004044107441010030104600e00344101120080100c580246089070b030700701c60f0b83c4c00440f04086940556040d580c944030101800c1d01410300015410940c07050320024840140d040e071000c12600c0050740e9040b8000c0403840c0e030051142c0144910800c69100501003030441c03800da07008046e040c00c80002c55034180d60fa6070b2244144e50200000383e42c0305050508110074560440750310517120100e008122000206080002c40d40d2030082c2018582c00004030f020301c00c0110820101210300802458540540c0e521040503a00b2103400c2046000030741100035500c01003804962442c080d17444085c0c3c62040a007002480c03002406200c944e04104000400000341d000044500207014007065040507942d50401d1080c1d00955501c6291881003102e0304041d98007156010400120b410360220409c1e0020501000c00d03201a07021407411140c45203801440011080f0000712641a10511340941d06079001c08114a403202649100240032900310342940d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 332292994 1250 332291744 332291747
    0x390908030315120a0f06141006121d1c12060803030402120109020a060c060b120d111c03050f0108060c070b09120f09030705120d180b030906070906030606080403 71
    0x2c0c003841c20316100c1110b44040c050b440e1440030400c01c04060301d01030390f21082c5007401487c0c42c07181544641c0c00382c001200c2c645052002031002e2240710510f100d55036640d0f15840980640d681741001e04d40b4500803140d0345070b81c40f00c1000e00360b01e016492001242d1902c0b00e44100d18880c4c00b80d18203c50300c40001d94210307a07807502406043c400014002e041c9559491003400180da40450345405054690342d0b2a441a84602e410011602005134140c400c101c0d4142c0c1182840000440c032480100a01d00301104140c2c5505207071400c100c8014002c61944d4074039114640c01c1c0e260380007621079121103010318020b90340c071514252280303000e86560b09027600c00c00c0180046500001d22b207800000e0070742120540c1902c0181071403e80c20081d1000e0142d180050510175500c1c1c1080340c01f01914049800070f08070300f14682182c2e030b21189c222540c0c06100e140b0010100c1d40e00c47e20222002040000b00040d0380345030004800e40c030b07904200c58810110f1448440401c00520910030b05041d901385849844843e21980c40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 332294244 1250 332292994 332293009
    0x3110f03010603030801030f1b1d0f130b090f010203160f02030313030315050307080a06050f070f050c0f07060309031e0813030918020325090b0f0d06030b07020106120b0a390908030315 81
    0x810790ec02d1203010301403010039900740b009501c222447c845020a122001000070450900150180110750052044c0072081100180b0003101daa0305040002e01c01402d032200c0c02e0320380b4481e8882641070051880000e40c404c808207402f90107620540003040280d81c0c4107112071995106503038001c00242130f215001d460358000c130010007000840b1000c4403079100c007001c00107103402015003003040065260310300d803c100768011130400d05e00c078501c0b8503400e54450200c20081c4028030003401880c1100030000341e6014103019440744409030020181c91a0a055100c016201070351050b01c0c1400c0c034103005091903c80014004010b00028601d030b6070800300714030b0b08010100c25000b0387c0c00921303965010000304c0c1d0040440c3c03283d030000394420805010079150568019007107800ca50311030120903140780070030f0001403c2449500e80c0040007032400921081980c02c1d100307040300c101c0f0700c2270744406c5042600300e854254448812000c8000d41c2d90000040d4846801d5038032030100342c1d200a09131405404601140c0b40a04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 332295494 1250 332294244 332294251
    0x150906080d210c020709050f06090705090a0b04090e0d05040b120403030605030a060c12020c120d09140a05011107020609010c03110703110f03010603030801030f1b1d0f130b 76
    0x80002042002190b0820100c0310b41d8892140944e00080080018100c28000c856100c1c9039850800058038085001c02c1101000620f803104001d4001100310190361440180c401a0030045083c1c1c0c0c6551300c4a15890003410281c4111107180b01d03003081e08548520810031501038807150001c0d5820121408040c1403501070103041203080c03542b40c0401080c02c0d10104600a0752500a110101d00c0281e0b240340900080140401086c0b21401004240030001000844244e102c8400001541c0c60b4021110000105003116004001c506203915030303c000070740007803420412400b07540200440c041d00715001c0320600c211000290041e030103019100f2690b014400700d0158601a09002140718244042c0c58140a02d40d00104c0e540440000703070b103095041c200e0558015401c20380081101a00b50f84015110440c144001824155500c003180c0400c900d00600c0449440344400c0802000d0311501441c0e0090b1042100a03094841d000000300d8140c44401c41ca4050384240d4807551291842d611411004040107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 332296744 1250 332295494 332295527
    0xb0a020703030503090c06180f0906010c02012706050406030e01020703080f07020a120c050f030c07030b1b040611160b03150d08071209150e120a0506070201150906080d 74
    0x1d101b00c0c5081d0300c8a034014403408507942c3c160031701d0803188010021608907054900340140c101101700680c0780d07001910981450f8090a114000011003070f1041c02d000039a00c0c100c08420442c14000801503002406002500e44c80d4400740601d0703018010290803402954005000102040080380c0d40490700c103c140d400400078810b075803080c1d100d07884454010612214800000f004460707841d0501c00c0038050400b01c25804030107903180030714500d80d07190b0b2035525000c09004402e40c00085000c002c22819481500c100440c4110740300d80ea16000540540070014192545004480d10001880d07800c0b080d99041d2280042c0440c1107071610a4150144a80155055005107172000003002041041c3c010380340140c0303d140318107050101c28200503c545501c0d4080c1c0070030b2030300c07090401b11140c00000d1031140c035009581551b24400095681c900d03110010310013500e18050102442140741d810741000742e0305036000c040e114242c2c0c0d0f03a164560858841e4407840f41c0e9900302010144d6000e1084003180311a00c2e14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 332297994 1250 332296744 332296753
    0x603070f0c06110c0708012c190605070f03051003030807210207050d110a0618080c0106050a05101202070c0e072a110d080c0d0c0c0b0a02070303050309 67
    0x1c5940d8002190070000f0641032090010075405800c0d4010001d0801a00c1c402000b84443da40709000c10170314011400b58a030b0b60302e900c0d0410501900b002c00288401000796610480c1416141c2800e0008210680f550f0340018001416801254080e00403240100044155601d0092035074030200d5611602419210030000c0038040b500c00c058440010104411007020300507034483d0785150061920001810020500c81c20004881454401041c10903516400010129854034030041c15400070024000044c40007401003025000010154800d4060702c030141c030307408c0465450300d0403c84000c030344083c80d100240c814000d003064981079401030807c10f80315240c1c8044458544281511514084610303000080551881403411f108558180d200700c110400308a0705c0701c44e2615034801d10809000f200b0b000360301701da40072400c0120000c1240d800710310103020b46001d00f14210004003603c2800506a80d024514403000c00c1d402c00b950701715854000031760000e1000f1440d56034191071755040148400d00a004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 332299244 1250 332297994 332298017
    0x60302010203090d030e030706120c0c0b0c0a030209060a081e10031104090227010905010b0301290a020d1101050c04051302040b0a0e01110c0f010c020a0f0e010515090603070f 77
    0x2030410044001c0d104ea2b4030303805d002103422144001252040c003058401c10000c14404d030b0100d0340006071903400c224070341c6c4116558001d50200703401911803e01102c7c1c10400008410b01802d07401001603001d2094510801d140706100405030341e901c03005035031008148805d0181000096a40958130554000151010a80e01010307000516490700e403990703025100ba902032115001c2e04805020700d01601818004210079410000c00b2842400140280b4002c4406865a10445c000c0c0d2448412020801e000060361202c2120000b9201c114130020710020440180d0149a20401070250901c604124101d403420185080c080110f00107240c030303600410940c02c12002c59040700c0c01e002001510728545900100d080321200040c003c04507500854a660000683c502070f6030390300301c4881440782007440d19850701411400007421000c0540e0080d241c5250008001a221040107002d504031003045680c002841030154200005200707035401e5507401340342000024004d82c0120120140080203203400d00e45042d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 332300494 1250 332299244 332299249
    0x18010e060703050a09060815090703021c020d0b150a200d03020a110a17090a12050607020c0a08071a0712080a0605030c060906030604140403030c0f03060302010203090d030e 76
    0x601c0890700740d00103a00001d522202c1c1c1d4200407004003c09440c50500760500d000200c04007803001842002d80f2070340c03900c004a2030603482901a26891620490040307030301c0c44008507e400130360041c0350070110b65081041c01c0c0c0c05480c18a5040c0310320403164181c545000c1c160b01c411213826681030716400c2005008d202294075070004010043c28aa51902c00503501c020403100508508003000072000f440e03000c2c201c07510000c0c1c0503980e1449004140c5109c00d454a001038002a45070356190400b00005884034450000c0c030600140e9280181c0036602502d040d91014400e00100001c5402a000c0682c0450300405c0040c0c2d0b0021810320380201c00300c40714201403007030b602c0d400075081070181303100000d101e40c3c180902448107219900c014002280104000c1c0d44200c0410458000e140c0428070030600800002d43c1603d6a4014181c000d4289100340b0b818074151a01070002c103a107841840005400c00080100c50b8001e1042e90240c07a0141c00031800d051801e010030a4031032003c0300850800c00031030192445038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 332301744 1250 332300494 332300497
    0x4060f020c0616090b070203100f0e0d0207030c091b080c1c0504110a080d1b050109050a0308100b0412050a0506011401021b0a120609020d08090f010306060518010e06 73
    0x40308115000004101d000100500380c1c2400d8205c204c400004000a01c010703640020800281c05121902040b08a10b04000400810103544d00041074000c007001803505982c00705814060b0381c0300d207850349100e545a4145000b140d902d0080c526008100448030f00a043c01000560391013581d4424951038507401000700400c111404183c500700b41d407224180001c10005076003071406444280c4200040510702902c00c4d5903000304925a50501034a0460001d031003441d01c614100391500040203010081036440d016030f441186c4001500003c2c0004040740088070312404100442d07030010110303400d03d0304021100200481e1018100d42c0340c0f0941003d0380c0052020b002083c004c00ca903025011041030000d001a00342443e24104000c400c0c003c0780e0b12049680c80c043c040050715184514041522100c0c641440100301541000c0d6000f09402d4040c01040200c1004104100040d51749100810045005505903102405401d0204000303000005212280b1b510505200030f0515007416001425808039080303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 332302994 1250 332301744 332301751
    0x7090207080403120305100501030b01020f0105100519030206031b07060c111506030604080a0c05010e1c05120a0f02040911180d080d09140102130e01140904060f020c06 74
    0x1140c0c07001c0740c01c006015031a008000314003440c1c1400d1102d49003448414101c028940219410b05076104a41c02d80ca034400c00205810814031002040b141c200210300c480d1203000c500c9240d108013a00c140310300300352105414110071268060841c9003591a840c04160303800c8140f02500d10041402e00c03044020680c103014029102c5019190102d061048044090900d12008a000c0c0180803903000c0c000c1d00d80b000544c0030382c0250080b01e6981c9640b41058115a000c5060002509541c00c0000240c0c5480010039a90246c2028042c0d81208260301c24040d14140640b4950070801030360031000852074096900300c94201d01c0b00c41001441c007a1140c80010484007110302000900c0b0010038031041c90110500080a200307400c03030b0360740a1050356a40344000b0344101c5172040c1600c0d031204103a504101540c8400543d18090f94003d40d1140004c40d0940d0500c40544920640604450000507648071480520181100044c01c4100d082d5203075247c0401070040d00a5140f101c0b6402c0181d03008040301804121300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 332304244 1250 332302994 332303003
    0x30f0f05070816110a0302062a06071701230d17070c030b09060115050a030f0c0503060301050c31121a071b14010b090a020d050907030206040b0c07090207 68
    0x46a80040c2408502c110314001058004d040b03581c8203001503910381003a151440c0c075004981007600074144440009c01060007050b0348a00c12042403000064112081c4150303444580b448081e5a0790303c078406111000342c2544c00c81e101294490390b221605051102c510003e0240300145803014031200001580d80c011501a0350f07000700c4800501c2044680d00d140b81d00889102c00619041d41010510340a00704066049801c1c13040000386403500c28061740140040d8182d0321020841d8074a50680544554821030350704c6d110703529000c00124502400420f481d6407c1c1105140c0101007d50240d03103800c41803002d000701001c1d1380c10000180c00380c41c401942c03030402e102d20030041684500c45160401c000c17001d0700d00030520248403000010103030a607181c0030b20710b0340202c4690003542e960706401e801440d04103105508a0824020003610110780e800030000c220348080700300036503501c00f0036840c0c6964050000035030001d801c2101304490003c1c00c000e801d940d00044142c9528564a103410303002ca07030050720b0445 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 332305494 1250 332304244 332304277
    0x10605040905010b0a080c03040f02040f0614030d0801050126070f110d08190e011b0207060305041203050415090f0c0e0f01210203030315040e0307030f0f050708 71
    0x1803900750060b00d00600c00021081e0030510017402c09050264010401241c3e81e0011001a05212400e000068403e0300640208800c01c05170700044d01070207483c0980d1190030351303011072a4101d040000301074a010385640e07100034043c1d0034a00110360300651400c550000c802c0c4518280e0746035a00c2140540200420f450b895541c5200b000050054070544106881d5074002280c240d20942e001114541d0021004149030b0a45803030142c1800145600c81140d5155032801803592420440921071840b5007000e602100c088035911703d41141550021a0300900c0c0a000851005841b80207400c0143c11610816107032400b0441054914100c0b012520191240c50026003808188009030410030080c01c01c282000340c0c1440c00e898110510380c410711840e88969144544c50002e4001c44804c1c43d1815401405e880d96400c041464118100c141009580701d41d10740011948195000412076024580c50703294100c14a600c0c00341541e28150500342001440000c21442c1c0004810000801c00b1420201d00b21 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 332306744 1250 332305494 332305499
    0xd1a04050c12030405060f040b070b04150c120203090a17190e030c0f0301020d02040f1707081b1801090c03060807060905150f0705100f0b0f1903080301060504 70
    0x1140790504885010b40241d4016007482d001d0b02010040b038040d283e0aa40c015514a50071203002d045100d184d12162120700d000c07940e0300820078080e2481e4080d9018003840150f8440000010044030018081c2002281010105010703010040d00134680c03110245c000d1360080c100d60341b1100d401d5940d00300c41c245026800184032144000c81e024401d81d825175441c00010311003444010130756501c1c11903071840c4140000c542140e9256825012641e4040c55090103549956840e2100014080036001d2040f666508000d07001c0a010002000340480c0c01d480d000344408488203903c403040c2914074211a801c981c2c0c0c0480010081e0180407154000e0182d0a80010087e08440c002000c807881c1d50041072468008400c200002c941c0041c424060362403c80e00f01074454040024413000788100d800c80e2a0b85e280c045441028490b0100360507031940f682030820b0080c100745035400000c48201142080d4440040d5001100c13604200b200e40c5807c2041e5401e20040f140c483e210507046800917800400083c400140c00d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 332307994 1250 332306744 332306753
    0x1c11030f01181b08060409060f090507050616020d0602090409111906021e03120721050f160201201e070804030602090105041203020a061d12090d1a04 66
    0x360020441c07041001c40c00b40140141803806440f500401c101d4080b01161841d82c803584500c4240f944000204000c548407801d0801518010000780c5043c001c0440c0041d181c108101180d540340f0541c0c0c14011603000a900300b01c10b42210130360503a1841c0e824028543c45031110310400c0e03807a9020340e0a0801030300d140010441d00d880810002501d0722249a010440e4540000e00200310400344042003015070f80440d2000d1441c001c031818038140844c024203205000d9004514000c807411550710b1217241c0310f5000c0c6140207684e016100001085a1030001031100c01000b4244070f4017000c28800882c050013903c502440c0850a0441c030480c0141c00030704080c1691001840300300d9140c00102c11820044a03845041841c091880007501c025000504180303a40e00c2842110041c046402c480044800c0f14240256140301c40306080310300b2031406c07403c014010103014060b03075841007410040102d03590122400041d500504a440e801c0405003440c2000110080d011401607c10a25401101e1609040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 332309244 1250 332307994 332308019
    0x105092e0512030a0f03020313050109081b03030c07020d08070515060907090503060402130902031c0306170a33050a050703092f1e03060903040b1c11030f01 69
    0x10121950f40200100c0c060f068011343c1c624480521400e00680340d03520840c0e0320103004003202c401042d6528081e18001082012805400b210101140111b840c071400d200c615901e100c256004085a0014095000107281c81380b128110b1a108005083c00c1080c9550b9652a02e19921200c0410325203c0081010342e08003642c40e198030880903e0003d10151910b0046602c07060003030300281c0250b2401200480d600321940004002c264003404451844580480c14810354100c1c0154000080c24010002101c1c5000070010b240c0ba050364000e011074602c075654035400040ca14003001a030445a52042c100428000300c04083d0051144020501e40390501101003119070050649003454600700e10034010442a10104000000050810890450007002407058070b2410a82960001400c0d5100c1c0805116150074580040107800300c03210341d06d9100c2e070651280918060412103507130620040e0100d074090003c030031021660507000520b2030340782d9503a501c01340d004865400b41a4101d000410140d0308240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 332310494 1250 332309244 332309269
    0x10b130e0117100203060d14010207081209011a0906220c09030201080a0c05070f14102403050615120703080301050108010e0919020f0d110111010203040b0105092e05 73
    0x40452940c1b0b0300c2d50000342246411500944040c1a624000c20308582c258101e4403035581291100740c80313006c7c00205005407042210700e6102075080128030074200724000a4601b815100500084144da03400c4180300656241c0c850b45121a4140a44010a1440b070304c101c202032243d176034603c4100f170305500014008000181a54040e030b40391000c981105580401943d94080c0c2c02034a4102001042c01c02c01840000915480014040c4102484204c45940d0010507002d5600c0c00c048440207010014500403a101d10000c1c005401200000d040c0d120403580d03c010b550b030000c1c0308084c2801d101d0940c6160401e40e400486120070004018043d560b0000e912038010038042003040781c1031501a0b801504c45c0030800070414008601c5e0a0725007190344001ca10340c4a114050000201d0401900f414840d9204806ca80c0e400710f40300e491400c80d84d803818000c03a44150b8203e40100607992803c0705102140c140180103880d030442d01807490102e03c025803e0314580751502c090081c0035506107010492903c1c00c82 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 332311744 1250 332310494 332310523
    0xb090a0e0f010b07080c03040617071d040506042403061b0e010c02011205090a03080117060112030c050307030f02010f23150607060e0c18010b130e0117 67
    0x20104400c45481c5495581501e4500e0800c41d181c060601e032141076802030340d810a10034000401c0104440d9480004001c18516840e52103402c0d4230340e040162812000d4001c2000900300b690740642c8a41003d0300640d401c00c0d000303000040d41e4140111107003694081081c0484031803101c00001c00a1217040d008904c3c505a01e2004011a1441c0c01c1c1d01400e0401c00340380d018180b0603251104c0056a0250781c00d0030003c44003000c14000f901e481e0b01c8141e154801c0c1c050840c08601a000003090740301c043c010031024007080d200104820790030a4400c40c2d185002c3d0b08110308103e1002c2203100042c0050000c0d100d003c0c400c1e12161000800d082c0041c0c03d4501c1d007003942aa1507e8500003040020030024501201400c00703144041c070b501c0b171118122582c090321840e181c100000140c00f500704420b5a2003100e58501201c00c2d141204040810456003c8186480d40c0c400840d060050026810041c024041d04c8000044043c0c16640c1e8940352411410983c4501d09076900f0b108242d1002800788078100313060800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 332312994 1250 332311744 332311769
    0x140105010801140f1b0313030906030b060d0e070306180507050904021e191805010504020306090c0a0302072f0a230303250c1212270b090a 61
    0x41c1e0454859405008140c0344505841c1c00101d000c0d0480901000140008403017801e980c0d01e4400c10030380200b0642c4100324001200e100000494034441e01c50b0b81c8001c0380003000140b80815a9246d41c0244c0051011324505000b108000400285c0720b01c01d41d80003401c00f503c25a6850044e040490804000c0d51015000c2c1d2400820440142d0fa001801444403c1502881d0208649000031a440c4103482050714602e03500500302048004c00d20320095045150308100f803281e6a280e200b40002c2c3d00043e00c0d074540004c141c8002c28139441c0c0441c003420a0525502c1e00604100301501d03900b10300c1000348407021601400f4170361603c49846a40724401c03c082c081e40d071050601c1c545148032031503032000c0d10781440c1161010440e106c159000d004440600800d0a040002c0e030f00040041000c0761a020380c107c0b9900103400c00010552841c022100714682c20020204000709403240076240c442c40e101c041c49800709000e21350352507285240041000303007104845c6103445003201001e016038090303c3d403c8001d04910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 332314244 1250 332312994 332313011
    0xf22080d0206040f050c10050408010c0207080a03030509030d0f0209130c080103021009090501031421032410020c031603111002030c0f010c020106060e01080f04020a0503010603140105010801 84
    0x1c00040c42504a64032009a40310750450303040482c00c040240f80ca8a52254980020050096111020b08192000d21008020800c415441039a032480d052041001c3c0781c21103c041008280a41d000d103034028001c2e0140da14040a001005045440d08030f05070312280d80c0840c144203c1c0c02c102074014120419010101702c1100a034030301030000001484001e01c2540071418020780f0a100b1310080009204091051015503124034085e0000d01035030304028039502c00d00f10071000c81400441004501e0030f008a2403132941e102c403007028402c0d00c404062001d849441031440d001580b2015150008a1969400341801c0c912072020142043e0034100c0d0440e00c0e007084001131010845640d981c0380c00170801c98ae4403100301494030041c0e0450181101680c0340d4043da0100c21181c08042d0008601c0401a40c000c20072a174aa0005840411b003807001f240c0002d85e59000074600304003426206400c01d0008290003202561100020700f954490340046621400002071507004080c01d001c0c00d405400020000d024002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 332315494 1250 332314244 332314247
    0x5040902061206010e03030c1509060f011707211703150108091014090c0301150e07030b040c0302041e05030619090b010b0703120b130906020f22080d 66
    0x48007001c0d02540d00a0020403c43e80c0658280d86020b00050280c070b442d90001118161a41200e59928008081d1140060b48594000c145e892154400908030344950f424a41c0031602e19400d614042c03464490a6808210550000403603a002d81c43ca4151804158192030507040d00d4802d050fa00e134080d4000d00610140170440307511111005020f2810f51580c1d41c41c9858640790009d681b00b801000c40c40d15a40ca10344100c2003c2403440303a0f80200c122840d218003081818222001d1582c9440816100c1310309000c07080c01882d071759410101e41d25000c41c260701401e0004003116800d0002e1400300b40e00140400c607240c00310105103e000c10807840024143d01d494040f03a2241001440710951050040541e03030b2410307865001c03001858001401c4d980d150b844142681040c0e02440c416004a44401500d1002c45507602502c11444005854102c510000c00807610203041d54403400ca802039000d100c8000039050074000313030903024030081c0e04e40c0031b525141820380141001900906041d8001801000300c05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 332316744 1250 332315494 332315497
    0x81b07030203030a050c0c12150f07051204080903060702010c030f060b040e040f05060108030901320a02030403140a031b050c06130510110c0d11101e0201060305070504090206 77
    0x120581c144030b6501c46ea04100f5508020320380001e0743c1e000c610311030244070400000454a030011001008030aa90301c61050301e00a11800310b0b0b40e02c001030010440d00c41c40310980f01c403c5800c01d00ca00340712070400420704002414808200c800c080140e6641a00c110700321fa042c001e003420000c0b1a401004000d041100c40c4220b84110301414105440303002c0483e040040c6036a0b0080425008030558110796100c0a205440e40d002d01e003003e000032030462040c103481c0c1124080490343c400c2d840c040c06031180915000c15140d00045031403001e500003400004041031010707480f00140200c02029240c651154038010b007000d1f00c420528403601e81c4100820000940c00108e8030721681c0110344140d1036000c541000480ba00e001e0b0405a0442e010800e02c3d035000ba00a281207100c505848240c440c000c0340da000340306124200321006010340c40c4241c242e0b241404e08011900c0003080780d140c600c0311420a601548900c03000444800d00603996010100213000091142d80081c01c1d040714217100040960700050307583d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 332317994 1250 332316744 332316757
    0x19020d1a1603150b0f18100206040309090212150609100207031a19020f07060207082a1b03070e012d1401031802030714040501050d0b040f050f0a081b0703020303 71
    0x1003180003d511044020b01813a58617941b84001c0100054203202400251110401c1d2012408180e000c40041040807950003034440c140d10400e00b5000d20390b41d0714000d161014030121142c0e0001410410746582d42c60b03002d03407481c640d03070036400900140389546000c1c3d0052100a904c0704145580e0400d200200c90750681010b00000800c6016883c0c0d03600c3c0d00c0510152150700c40090840388000780c0242005002c0d0090308082c0c051100445080c04011400c3c44034a65840f1009116080100e03c400d10550a03541a0184103020b821106200d4603011641c8911000ba00700c2c0c0000c07090740748911510060300c0100b000701c42c0e0f03080c403458199280404a54603001020601414103072140320f9907402e000c540e40032510a40c0c000b0101c41c0c0710395448260007071070050b5510450286040c000042240c0c148103c88641d450761181d0004c00b6580c49803109121611004400c54441c0690544224040b00421401034154041c80800350742c4c0d004e074558031601c042c100004c0b08403600840020000351354003006076080d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 332319244 1250 332317994 332318017
    0x6090a0c0e04080c010c0809010c0c02100507030e030604110312041d060d12080a0605010302090f1504081203060111060907170c04060b0903010e19020d1a1603150b 72
    0xa90b02e880c82c2400e00c600440300f241c00d00307629107001200c11552040c9007a0081e5258070082200090340982180e1100291501940202c1e240846000b01c610840007084114020f00d0103030002950000064140f8509540c01e0786c40400300d001c0c00005141c2030000c2000303c00c100000502d000d2a14503040e0503140855400c03011b0002c1c41000a4080d1034207260305a00c2d50303202d410a41c071030000c1003024000207000d481303100c8081d103000c4022846502a1007100c7e03543c84010000041c08442c0e100b00080204107490b01007a01d103040c400020f10081c01c00560400d604002c1e00b05403289003800c0014170403054001c407040c55512160503c0002c20002c01d4007420341d0b8810340313504181d040b03110b03032145040480021190818a485400521481004082c204c0f80800b1802071010265003c400e0765500c128840503490407145107105001441d04540606145220b090f0600c6200200005444641400c80d0241c0492100c03d00c5140311540c10b00c00d4807000321031401c4007401d40b824442d00740200e0080b20015034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 332320494 1250 332319244 332319269
    0xd180b0709030c030314090301020703081b0a0915090b0720041103130606170c04060806010602060a020c0a06020304140705040e250302151e09130f0b040608010e06090a0c 75
    0x64556513201e0443c1ea1604008d40250341c0c5414615000b41807003001c4658000350407050341745100d40081c000803680242042c1c3c0e0750880b25410269401c400e148108011400d0101b943e100182c0c0910600103850f855020306e04100d41200a6194800d40721003c0410300d224030315281d280684100881c060b69002000c4d01038440c01c004e80382c41d002c8014103d58103d507918401990802072100d80000c1c00086034901500e00b0b102d1707155903010071569a8000c3c02800b0158000f8000200004816030113000e0007500c000807220f0502031038589000700d038000d0310b0a44d448440c00151100a00082010000070101a2800c00c000064850807039103440e1808000014080288a4074003200028840c042c040c42d002840038040020325451081d40383d0101100c042c1c1841e00f41d14810080341c420007698041c0d03d002e460b0740b01500c170b449010ac0c001c00d003895982911a907200c8600840d91164030400010340302c1c1c100001004140c6072003903460440000d04501c0b0f00c0d400942d8000000e6012282d00044510034031030030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 332321744 1250 332320494 332320517
    0x106112a01120609060305010f0b1507240b180708012d08011e06080709020d330b0405240705060a0902010917210d180b0709030c0303 59
    0x125030182d4040900182e10341040000b0507044102d51211049078810402007103140f00c220410400d40c0c410300840c66000c0c2d85000c4402781103550000a213101da204500500c0c85401080900e21035401d400142d03005c3c503a40360070403201800c004941440c5002c82125440c4039103422f000003058040140541c0402c54407041031683c0d8070a615040c41c00170400c00034498881900c3e5004d590007440b2101c80528a42d041a41500c0590000e2207903800799002ca4001c0d1050a0401c1107160181d0b00000b6154116aa2406041c1070070b028040c2c4c60259180084e10300064140c0541018060300309600080b070150010441000a3b80c1c82510f054507070140301540044401400c10140307801e00601c18050f115024180401c07014440325802064007610076220102c9180d120404001011400d00d003220f042c0d0300194000b00c00c26800c08240300703500910401c00789070181c0150b02005031100c050110440e0207410441031301308045502600d034454050f11b40000428950744800c41c105405101c084c00340044a80031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 332322994 1250 332321744 332321747
    0x7120e060705030301120c0e0709061d04150302031e100c020307080a0915050901020a140712140c0f1f050f0721050903070303140c0708060106112a01 66
    0xa560019812000f900c0d103960b56060400500b801494080701c140c07154030400300d450184801c100740501d54603a24a8100ca00b0007100303499060106000c1122000003071040002c40d42d807400380c3ca50440320729020541c000d00c2c52050501d0844402240352003443d0005400741c44480026880f516006180e00c04504000b4094040c1d06501c1491000342001c01c001501c080010b03040b41000d000c4604011000065135a035443c112154040c1d03104030740c0141c000400420105060380409444005400d090f101d0701c1c0c0e03070f03450358a100b1074840320101ca02e0340060080c0c41090b502030000c00384440085e500160300240080009812020b0400240c2804181c0c5076000c040c03078031480c140e885901ca000615952510b00382030541c03011300754001d00402d40c03848100c038014952050003a0b944a5601500910280b415543e041e40e041c2007040303070215180b009101c58889203104010000082030440041c029075418250700030800703070040d100c5040581c801c05c0314440d4522030181ca1400c80484032100303642d0440d074000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 332324244 1250 332322994 332322997
    0x20030913181e1707050705180606130803030a0b18010e040f0c09050117060a0606091203170a0912020609030a0f0e040e070501021005060d020f030312130c0b07120e06 73
    0x401800304030f801042c0c0a841030340315004040395400340b0100c030005a40d505c2044122038010040c02401c1c4003000200d089810400d01400c0a540000000c044403525842c41518540088400c68821500d4400440da10f00340f00350600c07031000c0c1c02c6210349815070410408010180000e00020031403446201114144503020012002070074120f14180800e594a070402c07000709100804241045c0160004144444070398030807001210f4a54541c0c03a401440c00b0404c0d0b01e030382850003042e0300b841011b00c00c0b1551550501541803144074182c0300000d01109a041402d1040500040102558840000e200c517a1200209682480080d45401c024006059104030380c102c11406c402a0441d007450710350400070700045114015942e00ba0f00b165a00449002000c0a03640243da82c1d94100340a02c40304000350400d031000145090002e003c0b82d240403003040781180380388412142c0042030b0170412000010880c41c40c00c1c010040c036486000e1400c1102940b1421174801c8426004404d0100038480311440762503c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 332325494 1250 332324244 332324303
    0x308071b060905042315040209040f0207140321100503100c0e0307061d0a0e0f011d06010e0405041509143a2003091318 53
    0x9021051140c1d110380240c140a1540510383c413440c1054000440da8958031060070f80e0030382003014180552078466405010f0354003980343c076802540030420846a6250b0f40a41c20a6030118100103031f4817200760601c1c1d05020580a080c0c140d43c0c000b0001114038002498141380e400b090440c407080d441e100c0b220601a4000c041c0c0c44950103004101c5030500440403540a91412801510b44540c21880d680070140c03103078010b0191801048807882c1d0350020b9101070b4110319580c003004c6e144821268486005046502041711024007004151006100c40d62000000c096400c4120b00d203118a402c1403070018007181c281c4810349010b83d0307441c40042c082c0300d0510409070000c038a00c070003044005c110b400c0032142c41840d035201040c54454441c0903044c414004281040ca411140010400b515800d01c19508041c0c5d00c0313800004004a01c1004003c604210a158840d004030308000d580da09510014490180c42c0080a4000c1a00d40720100c0200844d140381071000c6603011a4040312076500502003010460000e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 332326744 1250 332325494 332325533
    0x120b0405090d03050601090f09090614190605101704021513140d050706050c010902060d0b030c012309011107030506040c0b0310050f180a020306040e0313030807 71
    0x40074448520008580000c0000181e9018081641e602d4010746070089107100c3d504505081410421044046a00483d05144119004200b403800d9540381c810f002c405503030908502c2c1071501c6003010741c412449940020201030340e200e448071000c1c04c0041c040348908881c107409100d18000080c21503898544c00300901850811040c0c8642d507074045002c1c2000140656244600301c0714810001d40303403a0200c141c0e20355001c80241002030520303c0840b001d401030a1418840e42d00c4426440041ea50328014190040400000090000f800010140f5104541102a060010f40d224040c0b0512201140307105040c6e028421303581d14992480103c0304400c498000e52054002c014001c020000d001c54901d01490150303110001c01ba4403100200002e1005880484c40d12208009c100011309000300c2000c89250018200c0c401c0c0e2344000910209520100c695031030381940001000940d1410348103034950010448029810030600046c03030300c05a00140406400e2040c0419060208800050099005080b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 332327994 1250 332326744 332326751
    0xb030309041d0d030506100e0d080c0a08040e0f010e0907050f0d080309030405040e2a010905040504061b14070602030621030408010c0e0321130b1e0f0a120b04 70
    0x102d010044c02084266038061182650000320100c03244580618111804010318040c8140056511040e0035400351204c141a802002079003070105182101030001000c881c2400d580700e1522181200032410160030840903044110280300b0700354000100c020980c2e40c04d44a8101c0b840d000c0300010032a000f903040081625400108110344010003001401c2100c000b582d040c4044220b0720907441d11207417400d4400004406290362440d07001c500014081d0190010b05103002116201c038041401c1d600c007240c1c151403a903122507590001840d01da2002148003030910700200c071141003115003902072190140c05045c481d00400030941903602e404800e07130800c02480900f03a20f0214100c401c0e407039410038440c075030485d442d00c81081e02c0349004440c1c02c0791b8070030002c01600d1703500021542148403172800218485800014080d94010800000c0054064103c6429a54403420401d892803a0004032500644400f00c05004213000169400180c5036030341c5050a11881c1901c04540c1d44000f02000e2030015441401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 332329244 1250 332327994 332328013
    0xa050a090506161b08040302040506040207150203041a0405010e07050102030306100e030f0a0c06080a05010b0304330e060a0204060203160f02100905010813080a180518070f030b030309041d 83
    0x5c41c10003801120b100365018850b075503840f000c000032801219000707080c0d400545010380c442d04d0707298010760f0b01511403101b80301480064a00d0a1951100b2101116603070f669840082445004200f144010034091008600d90f281600110320180d031080581020302041a1a640d202d0354103000908060103501704039441c10403141004050048284119400b00b91005d010901c8151180036060589802a907072505c0c6032540c1c1c0e911a10301e2071010300c40b124502c08500d00900200701a080241c0d0b80300c002c1000c40c3c00a00b01c0701050031b000f0040c0460107060301c10001046941d4011050740d00d0f8507065508840d01c185642424580c240c16020000d41c001c012a40d000c1801e13400481c04030543e40c013a6580d065903690003401c50f89a4140c200054828441444550005407140002c00c4451100702c48481c0700030741e99008100c01e820b50301c00071280d0540620401040650101c8188500802c03407405120340742c4a000400d84911075030404a010b181c90b914560460800034070354041c500d2103a000c89203c0718 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 332330494 1250 332329244 332329253
    0x150c1509060403180506070206030c07150218031b0d020a0b040b0301060908030903070306110d020c0102040614072001050f16020102010606111b040902180a050a090506161b 76
    0x2070403142100801c4000c00e081031501d6488410038195100903184c036181a406408001e40c0342c00013000b503075090b803040141c1000103914480161500e04100700c05a00e030f4840301b0841d0b14081d007402405010740d204115040c44513070301c601a04070514055680114a0490f400410039031491030b04046554500010002400d141000040d4120f0702155290840d03142c07a210403a44a07c03941c080f06905612600003400451010380c846c03250039220000c218034002d003038400041aa04160301021080e507002c181000a2500040491800700c00d01c10000c2c41c1c000c86035100d1031002440d2030f5100c680d900010504646902450403110503280d800c1c10161034002011120940094501040b0f0040d4240840090361501402280105400003005000b0b4000501c10808420204000c59503019446181540242e160b100102d84010807034042402c0b1850315480000907160043d129000080c0f4181030301c000711f81c1c04502c443d0003640743e440b00c0d140711000740d034101d0301c00c0b001810010f0302d41d1007a4004070400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 332331744 1250 332330494 332330503
    0x22110d0210020c01020c15072a0824060315130605040b060f011e05071502070305030a050f010b04050108040c0321030f0c020c0d0c0b1303050c0a05150c1509 69
    0x3c4400d0b402c03142101c801d0401d00c40403240507091100c0044040c4120000200c016500802c3d102a4030f0380c4030400500103c40701003121072588546d01d6500401c40710b05410346082c07603c0d5401300701c0100400060a00202080c0e8070744c4803145404980c2c06030800b18002002c10300e40842c405800c05418081c5090604045491502c02d40e103c1d4898101c0d8440d07800d19501692400d1414440048201005441080180e455600015046480311544812401d0b01591072018204135402680d07102e44a1400d00702d01c03c1180e10241c00f84032506503160040188820900c1101c0035241c0038030b44078100382c5441c500024481c5d015040144410078140050344007414004411601e81000d41d4284011241d04041c0c40c1240e03150710640c030040e00810003803003080c10000c03141350310310748180b2000f0340c1300d40d407040807040780d07009840d000410b001701150810a200d42005001082d540444d8101d45683c45c1400080300351007000c01e440264030010545440703214082c415000d84858180c1c08641910f4820042902e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 332332994 1250 332331744 332331763
    0x118060b030c09040c06030b031603060506010810120f02220209010e181b0f03090d030e060f18190807030207120506060603270d030522110d021002 65
    0x19101c2e50140e20345030b2900b03c200e14011500645082c07039072030070080110003416440b60820b40620540d41c010010f0032400048800660041500007018140040010940c94004d007901c03502e18517010301803007448240d074841c58185034400ea608406e01d11510110302280d88080381d0800c1c0e25210301501c445040f094000b000c040409030b94506034541071000700000c1401c00021949010320381d000041001058080400024010410403070500110283c11502a0302c125803c42e1540c10203541031400c141c25009428130f5690a90250060786889440d400d0700400c02418054124402c441c3d060600f4810311003810b06c080c40d2581e8482103107290a0996099000c510100c0061280d540001220701a400d080803159a006002d000380e0b403200310803c0ba40e900041c10341c170a080c44c0303043c00101050202260441c1019944d02401c41860186800741c115003008240c049a10640700302d0406620720050000c0110383d0110645404400f9a00402c00e0948001402500020a00b042c451b5a91f000100f4014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 332334244 1250 332332994 332332999
    0x90a090213060201150e191104061d04020705030d050411030106081605040902060403110a05120a1703150d0f0b07080f010b120c0d0b060d0f060f08031207020118060b 73
    0x100c5054440c0b024580d00c0a81b02c3c500eaa0640f010100340c60003d00f4404100305422144082019108401008003c4e40603500242c081809918000070340c410300d584504c140d580480d002c40c1040c0c102c2e01c1d026120301c01c034141040201d51f6840042c1c01c2000c01180443d000354083d00070000d803038507850b1881d501c442414644000e4116801c0c0005d8514260092407001580a0700041c10145165682d043c0900d84128142d80251400e0b000715450311003803540303640d240000009140c0706d0100d050485201454408074408440100f0412000d1000070503001c40c1301d0410303582e101031780341d6600f040355600d00e003244020074512505c021b0228695000c1d04540c040e841c00e110407141c69907900000c08852243c2e44010700c032291940700103a81c45410b14081c005d04840c048001c45c213000c42c400014031030381c021003d001c022686c42030015002c50091007000082d110140c280c00c0620f090100103542d901954070001480181d04000132a4580f00303421803810f10150707031409107600c02d00340b4051001d041c030281d2490 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 332335494 1250 332334244 332334251
    0x4260607110c040e070b130b03070903030f03090b060f031c08010305190506010303080c0c0f03130e0105180712020706060504050a0b1e030f0a050a030f09030c0b090a090213060201 79
    0x84070f40f03800e1213101a68401031005050451405015141c0b0382c01002c0764a50701d140c00030f070004000d00c00000640c412400e42d69450740860442c030f8007501e401c180c1310f0700d00e080502d0401e214001400712400207030044421541c13040001e4110002902d444042c4c1003081070304450b0b1548540c45500031908030f041c0e07485582524800030f44242c182c1c3c0d100394980c0014010754805001000403a004064894010b0a000300062a0205041d0350f1480c100b00304a003c0c1d903903840010100c5080c0c01d01c01000014081426086040c1c2d45410009103184240318150b01c030040b2113901180b03440740034811400b101c0a102e007055448030a141808002130100d8854a4061400c120009083c19418031406d804080020540e145040303072069203081c034041003111550541700d100e9001002040030420440100d1103200240084e25903490002d24844904a40f1028490b0740e4000b80300003044c1c86c44200581d0740f81d11200e070300c69000708006807001d075555000501052000805a2401c403607251550280c884c150020b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 332336744 1250 332335494 332335513
    0x140a0b0106050a0906231314031218030102090d030c0c060819110f13031b080a08090d02060301080a03080f01210206130e090d020607050426060711 65
    0xb5640b900c07807440d4007000681c440c4024458280601c2034054800c00ca96001a42400308070800d4a00358090900b005040340d0f840d0003080030f81d003030b5a5030034042581603002e40240401d80c000c0c5442401a940014419044841c3c01c0b0f106440940c1600c0045500a0584150302c01c907085c040c001d94005a001c1e500c16804003004640507001d81c800381d0144054901b51071019a011841c07000500043c14068201041008181281c003208009803c0d0202c0c040b404024181c650325003840001002c1605250702d484201d400c02c03200c140032402d9540c2d507400190a980e901c2440740002d414501c03071030000754410f81c0440081410040001c103241c6e001e100c1e407524101c41d00c4500c01540596070900c078202c0040401000c5414031180810b001550510143c001d5081604076081100c1d0048242c02000340448413908108100408001906080b903c40c0040c000d03604110b4001803040c425401005102060403107038808480300746014040010307103101600c205040c030300760081060b124140450348601c12280c4c070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 332337994 1250 332336744 332336747
    0x4060e010603020d12140f0c07230d08120403171302090a090c050402030903070c06170402040b01110609010c03060b04050303040e07091a031e040f0605060409140a0b0106 75
    0x200010740f900204051040c00c41a43d9010b440818404000c01b04000a02c210340200c100e40050100b4070140e900090311400061085807801d032681d480310a0b40c01e40450412034000150141101c140c00544200107800f980d4207003900d062181e0a100381c00140b0321400c00050543c4101d007600c3e0f100706c189072540c1540b5902100055460982c03030103948040480045545100b050384641c802e580716904059001c4c2d030f1240018100e800854a95200d03420004907101000b9014203104081d081a05141050188124000c08000750007080240240e42e1036058403890f030300030800f991078054001708071801450502200740c013800c00e0174088404241030640208040820382c05940039a50050011400c20b0701e44045090303d50b002410f904113101c0444c0c2e01082c09841e40058154100551401d40d03513034200075003030340010080480c4441c92141c1400511001032204c501d801742c0a80c10144c0031070a5100d11700014020b06204000400c4400790242c3c88600b41d41c041148046030f03008940d0400d9aaa03a80300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 332339244 1250 332337994 332338001
    0x11030f190e1009090b03160b0403142808040302041e0e03090306060603130f0602120f04020102030a030507030f230105060a05070b1009090b180102090d0b04020d120804060e01 77
    0x40b201092110070240070002480d440b134901050004e0484455100c101c3d6000001e880d42c3e00104c20032100000d0501c24003002101c0340380207d01c0700d0000c2c07030703900c40c40030031307458901081c441c0b0b81c80e4038600b2603001d02407040038820b840103107070004d1003048613241d035018030101960003801c0b4906031804d00e4101c0760709110120940303603001c0018010303140581c1c0e44020441ca603072000b00000c081d80c00f140c111801254416041c00d050512804005a41e8641e0008050340f0f0080140080000103c2e00100001030341d0100a40b0a5a201d500300400d2075107400209034007800010a025400620300141e13440f0744803d0381401107068400d900c0c2c480140c0d803a1807d002c1c0d103108944502010800810451000400703409600341d000d03d03e540e56159454950201100b45c84d1010000c0d16083c00074030900c00001e41c4c200c80743c0303e164083c00086181041c0320010882d0344c030001002070110344165000600b035446008241458a602402803c425004100d011b0410303541900d007924254501a22802e0740c460510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 332340494 1250 332339244 332339269
    0xd0c0f1103090a03021507080c0a140c060a030203100503100f0e0606090112050304030510050108010c09151112040f1a070507030209040203160611100203041211030f190e 75
    0x40a0f0b000d41ca00b5a02404520303500c4941025403035000708072001c04561004090880d00039a04007130300e0221a5410600c0b1090fa4010040d01c00d5040304504640a695140440c0c500701141d080140c0ca035a2085c5480c0d00c1e5009583c030081d00350003020b0f42a0316440ca240d000202c11045000704104100c0240d40a40d524081259650303088585100144801c3c0c220011500020f8499000c0703910303050712036031b0341400c4c02030710a90041131646500044c0704c5c9030428000c4e9151011280703000034110b807400c88112040b0b030036608903109002000e5014145c2d89001d1000c4209035030303507180e11503817203030b0f03460303645813862558483d1030070709140005917014203d42c01c0120740c442500070005210340303403c54081250124018208aa062160b841c04850030b200302ca07100740080a054445110000383c000046040c07403039000e90b0720741c114410400c01c0001200c5013184a10500b280c0342240e20303400c02c084030502e1071048482c15001c0c1000400c000c40503a511599070540b150041e40c07129520014070f01804000111207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 332341744 1250 332340494 332340499
    0x307031a10051c091a06030c011d0a03020603040503031b03150112020706090b010e070201020702060d050c070b040506191a100e04060b0408160501090e0406020d0c0f110309 76
    0x7218841055201d28003410803500d004515003802146280081e0031990328800072201c0d840c001411441e07a0f4080901d00341e000e082034000c0c119034401440003d010b080000003200401c0c00403424440700d41c85291403034019640c00350101c1c0c1e0340d0805051903690b9410850b01807500d07a038000030740c0840445c2281070706d010b410360040c00380b41c1100000041d25109030103405906000d03400e10040d1b010035940d01030458a02d016041d4500301d0350501c0d100c0004103d00610030b1066a004204520040e21a28102d54251040746000541c585034102001c80c85c0c491241e0181c41c030000c080c1804180318010641c1406840368034048803883e00c0500425003640d07250050070701c129a840540314070a00301307078054642c40505860640d0f03244000c0c0d800241110083e4200390034004002c5020310581404004425003c0ac0a05034031082500d00000200a25128083c1004001182c0003142c10820300350181d5020300b860000500804000d518014110740c43d010310840010f43d03600c203402c0076260110840c0e1910501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 332342994 1250 332341744 332341759
    0x809190b040b01361821140d021309141e040f03050c01060b1303020406091406061b101e0905060106051303080307090f09020f0a0c03021e030307031a 66
    0x4902440c0240c504801a004c9180c1c0302e038101090103506821640c011840341c101034004003080710340190341050710442102030103080070102084003110402c0ea511001a00f00159580c918460401d02d5005564800d0440c00c0c100f4101242e09450990920b20881c0e450412088146082e0000d00e410308056401170101c0401c00d03041d40129100b00d0040203002c1c51480080f419075511900c214842c1c2c001c80d46010040081d1400740308500d89070051400805031602c040c40211100442a00e401c41b0180c001c5200b040000f8403c8240042e944c2e280040110b0b080617103088441e00440c030f034041c00c0e1304904043d40c0b0f040d100b01e5601e42c1c600c0784200f40150f50040300400c0c0a81c2040e00549841e440744454070304180a0780e10000003c0d04850086114441c50f83d141c8281d131f440c124010b81d00a42580110060b41d0040c09080050710400c4107841d04098a07241400c0c40100d5410242d0801091a82e00c040200f084c110b000c50005d0000b0085004421507501082101302c260f11038070541c2001c00615601144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 332344244 1250 332342994 332343059
    0x15020304050105191707020706030e0606031504030c170406030e0f150c070c0f060806060a020a0305090a030209180c04061a46080609070809190b040b01 67
    0x484100341130f044802c07400c04600b0310000d0300c0307004e01d192800c503400f00040c0c3c001081808015418099400604003010040800341000c10000782c4980700055000c9090070400005810b051180400d417004036085404202c454410130302c40c1c4110390050042001080c10101d4071450200b0000700c51519003010405459542840c0c0401c42103c000a0407c6840541c20300586010441440800006198000c2c4508001e8680003014046040003007000344102014000142110380116849000c1c90f0315283c141d03500c8440c800010715800356900044d40241010080100a400d02c010041c0c1c500c04100071a5881500704080005545903802002c40501c040740711131200140c400040c01d400354642003640b00541ca084181c00300b0710501900c000d059840c00340b85a0143c0c89010a0f5250701c001441d281d4450300c0e00d07034003244034960050000382c00c0041d0000000c008140c1442114207408840104650307000540c01e09140b031540a580c15a4202d0345800005101c603483c40c000083d0108004e05c4015801d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 332345494 1250 332344244 332344267
    0x3070b030708130c08150a060605072004090c090c2c040f0b1018050405070806061305030706020a0209010e01060f05030a0207051f0e0d050d0b01121515020304050105 73
    0x2006100302c0c0c03004502c580104032840c1c02d001c040c00381c510780468a03800c0d181001c2000d048d50001c0c2d2240c02804010002d00e00400c0e42000f402440005406a90300600184800310300107180c0104090702084011a020615011135004401559070303503507501c0b00f2075124603011004a403070150107030494041d0300c1c210111401c1c0307508000c0004204c5840024007014040c0800c0c81b0241d03110b4000c0005460711846100c64440c00540400380005a07410801da21740340c1d80241241c08081c00c020f102d800049030b000b913449030003040c00c0c0241c20054240c07441160396040195807542d401c001240f140c19600c0003c24400e40d491140d604031b0f8282d55840c0303400c688281042d17402d6407018001ca4490343d020002d05c1c021690410804242c41d14500404843c9140c004100d02180c1b54041d2103603076900708000c42103085d580402030b80d0300d1240072000010480410b2005983d680c1405483c041a00e0400107003d200800481510041303601c0ca4280c6107250001040c126280d104901486001c50424050402e520 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 332346744 1250 332345494 332345521
    0xe010e040b0f1c0b130803010303030b1c0503040512010207050c060a09080a05150c0a020d0806190b0306031903020627030c0c2403040204020f0f0304030201090203070b030708 77
    0x50280c42070b005070014001040300d8100003400e9891962041c1070190401c010314804541c07194500c255915100130300da59036000340c0b006120160405072142d0031064103555203401c0150080c412400700548a030b240c501542c0f46d800078441c0f10b11801048000481404041c000c40720f203103900c44043c1c03480500c007034204456900140300340800c20007124004a404c05041004083d0355000b0340c02082403c401d003200a625000050189040300c01c140070103030034242c00041c840903a20307403400c208429684003c041550390180940c040d0030034056880000d0590802001035004110039401e40381800c0001c0078500032000b601600400617840003000401104103040c20181500d00aa205103903c0306515580b85560420303022400709410030a07454280f4070b000da4100015000b01105803503c42201c03500c1d2007140c00024000381c004ccd5000a81d00262071890000c41f9502403d0315900c0e43c40c1e04150500a00030008110101d00a101e17285000c24101c450170245c03441182c540d51401050383d01c40801034441e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 332347994 1250 332346744 332346761
    0x50702090c0a110312040b07030e0309040f02090d1b0b0304050712150e0c1305010501020d12060e070206010602060a1e0b01030f06060302180f0d030503150d140c010e010e04 76
    0x1040b103ca5010300401405100400c0d606403000c064240c0f60409060001c8121405414a424075180000381e03800780e000402030b0707980c1d0342044400180b160802010840640300b0075201c10f0340011403900d103504001c8400c0720b4800440c1030310300c503030022915410712807d01d102c107031800b500301d5020000402c10500c10301048007049124109095410101912004c1955001c4c03000c84184d070002011095503041072800c1c03d080302d950400501141d45850000303522008101006008c019104102070843c050680040e0010300c1c6c1807600030603a240008009490380780a000c0d41d070050140700081b27900e42c04030740208401104400500c43c501c20f540701c00d95006001e01070b007035418103845610001101b040e5100c5c003401802d02d61400350f41d50a40c04006140d50798002000c40c0b048001050001580d00c07000806000143e1508000d680e0351200c45135002400c0c82309101c40d43c0015001c20450030401504030b00b2422207400e404650003040d80b40019507481d8500911140091544001c101040c50990881070341d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 332349244 1250 332347994 332347997
    0xa020a12050f06041505130b131b06030b1009060f08060301510317120403020c120f0c0907030e07031a010806010b030439090c050702090c0a 62
    0x6051400b00c15203800c02804544c255200e02440420043c03214041c0612540500712803460a01001d940e5510b82c0001000b47ca604850700a0102e0f84040020114040109041c0e03e00001c041c10380c0c50b00010050306551a40a0140049104140001f401202848280d0301c440d04e5800c12120003150442d070700f94004201540c550740720302d9040c0001da5840201e107501d10944400d00035140789410300052220f001840020340080f501c0e10f0481154480740343c00c0070b80354840041181c0708540e81d5015014011400d601d501c5c29440010f01007050740000d402c0110601c1598200c401079200403072141c5034400c4c242c50700c03540c0d0080950310a151400e5200b80d40e00010324100011655900d040d018a010415041100c0840100310000e0418519035000c500520241004240c55814004030140350b00028100406984040c08c0d40d8140c109540344000c40c0803014800889000c01c0201480c0b076000d450304c02e07454024900b503014005940329030102c0d550240c024140c1c500940300c10070303810035550260807400d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 332350494 1250 332349244 332349253
    0x90d0303021204030c05161818021314010e06181906032405010b19020709090629031905120301060807031a1f0909020d020406020f0a020a1205 63
    0x46100b0b003401c03800d0f0043d4042e6030b941034010380e5403801910301100500301001411410408100c07002c0c0c0100e4103083d02c03082020100304484560701c0c55240203c0307004001d502c0608140c181c82441c000707030310284d503d45100b042c203080b5903a60103400000e84816510550400300380281c80301140300341a0a140c00154071078488009a010103020412103070705402c10bc07a1204404803401d01c41410f8181800c40401c2010200003a52403d00b102146100390405d0354a03a00500c1e0014082c10300900c509002400e40e14018042d09a203894044010000c03071024880c29124030410304415811845c0c41d21071200042c00601c4003254000c41000121505e2a00310b845210b000c296a4075000726101840c028a141e481d80310f1613040129003c1c0c00e8405c4c2840b411200f232480b03000349031b995031815170810b40481842010140c81500b000e0803200c0c00910703001090841d000144003080156160f0060040300e441e80d096a0920b00304581107600c034051281c1c00b0350312030501c590900102c001c038501603940500c10000c64 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 332351744 1250 332350494 332350507
    0x4030c030e1507060b190312030f060e01240e01140d09030c050607030509060f09010f0501180e120301030b1e0a050403090806060d0602090d0204090c15080903090d030302 75
    0x5071020140ea4000d80070140100e8000c1c200700b141e0045c1203105408070344290550001c4481d01c488002644000382c500810010760007852400b0358006143d909500c003060003c580c84141c0005c1040b400c0c0702c0c00d80e0203001c6c1c9481d1015070f14400303c030803070249581c1d079000d4030b51510f40b004543c5607160030041c0e00101d4040281508038512480b4203003106200c1c2e00c0f03207842040641812410583c00604407028503040c0010007515101c08562681d0011554601550383e403201d801c560b005181e2a142503002c03506e40000861341a07140200000c6100c2c40c0f0806005410039001455101c007140396030600d580c2c501713200501c0024041c82040e070380410001140c00c420102c480340c000300d08006841c0c0c12002c5a441040c0418158010b14002c0074100080041803241440000705459026410002d80902d80c0864200c1c0310b59584444035648980062042c401d0b0109801c0010306c1003410700c14400809400c411601e1003500941c00b95100b255450061400d14081e070f420701c806514003c9040302010fa08100d074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 332352994 1250 332351744 332351749
    0x8070905070810060c0611040302040515101d0d02031f06090c080103030806100219061e0c02030409240e0403021203090d0315030b010617060f060304030c030e 70
    0x10440100404580490036060001000e000004060160801c0386003110b000e000d059008110000c0060b4003480002c0c0d030082c046c2070040f4600881d000254424204814400000ca4803600c655208800f103034002203c0882e03a10584030441c000c1508a91080c6070751a1004d1807505018170b0421a0016080e6000c030501c100012804003500f0401510090756001305008030f04251052440440040c10034030758550464602403c54070780105020302c20800d02407903045040c402d2126207202260502e4400d100c1007140f512001034041d140781c80b0301514200300c05c0250030540e800780400c0e0b04415006940382c00c0c01c24814402030032180f80700c031000c0b002d000f600c4041c10b1000c84031000144400000046039007050f140c001d05040080d001c1154404090040c4014101c000c5462103034810942070006488245040030010707004e045d070000d04020000c04c0001369640d0865500603082c0042c40b4040840c0d5109801c124240d2048800240c024005100040003c0d00440c15141e4150290401010f14201d2000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 332354244 1250 332352994 332353003
    0x4080705120c0c031b12012705010509150c181504051f0e060d0609090f1a04080a14090307081015080c040b0d0c08010912050a080703050601020708 65
    0x91140140750001c1d812281e20010b2102c0221850304070082c1401403002000500c0c40031070070b840e0174071807426188000e80c2c011095002c48400c100c041403004c56a28030040c00f512003000a038050b5000e50130540000c0c00c038000420300c284000d000048624840d118114040380c02d800240e076002000110b041d030a242941d9030751310040000c0701342c0d00a594403400c00050140c02c00c13101003044811203602d91068007190f00844001d00b41d0a054440a8031501920103d84c06403a0070341c0051211441c00522030305001c52040b020f19658042c003404030f2000060072040112040441e0081d182c04018042c0200c40c0d4420f40c0c0807440c0d03000c0100c08908003085040001e04000040d40420004d5000000c556158010350003520020302d004218490f0940c90f1041040e181e0301c0a2001c40e20466485505405c0d036510200301c82421504a002e490f4000c3d12200b019000b0b201441040d00d02c0311140c3c02c0c0d2003001d07108070221004c0d0003070390740c0c9e80519841c0c0741000d90141034003030011070650280d0000415406410007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 332355494 1250 332354244 332354263
    0x19080c010e060130081c090c0302090f07021b01090b130e0106050c07090c020a080c210f0702220207050328050a0e1c050604030e0402090a030b04080705 67
    0x1c068000b6514140600c0d20003904070884803800503440c2c4400e0310b1140d410b40e0b124101900032860a6440c0403803448131055000c0c502580c02003e242400d50018444008412402d4034401e541980d5543c503207003010b0840300b50460700500164071060041c4203000c0300100c4500a054181009102c42c0d0302c42c000190260441d500042006080200400130100320451050042c0f8803400e11030700d0018640f05181c0c4851490013484032080e1903401d17000410784204169401c240d00300711050789868091440310b0300d41c9884a08290680389000080041030b9006040300c0c0d00b1100706100314a0881d0b1542070003038940301c2c42c102002c1c1e00044542d280c8105000d000400c1e00c2403080b009142d45041c05a480c400c8140e840c2402007030b460712642c4070340c1c0d003c0d084001c82c1c000356194101001844031035400640d59410308d29410f44008041180802002400038586003d94402d0700e94800122003181481f00300e0056038241030b07208648260420110721111034460f00140030360b03d0700d03240804a845041ca8455442c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 332356744 1250 332355494 332355521
    0x2703010b0612070906030c0c030503180105070c050f06010b0304240c0e1801051012060b070809100c1205180306090a0b01060c0305120717070201020a0e1219080c01 72
    0x8020060f07100c0e0300c140200054201414100401c00c4c0f07045004018090701c03000181400b0002021403071400c50624952140c032003020090200e458103d00042a0b207040e40c1c0226003c1c4954070203c50546000300384941070300e90450b1031905594503912030300c80c0505034402059840080c41d00c582c13a1562640a203540701745568454100c03800b000030030701000110101450400b0180d041c0103002c1980c60ba5140300d61951149004015958811990001804998801c01502000103444405c0002d00c1e4054014410203c42c00c01500300c0300c08041e200241e11110061400614843c1a11510b00400240c031b014101d071030401128120500100345401d400346c441c154203030b0203040e5160130000300001d40d5001d01440d1505040e444119038020b4401e0096035080e204a42441000818543c0701d000752a15065000035100c0c001d00f403030780020b4000c0d8007070826000014002c642d800102e0600b850b0f00c0c5014001c1400070010720000418140b0780c0c2c0d601e9602203c500104200190008a0900407940a0700f81d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 332357994 1250 332356744 332356777
    0xd051006080c1503040303050711030a26040f030f020c13090506012403180803100503120406051204080702030f010501060206060a03050d0c0c090606030203060f062703010b06 77
    0x400030040d20305405994503d10405041c40810000f6400c4425243c00c943d041c100850541c840302410354000e080358902d43c14510001c1407808880b580100400d4036002585003c0201c0904801103000d51813048901404069a20b542e940000b44140860440b034142e910640311421128400204d0300c250801d40b800302030361141c010009114040c080c130b03801884425410f11010388920740d190030700c030f120915030f5041c559511007200240c00189103540000341d10a4001c0d6403441d01191105440005001d624003900c07602d24104541303c0c100c0102d9003512110b4582c3c9061089400301204101c500500403103415009104140050703c04005e074006481007100003042e41e40c1042c000078a414001002c2501c9110b4a14007003000c2080440c1590004250745086038146555003040926800c07294030403051186445800501681d059000e54040d28007101c41c0b002924043d000c002890040c001142601c040440320404410b94240440d0405040500041481d130803810004405400210b42e0702c980c00b00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 332359244 1250 332357994 332357999
    0x1005040207052503260f0307050a02061005131d0a0c15090f03060b2818020304050606090703230406180c0510030905070303050c0f0c130b0d051006 65
    0x351200c0c3c41034034035070003000d0204540ca562221043c40c002108440d03020403107010100721165030582110201c0c801d8142c0d0a030380c1c2c1046000100b003503010481c0c1d41e0040c05400042071001c01d4030043e9008070745006003240a900c00d40c6c0c013000014403640c01d00000c0c0c8103c0022090f0b043c07206010300c4102d50f005840307501030549000e0f43d42c1c01c50814007410908120f080b00342406143d0031041c94205503604504005a0b01400e5404510400043d0403200600300030451500003501c0c40c05005003d80c0d01103e20040a01c1548400c03800360300041d40c0040981d00107100248050074200c1c1120342c0004140703004a84000e18104422107840c0b2403c0c10000c04a00d00d080009105041c0a240b00107885408140b8081c003d58640d13a800e82100d0042e80d12521b0a083c1042d2024800d810012013280c0280075540e0141d0f40b4640500301d507200314011001c0e070042e0140302807520004a54404030b82c00180001c400d030b070110840302000345100740241c2c0d44102c0280c90300c004540c04100200c18a203940d80002500c50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 332360494 1250 332359244 332359273
    0x607030516050c0a02151207031e1806050f060406090b090610170106020102040e090f070303140c01060e0402040b090108120708041d0603100603051e0a02060a050310050a1d100504020705 82
    0x1040140140245420b14910000072b014800700700800b14140b550004458210200c00e40c034112035804040c042c00d01b0242807008035507540390700a000d081c04850401036241c0c0c606030f02041d640d5503c005580540d0340700005004e82880654a9403e003030500d00f07021000d1481006054181c0c00380c1084005070350214013800200c40500307042c0d42025080c0018034000400a52917a561185800001d0030000c00036a9030000d002e90400361103044180d507000340410fa07100c54118904200032642a40701e50300307100c1000041d0170140c02290580728208090541007650040022803640320345012101d4070380c1000006179904020091004102c14140d031035820382014004c01d880c0480003015110814900501040003600003c0d4000034508044400c0f800c800303000382c8860400781c031040301035005600000e8590200741e002004500c200142030b10788107000d4a0300248110301c4040d000f00040542c200b540c010301c21007d9201c19501a05400000c00754503280c50204c4e080e81c12082c011215644860018000300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 332361744 1250 332360494 332360527
    0x403080d0e061b07030f0207080714030c040209030d0c1a0f0609010e1512030d050903030a0e03130b071506080c0411130302010f0507051504050607030516050c0a0215 73
    0x4180701c4114000f1002d8804900728038032074414003d0074000407100201c035080c001d1041400030241c100c141c0c1c1140396a000420007920140c0049032003070040d0950055945014420394001090141c02084030030000001540e480b40c0b0448203175404411240c0c0d0000440249018a00c03900310710720543e80c913090030000c0c400d012006030000c1001d1000d130001c110041c5080e82d007540040704111400800c0b010005819411449000d010b01201d5041904201c018207000000b18011072500034104031024006543d95201d01a5a401c801c20400b0190200807010b0791102400d8428082e001d0540c000d0510f8181004480040d44030f00c0181e0407500307440d551441c05100e203040c1750700d101d0a1140340c80a00004201e60b40c7c0c850000a040c08804240e22683c20b12139020f41c6c0003141c0c0181100c61007000004441180802110708442e14402c490010382800e12900074940242c107812115400c080c66402c0540e020f82007031825504901c1002d18070805695080482c480c80403600306419640c0b5101840d94011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 332362994 1250 332361744 332361751
    0x706021b0606132c0d0f0e0603010e0403121b0f0c0b0c0a05040b13090f0b01080402060c101d06060a030f03080c0f030a0b030d03060b040b0c030403080d0e06 69
    0x994020804001e07641d141c0d150b1900c070441c1d0403080002d51081841c0d0000038040201c92103c4403a000e280200514000080c410341d01268a0f150240d06c05000c5108079034001c6022100c070342100050004011038005c0c040d81c56003103403090030008681000707411200c04403007034041c403203003c16484c650b10075056401c941c069000500c6403a0801c180301d126120080714070f00160000311082c60015012040030310480c00d440150100380103950340c5080d01d00107000848054004c000c121403a111246840078980e104544040806846024a641e0340740c0070800290800300203001c0c02e0003103c08514180b601d51251000108903440c603021016841d20b1a81d00d0544010802400b84940403028000728a486d40704440b03041d4945807911640d520403081c43c0c840e020347d000b0452004030100522401d050250010303024210107400729021081d02100c21000d0381c00c94422500150001c220901007040700600034148100008110392409542ea51801107030b82c0000c40b04503621b555600f11548407441807188640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 332364244 1250 332362994 332363047
    0x40b04020408122a010504020906060c1f020417060a0b032a01050403120c020315150607061418070905190b0307050910061101060b070209040c0b070602 67
    0x9203030800000c0b0340e640d154002580840d40011886000c81810712402c00c05500420408680250400b0b2400b0b01030501070760102c0c0f0680103000001c1035414001d003074442c60b07010b0b000140810107051008100400e1582a1184003640802006c01c1d5180009401c4036070f054200010403e40c03514600c81c03000c48002c0d00c1001d21940100805070000c5214218010300300c00303054055030507030b9140001603919210f55031004289070301200340c00001c0f5030450b5081110500035402d844191500202006503040300f03d98002d0800c01390309132100d880c1001e0015003d018420715000600b611050030102c041001214010065030800e42d0001e40c3d441c0502000000340310147d41032040b81450003600e0400d040075a0464040c079940c10f915800e541e07042002034002c2c000940b41c800f09082c03030807005545240c2070080c1c01c0070404d04101c140410a05225240803580c080c5409402d0448a03070070841c0091028000b92072210000340b0114501240800428100f40300c1e640040c5e8a0408038420a10f00212848a80317 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 332365494 1250 332364244 332364247
    0x9070e060f03070303080c04050405010303050703110f1e070305150403110a0503090f1c06020a09050109030215030403090803030a0b1005090a0b2b0204050f03072313021602040b0402 80
    0x1d60030b4500140b91800e903a4141041d0341c5c2c65a44e1a980c103854040c03a406503912604000c000414160031100502001d40641d841c58007001084142e90750744c954005e0002e0346540171a459581c100c246000d58140707041b40005071941147d40f5101c0c039260019100801e40031988000500081582010039082600ca40c0c0c00540740c1a000c070b8507050723200d0003030b60940381c05016002284421642c410070b500c21344480d001d4000d00e5208030740c20841e0081d00b05844c0d0030302041c90300802003501d6000c7c0d0746410441c3c3d4020f16400700380c1d10031815014190000342040f0140004541d002c00c450308180095403181d2400400080c04110300000c04c40c0500c08183c000c4e06110b4100007801c2c4d152612014081901c810302003850740c90008804420814003070510b00b81030740b0039500c00e85010f550b0a400420450340300301d400703100b40910b03502090303260b85e11441800002a58180c14a207001d003400040e20403010028400c40c807903200c000d1032005a90040c1040400010805c070f1350750851030144074800e9003c0301a45c085 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 332366744 1250 332365494 332365519
    0x50709151706060d020103140a0b0906060702060d020f13030b07030c05030919030210230702010c1b020406030c1d0702030301060210020f040317070b011d0103140f0609070e06 77
    0xda00c580d0b0180c000c501036030b20b000e1840196406900010114640021810507626140d03200200502100c0c0a080c07141c1c081d200031070000d1074140305a0304125001803803207142c9220707174111034006d520284002090f01070900003601c544000c003a80c400114054a9194111300d00404020304680f0550b1805051100c02d00a02044000000d244904d049548207940240e204905069291004c60f01c441c4264a040c9504151a0000244462503030400c00030140150744806034280c0c203954500740e01000144c04603845418060421462602d564006000000c0320380d242e880b4510f10f05050381042d07075111215440f0003031407113100f1440c2d81c0c490352500c00307141154100320000f0340740c402070001c4044403500441c050013007444407802ca900031980044a40401800381c0000002038002c0a400c1c1d40c0f0a00720800000c021b046d68484000050003000e003e825682190345160481d068410716003c0b500c07803488000d400300300030012280207812840040821278a0702e110311000364801840f031409030010f038180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 332367994 1250 332366744 332366789
    0xf1706040f0305030402030f01021801030f09050d0513090c0507110a0b040b07080909011d010602071202040c110d031d1906051b04180c050304050c01120905070915 72
    0x7007105041d4586861941c0e615140002450202140308004240d4800940c040c42881083d42048030040b00380c83c1400b170a26100c0940085030100080504260013aa61110b44c43d13208000501102c131602c0c230f92460751612841d1a07000c9542241c40f46010802c002401024807800300200d0308401400c48002e42c2d11341c01c2c16048065401980700d080300d1001c02203900c83c2081803a5068401440380582000869a0349041407504030b00c079042c09443d80f81c1808000b248891010a2000a07101303ca44c01503100000d590901c401410070840700c038104a003800148000f208288003082890b1200e03034002c81e0401d0458041030f91251180c46a0041d079008090011941003018074280310250058000079190303a451020419400c01005600b111040004000c250401041b030b071102d64000c0513404007c08202c600f0107035283d08c826a0091305d50b0f40700038138100c50fa61248142c500000c1e403296003c500e8403056030342c00f480c0001d280c002040a50f12200007a540340c240c480340000a14482c8160203c40754810321 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 332369244 1250 332367994 332368013
    0x308090606031b010c0203010911011412070c0c0e070e030f01020a0804082a0607021005071b02060d1806050a090f03080702031309050708010b041508041103070f170604 74
    0x60718140b2404100d641e24241c1c0617500150700e046e00503000388400e10451800109480707415040902149840c07106000643c60201590390300349400034100c4860315a080c00380c402001c4600101e41c0016a0040428440b20f4032030740034000c0125490b6119600780c25420581010304400e0b04100c16841440203190b5140d105010a0f000758104203010303a1499011070140d01961b1000508284280306040c131171605000044039403250200c1c2d82569800c5d00c005054a0507640f058030507200248030b0322042150005440313400c6844178230041c40c40740350500010340081a03880c402c0d0304881501c0c0c1e0208450501c0280d0080c41c1e40b000f00284204050801a5207002120340031581c040d0070009247c1c00683c0540c02041201c0701e85034550040d0f11110342c0c1d600600c0181104980201c0000c0074a00002190a0380310151f60980e40c40041c2c0010340001c000084500300b800a10980b020341682c402400345031000d000600c05401c00c4681460450b00f000d40c489200f490002924540358011401c01003c40c1041c0c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 332370494 1250 332369244 332369263
    0x1e0c0f100c020703110409120f11010605180702100c030e0c090601171803070f020315010608070302220605030615030c03060f03030c0f0c0f1207090207030909050f04030809060603 79
    0xd405c4918207078100228000749401d2000400801d40d92190086554200c1c020001e00000c5a5450315035a000405003800e0f114140700740c1d5003160311040812403110925a065501841d1131048032040b002540c14a4240c0d180c0c0c080c10404296604180d0036181c20502100c4488034064640340c031907041ca02d0008003004111182510440c03801c1d00070600400006003000004041c0c041201e48500944c10184200e80701400100d1191250b42c5103002c0c403030040540c0c1da048699507101c0c40050740c1d40410031384c041d41c420450707800000700c104404e07203140d0030025008000e40b64950358140c492074004c0030701941e21150a8041d590301404e1003007125600349001280da11031802d44072056a0140700740440d24600501114a40d03c0c02035076110b000e068070018858000c298110b50702d1030160b00f180300740144101c0954210483e90400203091192a00ca40c0040044500c44e1826030f01c1240e03244850412100c058680e00b240c00210310a20080c5580458640d81102e10000900068145a800070f41e85c0c10310b11 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 332371744 1250 332370494 332370503
    0x5090307210611120403080f01091407080702070803161716030509131b020c0f030c0f061309020a2a03030f0213032f030a081e0c0f100c020703 63
    0x401031004424941e03010303501804082c1c844c0480c0390900e80b81c042d00303000084909405072840c43e8000181d0214034011170010380c8007400200c5007520350301012150980010403d174198480c03620005510b0310204001d020244a00300000c00340d98185c84e003003210340302c00c20921030010780500200b00c2078041c405460940c654542030043ea15120310011450b9801c0c658425295680f0f8010120316070110360410036150070842d400d403001151003200700902e0820b0b041300d040e095800443c020205040c03500a100c082c50000340010b0070403881402d401030058880d000b082001d070300420304000c0c03a42c1080c9c1d00810030762424100d0513904004003800024119052014080545890303a08084207081e6048440c4007a40c807005610042e2203007804965210000307040120350741450307044a68008101a80a01108000c1c043c0c81c003400f40e511244110f4001c00214292040d00070b540c54421502000100802101c4501030503601c00d00d100317800d080c030b01c2045200e0401410030011105017a0f020516000741c9900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 332372994 1250 332371744 332371751
    0x3120c300d090c090c11070608070e0906040e030a05071703040f031b060c050405013e2802010e01020d0e04020706020403020d0b34080405010b090106050903072106 72
    0x28200b058002d0500e5200700c6104d454280c0003a1481c0d444081c002c0b420140c002140c003401c1d507d540858080508484940c0090900c09051300d561402159260308144024070101e8018030f030010050540d8800040b070000f08200190f100c00300f01c1d1203465000c818210155190961070251503462002584900050412100f1817082038150700818400c103500b07030030150401040604080151041e401401581d000c505255210303400c203580c194030403002880d40030b8000c0d400000a1074241034240b0070510490540500302003180080c4080b03030840381c206990100b17501d0000382800050f1089003007006241c115004540300030300041d00030341d59141a690a40740107a81d5001400d00304000d004980000358050201e018560502c843c030764000e400340038140140700d50307120703102e480035140400c5842c1660741500100c0d0341c0d9030450007403100f558000d00030400400c0000302e50b0000750403d4001d8011001290020409035198101003040c01d01a00c0004040160140003404420032610f03001e80007000c0503203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 332374100 1106 332372994 332373011
    0x7050405010f030303020304020d0b04080a09080c01080f060f060c06070206060d03140f09100809010e0a02010e10030603080f1903060b0706090203120c300d 69
    0x360041080b14042c5595401d501940006000366071020704c104540e000301d600b03a4006480380b40f280c42001c0c0c0d1400c0c40e200192088081707400c101241d910840701900280d800100c0d0303036040084002520740d01d950390000a04d54407107490446420001c00b04002c80b1181001881500404040d000c0c0e4806035248000c1c0880100d00d52800b80000c2d82441345855440b075480001c0c0f081c0c000341556585070401aa0124000d6008100903c0004000408000c44128284507080f81341017240d001d844001c0341c5800090840c803c8082d214400c16101076189002c5010b03500034402541d004100a41350381c2d00100d05d022507008075821011040b040c90490a444c3e100b8441d000554002d60405401c221550311600003c0c85d84090407a014440c0741140070a5503400f002900003416180b0017484900403000d11941e4825140c950440c00d80700038454000300303094030300a0342c00b88602e00200044e01030 = true := by decide +kernel

theorem cover : BRFrame.Cov 332194244 332374100 := by
  have h0 := BRFrame.cov_init 332194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 332194244 ≤ n) (h2 : n < 332374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
