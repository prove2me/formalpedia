-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4108
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:35:48.488758+00:00
-- url     : https://prove2.me/submissions/20e71b9e-8f20-4350-99f1-c6f46ebde613

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 738669064 ≤ n < 738848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 738670314 1250 738669064 738669067
    0x7060507050709050a0902060a0c030f03090203030702041112090a11010f080615130f03060608010b0a180603020406080c040f061815050415150c03050708071a0702100f060308 77
    0xa101c1e60703c0c05820041e00f11080980c2d2081c0c40c2d40181c0d0b4040080130511441e49465420f000c00d800c0c0641483c40340c90190b01890308003c51140143e401004840d404d0381e04403000519000e05040359a414000c42a0a8400448150501c4480c2000186603c0c2c00d43c4079040903c0300308401801102c125607000c0c00d03100400e00401c042046880d0441c1d60b071503d101c20070070703ca0408461b111003150780700386944200f03103401c072580c010300038051140070700c90123000d036074009001850050021414140680c880d91a4440d40c80d01c03801103146582c7c000c0d0000715001403040c402c1545030345002e506c0391580c0c00d0091185140405002e101102c5008010480321000c0c2c404200f0300f88413129001130600f640404802054081c0003003620780e00d030f02c500402000e08076030140100d070074207410b4517064144c4907040c0c0c28881c0410403800080c1d840000c41d080b060b408805103450340058942900f02c066045031450341864903500b0450300c50380c0010b005025038494002404500c0c03240c0da010041307405030702018084150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 738671564 1250 738670314 738670319
    0x18060803120f09150c1e12040201050d14100501031d0615040609020a031509020408030406030b130e0303060f0d0804121b15080c27120a14070605070507 67
    0x80e4060352200c0c0300f00503189070904401007118099004c84454120315008221400c40d608110700c2a19204403031107106207004030a6550010b40c42c0000c00081c100000013070b42002c0322176140c116002000151000f0041ca080c000007840c0400003d01429000070300e03050511601e820408034024800a00d00060582501d40c5958018900e40c0f420080d45c1203a294040016070607541d200400304101c8035a40003881c0c402c09030500410680560112410900511040c0803020000c4212411030303c140c100001d90103004404601001545951204642d203071000500381064044021445158100e80749065015050f080011108030300704007030318120b020300040c40401d510b4030384078092a0041080f020f181c0215142c1044c10310300f035000030181122024070150320580100d961600000004005800c00000d59001841e40b82a50340c4064141c900640200042d1900342d0015429018202a500010440d040883c00000340d40c2150826215888000401c00d10a409982e034842e8000701411072a40f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 738672814 1250 738671564 738671581
    0x5040b0f09030f0409060f05060a120b040e0316030e030115050609011106040503070c090e1009080c1203011502120f0c0106050d0302010f0b0307181503020603011806080312 76
    0x41000704a086540300030060030041d8070089000d48020584039030046042400c040780b28a08600700d921540c000e420502c0303843e0042d40c001e41002c410030f0049a000807000d0404001070003030000c0041a26042c080012090a64100707002c40c46c00300340c029203607003400d00d898009040c200c40342580c03084030070700f418481807100e403030580028002000c0501d84100c00c24a540c45150805a051302c0c111096400004d4010070017101150802c000c0111160402203100b01da0000c036201c9490180075448560740f2209401008444c0c0700b41c503840413000048070702c04c114007210001e480d8000c4c0030300c400c0c1214100301060360b1440080c0340c00e6008401c0c43d903203050400c1402164910b40000d0841d0500d9521a9000710f207075100c03408001940d07406503002144407405d00100000f00e40640503007a002c1e41243c2c106100200c6201d401c103d0b0b6001420000030300c00492544800383c46126000254410400800010b4015a095550040840c1c0745e00421095684450260307880c0704443d0034140c401d07078a00c002442c50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 738674064 1250 738672814 738672841
    0x110d0e06090619260c13080303130c0e010503210408030d090308060108041707080f07060c1107060e120c03150a0b0303041a0f0d0e010b010f0305040b 66
    0x450103014503040c103400c00000354058010186101e8020380d60032a081010f9030207490030a9140280056020542200303070142150600200f95103540040000c9040481030403040c2d0500812124090301e45074100110019804c4180440503105d0340b0540c40c01007031044e22001e405040b10001070081864030303400441d18100002c1c1d080c00b103450f92005c1c000082d100c2d000784000d108003110078200080f020001d1901030801200502624104003000d0200000920080c94248001038040345003a140c0c0c6680c60007211a00c030740340030307415004000b041c0101045400d410106040841d512a041651b0f000b41619030307034020f10301c140800910703000301d02c24503810010741101002012100b540c50b958078800c003180c42e041c0c01d0100301d540c80c103c010030040415201e115018112804401961030103103000a030005810703540e000704001000024803d002003a4020466031410340a5106015030312040740c0003402807800440d0580494100341c1201130003442481400e2043d540a410b102c501e444107850440c2e007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 738675314 1250 738674064 738674087
    0xb0310050f13150e06180a030f030216050712050706051e0f0403020d1a0601090e060618150c10050c160c1a0c07061103030f0c040302060a1d01110d 65
    0x1903008158021451640b074050080890755400041c00d5030b05003001b0010310440b4420050001d030b04407200d0403000a0384090b946002d01481c0c507001d61945d09440c0400461a03540f5002856441780e9500014020148104048101d00500650300c0759592500240ca2a20621140c425080c4000c1001c3c66410710340d602502200d50300c9000307030382019100d40c00308060410b4860f00762072a03400c1951680c07181c0e440703d0350140d004800313103020b10040c0e1605102d1080c00f2005054684150300100301c55512001a50300c0143c1c4803801046c081004020380c124000580c080c2401c030180f8001d104e40d2401c203a495004650040d00034000b0107181100f03e0440b800d0320b04800000700e4414640480010f00075250301b094009415003228010303038610350002c0305441c040c8558840001d00105509040200201109482c1d00c601203240311196651581c03050701991041e604000d5000e200130072452842984884d2403224000d40690003002d10b14070f0001550040c10300120900c1c0381e4001b2044a0703103a44a4201c4202 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 738676564 1250 738675314 738675323
    0x100e0c040314030714010621060f11180103060e010306051f060504061205010501050702130e160509250516020402071101021006050303031501020c090a0b0310050f13 73
    0x2859101c0e50742c040824802c0d901803189900c0814030034240518202c14480701244003008200683c0352445051710020742640324a0704050b913918410500c078207130f0018014150b841000300428107040e541c0c03d00c26041400d400070114020f4000d0074055010703118003015509503410083c0307039a1850f0784030806808000d064030b40c1c2d07044100d2005209125807078500082c142c0d81d100c2d69252401d1400080911000c0003030702d10702c80c0c100801007100366006000c48880503015030b207400c00300381c60320081405824400741c008442d218402e05017840356070304e645010642c0e030102e64040c040d4542c034180072421016102000c80c0c090700803003043c10b6035000d98018030024501c0721114440c006540c0000e000c98105150030b41d42c031101d01103a190107681c180f00c6403603948801a801c2040710300f80b01c0802d5a901000703200d6103003a844280b400c0007aa0007000f0750b04402000401c0c4054518015945030090326004d03c0c2d10b8028403404a00d007101c04150b020300c5108110303040c41032140383c0e1400085000340341078410030744 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 738677814 1250 738676564 738676567
    0x10020a0c0c0b1e1201090903021c090315051510170c0a080106080c0a080a060504090609020405060d26210601020c060f0a03052806080c0306100e0c 65
    0x152211264400420b14075000c95281c544000c06071001418480800c00804030801a19210203104001c4034103407180b1180008083c02c03a03103816071500041a440d0040c007211545c0c89140301e40d01200103c2079903c00c030490348901c01c958030781c1c10503201e094604c1d071445000b014041c1040c0c1130059500901c10894a82001c804000800042c20a90107031001060000001091841c103908011003074010480c81c5800111840c0001401d9103070300408211404000485011580440f031036005a006050300034030070060807800e4501400100062181207014901f0702000034080e00d17090103201d10305a0041c10070a00102c1c1c950b44d0300030340c1d902c9101c050101641406101d000e4040d500a9910800c5604d020901c04e080c080c0c0003903c2d15100c80003051040c0c00400486040d45203020075035924083c207050100d03031904c03421580c10307140041c01d0500084c0807492191a0041c1035a4110720100e841c0c0380141c1e0180d1002c1401e00d600c0b000c08035000d11058007580c004000d510804070300964061602c01455 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 738679064 1250 738677814 738677837
    0x3030c0307090b0313030c170a1707081e1005040e0c0102012009060d0f05040302030c010b0a05012a020301150f1a030c0f090405071709060f072105070216080102090310020a 76
    0x701c030750f0059541a400141031030b200000d00f1406003a5650400c06070304203880a89804141904a20307040d03515045203155940c048ee02c0d90204035041006030030000c1050028500e03400010343c2e80c401821101d401582000d032415008074054001016070885040e4807458032010000740140d035442546000c045550b18045504405820b200700fa00452203903020b11b90764400c0102032070035034415400161041c0700c600410881d5a0b04080390581d03c80b910182214025425000e207080e04000001c041d40650800c1c100c1025070f24070f48140820760755940c40142940e03448000071207a1060501d00340c80000c83c2000030600f00b001d000b01800f0035210802003640303055940004a001e460055413000082500c4882c040c03090306070301404561248400e00105240e19100700480841480904110300388400304490200081c0070681804000002100a110a08007010025035442414040d2803a002c4c0200c00803170030390010300846180690050080c080c02160f1403084000b58841c1000109021300087c96 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 738680314 1250 738679064 738679103
    0x1505090a0207140d0908150f0f180a150f0504020d140a0f0b1006020328022b0f0c080a052107020c1f020a0f06020c03030c0307090b0313030c 62
    0x2801c4c401c0c603540c0c0c40991080c075100d040d510f440550410121510122010400f0b440c54501c0d90030f034800e200c040041300c80d45841001c80b41d0312010741803084450049007020300a00c894100a45819001c0440c100000000c48443c1c0044130b07003c0c1e80096010000303612210100300072a030b100220700d040c8015a001c03060750355542c05150000501c1110b81c1407030401003000d540c00f08c1040100a00c4070740007440c40d001c417100103220081084003030911400506000496018800c00420440c0d400602e070b124140d500e801c80c0550043e00401501c0b0010b1030103d43c8110311031203800d41e20191903000078802d00304681c40e841640c540e00114040300004100d8400202d1000204d03d4060003041150003030300e013459040c03090040301c0351001580c3d014110b1450000000700d42c00522129803903002510009015460718140d000b9210b20b1420580342e100100500031900340b00f03001940580000e031210722807155100000e6195000403a141d0210130b007020149d1010a000303412154a192080300c240b0303c4466010301 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 738681564 1250 738680314 738680323
    0x1122a050306090c01091d062b0c0302031e120306010309020607060e010b0402130302010503090c0415140306040c0504020307140d06090e0712140c030a080d1505090a020714 76
    0x441a6184c0c0c081901e084070355801946070009014450f120f10741ca0101010048200340016041c207009284041c550302022801103c5904500ca401d1120b41100b0a44e003000c5c800c00f0850b0006921034011803c1500f0002140030706507620303041600c00b83c170030580d81485a080c03980004004605064440000303c0042c0c3d1000010f200d80c603c0340b200041d1500d000003440d421a003041e0b41c003034061441001034030b82c0024286800b00c1160350901e000c6607250f46400032a428803604c0c0e01020740090501d45400c050645412441003560a040c2803182c0701d00c0d45108260303890600746c1e03015005400c0d641d4140aa401c05400544d80404942010812041220f4120f9070300c2c0d2101e0f0303030010415600d02c000e201c0c4107042d005403600303001d003000100801c6041c08210b40b0303983c40240c0d0045c1010911608118071400900440b00c0c6039000500745c4010a9042c20071400340d600421301035810300d01c3c04801d503040000848040e41500c41c05404034076281d95021204009512440003512944019140030090f27440402 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 738682814 1250 738681564 738681571
    0x2010c0c0306020a05070c09052205250e070f02031903090b010e090f0d090e060d0b07030518030702060f16050a030f0e04090b04030f050c101b0c080706090c03080c01090b01122a050306 81
    0x1421821031a1801840c0d13745000c0c040d01803c01c200c400d0035091800d0740c0c00819036401258480391610104683e60040d4000d200000009240c0e8403080d00000c0c035654505811031003401068160307440812070401e01e81c0c550840b0240e0360f01242d0007002c01d00c03d00603144020b84e40190040e103007601c0d1f102282c40c0c2c41284503080340c644000a4654007002001e490200e40340d480039403410011410000d46a0010b44c00b40161106a00c4600c030203d401602ca40c243e40340c000e40340340c102c1c059481013a80ba045c000d10031018080350801180c181075448280d803c1900c1542c001c0d540014881d0311a483c2c6036002c44030b080301c400841741040340a20260000c2ca509002c0d60600302616030000070200220105078012000e21280030b01444216003242c0c012a4001040f0385070160b00c103000003a080c2040ca004030581d40300381c00c041c140140c08a0070034142801507011744c00d140d00440500c03c480e83d0366401c2d01652041c4000061003007803c5221840d014052207410b07940c0d0b1031003018141c40280c0b00d001081c906034044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 738684064 1250 738682814 738682873
    0xc0503070b0709050307030f060e12040e010812030915040212191203060e01120804090501092013030212190f0c060311040302010c0c0306020a05070c09052205 70
    0x900690b01d8024800320010705098015014061a5450300024031309482c0c006010035499001d10210345005000000408030f510300c3c080e071960384460703540c048507100b4015400701d0310820181130520b00d400e0003070328420114000117051020000c4510440e41e000903004030b8004d103000c001d881c0c0d05c400a11801d645204403451000e100041401c00c111000640900c00f070a06250200078480052040d5040d419200c1030384c08c0051480503031030030859500c035642c0704034056880e000009c5209052030300602c0c3c2d040003034032a05010112a41c06c000c8030348a2a444000c0200306040c04100504082c8600390031120040161558080e0032410701065200140f002c0307880b4a2000c03001e00c1004036406c036110180200e4035040080041060003400284141d0201038188105995100100011502c0400107581d002c8000d40d15541203280c060480c0d00114400c42d803151000b078003c1102801d41c45001d00c2170940300c42d50303080c0d620108940c2450b0401000261018014041071200c43d02c086a08030b000c18184 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 738685314 1250 738684064 738684083
    0x9190e09010f050a09030215130203060f01090e01060510030b04020705060a0615030213030f050a0c0602210313170f030115090608190507030617010906060b120c09010c050307 77
    0x440140908441d401841c03450805e1801000401283e070002c5da603010030080e11810302c1503484018846505082d01c6a00035814403425007000014481c82200c24100c4041d01001c1c01140e003404001c5083c1c0d0340a008294011500390b9242c210307a846030300140385034200a400149880030340c0d10354904080044444110039915028100184d040c4201e59102c4c084852130110300386036510700c000468041d80d00c80907042031030582c000c8042c85401d2120902d429030210b03070030906079560074001e510740d04100c0000400c000e142070817000c04131304c503411a84610741c6110064010070b41a65408664010344400003100b40080c816000450103140c0214040c0144c0c00c81043e1081d04000010421241c64002004001000090044080c202c180080356058510404030b16665820012001011150702403007034900030140040c07001406500200c64140605010f105c100c0c0c0303594511045100c3c1c03205900c294411200003414212450015000b845014074000b91300741c02c203844443c40d50304201005d5400009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 738686564 1250 738685314 738685331
    0x20f070507080f12040e0c0a050f211605041e03050d0c0b010b09010c1104020c01061806060509060f183006090d03020c0a0203070b1309090809190e0901 67
    0x70420500c0092124000c04c5460141804152000c0c000040d046118205010401c1404c86000c1c0003501c504020506819841d108881c0400880e508600d4002550a5050700443c08048031540325000007402900e44514003071820030400d40d02144000d4013800040485404800a441440300c2c050080d33007503440303040303025541c1000541c1d20f106900072441504200502c04490740c22a10034204950401c013200183c00091001c24003a124842203407040e94a0110080b6111441c0d000d840d00300c1000d8101041880d4031400e00303544074440c490400b030740810144050300303003007010400828a0b1000c1c9900300440100a001240c91849100d100205440101e21005501c06241c0305280c1042c0d5848000c00d541d0a00605ca95260004003002e141050f40001e016022001d080092400d610350207003c4403029691102c6161003038001140040d03031006d0300c102c0049c00311400d00907211b92035041580035140424000400520022010903a201d03a10741d0b20001914040306501d07144541e02103400810500c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 738687814 1250 738686564 738686593
    0x40522150302090a0218040f2301060801120f081305010e0307030c0b09121518010903210b0a0807061103070c09020a0c150902010f110d03020f07050708 67
    0x503080c0c20403885580c000042000503940d42d003403041e00540050401070b6203001034640d00d503d8821080002da006810160743d0b800c0808140d22100d500d00042252040c40e0840c41001e142c100c1081c880d01c1c0000745008014000000ba207003000b102c4600c100355400b400361459580414a400501000e204210201002c0165581145880b00084021070103043c0035411981d504801000c81e0207880c00013035004c01c83d60a01e0b1a90144004090b40750310459a03650312007503103414660400c42e04401c042020380d2088110f41c6050107007000c880e5060316403110b07540481c3c4540c1e07002d039121000e10a20383d03158044a203a17a201c042404001e0318440c00a0a862803c0000213408050740700340030b201c594010844032000c6040d26a0700e9042d00c0501c0c1000d83e40707001c0303071070111200510700c01c02130070040810b100c804071b0302100c0d84000200c41c400c3e26503042180514005031542c1646986080e11074200c03c442442c81c0307109500400081841c0441c0509100060722404d00c0d0882c103030401d150680c00158000c03c2d90307 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 738689064 1250 738687814 738687821
    0x50a0b13121d090901050711030703091a2a060702030c1b0102030712030204050a0b030f0a091e051605060a02031c0623040605030313031106040522 65
    0x4030440040c140c000320540c1d0303000c040c00152640003080042000802c656112011509401030b800202103446604041102d180200000e44202d00802c0101c4d4900c0795121000c016502e4650301038561b003088503e000e28403c0f440032000900c641ca010100704c29001c1e412007100250015400300c2245111441c50100ca511300500500303079509546c010311550601c2e60002442c4c000800c0500a0103103d002c05400503403660084c3c070801003042d10b450907050300440d4181c4c00f8204441c1d04a40c1c0c0c1c03a21704da88070b030409084d200a5a500000f031110b50000b989810140d000125040d00c58500c0c00c50700d100c0c12282c0c3c0c422070644801141d4075040141e00da03031070f4654101140c1c0a084101c4040b4540126980060350740c0c0729864020030b080850042c03c80c0d603081c0c0796014000905034000f00c0c065103a1021002c5860969001903113115500e003081c04249818000191040f025501c04550702142c2591140900359001c483c0b1148d00038410030010595807116044220bd87c100361441180b000d5011440000381d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 738690314 1250 738689064 738689071
    0xa0507170907030311010f0c050706060603140609090f01021c270311070b0304030c1401090c1202042004032001051902100c050301050a05120a02060306060d0603050a0b 74
    0x340400c0c9014811081d101140103800c50b503142c103000707108044081c0200d0151514841c000301c01072501c61203014651f0000f005103110f5106000810200340c940000b5011203102c07050701c0e01c000891800085079070a003000c00c1600124504100e50300001c130210458207a90001c0443d6007810015691480d100c5c0d41c0b80120340030300c280c10b90061030142070800013898035484403802a04200b02443c100e1882241400690040c00f150411981d4034902400e019102a400d01000c9404002481c03810680751018850341002ca40c1c0700c0712500c40603280040c2c444000401802c1681d200ba943c90308844560400040d507000701d103400d41515122484d6080c4512842000b5542d004560f000c00c0c80310015a92040883d5025006c1804400310104120030807403410300d04406051000b490b114113402d0854006000e581220000c890310f5039050307214014098052212041010a90f0003400d1180052900c2d0020b56880301c0301070007003410140f15401c001d080d034905900980c0c0a420040c00759041c851060500c551 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 738691564 1250 738690314 738690347
    0xc030c11010e03070602071b0b04050a080d0914040f06030b04050f0a1a070c021206042319021c110102010506010c03120902030304170609011a0a0b09180a0507 70
    0x8100c2c100c5803180d00d038481c90600a001c144d000905504000b2038905881200e40b82c0743c1c91b90303106238407461196030503442806400d120b10a00d890008664100040c49142800c980d81c078176044c54039101c8818aa007a1034044264060780303c05440700c11008074400d00c402140104007080044c106410704604003003440c511003103290401d070b4192011030748122440035004c126038400582c65503017280886007101c1012009520414082c0359a803080300000703000e030095000b05003405442840c4017a85202400e150207050741c070340100941032024803000c4400000d150014010020481c4d40c0040140800201d41d02120540680c14000308196424455540d00001c01c1c00c101982c0181d41e00c0c060103c08008500c0c921864445800e041103440900640300101b07408102080701002001849464010071181d16a00351304e4040c0b0484c00b95000c101c08003500d0b00c081d125182c01070801685000301e07030041c2481c40d001803924240b003242c1c45e01b01202e01d1055106260001d1203041c000e2008000318201d030900c11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 738692814 1250 738691564 738691571
    0x30c15160801052b0212030304060e07050d140c060301080f010b01050a05190c022d0a0f0b0310030807030c0b31021c0302060105031507021009050a0203010c030c1101 73
    0x55140d44d0401c0e041c0103d2030128034000011038407040b40044c0b12142c001c0d000901e82176801d50582c0000090350159100300303c144003c0d0966032480d90303034010300d114156001c22504a0a404980295041c4034205a404c3c20f4500020581c03004c1501a402a0301c9200d841d80565642c00044a0030f10a03a66819000d1924525152403441c00a280b0b0040210709041c0bd01034601c60044140203a0380e6040d0700b680a810b110600700c000d00300c50100511141990542a102030341c0641d1403030415450000d542c2091600d07a50700b03041001281150b080180b068412010359400407000c2134811000c0c244041c46650b403c0741c040390a1070155203041e03002c1c28030100311440c041441080c40d108121030540c003014034044402407040c2e0000031a99540d00c100c880304040d02004800a0590118030075050352002d0302210303400440c5030800c6821150444941005802900c01401151026007040b40c000740520203e444840141d000603084405c1d80c0c0383d4034042075803280f00342003031a084562401e203100c4050081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 738694064 1250 738692814 738692819
    0xa0815030606040f23190e121312241a0103050603010f020c1006060212070209130b0a0b030111040303050913090f03030f15080c010f02030c15160801 66
    0x80e0340e0350002d0300080c0b140b07442e01c1340c0b462003070a0340c0d000304014800c0071444070715080402c0709040190f100b502c08440401045c1c201700130501050080c4c8016614410040143c40c40c400fa80c000783c2e411a020640001c6503081f00058008403041206012501804c0b0000e02103500d110034207031016690101c03664030380c00c1140040e00f8140806024180f58400e0a000c079803a43e80307500007401061801501c60b80b1030710200d90128002c81c00070703401403040c0302902c1c1001390720b4940b24140da880101007440302469104010181c014100002c0c0d03181c010320035100d100f180a0040d034038511419000c0f00c1a070003030b598960001c0b00a1409020714103039995441e000c1441c16007191030003001c92095141c0a4090308050f041007841101d503a0190700001e0b0070410802810006180042c0070301050304441446506000c50541c6000345070300030303c0c1140c050340010f0208401060066409220100e40501980400d111080c0f040c0c00034410b512501700c184212604c14901b0b114407030708090441c4d24150400c02e841006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 738695314 1250 738694064 738694069
    0x1f08030c0d022107140c190302030708011107060b011b030206070201140709030605060607020a081b15030610020c301513050a151a030a0c06050f09150a0815 69
    0x484c0c03500b9411000040b10901400703c0c1c2854039041c4d496843c0c006900c1125184e103070a1507289501501d108405803540c0300d0362640b00b5400e039034411005c24828482040b00b00c0000f510355010100140e810b040204000a40031214814468098410707070158000c2c4c800c0101030350742845020105645400307420181c5c03c200d40d00605102090000070f2840c5d40c0d03100484c809550ba00181c4005036401800c10540e1070710f0f4184030b03844502c0d4004844001d10b01c1c048a081615081d85a0300b00342e003c0d8500720342035540708410400100c0c07114000d1419030045032803140c4075460342d81c0103026000410707141800420394084404c8003401d62028480164015400d04644911849400d0340c221044d078075400c0420030310781800c50078404080c40c02444054980e200b8000ba01668200c80048440002100c250701140c005150301d8664503d0020034001c0c01c0d100901010380600c02422404078070115a500303140c60b44000c82c0d8050200040a10034901c0807410064040d0300032080c0d40d110350015030211045480401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 738696564 1250 738695314 738695317
    0x90303020c060c1219110613020f040b04111305060c0d110f03030106211a0913051204140102150705030402060c012c01060503061f08030c0d0221 64
    0x80e2900c28074001600a143c0f1004000300c0042c059075006041d5100c442142010549a0743d00800c00819000944016071000100d41c0ca84148031268000520381000c0d403c100d1712414000f11241e00c195244106841525a40b0a0001088610f403106a403004486c02041c0405580d0f40300c0e61180c1000c2002010600000c50100d00c03510039804d140c040c45070400000e0741041c4494028008602c000b10001a40c1980b0164480911502a01801d90300011642c090151411402e11745e03180321040c613400c409402e0114800b548042d4103400c0301d42c1e410320b60b5905408e04c02d040504201b00040031600307000180014202c240c0c056400d000800c3c5007000d404880d000c00030024032110901601200040954540303108076031460013030100070008404034a075100c4442804509203510102c90403100c1440360814402c0303c0a4541c014010000795941a401820404210002c1e100e90001082d00103038130901000507010f00004c00300904600c00520f0702c000d181c010756111021840c00008002e1310751074107031030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 738697814 1250 738696564 738696583
    0x2090f0402071a0403090906050a03050607080a1d01050f0601080402030d030f1803020a050706050a0e121203190f0209060f0a020c0907020d17090606060d18030507110109030302 78
    0x3540075071509981d0901500c501140c50f4012030540755030b0308000070140d108198406403a09207008002c1d550700d90b01885489052400001c14551002010940440c011446190b0016224002003420311794a01c80803203110488518210503034445040c0f050030300e00100440d505c0542860507180b01d00c1c054000a0380e90002880302c2c0207040e9600300c00c4000e1665500850040c42103d10110404e03041490700a550711141e04007030710540650000440c246200d541210b080f0911544d942c0c5e844a203803020048080c023a9520300200d80705428810407424030840145101c2c0a410320700c10020301c5502159416035001e1074840c200b05204014140b045d0303903001c0655800c482440034254945d076400307400340d24103500303184101d6020b1044010002c00c554001a090b11070003180d5070320b402d4004440f0512066200c2070b200a5134980100d0001540c600b040000b038280c615003000e0100d40700b00f1024103110741085c881401e5000850000b800824040d1070406c080101100b071801c81810707481d50318000d44524545 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 738699064 1250 738697814 738697819
    0xe0a0b1003020a030f140604050303010603151802030f070306050109150516060c020c010503010f0605160606090209120d08040b0606070507090c090806070e010c1a270102090f 77
    0x5001154112240c12900009507501401c1c00034003603142d00348914203800300301007140c0c130350660207030409404000700c0d90034000d40d4044011400c2d642880f0b0141c0144c800b00b10b400c41211520b110001e040214900300c04011420420010390768206070074042c0006100420351400d041c1880020015a42d02c248080d00703e034460706011107002c0038100c08444070301c00c00188000740f901c51000e5030140407240e0310110140f8410380840360b4000c00b4000540c1c550000744201500105440c008010881c0500000d0a056603c002c080800122715668501201c90b0f130340008141e10382c08204c010301e5042c46c8800117078131820791000388083c8040d490018200e40c00144000c0050038000042420341d200c22041e111110740c044155203c1984440004c1d00408000d0540310000c2e0307230481c2c0010a00b6000c140f03107002d6001e69440040c44203005006461888840d0812a0100c00c0c00700d101c3d0042d02c504048034020141d012000c000074111006c000c40350a81e82e000314046034410003280c09075940c1c103031048001c40d509 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 738700314 1250 738699064 738699083
    0x90c0711011b111003140a09060e060403020604021c0503191103040801050f01091407050c10050c1c060f0303030911061201030506010e04080906090415170106090e0a 73
    0x35000100c035550a201402c220207692124000100070600d102c450030040b040c0c0341c641c0b00e48550002101a95910151503540d070000f03a0121b40703180e44542120005134087c59020400f40845110030713182c01802c58040d0b005030800300c00d200462a140c90504640d400140090001c0307000740c1c0310140c03030f40b0944019928400c8040315040e0424042c40e0718032600340500013503a441d10382d905002c501801046444040382945040041001072180c428130700303051849240e859541d41c421200ba151507002d581c410002d44594440200843d003540200e51161948640050311020f01105100c01e00c0e86c1c05582c4119181047e009010b40c1c0c0c0150742250880740c0510380851881840c0c109505143d2104200701d40141f400201c9400c05604400c45604aa208108481441e130340e84441e01c445a4064900800ca003100304840d80c103501e04000a89518540140000340c2042e14549410701c82c4460350000042410209144144032400e204801c0101070104040c464034030210b01c4180c4404140c0e1005003200c08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 738701564 1250 738700314 738700343
    0x1b040806040606270e10060609091808090603100906060306090b0a030308060f01090f0e090d11150a0f06170d030905030a03091523131a071b0f0c05090c07 68
    0x400c06d02c482e8103a6140704200d4a0388600d402040400b1500451981d11b007800b02c0710f40202c1540e400c411201c0d4200404504000b040e10810101c1c1e400034050313000f4000074010101f0b1481c1319120b01070040a030758800140302e6207880d6001d4113440d950500b02c0d200d103a80d0002040426008800185d102c3c20440c1c60501c20110200180d4024003290400f032f4007a90030a00104861100c801c140303014080c9202211418050a134040340ca1030081c01a0b8803a039042003020b100da2101020102d80c0218480f400400e02c40168840b12048540c1984800d008036504030320084600c80900c0050010121480c040c001210603840d82c0d0356034416004aa803c1680d100480410f11510592000202184d46400d0180312410b11800000084a8482c048591075110100c0e002200441b01642c3d00c640c440c000c41a81d926080340c2c0c00c1c41c1980104000705200441651681c110118400e40600620801214964450030305020a20b01000e4000c14010001c0105122449282e0420740c0c4215a0160407800f4040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 738702814 1250 738701564 738701591
    0x306060f12030712140a0906081005090403170a020909041104090f0308040528170408010914010501050a05130b01020c09040605250c06051b04080604060627 69
    0x20350740c0d49150114000854154100048443d0110381050f05507510350290601e481014400d00c0f5041080c408030320414000c20003640505581d552022036005902c280607500e0010400c40e5100b140d04500103015141000c03044c08550001a401070303102c080071410580b41001003054030304040c00c0a41100c950b0501d8450710740c1c03183c101c2a1202c3c0c0c0802c001a0f0b5054600d0003030700413001034604860764013404501c418000c50f400300e4031051390740c81e102d020402140c0e522841c25000e1420700401045404110100d011002401078121651140d40001c4070003450000c05421600180c0106100d0008903404000d10340c1c07103089101890390118400601c1c40c1103039005030700c0d01c0300101c5941d030040b0740c401c20407081c4a01d41c2d000c64420400b01d000004150400c05204101140000b00c1d5801b0a030400e20744030200c0c0b1103501c81d6900015a02040b51110414081782059402a6001d02e0072a032000c0204400c010140c09003000a0065034aa400d018503c600700d040c4c401c031186024002c1560b41d654420221 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 738704064 1250 738702814 738702829
    0x1205010b310b07030203070b24210d020309030f0706020d0516050a030c030e030d1b0c0b0309160b0703140c0c040f020a02010606140301260313030201080112020306060f 74
    0x308460b02c091503031070340310340790194694010b00c0302a07e0321366400700001c6080407801c0761500d0395010080640305c00100c00017041500c0b24085054084c5600c40501003d030408104211070111820741c0055403070302c00d003c04061415a8040904009801509003004542c0c1c00040d441102d80b05818403540342c1811a0080508030200907002e4a1b038032503540b1f402d0034141c02080d00c4499038046d82d500e210307030031a5a0a041d9190030511541001444040600e404020f124080482d2a80b0134404801c0c00781d5549192440741c4c200303641c460304a0b08801034560500051a00c0034001b8034803040e209081140585002e0541008006036031f020200004817407040600034032a0f864203000090040065003903103038208000350014810300340550b01e8510041006805010611484450050001e20710380c00c0c241e84203030351486240c9680c00004140d256900d18201800070b0480440c2e2220b00e40059842e40c00010017644d010b90000704070051039010340001d03032004508584e20010564103220144840c50100d40315 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 738705314 1250 738704064 738704069
    0x11d0a08180105190504061704121b0b1518011815030f0b090d030b1e03011b0201020304120801180c05090402070602090f040b0d111c031205010b31 65
    0xb12200c0d40980d040094100028101f62107003503031410460f1a00c841c0c410300c1c1c4103055a010b42509145250500090b1140324414054510140c001d89114401e0395150300107401a250001120a2807511494605243c41c1190b12401b080000c4a00d0394076020340ad81000f2520208113002503101c102d200c0f0040c0056092000441d84411400c0200700d40e030800e284851400e40c1c43c05480d01454400200e0941309005039850404010300710458441c1ca0400502075001788130f1010f415540340e8840b4071585501408044002019800243e039030300d098030b450011120804414014030800c50b005004000080010b0381211130f58000000f5038036072020b4150360134007c82740500d42c441d0000a01ca010406a074000c0c01526805443c0c05007050550001c00040d80d50301d001071074200c48101754100102d114143c410652040c00382441d02c0140610102c10380c00c013501c0307034194007045180c001050a07042904c6203a00400f0300305c850034100100d0408000c8000d81c0368050b103100041c0e1400030004000d0002201d0700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 738706564 1250 738705314 738705337
    0x114151f0c12050c1002090f091801091a07080115050304060e0f01151a070b0403050f03040606050f09010b041509120c032a0303110c09010602011d0a08180105 70
    0xb036403401400040c00d6038004801c0412601400600d0440c01ca018000d4401440004007225546500309080c0442c51000800300e080c00c500b495000130150a080c480c40100c0383c010700e01e418180250700c44c00038070440b02520a0041242203c01003120404071007000101d42a10b25002e5525102d50410340302034031100011b440e0750f004030b0381c034002801015071000c26005030701504660301d40e0b60b0340d2000c43d103091803101120303040d5810003100c0c00190b1f080c01035941c0f05110307051880c144184001d0341c00094204440498500b50307500d40034401c51611000d4150100d45c100c0784101c1660402c50088028040c0b8410084409a10805217204900414083d4040e0024a00031052010681007658980010f8403080d60400100c201c1c0b400140c00b4980700d01e008106160b0400c0c07440d4a1558100d401c58440e0f452502c060240c50f0508601d0f5481d02e420074020030284d4000304418804505112a148440c03074031070039075440104c00400041c07601055a844c04a24203070402c00490760001a6400d120741e032203150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 738707814 1250 738706564 738706583
    0x304060b0d051f06060302043803041a0105060c0a0b0709051801091d031603091e050a0b0c0a060c1404030825051b01031d0114151f0c 59
    0x12400c011864196040006500700380046907071740744143d080348141e0040c3d40080d845081502c03000e200000c0245482c060014041d240868110080142d0390001e403000c8503202c0c494800780c03590091400c001c84c05041c3c01c842461030141c0303c081c13903603540080102c001d1040321032a002403880340c0200c1804000300703c090003443c1442041120640c0c6180d09001c0c4a0a82e450a1904030302070384125000030700201c9400c0118544908440c02e0000c1c0302140008804000711144c0204a07402d030960115520800440c502541a040c94104000750704203030450a42d0381030070312201d060721200268070455541c001000189044200c81c0841c0c0640c45d6441032032051000040000810060344004c04143d91400f05055041a1b15401d80c00201e9241700d0140c91a03000030900325681c5a891041c0c2055a0305040029600c1d1603005c2807140c5480f81c1040039000d0f55510000078021a14450081d13101c142109816400c502c0d600010701000300048010b0403448201e008800c0960090104040094000a411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 738709064 1250 738707814 738707833
    0x2031006030809120109020d0813150e1302160809210a030305090d050a120603020a0b0702131119020a151a04060b03071421060a0e0105060304060b0d05 67
    0x54580e00498030f075400750000300c00c03a00440006106030b640b880d07801406040c60360b402c1d44a00c605a0084081020302151040d0001032000700b484542c0c2e41a82503880700f4031410031940c204001107803080401480c003801001b20700c0401144030740e001405039201b061191158180ca011900d00c40301140c032840c41c2e0300d8850394403140100c002030a480c400d02c20b81e0140b1050352011240c40d01d43e20300c400340c240410010300000e40c545d8045c1d03000382442c0014600c005010740c0e90340c00080d08100c40d60302805002100190110039030800118000d1041600c82c000c0c04407822040d070752101c52007000d0044400f050305142500c00d040c801e00810990a82042c00803414aa002c4401d10082a0400c419908110f8180910f000da05150054030200c6184206450440e9070300a82507400301e0001803101c40d120010442d9001468806802c0d00347e94102072008412031925805024404016030001d403580604840100115a1114120303640242d20a802280ba442e03890081040c07105c00d0b1800410a01400140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 738710314 1250 738709064 738709073
    0x3080d0203040c0b040509221203200f070b07230409050a150303110708070806012105060c0d0209091303020c0406050117060a0b040602030a0207050108070e010c0203100603 76
    0x1841c0214000e02d60240210350301c074150a5030b0300c00ca00c034050704503461400141c941194010070030412080d080744202903e00f1a40c03119a50b0009c105000e000c0b03680c5e889101d052125805604010320105404286441099840a0313214000e0b800000d0014181d200001c221900c43c0d00d408010301e212b03d40e00d80801114800c1704c4950b8203e40101500e240c9002c2c00500d2a004501601c24880b20306104000c00c642540c804842403442c111801c0782500c00c80b04000740d00e0f00c08000d040001d040304005001c1e55410862452030b4041501001285201d1100c0540041b60b408607003950007a40054110b6542c1d07000c1805040039008101500c1e0307120554500708511010b41240c4100b50500c29420780340c85c44102c1c1704002c100c4001d0302400d1f00050900ba100041d050704d0748504c60f0403280080104581d250b8440c0b0501595225820020058002240c0c3c2404582c0412038240549400d00300303107459180091000707200c0070312080b0081c100143e1516083c2035480c240070300d01900ca54510144051a00d81c01e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 738711564 1250 738710314 738710317
    0x225060603020f01030504081b030415200606060a11121b0d030203150d060b0904210203041401030c0c0204060807030b01140906011d1f11011a0d0c03080d02 69
    0x2c2c0d00070a00b019000c4810740c070a10406100756480386d0500e007050442650170028005003840460315100812012616500541d4002c01d40e90300f542e03a0b038091031000c04000001d000d0003401481603034403840c2402065034588050398485101c03854a0340380c601c00080c1c441e14142c1c010248801d50f8900290091180c081c4c904030300782e1200c403078003240c544201c121011130032840300b29002820882101c0c098140e61800d4080408203a0088c00c02127030010310100003440c0100d0584007225641c41b6919100503520611200400d03114107400a141018581805202c0b400e0000c40158109a035640c0002c0b8aa0b0044e40041e642c01e4014004001090321000380540e1022a400300b0340782124071100000d0300c41e59032260564900009407408100341c0302c100054444040500c881949004812030350065070726a24081084011034800e490344107610520054004c5907039030704802c5181d05000e80c1c025080303042d110010300c50070b0944900808050a0504003101005070f0802800700b500007030074550b22080c640 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 738712814 1250 738711564 738711569
    0x2060a0e1011010e0c150d140921180d05100606030c0e1c0803060109080105070207090f1803050904060306020f0a020106060203070b010504020306120d020d0e0301091502250606 78
    0x40003040f1221440c0f4940e81c1d141d881c20340c0c880c0c1c8003012001c0c04800c0401b04000e0499015189004191169581c80d10b6046030021180c1c64690b60104a015400042c0190584050083c0e40001c5240584411a403101450784c105181d0084e03c0c0b9100c9241000740c10130a40f0307050005420204030b6107407030301c1707005000d03002170b221090009900b014004001d2414941d8500d07881c052c24404000c0d00c2d202c1d41c070784805030401044039051000c00080001c02d910207020b4984034141590152000394103082400c1b0403100036082c0d40e082d451034903030004500303c18240495907043d0142403040e20b070410000014060f03d00f03500b00814260012811004441907003026010194040d0001d004c0251034410807030307aa010f0b0601c081c150060300340040145060640c01540c00000162004006150600c0418a01400e00140030016480000360030081540311413181000d1004070001d00c0454510745800401d40180842c01510543c0000d0440b08035003441c5104100071b50759003c8641151640c1084c04c000d11892 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 738714064 1250 738712814 738712847
    0x6190b070507060f0f09170c0a080a15050606070303050c0903030c010e0708150106030203100302040218010e040507050a031812020d2714010e04050c0d0f110702060a0e10 75
    0x4101e00d518240c0101e54981003180d80343c2c1d03180c100391f01d04000466040c480c5214144c5a0040c5500b401c071503110f902e0030f68040c0c007842d801019840700c0303403810900b6841e035504440c0e080c600d000f0a2100e560340310310890b0282a054503001c90680c031021508000741c07080d840c4555041c0310009a9001c4280190000e00c03400071f2901c251140c065640d1506620380c1c030031a0b866090a20b8000041c081d10703019030302454010311910b0f6000c0e005a120ba003c034080381d103c0441042d078490144a0351900b980d200c920b0000c401c0054400b030145041c03201c00500f9500404c5034000034940c44d503804211500c0302c00800555507411660001c10002030001c043c0d210742c42d421450380082d40410390301c854441d480180c801070081131412214541e00d06010500f81001d5400554100004a8800c5c616507450340103960040311025041950307060343c008003d04480100c04034543e01d60402c04922b492060341010382d1406501612656079918174410125025031000d001154080d0340c46a04040782d80c2d00c00c0c0f04d10040c060a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 738715314 1250 738714064 738714077
    0x509100527060907060f050f13140f010906140910112b0c020301090611180f0a09020f040e010e040c12210203090631030b06190b07050706 61
    0x78201003585800c01121000c4465000c0101000024422084c00c0d05060540c0360480c02e000724a598a0700c1c56200d00c0c4120b00c402c080761002d09c4000303254050b007002058125007621008000400190109141d0b200b403a003880000c510003810300030000c0485d1003e41c0028040300304030110707800103400d0b00e200400d130811038420b10107810b0350040d0449041c82c2d5a0340c00124104000c042c050100e4100aa03c2c5040b6055500e03525400c00050070741c041da2001607a040350f0107888030303c2d000e81d40f1000b0100320480f52060420888191460b1103070204c29054602c0c0e20409680c03506505c9401c991480349174040e00c160001e41000183c101c0381003403a030340110300c81c2c034406900c0356544040450704482003001504038101900441c00c0347e802d50303400501802850047c0c0f030400c40c02c80e0000f003054101c3c0000104015072451102d41d806022102d02200d10b81c10180b8081007821501c4c0d039110a81c0090045000d406031442c0c54649160040000b4020042b20110360b55884103440c2c400d0300d407c454480c0d074010480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 738716564 1250 738715314 738715381
    0x903170705071205070909060f090309061e1d030c060c03041806050f132702090108150a0b0109030f080d0f051605030a150f030309050609060d05091005 67
    0x19204102600380c0e044030080c00c58a00340241d0400a064048046035055270b60b10302c94180107582c1c0141d1321464081e807548240c103840c2500c0500449401d0545010000c814002243c2664010340728034000c0079a03132441c806600074140070902d04440009070b03982c00107000c01c502030f4a40d0008010816540508039100424000c009003d081d200f00f03009155000c00c07540d55070201814414190340356114607000c0440d03060ad1641c0086c1e070050413000c2d00742c41e0f0315101e41100d0550521041c01401401640010205054441541328840c1c1028001d062015107456903182c8680c860341008001c0c0d604030906a000d607445c0c0c079014649900000020002c2e50418400e040c1580433841040c2c4203c6802d140c0c1c8580d551900b01c2110f10380e01c0203290804942c4c2d29901b410b041d44490909101900d2010302c080700766030075400c001e4603070b08060340315034842c600c2004030540ea07031101010358495140070302006c5107031349880e50514117140001c602e00030001c1c504410801461500c0d54081c19111200c0081c140c0c3e0324 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 738717814 1250 738716564 738716579
    0x271203040819020d2705060408010b041103011a0a090b0409021b0609100f0f0f050906012c0c120a02090f04180b07090e0702011b020a021e01090317070507 68
    0x121200c001c0c040b45a442c502281401030118017803506000040204ca5540c590000410b03e0b00079400100e80f5a65598240d10141407500c900366440c00c0020001d41150301d405d8107201c1c0b01000c00e80c4030015007404101080500d000d21141400344c11540882619542ca50745410001c0d0040c040390104a070710021a01040c10005c10520b000d0301812002d00701d4081000b259030080c00760468172445155413440500084074442c0300d200e041c103401e2007001c5198249206410718106040e04488800b98002c164150b0440c180c03003d034928008104485021680ca08000c007101c0d029011141c031113180a4402c12104010990003800c00040450301c001000e07602d4070600084134442c1c081c0000311318500c3c3c1c0c4c83d00030070f603500903a40d440002c5103070911829031114071210300000281c5044026030f4403060555120420710300754030140d00451009010640d2140c00188a40b0340c041c1c020130b85203554201c000c1081c4d108040c1d0901031070300f0510240c0884501004802c05030701c000c100340d03081d00607004003140f040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 738719064 1250 738717814 738717823
    0x10602061b0c06070f0909050c04030c170309010e060c0a0c050a090605030316081303110405011406121b0a02030c0f0105010b180a0f080c030d0827120304081902 71
    0x200812001401c15545040003541d0813172612900c0000c1c0102c0f0b450001d07540b00c9a00a03180320707420789049242c440f4a07602d0642007121040e008580852540c40f030031107074940c0c0001942c4a0303c009181080300c070000e410102d031a0744610031134084a03026041590003803100224040c800c03218242c03400d81e5240e98503c004412120103001c1c60b0b03415002040340c13807101030900001204980c080c0710400d00d01495001d00d00282082030b031007200c0e1312000448802c0146420311620b801442e008440801c0f03440c5401c0096154420200003400d60f14050000c540523f00704420560400e2150040b0350303864145680181d50b90300280310900b041e124000a450604906004141c12621014585410300d4010f61201c01450b1a11040e81e41281800000094144010744240000d0015502515504003000141402c1000424060042c01840001e0019046800b0321200c91204c242c0b680c4210306840010b20f42c2481c880c82108291300d2008000c0c4000d0201c0480205080c1c100c21440d140c1c48121504280d841c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 738720314 1250 738719064 738719077
    0x40303091a0612010c0905091914070906090303090603020c01110c0f0105011508060904060e07030825031409010306080307060501060912050a030e011e05030601030b0901140d0218010602061b 84
    0x240f040002040340d4200023010ba50484800a55004c03440f03a08040082243c002840300003288542e40c09105040780c00070005000341900d850142c19090558802801043c20b5208203010140c1c0055a210519401e40c07003501d0568071800800c0d81c0b000c89100841d510b103024001040715502e8040005508111003036a01c0c0500c07039030b0701c0c4c0d52015945d4408000410740024016907815895010400d54494280000341c043c5100c1c1c0829525011642200d00784032144040d1007003080c041540080c0480c0c1c0140c00c10084a0b01c0700302071aa00c90421004074060803a036840780302a4403001ca00702c010022250000d5058170b03441d6481d542d00c290b40b0903056506401541f809820b0b60400003035800440d2041e08074541c180d00605140303c58034103840d2144981e400c0700110b02e00040d00401800b9983d0307814091900122000c072000c401e29414180745400c82d00f0403200c1c092043e07402628120441d1644080c1018400804a0107000c0d50f03940d01005e51100000c581c0003144070440d01c4080c0e65070300000103030f545 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 738721564 1250 738720314 738720317
    0x18070f06120212070c0819090e221e1e0209241c1407090c14120a0b06120406110c0c2209060f06060f02060a05040303091a0612010c 58
    0x107064860220030f50b8440c03c50017059403031090801c04644004038804180580800d944e440e003160710f25142c44507076454400f034866194200702c4080380034000d810360300d8007400740d40010085540660918800d001c90400f02c0004109072001d0950110304904120b030894518000d9a074104180c3c2c501c1c0080c1d0410060b01e209010a200c500303c80e5885003440446080740c031800403412080c221894a4601c80b00c0c1241c12103403103941c4080f40078400d156640c0141c029451160400c98051200e0310007101c80c1e4003030180c0ea00c1d03c1c4421180060307400c000941245201c42c0000d0700706c80ea00e1030300c1e48005600c0c1ca0220750640b10241000d012203242a10042114003a4131700b10060400301d6124401c00ca0164020703840e550241c0c25070400c14001c08079900c2906d1f00c0a00c6103c0001d00d10360103030007041c01d07200301d80c2c0410b0912002954000c2000d401040e1254004188080054281d5491505138001d11074030320302800003555040024000c1c1c0d500c0f820640115030840741461031110110b00c2500746c8503110507110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 738722814 1250 738721564 738721597
    0x4110c07060c05150a05101712030a140403050c070e01060507230f01020c060c0a20120403141b2209050a05240906060918070f061202 59
    0x1c600c0c0d102c0c070302558400d4456019540a0808030003040c50303510040e148190920350f110144203039070440c0e401400c0140b0b4012031041c010002e50b05a161580004c001090044000000141841034140d200c005114504c43c07a54009041c00d04008001c6c1e040080440030300d02c540c2c90003040411070a800c0714100c1d051075a410349000300e0341ea40d11040304026240711040c185003c04c8207403000400d004d102040c09000c000161a1031443d1f06061a0581c003030010903c02004000400c0c1040e8898105112001854004007004030710098091401c024886901e020400209000c010009011405851400a00c003150282010007820f2001119a402850b03400342070150005580b03040301242d0b002507504613000040006140c5c6826042c9411180f080391540c020040407458004d15803640b00f03010305001c44174a101d152070034900b43c0d81e0030060a03803449402c191002801a026550118000038540fa0a4a20450783e5171004028003403180206030204005404440c110b102902c2a030b446103181086a0303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 738724064 1250 738722814 738722819
    0x50909150303161103071a0d0b12150f1f06080c0906030a0b0a0602190b180d02010f0b0303091c03110d051c0c0c1205041e030204110c07 60
    0x100c160000303510150940030074020310400d801c0030100301c10010b02600444100345801c008040c01c24542d60403412145051007640390798132610300d0607942080c2904074001044002c2c0000102507280303034a5500d03020700c2040c103000143d10300942d000780038940e424040340703c40d107036441c4211417003010701c19507885046668020030401d41701d003d40c81c3d089031520147c0c40c0b4154810001c5203040d0310495122865035200d0783e500d403090515410080c001c0c1800c0c8040c06000e030720410b2480c4d110362416005810081400c020640f40342c0341105e1208088042c1044440031044454041d0291900003007072807c4924002c85074825050100842d40402030080100311b00291480c1040503001d100301c015002c00c20a05410480e102041005894405040d08c480351142c0d0300e0107605004410080381d80740440d0400d280400c240b90090240464181d000040d8800b113042c0c0e80003180c860103154840c1324000b0350540e13100d0a0b40e40f0810100300380c0c0c2c001c2e02c00b4082a00708110a0000b0721925182404c103510000c0708 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 738725314 1250 738724064 738724081
    0x50d080304021e040e0309030f01091a0a110a020c0a1406070b0a090203070f030b0a020403020d0609060906062d031101080c0c1b0103141009020a02100c1e050909 71
    0x61043e040340141c00d5001c00b94a036004282210440344026050b54000a000f0705a0319003000002840044500203000c2c035003040d42c600713804e00e003181d01c000c3c060484e903030100312014125003001084c11203460181da2926a40b03d0001c1d07503400c0c03890601e8022000701d400400e004038401e007100540358010342a146071002a648074800030400078000c01c001a07a40c048100140d0703060014100825604610995240c1181400b100040340070700345482c098810402000144c40f01c14001d0603094000340c0004086509042c43c2001d4519440010034071403901001252116002c0c021201020310703e0551070710420002e40500c036103034141c0005800070b180c1c0f00c071549040d880f0f00600c2c0c2d070055062000f28103120104000c07604d403540d01c07440d0340030401820000c00781039685031080c0e101e4020b00c80070b52440b81c02c00079800308034414580901294550001800100e02d030080001d00d140448001c130400c4a011300c0c0d070004000281c00c0180a007242052050000001e1044040d54112080200340040b40d40b5070070b10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 738726564 1250 738725314 738725329
    0x50f0604060806070507051501120b0a091509110a090c020d0e0a03020f15070606060f0216030b060111240f011a0706061706070f02030708030c07050f030409021201050d08030402 78
    0x44580e84070f0329231113036140398103280e03001d0090002c0d5000ea00e100070146080f0f1072002300104804101850074480402080314484100310188000034000748203104c504246c80703098034010742e058001518010000d445041070b40192899001507003500d52095508000305c8041440c0324141d540890b040000740301610b003034003004e0b01c0610300800501019500c0174041146401440081e2095543eaa10070042d694010b12000d5035407401e4405040015100754010008981b0741c000500b000c404200000c2c40790340038a030f11008004201c0b0440b10504002c0c0904c0014010403403c0c180d25400701c0011404c180d50a6000c2d0341656075614030451425801501a84203410540003a2406500d03560002080041c00703410040200c0e0800c0035203564500f121020b403e5580b403004060071980104440000302c2e95101c02e980d04251114046070380ea000909110f854601410045d00da03500000400042c0c0030025030042801c00761400414000f681d13500204072021142800c00350240380100009001841d2041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 738727814 1250 738726564 738726577
    0x702060403062703020f01050705190e03070b04180f020f030a0c021002030a1406092802040914010e130f06020a1119051005160f05070204020d050f06040608060705 72
    0x26414803d50a00c1c40900c0d039410b0708042540560429815003803003201c2805425846009400d10798039200403039110000f00c1800b0300b00c1d0010000c05a10ba03c4e01d41d40d0070b204940c000c045601c01591655140c01012100c440441c140c1704000b45030500703d0010f0640c5000b61070b1209183c2c1c0c4d140341951340341c40c4c5040c06003212a1202003180a00803280800700c11a10180d40100912000010504202d407144104a040a4000c1d44a114040c0401c59003403050f68445580d500300811000304070035920617030006806a41c00c410000c90609003818007101050510314104c1d880c400f08001343c0d849203c4088060740052001411460f014001003000c2503058005010310302c41481e003005040c001c6070301d06041444600c803900c00a807200d01c03810180b220400881030f10b080c10079410000c0742050002c200d0601581d2614405100369004020700f4103001e403003520140390300a0300640d540c40c8011859401400100c0d000f031039043e200008030301181014800d003815030358400c006181c1d503291072800356810740100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 738729064 1250 738727814 738727841
    0xc03050a021009081b010506060405042417100b06030609130f0c090b0f030c010c14030f09040c020303070e1905060c1006150507020d031103160308010b070206040306 73
    0xd032035103101004034407074983c80c02d000d08056038650300941114880c00a00c03502482c0540e0400c418070000d60350b08400c0303508888086a0006042440340401400c20303207200b07910a0a0380c40900000307122803041c21411a802030b4003060343e403108140545d21f8129450842d07281e401079011700001d03c0a05240395000e23000095110320310002e820541c1d5000640407592021039400852481c1007010b5409801181038030f072004c494034402c140b90240480d6960b00711040d100e040200c03c01c0e42a050003d00c00c0b00c0007402c84650192540c4010b2101031440650007407005500880c03600c0800310b000e61000c0b0990340103280da60b84103100c07001004100046441034807840a4114a411400603042c0e44410040c03100c1301078003010f4040021103c54980413160305600030640002200c88508006030b0003005c07200310325411120344815005508046510907110505040b840c071001072030b08ca40da0b031010501110300d4440d40c1c0b858074580c1c03070b034500101501401c00001d4004000f84010720004525030080910390004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 738730314 1250 738729064 738729073
    0x603050709090c0207050f060c0307020409081b0a030e04050420130213030b060409020303030c0f040e090a0b090715120f060f090609090b040602031017030d0612030c03050a02 77
    0x100c509030022540c0f85080c480240e40312500401160818036889204030b001218014280441e075a246610380c41885c9000303104540d1514600d040100350b2050b66040c0294007001124030400f8601250b450040030001e802207034221785030418520302801918401e5600403042070002c8070039180e95014425540c001e903484110411024003900c402d10140900407056402d0302c410601e5805c0485a14401400caa4041c80c180030340c20300562000401c481e000394881e0310711503a50159040003481806190010078181c100310302808031000c1700188078110180540d10100c415150103030301954640e0f85224510399100501c83d50b00d0701a020300c01c0704002030000940490f0303030b000141440d4222000c98001341103400000205000c02d4140307108000c00f610200c0f0b01040b8002258a426850480007800205659000400101742018544c205d600030030f420b024610b03560340303400525612600100850502c613458540000b500500e80400504500e4058860700383c9900340d034804490366448910f260080d0300c03c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 738731564 1250 738730314 738730319
    0x906030e0a02061c0b0a1a0a050720030c240a031103090d020d0c020105040504020708070b010b19210504050313080115080c130b01030b040f0506010306080d090603050709 75
    0x549400426484184c0e007001003510140300c402008440808080c43e000b240341840a00c07154448030310403512010002d0380345d9154000000211600c0c03140242c014101820040805042401144c104d0b4008004400f50380741c40141d141030040c000071552003440f20b28a4410b0b5017144061201c0140200c003024030700403e0b038030000b03000341c0390b07d41c0180c4004426a00902e2885103c0ea814041c04044041c07071300c1c0034140340715540c0008045000d280601440303640d00103152010003d4903401c5940040c0c1c404040300066940301001021501302c1c40510044148084034264003611400345195050032403224002c400d0241400400207110080c400c46080c4802c204914055101c100e0340c500a00222002280350f103036000e50058007403e81d9000345600d0307004403003c4000c0d40e200707240c600759158441d070000b4422084900481c00707044600102908640381100759900001582c000c0b074415102a2000d024050341c80240700d60f00d4000e50010000540e40725002d000c464841c0e0000b581091052908a602c2d64 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 738732814 1250 738731564 738731569
    0x3080d0b0d21091a03060d060c03090c050f0607060903030207021c0318050609040905251508040b040f05070b041203140301080c06070602220906080c010906030e0a02 73
    0x40003101c10381d00342804261000451040b0100110004800c1c504446098641080210748400c181414005440080001041034a9000c4160b500580105e42400800e5400001500030282d0050030b494a612a0f8404034250600c4040780318941d001400e55840c11600340c941100074500e1900440170503808100304405607482c0400010358280e513040080702240245005411103805007103044c0150107200f002c0021303940b44070541d001c0c034078240e4000c00c0303903122440e180d802c0403075900010f040c51956405480d0303044808036900c0103407448142c54814103c0c4032482562204006c6a0040c0654200400103002600c80c2c01c1c050305c0c56100d00f088601742c07502c42c0344940c400d801c2a0820040030140c2210750381030560280c2d904114a1200c0409450b5504115805480304140580103020707038000078046040043c15030407141c0542d1884410709420000c92030505200c03500d40300f2180b601d412701c4004101c200003c40c07a803085501c140c45a01201d85000c800350003a24001316840d0b1180506085070340940c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 738734064 1250 738732814 738732829
    0x3030503150d05071e0f170f0f010f060815130503070b04030806030c0f032a060a020304030201080a0b090a181205220807060525150f1503080d0b 64
    0x740c85180500380c503505042409a07480c0c002101080e1a950b502e60800107a1408441802905c2d00840421000050b00307c43c0b5242107045100400b00d4403500703480d100300c0c11040d0300c80f05202e01150403c0c02030558811842c3c0d80c42024121030a032610034000411000b54640700d504d94218442c00c2541e081c107005031622500c201080b10242c0126500400704017903490144089030300070000f1290380700c0c1c00e010040400e40da80900726035420b4001d00c0c0458440301d01d0b03040c0c88214201e400200455030b20402000700039166080351108a011502000200350340701154040d14940e03040107091030341c807a554506403501405e110481010071400c10740303011020885910901031074081d04d07161107070b40d5940c800c0344a404e034440b032041d030f9116403030300d2401d02ca29130011500c030007101c1c1b01e0316240740c80351666810248001c1450a500060843c0c514a14040140300d0b1888440a10105020040f07124480000d400740c5095030543d414003002a90706100164112000d40880e0070100700026480710110041804e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 738735314 1250 738734064 738734089
    0x12020f032e15030518071505041721030906060d0305040905070306080607020705132313050601050f061c06091e0c020c0a030311030f12060f01180303050315 69
    0x40388440180b0116a50903000e190742080241c0b5171013005170403450610f0385412190080c4040c18000081c04c0fa1880c0c400ca050300c020348030342c0601005880075080c01304e549100302940c13403446603040c1d0101c00c022104001035170711a14802001e0411070742c8a104205000d030100301c0c110144001407102040d5903015100302403080c8004c1c0c40000b081810000d41c0c514241005010f001158800e6005212503103604189040d240004075000c10303908a085200c0710040c400f0a07110085500503130800591107101c072040030318103018105440d003598940081c41078401a68039401c0e0044002c0290309030f0130304880070a99800d0440c460010790a0303101c0000d4010780d480c090031280d444041501403002e0343c14901c648a107002442c0002c12050207094041080031256100140a2007412020301222145c18011141c1e14100321403030310355036103204a940e0100740080c0c826500800c500c542400e019401494499030b8034044821003010289541c1d401c94203584020040e804180d070840b038400250b19015140303500e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 738736564 1250 738735314 738735329
    0x6040306052d01180504020f0306040506181903110f0f0109033c05190915020703050303190609020a020303061503060927070306060612020f032e 64
    0x900c40600602c4140d00da8460080600440a00400124402c65408400300814000200300c995542c00000c01c4106030504041d054010081004200310010912510032040039191100108210741166994a4405409218940c80004e8040428098180744a890801000f01c90101945581060070024a11031070f120700d86d11480c841040542148001c10880701558a2003944808412a05248a02500812408000d9804440c0c03800d1050341210f80600c40076850210303071308400e0301c01810352900e03115030710280d0180c000500030188003240110840b0b0300b1000960560326400840d00c801c8004544004065580c2c1c403001a900c0d402d40060f00c1c1c1c202054010f9900c0b07150220901003014940240d01802c17039402c100708a00f958036081100e400c007000c05200c0403070030782d000020f0181000c107501d03418162050750400010030903590042c20940d2000d07a1380841005111a294003a4055042c0880c4401d00510000d08140d25150003207540c0701d4191080c103041d12110322800507102503504940ba = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 738737814 1250 738736564 738736591
    0x2150a0219051306020c0306010b1605070605180618091f0806090d0903031b0c05190303020d0311120c1201060e03010506010f0e040b060c070923090601030b060604030605 75
    0x205030381e035040c40f80009000300d0000c0c0034004c4848001a03101c4005000350b000c0e0010108865071070075581502c820340c89501108484842f5106c0e02c1c050142e0700014501c0f8560034540c2d600c903080b07044c100191581092440445040010340004100d00c4034001080c0c50400781c001441401e200002d12000340040c40c25902404413800c00d014104d003044440c054040a102007180200002544090b4112095554a20a415815052412443c9590994051a0700c0840d6940c0100011896003640003120322075000c5034109a0f01140c250103403128660300031a242c80500410441d5241c2c400e030039501405076035003103181940b80041e0285e218400e070003a070b00095204c480042d081c04c00f403241c03540000003428800f2055080004c002c1084103110000c41c041c5449040c01d031200e40f105801e41e5841e410705801c0d148004c0d00c40c40c071480105441454811400503c0b0743c591135640c5d51600050140050402510683e825034a071281401005403105030884020040040070070884d1040c0b60103651900b6400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 738739064 1250 738737814 738737827
    0x90503130b12070e01090911090405010603021903050c0912070905160206090c0a1701060503010615143603060a050f07020f0d12060503030301031a0f010602150a021905 74
    0x40c680040024207003018489844c2016407181e81010444044032516100403440d5640d803a804280c60244449480c1c1150030710001080f0f49030550094880c0e042c0140c010140b64510701c80883c00e80b5400e071402c0c0f14110341048054a00d040c4403514641a055908c1103c0001e551008000100c6208a034100340c01070140000550503641800380c1e503000b40502008088001c1c069000800d404024880c11041982c0072101ca1410355082d00800c0007807074010f0003003007600d58814004080c1503441c00d003c0000340081103507040c803100f074005a0780f03000c0203104090b4a41c80444203400c081c0f0322075405a4001002e00140541c20350f01003003000c2c0700340700c201c0001c2450f0a0103607030001100006800cac01c041d5044030740d02c0412101c00140d01e00914a075031408800310841180850000d2419400064041c003000001100b03000018459403066921a01800031983c0e4421044444020070301800300180c1003504008402c1440005042d00105400c1005103030512058080c03220003d452010004510040317605e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 738740314 1250 738739064 738739087
    0x1200f031614010501050105030a0504020102010b0d0605191a06160c03110414150907140403300905040c050f0d0605100c0209012108030702030403051903020a06090503130b 76
    0x1041c00b0b588560300240300315410302c1c002078224000240548545036903a0700080540e03200750416008040042e05203172607101c07a4200030014040407039081244280d00d5941c04115041803045c001891101004960050504002c004603907106001403c0c4a400d640d0701400804c59000d4080c004521462041244000b61003d0200f900c034880e141c5149441e40c80c00700711203091480d5880840c1c070401c9503a008a59501007040ea01034030403245507801c214000c030300881084403c41c0c4200c0c0c20003042c0c150211440844104c907012083c01150cc4c0002001039400b00302d10305181c0c10050200c0d4550400074201642d185440100380c0001e0b0a96010b02e454401c2084075041c402c001104104003031410342081d00050700403424404040c841d80c2e8440341d10415444900a0300200760341101da000380d00a9690401c1c1c80d00a659801500060342d0600a500c07691441c0780140e149200080d038150003400c942c28071500c034140200840700c0140c0301e6010801401380c204644c81c98040113000c0e04660b00e44c490190456 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 738741564 1250 738740314 738740333
    0x40f05010c08120402010302040819020a0807030201170601120912080f0c09010804050a0204060f17031e1b2a06031b03090a020910060201051501200f0316 68
    0x200303061006001d91040451a4402210b008200b09007026010741c54510048009100d6a440f201840c081c070026203c2c000880c400c40c0c0e504500840f004081c4603207070280a9201d00c038034440240411140310f002414458a015005e610681c14140340c500b01408040130400d8405060301165a9010350400440d25500101340a400c1001d10005c400b00d89803080d80e5054601c6600d0400d410b10503620001400c02004001164219030701800a0110310f0381c0b00032108214056024400701001607100350a850a8000700f90f9500a05080070b1014020107511140000c2e03112100d505102201102c81c00c0c020030080101c068203848090010300d0710014000c1c0345140c0310300580c3d03083c03250701e0410034008030140705500341d9010180b10300d42c95503d4641440c11441c2a40c8560300035000f0207007800300080305504051074000c45075240c000f8801a0384039000884602c03520028117010890311405007603c0c100d0b40741c056605039070200031a04c1e903c400001d668515000511400c280c004004100e10420402aa = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 738742814 1250 738741564 738741569
    0x30e190b0709030201020c04021e130501080a020c060133080907050a0f06030b0604090906020910030e1e01020403050f01093804240c0f0e0603060607050f060a02040f 73
    0x900007482c54150342c0000d40751061700615610554010401120f0b0094400d42e202030180c0d00698517688000001418407411014403c41d40890b80c5500020005415402201d00112904029141a03804c003080092000b03a4410180c90a40c15620194036407061007442c1101003859846100c542c6c41c0901500c2c1c03501001d9003043d400b80300d04002c10405440f074503c3c507000ba1025070801050451a940c04681030b400b0f00c1d07021075681c5080c090700c61b080c40000d13401807140000654400c40007a10252041c1c1c1918515492001c40d03a22624010003c0d000404113a0180e881c0d0300000341c5455131b00c1d01c44500c0d00d02142d40c80c4a45954541c424801c200d1322001c1c0c06541c40000d100149103a100860f100401c0a282240703111200355000020308010003200c20781c080089482d04690003107189a4104010403040f141c05010400d0079285409842c0228410f8403980d40c0100301e00e141d651001c00b8030507140c1101204986900c1100030107000c8030b0080c40110302c00c021170350b00141c03600d203080d17030840e2401401d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 738744064 1250 738742814 738742817
    0xc070c053706050d020901180308090f0904051903030b03030c060603070608220503040f03111302130308070c03051c0305100b07020607020f040f060512030a1b03030e190b07 76
    0x2010800c42c554009050381d054a090420041e100d080b02001078031010803501007102410007083c00442003040c1ca401400c01d440d005d94900380c07803000c40002e0000c14903050b00c0281c13060303000c8001a501a0308000018640b03e04c2850003054628036a8040303495504a40010ba815400c6102009110700b0304100050082c03e240c58001c0c2c450502084030f20089800d25400416282ea08600800b40b18040040781d00803c030105c000700c0001d40e00d06021341341042c82c0128904c90203031102c055030051014000e460480d0301d503900da1162285150348a104a0744505411102d40c16004070000c0415418070040751303002080b10010082000c0280000c00703c2e4402886805510300010080c4485801039040c4c1d069240d0640d00340f50385441c00d0001800f550003c0c40d14550250070070540c400824a5904102e08540066a20703034441c90b1103400c6180c69000d281444000034518000c60f5025510748528001c40714024140041d00000e1034003403a080502038806801300046020403002089201e8192a82c00b2115 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 738745314 1250 738744064 738744169
    0x130506090601080916030c080d030603120e0f03060403050306100f0c12020115090b0324040303050c0f041d010501020604031e0e1c050114010e0c070c05 67
    0x55000201100409003141e410801890005001141d003007241c180b8007070a4a2501091954a141000c2401d00341d0047d43c2040c0a10320f000c010086c0640550425079030300002c4002d1684060b10304450f0b90a4001a00c0d03408811f500d440141a2011300985002d02e009070f44a90703072460940244502c0488090680c41089214038554464030391043e040324401783d00900307402c41d0030b0000008034090700000300000c01118066000042c455480c2d0b00c00c40a10b0b84c25016148168003900c101d191034034094040000c0c1260100006001910039072020b80e101c5288080030313060602c40d60320840160050b400017080e040c000c00c0302107500305440749214014030091000703165038500303550028290028460f000020702d0484100e0803a05006090442a100000c0d00400c2810001120f0103540031401200307554079468041d000b54180340c41001a4140c0c1c0c400343d6442c40701d80380e44012001d15441140140c6485081d80000b14a507a00c10301249005070540109002415102d18565074891411100c060400c99 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 738746564 1250 738745314 738745321
    0x622050f060715020304060912080f0604090b0c0904020403140d090b0304080901030f2712020705091303050f0a080a0507020120070f02100507050709150b070c03201305 74
    0x240b40e8450326a207400e049000d41ca0342c40c1c0380346c01f0000d4030517044014402200e10001c5080c01c4e9000c40b899125940c11003440c152509c0d00400d000496104940c050030786108003001424440200c80104989100980010319040d0340741ca940c290322007030402888040e0000090f107400143d1240013400a0100c1458213465801c0a50700c0c0b00040c81002d03c4207051644600e580c0310f809103682c2c082d0907040a10211400e012101d5141c500e55110349041c111003280c04160b803107c020f480000c1c110709945024101540036240d12001540100c8046421010400200500c0b68040300d290007074001101c00e03031500d26090428200f0030307060b200010306041c1103a24001c56034600c0b0030000d9a50345d9007012070000390f640740c009050108049103c45406034006030360944107000b49034001c00a041c40340c0610244e4004580b0340f00301c0019900c109181144481d15407800740440c0e84220000e140c0648110158031b1300035500c2c0d81c0c9600c4c000800403000300300c10f880314240c0341710b080c480c2e00020f0110200c00108490314 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 738747814 1250 738746564 738746573
    0x6060303020615062110030813090f0902010806090c040f06031d0a2d140f0601120510020a1e0504080f03070b16090b0705030d1a0109090b0622050f0607 67
    0x2c0302c0b60b400917543c010b18041603040c100c081d841d802441d000000c05a940c0c01060320018218000d101d003041152030000310312400c200c02c0c0b0503ca1103560580d90f10100d601c49004010503074002402c0000c480100300400501d40620442c018001d0465031004260200ca1441d52904144600c450703000940005600a00082d48401402c42800000821105191161000404100c050074000301010780d210240070b82c504c40001c0482c00c50700410112441680c0742c2d8040c002c5001c03524070044c0325501000140d810654a1780182600e4000da02c1c142c2c0300710b001c4902c0c030034413076003004d04100100b04000340501183d4420302c0720100403203609004500d404840e5480b1001ea640040c0314040c04ca540e000554041403140b61803000a0001c51501a101d22450400310380320b6000e150020307001840d09543c0c2010b488076102e441407450050715240c08003843d011904c009800c440800ca42e000f141080807500b800c1c1d6000800d400e900c1c2402403600a00d040c03a0510404403c030215291045e20140641000103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 738749064 1250 738747814 738747847
    0x2120a0c29011701021b0a02090603030a020c01031802041506020615061e0f0301091410080a030c061803020a060e030306060d0b0102010b1309050132060a030606030302061506 77
    0x10f9410340301110950541840960080c010007115020160714810300800b0941e0005141035032070300031103207520151940c1040540e0307842a42404070150300000c04561580d8040d07400110000400034081000d41e4803540098215203403030b460001c0c0843d96020901400340c2c10001a03511003081d0404120a483c000002843c5000d403400c00001800d007004610b40c070082c281c0a4840d820b9000034101d4403540c55807100740c090940b0b8034000c0c80d40d400b01c00000c6c0c84030102040384030403a801e003005446204040d80302240c003002003140a44915403980c0d510320900b41015204c003c5903019038083c0040744080d00d040016103246050842c0150302c02e006021300e076036440003103c2d090003600c41d0020300501c0080040c1d0140402a1100d640000c1b6400c0710322100d2050b4014180c581e00c640000c002c185080d400f40711141809400c242c074146040700c2598130100c5e0035142503410200003451f0024141d0313242d459000707484041d001140180c0001c1300380b100b01a0311402c1507043c140102d6070a800d01c400c420301c5481e41c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 738750314 1250 738749064 738749069
    0x106090506030417040803250209060904060603081812010c0503130302010f020403152405130914033a0c111203011805010b1902120a0c2901 62
    0x654001021400f0858050a0384445204112131342d525181c0e200710b002d80341e0b0091740118154040840b00d1400201915090058a681c0248003055544a4034144503400310014000c0322100c0d030b501c0001c00030503603582c0039044031585002d0144540807090240215030144248544241c7e040c04c003201c034042c1d0820180c4e81c0c4911310700c29442c08070843e4141280500301c408558503446100040100c103001d00d005200d501d010948505000e02010040042d16074801180305403100ca100c14414410f9181075803480344c41e49a25000480c456440e40c9501011452556000100c0c1e0b1000075060b0402d040c40340c0300210703001c5d04c6608040a102510040d01000f001d0034060810035580e140c2100c0d440d008141c0c81e502d5450240444400b2111422404101d43c001c0c007a105110811610742c4018020b80d01685040e200394690349410b00107540902c3c120344800d20000000c3d40174140035101251904406403844440745d40c1d171103036845004d0501441203404408013030140403040c181e1241c000000b6446504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 738751564 1250 738750314 738750319
    0x806010e0403120c09030b0c0c0a1106120a02031b07030203070201180e0a0e0c0f0312090f06030a0204090c080403020307031d0a0b030603060a090317041a0c030a1401060905 76
    0x1095aa41c60300f10350100902ca25650705503d00401d22800380c1d400307141503054034800d580980c0c860301c4080a0101034050402111000e51242c0280000211007181c14428004094250390510180003000c04114030102c8481d48055804000c10030400c550b0368403280d45881000820385030980f992002900d91150704000b9060181c100c050b0308134007000d10842d5000b0141c1c0040800740d401e1070031400020704058850107056104802c1e1418107440c002c1406181102c0c000c0003030601c0c3e07207013040304407880c4c000c0340c105540a9000005503902e601c0c0e50000b10b21448401500513500c43c00d29032044200d52201541c1c0e01000243c004020000b60000211002d040e01410501c001c440e544103c022041000580c0c01d401032000c03040003c0c840214000b55000760021401d55040c0d079a40c102500440c0c3c0c1c4100080c0026501240110903039107604c0700a500a0700529642c010a00d0407018192aa401500e0501c10104008204000c610807032080b40143c1041e10321007601ca5240040040080509025651 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 738752814 1250 738751564 738751589
    0x1109090d0311072414131401110403120306060c020a1e0b0f091203090a18060b070f0605060d0b0a020a030213030b040311011103010b07020d02220e010204080601 71
    0x52420510000ba5040303d5480106100102c04440882003e040c10010b076262550400506540e43c00400c070a4611510480c0444e401190b1141c40c0c14015400c802d042800725540d031207100c01074100e20001040558040d0b85401104004080001c0444010390300c404100304043202a4001a6070340c89651045810181c08036070883e0f1100d90b14216040c2580c0b0030217195078001101205200b1a00141076281c400321484540c44544114054481c49003a40255000001c081e0074403144800508045c200c6103001c0340000c2090b15001402c100364058039060700e80c03921081c1c5203410041c050144a80c0440f056a554480b44081c1d9103103840b40b000a04008040c0c0d13000700e01c10350f52610a0b0305507100c10b01900980700c05240d49080c128a94582520213900190302145904100c1005014503000d40181c102164916840c101011680380c0211900300da1211040f686040940c0c0c1d400d40c03110b56011000100d100c3c0e401c1c2c079071a4208540e021a104034080c0d00601c0208944480032407650304441da06817044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 738754064 1250 738752814 738752831
    0x601090608071211280b0f120414030a0306171b010f02030708070b06040e1203060405100305150703150806060d021801120b07080112300203071109090d03 68
    0x4215021320001c080740c100d00d410100700503194101400c4401c042055050350303452178503102207601382e11404030a8002c0e95000c005100322030780b0310325210341e010340101280b08512600c548903e007149e2147c84e101001070389072403051001003003c1803202422410140200500c1d52a00003e4107070218805110341400040b4200c884018000d0045424040c1d01030451980c2e01c0c4249003041d2914803d440d0140100d00c0c061381e0b10003402c4001400881c18450000150541e03031400104006448020404c01c2840c0d06024000001a0100801080c05c05203000741119464102c0c0d005040711040e0042049414103a034082007180b10102d06540c21000030b07518855942c240c0c0c0041808841c0081605d01481d0801000142a2800e100c1e03011400744503c0c424421350b01c074502c086074a000d0a0207914101041c100425000449402c460f40c80307080d40240c000090400485a510405404e29480e005a0000115031040107807a2440e08071120b001c8400e0207450800e1012140e4030703040050850300385a0b80d403450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 738755314 1250 738754064 738754073
    0x15070315090c2c0d1401140c031311040e010203040b060316140a120302070306061a030a02090d08221a1b0a060929010b090105070606030501091406010906080712 71
    0x120f007280c1c002502c4c0c4c80f160701c038038501050703e6041290445401d51038683c80b1240500ca00690a008051660300039095880309803040a103480e540c030088030b544d0101c0074024003d40b01d500801505041c4100016249e10301814102c400000040005100c3e4000b0106102581d9000103988141c45803a080f1203812030680011034154505500304441158090348800100340c0d0000b514800d40348030b50800c3c41410f54901f8100302c5110340e034420321107a02c1c003440041d201000c1a80038008990000b080d2807900034080c2c448074025480303e5086100800306500881040040281440c0103010308005d20602c6802031229906900070100803081c1e41d00380788080d080410040004940c0d072600007104202e50042032408401c03041018880d0740c0c42c8502c226644000f450b04441c20790403a082c900400d80792040c0c0100440e1540c0c081d0400f01c5141d607032008080081903092203500c1e0355a10031030440034503032941601586806816031000c44010309041040c040c2900101d103140844200c048406c4980460f80b90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 738756564 1250 738755314 738755387
    0xc01080705030a270804080f06060a0e06010203120406020904060803090a150903150c0f030b010f0e01031404080301081203040c050f0103020f0a030b150c0a0209060315070315090c 79
    0x1c020000d101c042440304c1403200031002002146c0250741158000078040c84080c1c1c503032400b114407075071016035420100320f20b00640e21a25400041441940c1c5005884c08401c0318440c0290350686c0e941c4d070701044a443e1801d140c030450014100c5c03600111300b011f00050000f5042843d40c010481e0030b00340d070650081000e0003056a00040e60380704c541400348004044581d402000c0305103801e40060b101650f112007140c0640702d40f0b0b190750010394a000c51400c05510503500b01c811107400342c2c10075070ba80c04e9800c1c102c9141d00c407040c040c1e8802d925007940d952501c0300c110f2400142c0e00241144140801c28800040e0190701d0f103400b110381c107445645c001d000060058009000d03202058200d02c80005003240c005900d5031080080c41411200c011040c51440f0f0f0900f8030f401044242380d100e51052902001600d846550305038412002001c880104042c07051580d42048182d4050022a031140c0c2c0155000380c070b0121410143c00680410010008008401090103c6690105508035001c2d95092503a04a010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 738757814 1250 738756564 738756611
    0x40c1a0702131d06040501020a0815331602030d09080a0f0f080301060206070207060f021e0a020d1b080a0b04020609030f0105010b0702130b0607021003091a090c01080705030a 77
    0x20a840c5980380c0780c100540030350f00c03081c2400e0000d0422400100d92642212b034680390301001800702e0101003511a0b2801c10400c185030410033341032001480500c200000001081d400409075258010f00740700348140b610700020744403040180110b10006010260000406041d001d410030141200304042e8200f80340c0004800e100030707113914000000414100d80000d12076024202640c05c071103030166201811500c980603403d400e030041e04078841c860f414001d0400c4588485d541c1070151010441d16500180008800100440e100030034100700500852140d40700b00000d00e420700c080c140d407039015a107aa43d003000040c0002c1c031810700411480b0040e1020848031035446c1c1c51700000c00544d40c45074403c44482d045050200e100c1c100107070200034038425030300801001081c060801800c21001d582045807441964a45904269030394481101081c0b0026940003007498641003500c080c24004280d5003405850041e56061050800038050b019a002c000c503036015803501c000081d02c290820098143c81c0250 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 738759064 1250 738757814 738757871
    0xf030a0e10030f0204150e09070912020a0f08070810021806180a0e340503041a010b0d230601050c010608030301090c0801080f06012c040c1a070213 65
    0x20a001ca9013281b00321b001d00c0c074030041c0e85460010750030800410680a10454070500002c8a680c01000744003080d0b20307162142440104281d01c10381e202d4103c7e194481c5150311241050b4404a000c109204040c00140e03990036603020305510301411b115a1400c065548903103507010324400910903e105582102a101c0e951000307045400c45176076003140071038116040d01d400300c1a1500d100a41c20348803e9010100b08008000e40f01c202c1c1c03107190001a102038000600c1a03415050007407800b1500304600d08a40c3c041c0c03004440440e00c512210023401c04a070100045141c0040c03015403000e58581003c120107500034000d03c0c1141da642400d2044c540501a10350084c0c40620001c400440c01001c9034101007400300c0c2075950002c09a90b20022180d4500843e017000a0070f0f0071410041c80350300740e42032043c65004202c04840c00d8000c204c2d40b48000710030088805858149150505001c541010201213002e0901440010300341038480d00010007808510811f8140c80303503608074440c42c0001703c510b207a000d331010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 738760314 1250 738759064 738759067
    0x501180309080a05071511010e0a0c061715030c1f1214060904080408010c020a020415210503210a0c020d14070c0510050415030903120207031701090e0f030a0e10030f02 74
    0x56090656503440340f504100d517080c510bd81d0116401d407083c44e050000307003800711384c100c4551a01e8401d01841741c0825009909809400d11918143d1146450101075066440703d000c601e403030704030000b051046986582482942028825519120f00c15140c540004003180c01c651035440e10f1504980034405d5500490080d428011039002e81c03074001c51042c1c801c1e40295028002818106254043c2d40f540d4000c403980d41e407200190050503541a041d40b0300c550705c69000c0328645043c1d0515280070159a0f80b5079448903640c001041451485400340c80d2150703240e0300040c00c1e10150310130040e010000035140d16900035404075600081c030007005540001082e001c3c0c014202d0040312400102194001e028010403600d444001e2481c4610906c41d014450390180e640320751319403645465002950001034280c0c2007086c4120700d0140b610f41c1d1805d15008205151000070318201c0007501606000c100c1031481c016400a04c00c09251a070004040c2c0d03c01a02100da0b04203480c0840400c0c0c00400c013038480a13800c00d20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 738761564 1250 738760314 738760331
    0x1201060f2708072d080a080a0e030313081009050c06160b0c0306150f0414040207050d020f0f0601030c0603050c0c0607020705010806030109150b0d0501180309080a0507151101 77
    0x34030544c100e0b1030551021505040c80191010307400007000381d2007a80e5450b44020654000300f5005800707020441c506140c59440f9074607a1000928503040400c00036103081c0b0500c420051010100401900a00390500c180801c03c0551200e41d02c071503c16040750b00590000980c1030502140403900c41f44280d100142c032680c1d0030a446804041d4100300c0b5084c0c00780d03040600c1401e03444c503110140c8200350380c115000340c9060305246000c482d05025109890b009a020702114000840500c1305100791400b95000340b21805025080b189028074124a45040390000c0b07005102040c50300c1c405c00e007a01d60301d0401280075116072076591654070801c40b0296a6010384010f20031100c0d80800c000003240d600b40d840c0e00b255121002050f00300c1d01d48240050449402100381c0035203010381d8101440000c00200300c458004055251542500d29080c0d02540c1d03040c0c0180c0394001c05402c40150000f6000000051880a00545d02c50ba501c9005000b0301d03285540039144010322a224629500141d0b40000090080c1e00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 738762814 1250 738761564 738761579
    0x5061207080a03260c18120a0209330a1a0c0601211211010c031e020901020a030c0203120408030a0f02030a0c06230c1201060f270807 59
    0x6002481100003c3d40e00070b04114050b1004d107a111940902d405004075901c0b0009078620700d0b40081072618004010903034248855841d54040894000c14001500f46400f01c0c0c410444268401012454801123000240c2001e0000c05003a06280d020080c3c036041d801104030010300101019032106016800d19003489094030700c10380c064494a074071401203030b003540d0b00c0e0f400c0d406d5250f0592182050140e0b0007040340010074200b006810380310a0500340800c1341044012160b0075610aa1110004203445d981c003412031021203400e400b40d0010042c0b08506015500e0300003921110340c13038409001c00003040e0b898001e541d4240500c00e00401c0d100310540c0d840e0f40e500358054803508055244000f003291203e00300c41d0b05001100325001d010725030fa20486115950742c0d42000421440342c1c500901243c4a00c0c1c085445006480907000d5080901c0d02615025030a00e54028250140c101608010a100d50310b40041e0300000a030417000e036012540c441508040c0d10010100641c1e5101445900c034000000403841c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 738764064 1250 738762814 738762823
    0x12020c10090c050409050a1e020913020d06181a01080601330807021014010b0a020705090103081308010b06030c0c0f10050106030b03062707080a080a030c0e030d030506120708 77
    0x45125840070b500d1000040e00c0002c01c01107000010750030454840004071182c402f0402c0c80c2080d48024200d03850b80a103900d4071000ca59002520246d11040e0008001c180081d0300100c986041d0400f03101c142e40c2d0b04040409480e8074041c400c410f9203a65140600c499400c00e0700c004c2502501140c861651410081e40050080c5001d4a09001500500003050507002c09800762a0200c001c400388076100340d18014544038640d000d001c0d50002c500500b140031546070350b0085c550b4000c50140840c6a217030680d03041d80b00b5440005038410010303a85424412102a2079240c140d07a171001405000f2500d4012004d015814003201d0840c6056900031a10b0741c04e4191f04550003e8141c91060380c00300480e81c015001e1660b50002a203100c2280c5115440c1c29005412401507106000c65000a0b5580c1c4c5507a281e24510300011204d0403940c10b90301088540b8465071511580b040501c080c0b805074180310245001c692110070301c3c1119000c144e203800000750345403910180c0d0804890b11104079041e0594684905896 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 738765314 1250 738764064 738764083
    0x30a05040c080a020d020603101d01030b010b120103081b010c030e0d02030703210b03071203080f0c120c04050a0902040311060327070f140112020c10090c05040905 72
    0xc25600007800b041205000a92407840c503800740404120582c150200900f0b90802001a00300038000740b008107240948500000c484621130740c110360325505614252810940581140c001035000740004000003170030031010f5044079040048640c0c0e070300302d40d07242415901c081c82140c201036003005205000c40346c1c5903019482c48803c2000351803440b036008000726105e1103020405400640000000e400c212901c052303d03a5820381c8080c00040c0d0300301400100382001c5880d40000014018a059030342455040102283d0122095500e0090b901d0304000d201c081d8003c800001422001103800102181c91503411280500b2000b1304400b0010355a07807442e0040d5000d80400c441020248900340c0481c10710f40146c82c041d000c4041c9807000050116903029000c007001560501d20b1050b0400096007000c01c000c00b2000c0d1205d4981c162040e01c4810002d011900708800941c21140304000c00f4000600200c0e00b02144410407101244007103031030401d454904002d800c43ea138445d00c0d0010b003004114001903461203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 738766564 1250 738765314 738765323
    0x3070521060a0b040609090518010c02060406060807030308071101141501021203130f081e04031b240203070507080616030603150504081b010b01110724050f030a0504 73
    0x10056103a60340b0f40b54a001e0f500c0f82801080b2070400501c85040780750401030348420815030015880d8222400f03103003552940381d4210090780001c800d000c1440001d01401d406840d51a0040c4503091031907a008221041c010304900800041c103031a81903044c001c0d001080e80b1304198690030348504003a070b07454200b18118103003240544102c094001e07400c61440260f034841c0b0700c004180c855001480e1035a0300c0202401c03000b20740100040141c01c1c1d10041c20b10081c141c40d031444e8070b021303116415880c010380391150150b41c0c90321184007a43c042101c800303228401040c80550310170010b4501010300040e881c500032810005c0140c054100003140004001503101e20a6100d8100600036045014007035040b64200c1c00b001c0e09a040c0d800d40030300c1441c0341c1d41190360000d204800300c0d85000071444101c01d69070301245c4250100c2c1d440310484883c66034460f11460241d01c84101404000d2f01e0134512100e0f41000d02d514514041d160b00c0c0c031010300750042054070000b410000d910350b038a00d0000d00f000018042224100e0b03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 738767814 1250 738766564 738766579
    0x50102160804051201270201090b0f04050f010e0d02040c0201140109020c07050a06020709090206071e030e030102090f10051b010c1d061c0b0307090e300307052106 72
    0x140d2200140900220301c160140c6d03442c084207480045110501c401c0c001a814003002c0580011035403014070040002c0c00280c140746031a02c3c28101044010800d210800c3c0c1005848901204183d49000e2070041959044400040c0020050405c0c3c0c00b4000c0d9034604003d003202c0c0741c0009458041e640003403a039112807000703991200c2d440380b08003c600703481c500507000140d0001d207051040115a6108100090000b0320150802e00182e031001000101c501240b581c82d0901c2d2416030030150000c20010703401c0b40450080d0704240401021502e88100f955600b8131034044030f020600d00502800031175401c4085990441c0404621300b44442c06810888004c20000f1103000200c5060110003400007025030b0010107440c504a2090603030401c05420a40e030004843d96458044016a000c00041c4014400042c020440c0410b00b0800c0d414401c291102c600021310381c16210318a10b04255402d00855205191640c0700e0b160803000f110140aa05020720b01d81c41203a10001038510032106562013002c0840c0e444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 738769064 1250 738767814 738767839
    0xc03060604090b070807030f18050d030c1409040209040203040b01030b0f01060c06021b0d030c030513080306090414010c030b10180b18090a060f0e091905010216080405 74
    0x100b25480018042c141d42e000e10040f560301c6205203001508840145004035003a8040e42000045500036502a940c40803540d181c1d40401c581481120010b20880c142041108030faa900501a0b40348054900381c0300c240002d006603160750b29410341d46901c801070300c11900e91520345404800c004c800e0000341c42c0c940e9a00c00091003040140c5200341a682c1550303914000106582d520301c040d4000c4000d200003102070034428030b00307524200a1000040856600030030491384003131015040b140094081a0510014204030010840c0807003100d81040090343c28007600d990358104030000c03601d9900021120f5081920b40c221680d41500500c8079000c1c1142e4614500f0810700003910054a500313001d0b601007030a11400c211140c8040f020f410080c800e00f0703840180b04901d0002415180048070001c070300f80e940300402d001000d00031590101502c0d650500414a08020440507510078983c10b406003100a280940b404105c1e081d0182c0704203c4006600310810a014506400c00750024003445000b900c891184 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 738770314 1250 738769064 738769069
    0x2030f010c120b0d052b05090a050f1306092702010207060f0212030103050607030b0a03081c0b031507030b190302090601090e090a03021623040f0e0c030606 69
    0x110510509242c882d84001001c000d100d002511518034210341c4032031407040d03801c045203040c016034900c1155208403046062548014440c0b60039844200403c01c1000c0c014598035440c0e0307a400c8000d8640844a4003005506540040d9201041c1c20090b8030031410041c1c0080c42d0b00194000307850400d10b146680e548401c0d03481035441c51004007034003e801640084d00800c20b007801070300191003041040c81610381080382c02108480683c82a40308860692140d0100b142c45031340b602c10f494850500311030341c4172001d00d96100d80d0b0160203041c445605803460f18050720185c0f051a844407040101c0581a114001c1e40d229038069201381c03c80d14840480d082c031501e07807010310b051801407801070b01c0c3c500c40c4145a800c2d40c0a000102c04000c0060303040c410b1002000c84d40e01c110986043c442c10850300209001e01b0f00d858001d0403d804048400052035000c5014001d00c54107200d180944440c84425024800043d00001c0182001c410711144803442e010030030a2544002c140a400d54000b54110344558465209 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 738771564 1250 738770314 738770321
    0x40602040b04171b1c0507120c050307080c03121303140d030f0b030a170d1b11030307170406060302190303180b0417030c120a030e070605030106030f02070510050402030f01 76
    0xe046500c0140b0791091880017907125100d22015010300c2c2151315154550014204a02c1d00c2041914030b01640201007180746010004000070301003100140803e0340d442070109a0355103406201034110100845d40e29881d00c02c40d0741c1c0e000115000000810b02010814030a92180f490b100c0e4900000c1c00e0a8420700711118500842c1a40710380a4014299182c0e9619101910030031040c6d40c00008004200000301a82e40380211907130040709040d6070707100d4070365000080c10703440b81030b52512038580052003000790558020f8044100075142c0c1003007804580d1580b0703101005000c1508000c2d40201d5034010002c0182501c4c1c500404d40340f082c0c031481c081c0111034aa00b14101454420790603480e80400c0207100000d0220490030720341c118001104c2c01c20a411145605000c00c0040e00d000301031011a05d24010f03a40b6004600e501c1d00b0820140c56002e050600003042c82c84140251300615446481342c0e45000241d90480d118140c100094840c59440f081248018010648080e8401e105503440c15070b08030380611 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 738772814 1250 738771564 738771613
    0x507030506030c040b040f0504060e1009030804022e1e02070806040f020d06050103110f0f0a030318180209041d0304060806120303130209070c03080f040602040b0417 73
    0x6006100c01520b078410840175244201c0e049402986500300b001020405c0c1c004c040c021489a01c000c2a00c900100c4010325080070130042c02c0391182801e601130082504200c0707164002d60141d80e22000440d0b02014072140800f60b0521084041140c001c1c101c00690005d030f0120041207606d9100354618100c5002ca0782e41403540104101d64102902150009102e4540441c4180c40074000a20303da4158582c07200b00d404c242c2c026200441015a01c515078540080502d01201e4116003001c1030b411400c000c1840c003012800024148826110382c0b03480d001401d03058400400e200703000501d101160103003c030040c0d003100b00a18080c0782003505c0e4080e050340e4100c1e00000c00e51890011812306141c841d049072825005010b2a81011070038000c01d00c842010b0008510078403640a010000000794418071444240082280003000340100f210350010764001c200c0350700706506400756089031301c0724208100244650340c03054801c0c1d80000350010300d207108100c0c07000c0101c910800b44da0b006052820b901040e504000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 738774064 1250 738772814 738772819
    0x609071a1c0203180a0c0312030203040506060d03121a100804080a121b0203180603160c080c060702070608090706050f181309050105090a03140a0e0a0f090507030506 73
    0x126038995030001c650240d03500a07a414040e4402440d0303000f40e18140300c4840d109560344801480d050003403081e07680300241203004074a021441c2d440c0c9038542d01d8481d000580740610130b404203600a0700b40761203091058401c581000d0104001e406a1010720104101101030078014900d01c2011110280608030300e0748196081118285807402122080310300364151224011203d9803920341580300b00c002c081c440310010141d002940d03229251174401050f49511500a88200070030420418079942042410300c00c244075040c1440031090f1490090740b00d000c0c400002d1010b100d00020464034550000d041d0007181c8c0c10761204a821380b90b00f0012a03c511490140c840400c00401c564802c03a06c5140040000000325401901d202c041880005c01400c98a100c2a18070358542c5c002c5802c0c40780a200d5142c101c4a013400905441d00c02d95030142103100743c0b90640d01c0041020407101000b5000b0801b50109500c01800b00b000740da2680c0f00d04840051602580c684030341b505001691450080c130400d402081c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 738775314 1250 738774064 738774097
    0x102060c09060717040b03042411090d1406070c02010f020a0b06010813051b0a0609030b010311060d0f0c03051f05040c030605031c020c030a080403020415080609071a 73
    0x51351a07103083c1c4602c07a1801e80503200208000944103020b4030245001c1d5101c0d060754044c01c0e0032070400e425200c5812003003501e01e5182c000810032a00c42e181c101e441009060b920740480d403010b820850b129280015241600740600c00410411592040310209071034400d80300d284900170b045004a0341c420025074001c0a000c0e052011640310f40c01850010b6010441e0025001c140d2080c1d81e8076404c3c0465040349840d1081c6034031069540c1e2038032a4044014140524049092502c0c50b100c108400342c06200c0580a5429034820307503080c0d1141011500c0c00403801c181030180b01d91060101b0003d0404008003130020b0700d0030000c24540160451440c50940582e80b42169150401041000801e1071410000c1410365840c4001000e0b1014840c040243c80c83c50780a4040b03000c00078003c2d00703000c81d03400050b1198000240c0074001504c0c2c0c0064900341e940603200040d80f0700240c900003943e05050f4000e046a40304e000c041000844002900d107090781d400e0312038101c91003c0302d003c4810501850076132401e41400b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 738776564 1250 738775314 738775327
    0x403030507020609042c160905040203070b0309060a110a0806040b011e02030c07061b060b04090b0415060512100f090c0b03071e0c15090209150102060c0906 69
    0xc9240a88800c038001004546441540400201240c489405a54000f5080285140c899600322007148080190300060b1044035111034602c4090706540c0038401604d43d462002c01c040d900e0800240000e0702142050640e6414407034a06965440304071854000c4070300340b413000810031aa90b0701b654400c51f0700d80c90b000c0c2280c0300c0800304809004050400c504110900f2604260580c00e0483c004070680c2d1074010307590710520802c06a08100440d04807030140f00702d910900e003c00092011220116030030210000314000f000000038064608098003600007001032050006210715000d16100c0b05c08512020054165a5400c1c4803000810580c440916008168150340743d1400f500055600c809440e00021030b0403860f9940308002009400c0010005004000c2280302034000308503194080c0150b000003c1c0034582000104001890300006100c1b0103201505111001c1c15040b00900d2903004059110794940007004104a84122007014014450300022504020044048030501c00e805072a1030710b00713130 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 738777814 1250 738776564 738776567
    0x30a0b041a071d0d0210030b15130e060306130816051c020c01020f061906030b0c0702090f1302011d040e1b011814060d0e03090406080c0a03031409060d0c03050c0f040303 75
    0xe4908c2000d410030240100800044500c40003000a5081d0360f00c001b66450801e101750302c25240061009010360f010a00340f00c000e40c0d5a0441c142007681c0306844a07a40c4074030840003e9020500f020007402807003014200000c1002100f6010540c400507400c640000449000480c1d4407c400b01480720140c00c107101081085191801c803c00c0c80c1c0c484040450a00e03a070ba6a80111464201c400710b0f07074000003007040300447c90060405500403800150004450a00b9031004c00c0a09503100c00a0610644040e0004a120543c04c1c1e00c40c0054010000c00040c06001c90700e54582402040c48000700b1a051040b1a40b9801100751082218002520701032031820841241d000b0500a89400d40c010820f014100030000389001d2070910562000c050364807004a1070500060b22250742002000e41c21410140b9041d4807080c1020044030b40500e80a4485101c0b240480043d20440c0c0ba201e40144000641c00c2018015420108003c0c81c40c1e9000c12144c1d0340c040d0506458019201803420700407040100b0008a03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 738779064 1250 738777814 738777821
    0x10f0c081614180a15080f090309040c031b080901060801110405100504050303070c080105010f05100c03211401060806150c0106170a050c01030b030a0b041a071d0d021003 75
    0x1074421551904188103c00d0000e0000d00f0319038000100050102044810a54001d8089411844540c1080d9090400c5908240c40e4090159054001d03565060301c620954800c0c1c020600c078400b6803500802d0060702000c000c1c03200c0c0085071900803560800c00c00282400c0d05105191411054403203190030700342080200a01041030080e0182082001e1202082680e000d02c000d1070304511518002e2561840c0c54880703425510164801880c10710f80000400c000c1c0c407400b0407140340c0c0b1001c1c90b0003d8102d40c40c0c83c00366803101c0009218032240250b9000244800c0040d4015405203121200c0306030b80d6039070b0714412265508101c075010b8019a103040440442c1e070f8903002030300300343c030f4102c002042c0c1603111030040e10724802440950300d269010b109040180403061200c805401d030b080c40d040c01a0326020000c240e4800001c5001015003620030000f4060001c03003103600070052120ba40f20303011401d00d8075000f00f41c4201c4e1140c022040445156245d6245007070f0031002c1040764050845c401008000c4410b5006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 738780314 1250 738779064 738779077
    0xa11011a0f0f040e01020c0307050c0306010b120910051815270120040302090a06050a15140c2a090103150b370e0a05060111010f0c081614 61
    0x102e41c0f40c00c4030328044d01c403e0018000048012000750f407201c0050415520b0051100b06e824040d41042c0f0042c000400b03c0d40494a418800e20036080700740e00c60418181c680103c02c0742190388149880f00b40132003218008000d10001c542002120b00000003004015611141500e8007407a01c200c0041000d184c2154407100380c030707011081c0000541c40304044450780c0307185a4081e074262007000000d02441103140000520350456440302d4100040c0e801d0001185000b0f100b80074101421003190251500d082c410013503001c1c01c02a41018a07142c40750400003a541e130400403040206a2140308014120740d620007007003041000006e0001d107150746107891b01c1c00c1e444d4501018074292034840c45009403607205d990701d00d0081d00c1c0c00c05080801054590494074846003611002030a142106c1041082010500c00300f90407008891000450351503610041e94050604400c1d5142c6501b02016494103c90f6079000c0383c0c1900031906c91840039a02c1c1000c0c00d6005407a1040d99001c40c0e40d995030a82c0300e01d00c1d071025011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 738781564 1250 738780314 738780319
    0x603060a0507170403020703020103050a050f0705090a0807090f0615020307120e1809070b07030c1e170903120702010f0f18030506150118030308040204110a11011a0f0f 74
    0x120f403085600455568182201c0c107401503845a10300701f0865a041c4103165010040c503104000500300b042c0442c00d22000070b042c42042080c00300e1030b501c0965917008140002c10141085405083e51087e021002d08400e00004480619010002801400781c2e8940b00c02c0079101d03406589000f48a0740c030350841e0041035a2800030040c000740c1c6000386454420040e0079903a054078104896240c4007040ca407401c100c503044031903662811f110100000b0b4000c1c0ba541d20103a400002155224018581c140320304100c040c01030300803904901580d110201083c010041120140c00303440850f10300d940c0c1c001180c0f2900c10000d0025040c50122002e0501c1502020700c99040c900c0c0c010350003001c0300031144d03004035250410f83e01504a20184102c074003107084c09a02e082c4080c02c102009000c824941600d42c034061102400780600c03080020115070791544141285002c4045003a1a507840c890002e01b402c40d078030841641c96103443d103540241400450b03100078820000b0f10000310f004680042c00841d1800841954 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 738782814 1250 738781564 738781577
    0x603021305060f1b010c1407060b030613050d390203010507050c070e0408190302090d0807031b021309150504050d080109060e150607060e060a0b090603060a0507 71
    0x8042c1d9621000b84000c44180c810345885030040c9507803030700004078600200382031783c50022200c03081500b00750003022540710301c009951500c24071b0500754060030b001c0e0642503160042c68104040c10300e804000c441c400c2e01440813201c903000081800e803010000944043e08070502601c00e00303076602000c43d00c00217034040060344848454036035010909440c81503484101249012900d0424074404006040041502140b8040141810f4a0f80d401500c07600300d0514070340031209514003400b03021f0b0301110005040501044010007483c1846141500451400c400055041440305100e220340042c1d20380840c1c000b03280c2043e60120810000041c04040811a0a4059040c588407042c1c06841100e00c00d038042e001501051100000c024040881604078001103450084d040c04071582407600c580d840048010119240390000340000e556010b0880b00401050500e40c8002c03664401013100360059041c00c01c144200c080304010404070303c40498000c0d403d61b10410000398403040c140c1002d50410b60609140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 738784064 1250 738782814 738782819
    0x513051002011e0e0118120305040201020a050d08040c0501020105070e040c02160e090d110705190e07030609060602030a02031e0f071a0a0911101103040e010f05040507050406030213 80
    0x1548403a2400300b0444540d511383c0c0140e8020001e000703220b0184d07111344a0b2406002182c3d140031104d0b2039058410f0415568000003421a4000c000d04880581c110701180c210300780c1f0304401003000b04101c804a070010212440041c082d4014000c1e180600420740301d43c01c2e00b244020502000746043d05d402d0085110b6114103800000100700c402c409000010030b103600314500851820300e418040520102040fa1400341c12a20000200b0000700303070341d0101c07100700d100369041c030441c40c205000d41c00070001d56a181081c05282d0380c1640c801c908682d82c03040140300d110760310f610a03a103900850b111400960020001440f041c004132001c6001200e031443d1640c1484030960714405160012102240c080c2500d10703104145045100313a0940c003035040ba20070300400401e81d84100c1070240401c10320703001d40910140b280d025405807004001c5481c040d01101c0d00c0d01d940303045004829000307115a014070081c100010806090078005c181c49407a41d5100c0301e243c2807511404400a5124058040c0d005c030110002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 738785314 1250 738784064 738784091
    0x50a0201030c0e040609020d0e0705010c0b04060204030b180606060c030403260c030d0b06130603050703092f060c0309090a060b040b0304230706050c1006080a0c06051305100201 78
    0x204006482010801a208c540d0506164200c07182c1440000c51548002130070021603a01c801050161a40040245080d0711140b03803900180c050f0b80c10040c5440c1a220411049030140010387c8523a9500c40119400c5480343c5003401000e04c250f41a5031000e400030003050002c1100040e00c449002a140e001d1008081058000403860300808142d065a400028222017580c3c0f0350301881e403240344104c41c075522380301c5400300e80200409144107210525444800192400d40603901603e1003540045000b01440c000700b5034100141040d80c00c0c1062114684179810640c00c0c0f4600340d030343e440000c0c0025450000007108004405600904807034205844940100d500c0d01c1c3c00003d0801400d0100d10aa04c3e418036241c143c81101504001d4640b040c42016440346000d8001250001c031980341c20065681d11100c41c00270708041c5021990310303442e03003484800900740c280000c030305003124001c0c0e04038522651100030441d82072140000100340c1d039072103400c02d020074917003241e40000c40c45d13440c00002039150032a0300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 738786564 1250 738785314 738785321
    0x1009030f0803010f090b031f090b09010c0908060411090907181517070e1305070803041502060108211b0a060f060303080a020d0b13050613050103050a0201030c0e04 72
    0x10111507074103000c00100140321034040b00c00f020f4880c4000c01d20100c0c4c4a000420f03541c640c03030803002c0d182031920002c840c103031040d03130344543c0301641c1191141140345420340015000c0c0c02c1c440c00d207400040c81c81340300291555000c40c80c5809076034042d50404c681030103030040005c0d200002e0100c100c14000c0c2c01d40000c41d4040c0a8032064036a86031600440c3c2096028a51549840c0c144d010702c828140300000a8641c0001062020641c2c00045071024a070711002006120f0454000d03000b40648a00b45011423103c10001c0603200b2113101d00783d4030800d00480402242c4a603000e2040d0f400360707400340100d40540044512600842030381140b00d5414000408401c44043d071181002007400d420910b0401c041c401c890050601c2e99400440034002d851079640c0003420254010540388100380c0c0450105406002d0f9000801210801480b5070412411019458001e100517240a0710401c0741d100d502c000c6000c00c2c01154100ca801c1009849a804d050b00194041c00d002032201d410003c81400c1c251035580c0300d10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 738787814 1250 738786564 738786593
    0x50d0b041803080115050306010804150209100e030606061c020c010f0207030e01140a090626010f170706080103020f0a0e010810051e06150c07060806090f06030606100903 75
    0x3d80d104581d51400000307100304a1248000300c104a001c108000a40c5d0300b20280d260020352002a0090007404109180003c0c001c80c4503e0b90301400d0107003000212a0301c0029402013507001c41c1a61420745a91040107120302ca0710540d9810300c45036003607040e4001c2495025200c0107080000100e08160106d00301d00482e448030340220007007691070100001c00d5078000300200e007890b10321703207071a252001003d8064260460340c810542000103400c12a010b441d8507410304840881f050828160950310b841441c900700059005c0d42100c01d5440c3c03402c0c2c2c200040050204112030494403460b00590a43d024400150184400d43d900b0075038296002034116140d1480d640205400c0002e025451031a40200702581c00260411400e1505040700e00780840000043e5174100d0022070301c008900380480c17131258480c095210315030014054000c000640755000081144140c004441f030f500c0585d94542e51400404095401603016800030b00085c010303042c03044080c3c912140505082c0000f503944d41e102500055400f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 738789064 1250 738787814 738787817
    0x105060f0607061820010f0813020102070b0f1c020f04060327050f0d450807030309060f0c03030e010605061c0c2d09080316110d03050d0b041803 64
    0x4000b017401000480a46540240742403038040c2071070f60b120300002c00920018103005800c1595500110845e8020400400200100e0310201d80300c2c56003141c60007103a040394609003c4040480200000c07020144210b03030100907124a1241080c0c100103088004254024440c66211030001020156140b81c48101c50302e20702c00c0000b80b40312800f190b21a414003402004070424042c4000d00c1e043c80301229024441c214040071685c80f01e07101445c1e00d84090000c591070000c0c0c01c081000e401300e131005e404500407017540c2c0170b61601078042c2c0d07890300c044840220f03a040841c001040f80ba078005c0000c0c0319400c5040348160000000c540c80b5190720004010360301c101c00e0b821400c0e8080100074081c3e1072500401d660350172141044a040303407559090407401090703126401a000d0300300c1090307042d550281b03881102818003003048a46408240803c640403005450b0142c81040c070910b5980345a140c8080750145d115411381e140380c2001a05c15046001d440a00c80c0303d58059107a807859008030891440c0c0c0c11010307019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 738790314 1250 738789064 738789083
    0x1f0612060b0a05010903020915030307020a080a0b0618071110020c03120c12042904110406150e0411190503010f1410110c0603010807080f0105060f06070618 69
    0x1101c0070012144016401039060016000e0308201607a18051642d40c070191003001000002686d01c00a03041d80b1a50900943c010708940f80495001b500250461255100300f0402e102074a503d810000c0002020203200707408100280002d075007500c00d0204c4480f407510320048605100d6402c075024140c4c1c01031244810f1940c4085080c501c0d09880461294200901910b614542483c2c01d07046090010b0050002c4c105191152592840302450450030b0865204120005801d0130680740289240803440b034850b104600b01040401c5060f140110740d0804000c540715010244003031002d02001c2c101445961485034024040c8442100c0808403c01c1250b48a594444c0c1c1d039030500c80c0c1d44040e840f0b1a00301020151480c20040f541e91540c138180728900006050150b40014040400d03407405030f03010482e43d0400b8002c400091200b00004401080c3d841000c1500c40d18550040718500b2183c0403101c09600000c00d2a21422a04000b0010a111401294040380342d038800c05928a030030f9003100341201d0340c400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 738791564 1250 738790314 738790331
    0xb01050d150f0f050c04080d0f11030703030506010314010f060c021201021201061b08033103021b0111070905042102070608090a0b0417220501031d1f061206 69
    0x11075103e40c81d449131780311000b1402c0c141041d030840d0303582910018020500801e81100426180034064092500f03421308201c2c0d40e01c038210701c3c2c010045e14058600c2c6000c2420300d00d001a410043e406018161802400c5104085103030010884404103030440503a0080da0fa0160954814030038001000d60314012104800346503d8014024440c8120750700d9441c9030140d000720480015500c5003140c2d00002440240d124518441140b0495105080c03a800075001c42e8040001c2015004605155884c8041d030007071005c254807d006540c2c03c0c0300c010401059030480e0030709018101580e446590841d0142c13100c08103000417043c1c1c2950310f035a07110510001d03a105003c10400140d100c503210b41d00944903005411000b400d43c0c1d65160038100a800141200311415281c0502041001a208025404002061702c207903000322004c900c5426000d5640000e0802800036001c290305043d540700d1110345c4008003080350b02c09203000d8680399000402100140c5609002881d00ca0040400d0300c458044c40d40040c4066 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 738792814 1250 738791564 738791591
    0xc130e1602030c100531020112060308030118091403071209080c040c110102180a0503122203081c0b090105010c08070204090813060305070c0b01050d150f 68
    0x1110540c08030119407082000e030452203000b04606035600060000450240c4410a0710380c0300c0280c0d29094000108000303803290364104404001e6005074000c1c0c0303881079542c0381682c0d482c056504500016000240c00c10042107401c124a03003c0300c00c00307495940010040c50650300c840c200002c044044501ba80046a504280004440210440c024a007080140240380c00d01c0c440d110444508224070039640d0b1031280e034020380642c0c0e40000641c0c3c1e0030f0085560340a50b485d0b10220302040d0b0141030183c0510360001c03805e410300190780058403504010312030600c8040c01902c18802c3c0c2010005103140400480080011442d10241602a1102491a500001800d070803801c44000c1620148030700c00399801009166044000007060315000581c180d5200301301e0010bc2d014191810008012540000d003c28444120140c01d2045c1c80255400b4006502c1d540400c071401d6007000301c081d25600f640e400400c0546003002c0c0c4143c4043c030031902e074140d0010440c101011550010031045855480712031190041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 738794064 1250 738792814 738792841
    0xb070804090504080301150c030c021309080a02011d010903022a030709023a24030501240302090105130905010e0607090501090315200d021e0c0d05030c130e 69
    0x4100740391500f08220a928014015240ac44002c1c1c0185a14514610b034034105420190150f504140002e55907840e450300240200540c040341e060304004903040840208041c0929204207426a00600d0000030505201c0d0140c140750b02d154148030961040b41c1e0041e01d041c44003d00400e11100010380340d40c100c0185d2040e020329040c503200c1c0c0003102410035400049644c601096040001800506400e09031010036048030301e91407048500c00c880382c0000410005420200010084400d4141c48801041c81d2803003140907800700030360000e0001c0041c00a82403454508840e400084004070b81000c00e5104d540c01c407400301b00030b00030035080b4008010741c041d00904200d000301802c2c60850b00c0103245803296042c92a820001144540e241c50210b4401d0760381c0701a0303001f142c001c00c40c00c0365615103104090009500c8504461400c0464060300340219102e0304c11343c0e42c1c003803101002d4411340004483c110f40d0b55000516003030603020300340102001c0042c075050f8040078186001041c1030a040c84046846032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 738795314 1250 738794064 738794099
    0x30c020111010504050703060203060d0204050f071e09030303090c0b22290702040e060c0703080a020301050105090904021909050a060909081e09040f051609050a0b070804090504080301 81
    0x4983c10081480001000000e40b4800c60390003210043e1240c581a000a0283d42013040196102c0c0c140014444016826043c0030f0041060b0348500b601c004040541104040030000607002049a220003000440d00035084050158854419101040d0301c4284600c0550030885400c5142c10b07600e020b1148a000303420300a001342c0303070504110341d0784480070700741e401c0e50900395092142c0aa0b010404004545454116802a02c032100a55510b032414800c00c5065411820095001031344001c049a508002403085074103072101030791690300e8070100c801400405000078000326001940e03188080c0e40c0d00440020400904400c05e008204c60918646020907194031f500910030452030032400c600007a44580480305240c08510302d1030843c0b81003040c04041030141051080c2c025041001e040909200c1d94041c503c19228915055400032041c00121540708060084540040002c0010302134048000e0180c980c00d44a51000381ca080e8940010340c040d20015141200c000001100600001e01c02202c180700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 738796564 1250 738795314 738795347
    0x33180203010b010e030c1c050f0607030501060905090a0e1005150a0801060e1f0b0a050a17062404030f1202070e2401020327010e0108010e0106080702070f03030c0201 73
    0x32440b5280b40004c3e111b4400d083d40d20f1144594941841c41140201400340b80b054211007034418008211014607240c01080303480d00f0001c2d1909001191705409440d0210030768502401103042551180300c424002e1040c00c030307507140c28131035607440f5007020084d8040c6610039150f043c072903408840c041040c4134109000e600040c2903070341000000e01601ba414101240e104080d0b021100417071569011402014406070441001950f0005650308100d800c4001041015080c1d55800108135200c4039440c00e10310300fa540207900001945a4242d240c04042c4a03400d04043d83c60713010f10b42541c0396150406c50f2b202080440e0391740f0b1500d02401d4003d0301802410008d11039004800104d1421100696825480304140384a441c0280c1030300030181d1082041ea403550740040010304140098500c000c030500c10a90b03096000030311065080502d54810aa202d040b41d240c40c3c0c4c00078843e424102c00b55002040204000d045101c0c1c00f400007a10505440214008c0d4001c0e1103910300300704140001030441a0b83d841d01003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 738797814 1250 738796564 738796577
    0x61202031303260406060e060609011202130b160b010f0308160822090f0e1c0212120a0615050304121e031a0108010333180203010b01 59
    0x4084140d018551111540b500c0c0110485064004900304a807000c0a81c2503401c8048003040b04006140c0d20507401da404e940890b220564809040181d1486030042d10790000313903170122070000d0080fa500540880f42404106d40c809a48410100352a070700304036045002001000141810f001d240d10141d030240401004a800342421912604000c1c861074144402d01e401d150b100900b4421184113036404507500e004803c21180444850180c070462a004199115181c89420394048080d0b105507030400c01c0741806003090a0001280d0546d4441140380310040d8012840d2180c5122407400c0144200c0c400503144004174204100c9580455020340c10180c0309122156030710719040c1e0880309982e4010750084004406000d20542125040c054611020340b050301d81e045402c40076050740259104050f06090f118840d00c4503001184c0f100802e02c005045140c20000d20342c8100b4404281e61585242d0020498101c0680401e800c00c50f50b110b03414040c40e006500709041103140c2800380800a030000d02e02403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 738799064 1250 738797814 738797821
    0x90f0b01080712080d060509070e040501150e0405060d1b030c1e1503060519081212010506030408090307061d04090c051201060b130314010221090a0b07020706120203 73
    0x507a6003580c80304013810008000c40e4075920034420303810140c007928025142c00301900b807500000e00ba00c40c412081520590a0000209100382d44026000d059001075840b4000c065a52050000034000a0400e54010241c2c1155102040d60500c00e0201c042240502c5590303545503003401c1003120110b400c1156020002c0d20544903e00701030b40150255840c0ca404c501d00305180450941c01041c950f844507030000214410121000d20f4078541070115010a815654070244030700030269144038003003a40a54143d1280103000038280700b405154047d104115840c5408100b800081ca8580a588000001604640000c0038602c1440c20314000100c00c2d5410b0201c4405680d81c2e1800e61030b10300440c1e0149003400d041580b0020309400c1580240542c11100d5038800a210100c41e184100e80000e0340d052860b42e0009100450501c203c074184824150040c030003403c4010000c3c01d100010740b100c103a6104420018001ca00f09800c882e014084d0f03071300246020380c6000806001c81707400c2d0041144252052081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 738800314 1250 738799064 738799079
    0x13140d0e041d060718050603091c23070c0e090d140717090405220f15020a0207080606040612140f190203070e013204090f0b010807 58
    0x25420003039021907022440600d1200a200c414001e030550111600c1507001340456103070000c05114100c41c6041e0302070700d500c1d142c0c82030120340d01c020b8401074010f40c4040b40201080b0480e01078966101024a4001820b905c440714809682c0100c801807013103180d0008002c400c011000300c6036001007030900c401103c1ca01e0206180ca881c1c075170307909000b41072002c3d9119541c056645d48084072003e80e031000900c03201d0f42d400320180506420081e549406a443c0601040b034049050b0890400e403404100450684030860359200940d60004104592000701a01d442e880030600780058844da4009500608034286403411144c50558050001070096181c03039000c1c4003907900014140321554100c20003840d810340c0402c445250101c400d1120311540109108410031a400300a5a00b44034022000c5483d400d84561411070902c40030301c40c684c03910f07090000c5e0f94141c40010071600d80003c8685100b402a440308000300701a0303900010300300d41403044001340c0c0040103400030040c0e015001e0340005003200c6040c20b84 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 738801564 1250 738800314 738800327
    0x11b09240e100e030d09080615061b1c05070308150f090615030403180905070504051c0803131709060418090f1406180303070f090302060313140d 64
    0x814061480b80980407030b040d0003040d20400251000c0d046034111000c0d014000c009040501900c00306025a43c04202c1c0d80c103082c03d2810250303200600c80343c40e1800d00c4902011140705400000c0460103054815640b002c004040d0614101c09519015900c1c04946401131880c41c0c014100e011280c07042c2200031040e11415010503185409a030345200d5908d40000058061449540440c6403400001c104010140e02c0400800000c0380c101c85444120303244c0a001054600071a10680010f105100c00c105502d040c200600301d8800300d0140011402d00e039101c40900750303c01c8848242a40c0c110101d0020030005042e40400407005c90381d181c0c241800c41c0300242c20b41c8210303c140e05c106041c02c181303002204110362200100f198440c0303485d01c000d20589400c007da80212007404106006200010f081441c902c2020301c240504580554910360f142c0c4400e5801503040c12500741044090400800140c030344a000b03500030908480c1021018805184c00801a110806002c034907401900c0142c0d6019000f44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 738802814 1250 738801564 738801587
    0x60717070c050d1d0d0606030201020706021203070305041e061a031b0f1201140a0e0a030f050c030c030d0209030d11060408090d060207030e03070807031a040302011b0924 75
    0x2a0001002080c1c0c8969260940c650078000e5004c1a065a1705040205130303030101d01102e00c00c1c0c095070107890751040c060f61210810705001100344810030000c1c00342842944100d502c28450202000d03031031281110985201d440c10421180d0a55640d031002e03aa192180d021060264120014240032404140094913a00c805458034000d200c00382c0500625550740c400a10903040d04c5000304444800e1b111841c0007164152000070286180c8161003501110201b9040ca40c150503481d10070303c805680f40c00b1a60380e840240f94400c0380c00103100c04501c010041c4001d003240082c4d2403000d61904072510426080c04c00c07945880f424003146031343d0380007104404030b1803079070144d007003a034441e2104050004240881d07400c40d002007600b480000d01c14101038208903100030001e801d5080b50011500e803040982e441709140405802142c80c881c4c044500051a1916640540700b84004502808501c880c0304000340700950040c08138208400620041102c902905584814041d00000a24004102400c6a01c400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 738804064 1250 738802814 738802817
    0x5060114040b0f1b0a0609110603040b060f1309050715230706060906061701080721050a06050412030f060605072003120d0e0309010807180503060717070c050d 70
    0x8a04e110711595450792a40842c0c61503802d0f211030302500d14281c4000c1090441c101d50011100d11f070000a82426010340b48650f603c001040e909460740307c200709009510b0410958005040b03c0310b41140030b01d6002d60882584a04000d0404a00740040c100c8074254011507032080003c8004032004d490725a010080c004050906195522000c6082000242004c1d4100213443c40c04c241c000200b090303105a0500300d90000d50042c41041e6240d100701903c0745088d04c40c9442e5200105054507290140003007039010240714000b154414281590345030181c65003105e043d109102001c5800c0412601402516510701e0701050410040c0c0c00c141c0c014201d07001e00c8001414191145540011109540c2c080c00e0410300010200d406c1d51441854044459101d0074040c11018105a242c010351100002510452081616420b078540d07030f00d0900b1120110031a2a481484040c043d00040c2d0792000e0022600424565a655150b00e540040e00d02501f900603080604102203143e4617004281d011038074046c40f244a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 738805314 1250 738804064 738804067
    0x41508060f1c0f0203011505120703030e10051303050c190620011e0218010516060510030812061008090a060c0908030d060311010504030b16170a05060114040b0f 71
    0x443c2850202c0088000e4001c3d0990710b0a803003c520324500554100480d02c040301e5101c80b11081c0751842e038480c0e04610008020401030020703a0224644030f0504040c1c911245003031420722005401000806c0215070050b102c80c1c00ca0042107105040801c1c40c85200960300c0352011800740382082c01005008080311340092500c05d1241100d1489081d0420a03031011292080100000101e19000003903001410032958001d88101202c400d50290003680e041d002154a00540d40050b0b03201c0c900903290080402c8420340c003e01011000440c01c1000d020010710f40046899a885d081c1c00b4400e2141c0d10045031000d120110302040b42d0b0700e0000510951030380c0c1c8120040f442085039042590303511515000115203010204240070840c61550000c41142d0003000740d2480c2da0100e200550b02031145000181c03403580c44400080c50210640010b034840b80403440c11880c06175034101d00399007003403040d1081080c0640340c401780f003d01c2da480552007208210551104e450280b402e1400400d40c0300e0694032203210f01d070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 738806564 1250 738805314 738805369
    0x90d0f030f0911030601061112281214190c03020415170106050a0207060509030c10030e1006060e01110f030a0512150d1511041508060f 60
    0x11035000921500e51007102441014014946000c0d10f8240700341e440d00078403c3c0000002e00c24812080130501d81d83c91009014040f58504882010f0f1b03006a401e043d100b41d40c1441d6514511041e4850003540c17100740e8a8504071340004910100341c45003e620054600409810702018040c80c1d8034002c50003002010004e2917a010705002d0340603014a501c08080107200340c10440c1111307002900007128007021124110310341c1c0c0b150410360b503074002c140030280103901c0301e1001d0042500900c014031002c0b200900f10f8586001030400201c02c80d854501c0d000000e43c40c3e030100c1040c00c4080065074000c03c240c140911203a410031200030a4a403800d261581001011180b200b28004c0502c055104c005038a000d0303941d6414803002c040d00d00d5000132280403c0328441d01c00180c40d040c1c1a0b904080e01080208205400540794545995991070b41c026070000303030366950484056840f1300004100801d51001464160f00f8500c2c07020b004013000900c0340c3c1c041c00c1400b210800c15641c05203900000601c54500340c0d42d048 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 738807814 1250 738806564 738806567
    0xa0f060305030315011701060e0904140709020d15270204090207080c1501050315041a01031b0914040f08040b1c050601020a15020a050904060e0f0f090d0f 68
    0x25880507126000010511480c00c040341da0705404c0c164284c880b42115a45410f844a0807a001d01c240000662140030380e82082c81d2860240e0707013007801014094000c400039419a030422000f136016890165001030b65200c81001c0c2c1c010300404021814111000f14031741040f566034a6500034107010403001640912030a101782d503040d64040c0c40b00c0f41c02103448810310315203101607034000d508000180c480c0d1040d20510f02104040d1905940e03000d40034003100a9982c480c10082c14019104a415040e8100320084002107101128020b40c001c00c51086112007112461100514a07004080c030542042040f6095190b00c2091075049a4081e81d01c944010290800150a002e00e0300301a0541d8400207220030800c00003254050201e1010004201c940c075150011b917074032809654010241100320032200e080710758690141502c0940d038101640f41400700f42c001403c03030300550091001d0801c10b0003400280199042110390145942c2000c0065007400b0701d48603500c007036030b8080404100300d6003515202c40307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 738809064 1250 738807814 738807821
    0x30807050a02031c0f0b0a0303050901080a0f1a123c0d0815010509010c0b1b12041103070803040e0613050108060610081306090f0203060c0d0c030b06030a0f 69
    0x110124541603282001106803002e01740000b80c181c0d2407030030001c4003450f81c50140a20011030ba4161546450540c40000550704924001c0003280d0640d9541041003034025680030314080b45030700c560701c840c14a400344100b1410000081494042d40c0c801580403041d0360417040924a03580c21800355400480525001710711484508076500322500a14110a0480340c00020440c0178500301c606088448030036034011200e80c000d91845034005450b4140c9840031400d6050034903009003420401021802082c0a4030a9560002220780502c0e0030002c1044140018a04944a2141d0032400350820758a0425a10b03600d00450150b9a4410800000b0940ba0b0790b408618421850310310405000035a51000001d455040c1181c109000700062003c4040d02481008800d2141c2103c2407142c040401e10b40b0b8480c0100708482d8125003d4215803248009070317808001852045000c4416190340d5502c845002c2c0a0759403200c0d0b15001d041c108016142250b0725841980e0703005142d0a0001400c49000b464803010303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 738810314 1250 738809064 738809077
    0x50607020604080715090509060d021e06030c070b0907030b1b09100309060e010c050315010e030303090a0c0806040b0c1810033606020c1e07060e0d030807050a0203 72
    0xa114400c000117964400b22101260441a901da80060b5030b41c90007400a550000c843c850b600030303140300d00c003001854a0070101e148083e5120a400b90b540c04100811203541c0181c070700d181a1040411184108920940001d900c5107080014022491440c6d8038001459805041182050385101d04900c0022420040d1009140000d0001880810070742018008104603035064030f19604140700501403480500442034a0f50b0b00e565650b03e1a07175200820141800740001d1181004603100001c401c1c2d03a4104007550245250350013070000001d007490809440703050345d405440260030070002c01c400b00d655080c1d43e5038010f07002c007a40c0d41c3c0c0702c071820304030040302c405004921350108440c00000b20b441da050340514001c800300354038001c001141c0c0d02c412050a40c0c01d03a00004003076221400c48000340094010704030103d440c40072102c0514a494900d01500d1804550040e554080c04d02000400e500194850003500c058404c6a264050358a0041c10750800030400ba0504c140011144070a51081048804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 738811564 1250 738810314 738810329
    0x109020604090c1806050915130302010e0409020904060209120a080a05070c050d05010c021e0c150405120a030212120703090c08120903070f060f03050703020f070b0a0f0e07050607020604 82
    0xd450f443d500e020301b031038011a841901413030320081310340700b030361182e004807280c03c1021010074040c546164011154541401031841e0800c0d00c42c0c2c801001031300c80d0340c2000e0080b4070503400540c6031018141071109442440203003004a80c0890700b40707808120514101c54650140c0d10b0030a5964045040210b18040280d03c801e81000c07982a1444c28050194130001f860082c9600792071915061907d00d2104a511f07002c10390142d0403040943c0c2080ca003a80d401e451852507460280e09041d60341000503c620502c0010b092107400c03510080d401c140d4140242582c0e0380c11a08418241810000301a0f8411402400d039014903603503600402c240080700c00942e0003082080100c03880ca55200021118a030048008280280315641c80400c0e0815085600410b844c4c8540e10140c001c18543e608070003400c03000e031500040c5942000110340d140041402452041d0080c50900300300d040101d400c6045403240140000c0c00ca00d0607240d100000c00114406007107810841b04a41c80302800d000280c02d9110320b51003081e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 738812814 1250 738811564 738811607
    0x70804140609120a06050105010816030e010e030307120b04090c120302010e120a02010b0901080d2109060501061d0609060c0c090901061e0308030c030705070f230109020604090c 78
    0x1c0d03c03a100041c080b10502e01c100e40c1401584d0f60b40b401503880c010240c0f0010301c071500d045409110a4460b50020b00440c400304000700d0401c20040c5802e081d0b51085c1c4400c0c0021300c0f103035101140c480060050108401d001d6408001507a4240c48801c604001d03809030119204081c1c40d0241894400d40007056104002000d03902d407101c17100b0345c0764050350004211402550070b00e845038500c0d182016841c0e048401c5000038002404070780780d003203800440b8112182408540030b20014100400c40c46500c80d07c0307105007000142035052500c0a0800303001d00d00030044110100410540c00d4071880b081e100e0741142030312090345a580c4000400d0034240c080650f69001120b6404000340383c0e005401000032200c250f5a4049207a0100e03840101512980c00040c0618800b04040f80c4968808001964480c1c09803070075506019403542e9460031408907881c150f03107108034000000c550a00c00700050015802c0078000b080801e01d250f0118800340141d1213204010750b03840319082c80040c0a40381002a520720804c408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 738814064 1250 738812814 738812839
    0x610032409021905120c0705070b0408010903120203091e0c040509010c23270d0606141801150e1206160f020c0904020a0b0a08090c06070804140609 65
    0x24029003107494581d20f070030803040c8940f00940c0100700300c5582c280c42c998a4040e6603200031016200d03038003640048809110b10400029640381320005400134080d541f00105d24043c1d28100104000340038603041c51107a01c10024458a100000303600b40c014405038070700d04003801c280441c6608040a104141b5009070918080185a150660040c2d40003c3e258540021810f681090740c2e400881f840c0201c0441241007201480b10742d2441220840b40740c580c404583c07903c54220108400503517074002200d94586441c400d1144079a80000c0000003103095070b11403680700e120907140f000c101041c4911381c2641000404041c060348106100521500c000d4640c036410080c11003095030f01c0d441111034210340c5c0c01007020700500c2d03480b60700c1d4442d041b00b80350b0081c040790700c107001000071615025000701d0340000f100600080d282000009088403100c0d84e01c420f03d403450242d8405082086245c0098415030041064000040c082030942e4166000c02074065500c0c00c0050202e0070134803c207014164003c5c1c4110b4903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 738815314 1250 738814064 738814079
    0x80a050c0c010c090518010308030408030903250501060b0f0a120b0a030308071d091603320108030301030b22150b040b03010c0906110a02120f1506100324 68
    0x100405c0320f00035103200003188101c90f0281e400741c2c0203000041088804002103808500c1c43e01c059034021048000362450145c42614a0400003000c81c0701c01d290120040702c2c2401d2200a201d03a00003071808031000d62620070368481e038514500c1012205001d1160f25903048403503040c903034403807501d0035400340910f8141c41e184c0c00d0182040070126444000124003a40c1c6510107004c6c10701c189079101c0702030000340b41030700ca400d0f00380d510a1034210001d0030155203401c5d4012110100441c0e8408410030580b010707281401d0b481044030460141c205108691003000100300060ba901007aa6004000040416401071111050170300310319140701c050702d840010b0640445511980e440161284003c860400034a10b112003490f0980b01d204500501083d5110f0040058034021002c201c9510301d09000d81c1d030b1403516940040c002c41d000d24010030307103544100406044c0e0042001207082e40c00c0da10f0b411110610b0070300c00041400020b00500340c105522404050390145c0d40d01070049515001c8602050f2aa071143d11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 738816564 1250 738815314 738815327
    0xa0e03100603140a150209180a0c0f0516030309021309110a27050601030617030a031107052112070206070e060915070804030804060203090906040c080a050c0c010c 72
    0x403d44071014004000e074040308000031010346696200c98403c1c1440c4079191920000d4001d42c1d03d15400a400500607145078846000b03080c8201c0203010001a10103c15a008000300003801c00c00086c8801005041c0ea09824068403000746076061801140701521880170800c80c0100c14500d00c0d0190038881c0050800c055188000c4141005031440e2501e16035404c8101005010180250501105648072581c0c0c203100d6044607900480c107040115640c3c0d0b9400c3c07042c01010340c0d8401d001c1540c10101f20032807920740c1405440c12000410200c507081281075280d09440340206816802d030748034002c604695680c48030b419500051200c0c0c050000a103803120003e91902001c4820500140a0503030480701444d005007610100c44c00035207192a0201e400010001c1d07903000710300c1510076003000d10002000680d200e006101030111030b07002c1e40c5c8030a00300c0309121500a001c0d084503c11818070f100540c0071340c1e1214069900c81031603800410765482d071f40074582040c4a107240351f0040d5420b004c1003407612a003090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 738817814 1250 738816564 738816569
    0x240e10083904050f0904032102130806040c0e0c0f0c0a02121606180603360c081207060b040f0608031e0408071205120703031a03120a050a0e031006 65
    0x688140b8000300365001c010864130101d030700070b000c6000c052400048110f41001450008c8040310014580405540b4400c07184500f58045900c43d8001e1042204000ca805006002000d20aa00701d50900704969281c0342809900040c6083c404041452586c2040030424404901d13000b50070b07109807203c00c045030f580310700d68000f030644a207088840000c0c0c020312611014085003c814000e002c0c0d5030030198201c0140114009001045034100200b40c9801084103500751000561a446052943c4a05e031480c80c02c04158408882c64006480340d116a0703045908031400725911a038001a03c079200070005000348012188090154a002c0f40468182d000000501c03010b0b018288004224600441c028a40d205a0040620301c2d0000041000380619503160218658454410303501d20341c6a81c2c01c1b10620f40c01c00e134001d42c00130340c07201c140900e400c40054030000410402d07400f4040c0200440441e811b14401e082d220001c01c0000100807081c0780c03244100c145407842c010143d980c6600980c03000009800d060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 738819064 1250 738817814 738817819
    0x109020301140f011d031f050121020a090216060e010509100203040c030f05120f03060a0603090b0c0309010b040e0f071d01090f06240e1008390405 65
    0x80c07103607542e00d203049079540d641d0880581d20072004003880d22582c1a0300d44246039441e018810016034220f8a0310303400307103880c2005107808001884d6141014242a170000880720791a0401810300b4003000d0789901c068003040d68060480980d840d403810704006001c00302240050002e91820400e0480210190003050043c90210103c4603920270300d054540481c407003590000e11010400030100006140c004030220440d01036001d5829030160120101c80c40c2e400b03400c07140310b070351400010800c140c070340a2a1100034210510b000c11918241c1d030303203605462402500550b140040400000e40201c002d40111b0050f440180c0140b0050301c0e01c1c207080340d84080920700ba55190103044008100120b4180d004d280c01180232002000503480c200c41c42c1c004001911420703040b01c0e01d03184041200c071900c504d441c601001d060603aa00745003c4140082040c112100000c1c454901100503420301580420f002d6040010705500010302c2a86920b804442c41d41100c2540803030800c0045521403000c0030340600100e0740203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 738820314 1250 738819064 738819089
    0x609140a0b0712080c0c15040f05070f150305091f0e0307052a03120903100e030c060a05070c140102041214070f030f030804020a030c0b0d140405071a04030b0109020301 74
    0xe00e8210b5010b0700846103046c505074800505111060641180c3d90b40090007441c0c1c03505012840e498032400c0014a0700030501d060254142000483c1090751055074842640c80e00f0004c03420101406511100c16054034031500300007005400e918441540000c802c5003801c030407690f075000d640c40d10719196245040c02c01c090314001c000c1d52120141c054075a04170075000402030415802e170000d0b40000398209900080e00b42c41072048003048484240703c0d404640101c01d004584402c000611700d481d24400601c80b8810074141020301a00c0323a08007001e0304441da400121031940c8541c01840b10300901559100350011104506401c007800700f02c5c411260050318610540d007106848100d00800c3d84003900c402414201040c24000110b44142c0803940c0051001300651580b6030f403601c602c0c050308556001003040300c1d070010384500440c401e0310401c1142e1411100011440c81c4ca500d40d2500c17050b02c1c2c0308100f10000b0040000c9104a2505d04540c050b5501c40b48000c0b030303540c41c1c582e8500290001d000d1511346004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 738821564 1250 738820314 738820321
    0x11107240c0f091712030705090612150d0209060d02060d0f05043c060b04050106030e0f070e061207090507020a0b010501180512101a030111040609140a0b071208 71
    0x110014188100c144c04005145050501407241d00680c002070031380d0100310052018074035550320030004280c0e007407884078038586600b03000b1480d0748c1b080341d00f10080c0e1061140a403201c0061f1102c07003a00381e01c2034045980c46500080c0b030011906c0c0f80f140b142c106103010b2808941d0700c0c0b0f290b41940454019402052800121000501110480e14241041400c4101541d8514010620864890307502c0c9215500200303030300310703c00041001e6510a81140b070100b51600d02040d00381c8410460303008442070070f034020404036260281c5640c06003400f601c1030f401103828598100340101c04001c10001405a402d042289160071030009444004103002250841e0f40f1400000d139a601c5002c071000011000b800f41c1641d00d2419007004a00c8602d160104014041c2c504143c000d103582e441a0071080c41c990a01c880c041c1414020107007141c030005020a090f28040c0018800d06074028074120a079100540c805403c44082c0300003c82c8030340e09a00c04c615808001605200b0481c2c001c0429551030501e0310790050039103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 738822814 1250 738821564 738821579
    0x6070807110303060411040e0703090b100303090504021614070e0709060f0c030e10030207211d01020a020a06030c1205130206090d020a0323011107240c0f09 69
    0x1c0101c0c0c00400e6205102080c80c2e0b141544c80083d900b103501d0407051070640c5d50817042c214098201c50140200743d4a40700c45082c80200800d2a50001000b90101d981c9821660090000240f9000340c500941c0d02050100a62888100c0141c030607030400010110384940b070070400da0701c8816000e100002c0c000203000c40d070014050b000d107006031401c0f601c0d2045440c81511781182c503a040c0c90010340401400304490100e82d01c0305c8942020141650360b01503030f11001810041710009012000c015246550040501c900750720069050303038a04104981d9550904d8400101d10305032004c200a5440540300b8070003c4c819806a00041d8140104c1d2111440d020021a803035088a504039041d41084c005051100300524010000b06040c10008180b01c54404083c1c02044122070f2681085038280c914201c01d5a1154903030104c002403c1900000b8018a00c90307241100050240c460010308c218214610500c075000045408040300c1c40507001004641040f40d8010058030701c0f4500203000c038038501d40108040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 738824064 1250 738822814 738822827
    0x507080d05160809010215090a1a0601270902030708070e102007080304030c0e161706040e010908180303040f0b0f040308040e010509010506070f03110f070806070807 73
    0x4814155098450b002c142d02c41c00c40383d5010306039190450085011468107040d910b0300c10341c00380410200405082d600c902c0c15020440c440c4601c41d801280b10380810800740c1e8130420b03050308100d0035407e01000740d415029020b01901d40f0b8000c6482c0b2800402080182680028000c0c4200002d5440c07980070045141803043c5280c4e220840c80028840c00620018422020700040400500d502120b0005644100e10307804c541264004441c1540001020409161600080c6070802140b4540d80c440030008003000e0103e2001844081030b05600000061855407a41e110b4031001115400a0040500e2403070f08418a9100b401c070070b44c0081112030951401e040020694003618021010460500d05001c0440d00503041140381c1ca15100c1c04200200000d080b080141c030007031500051007621541050100901584160003090003070354240a2075010900348042023803081d40508020f801d483c0143c0c0054180490b61001c580d10307206000001605440c0001e4861160313102d0b0761100c056072103090040700d08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 738825314 1250 738824064 738824077
    0x30f0a12050915131a01030c06020601210c03021e1003090f1401090c0801140604050405210d150e130807060509100903080f060a1d0a02090307030507080d05 69
    0x55000d280402c44407000100c03e42e030461042940f501041d0140d66800c1e20b40c0c0380d120b001c420303029110b8004000300440d440e2004080c0c11180060301c0342d50f060198200b00304040c10752030f2002d058032403900d0061090000b034a070060343d00030b014078228040100000b5010f020150502d40511200c0180c9810140b00b8445c5014040d4011254400000b0b16104c00185440301003084000755682d0001100242c004030000b40140130103c00890308c00c002d007844542c0080010b03e040d008034200300820001500210300c0900d50810100303040a0b80a00c8101c009541c090000722124040c41c00220500c41c1810b82030319412511400700b03201556540041d07400e0341c00b0796034000406800d0140145400204540c00003507000702014121036480c01901a40d9060781c0d510b90301600445c54140900020300da040711380c244d21581c01e850446041e40782c880c988500c0705440c090391165514020110380c4080160f012150448401001c4905a94032030801a448030034030b00c55641e8902c0381055054102d8001e00031750b0003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 738826564 1250 738825314 738825331
    0x7140a020a0219050409140613110108091c0513090204050105040b031305060708090d020f1b0f0d2405160e03030c01050109060f170c1011030f0a1205 66
    0x4403101c4680c240701c0e0103181644022002c603e42800401e054540e44698440b0a00400200c035909880a174200c0c1007500240c07442942d00707120701100300450100815100226401e1130181c40319a1a1001603007013244441000d8090040200c2100103164450080c003241c406068400251301c0d0f944c80403500b00d00c640d2051038041807007071008000030790840028550003010551941018911652100e0401d18110307081d90205000400344841c060040113002d000c400b80e40014006c00300c81442070759851200070303810100428180340d403044c252030325140402d40003800740c001a48010146803112642080c100c02e01c4081d200001c42d049617480c540140c0d40114010898910000035000307085038001c02000320103425100800030441d00010034400d0340d000b86890307000000c000e401e018480c802204c0583c0410b41c001124000ca0101d0040400c0d40070780000112515007001d080f008003a51041c0c02109403141502000c280f80c1c1901114200501004105a4810607160482c504d05d000315041940c0340c0781c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 738827814 1250 738826564 738826573
    0x20909010603020a09151e0e011e0c0516090b0913060f020f130510030e1e07051206010602120412170f0a0504030b0a02190f05040b04080607140a02 65
    0x81d00c0c0241e004100c020414074088805641350001c268019918180074000247c1026024074130307014154603150707059010303c5d01e0380300ba0805e600001c1500700408241c400c4000030030480340900d4012584038844950010585006000c0800751080c2070100c0d1040701c1c080390038094052035500e4003da503640b203982900132540910540da2240d0008000302002c4d403134200e03070811800340c0b80c8002c0e0300139200341c0085406940c20142004248100a5a5103080c003040c141081c0183d10b2807500071a90441c0104501c600210703001c0300300741a5203000d40e540d004942010390000115501e00020500c00d0503140e50380c007190004401202200c00324030651084102c40c8940c0b00340c050000302030511ba0a80e800320303100c04d0390401c42c032000c0704034035540a1146000070400005080007001140c10b10507501040102c1c0441c00e14023000c49030501500078100b02e50801000c4520f1241d00d80c060000d58014142e1840c440741c0325030715580d107240d0302d01c03007502c60750040344c5680c1942d2170703920086040b503583c0a460307170181 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 738829064 1250 738827814 738827819
    0x1506060708130f12050705060a05070f020a030f0804030606060203040b0f0c070302040c020705040f051302220204260d020d030b040e01110301170303093a0207051302090901 76
    0x109034a41142c0780e14414580d4400c000203409100420020203081020000d48200640f0710f0710b2454003c1c41da0101d8040ca20900c11039500341c1c1c1003019240042d404c8503e00020103058400100b00e00300d6600b0080401c8529092042400500000707001036a10622003002207a485043c10ba9681c0030384e01c40c00298a07010000030401007185c001500100103001e04807401c058513a8005030644200c003c01d040184e1000344100110301d81801841200da9018500f04814181822407200000c0007410207802400b031800501034240d54010384148602c0000005c6454a848140c000503080f294843d002c0b5000e40d8488510b04054086a100d21209450b0001c10070041150015409003902d442c02c95405590f414070751460484c2030258040c0c1d8091802004d030f803581000d4401d0340b0381c02c15a0000302581c1c02401001101040041d0001411041c07206084a5051801c24092070b014a910103102c140011004840e131150000b40301021b491044511645c02c002054804049014844c015a440304448004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 738830314 1250 738829064 738829073
    0x2040e07032403050f012009010c0206070c0e011406031504111b03131d01090f0207080d0501150f080412090e0903070c050d05030d0506030c1203030915060607 70
    0x80001c05814414000d20a2885840080080c402da030080c3c82d00d812001d400072842c0030070300c501114459038030382900300404400d819079880c2c01000511418450031188010070740d901d050a5a903000e502a0041001d84d0719003049008101081c803030f4840200c0da06414118a00e404810790348100c0e4074540b41c62148900f00200805448400d14408074a4010880c11b406283d0724480a01e03012a000003c5503900385210030b110485110f0fa109010808500203c0e503c88074040700501c0c1121100e07940030400d0702400d05200700a2284030750040080c0000a250900c440c01360304103c0c12980000308003074240c1000081501c090b50b520b00b001c000100c20343d0001d80000c20b0440030b20b5a50352076203045003403e9203403400d179840120300b0ba4070180e0310f500c0800d490302000300382004d1602600c0c0554540c9480d4a103a40c070a42c3d64090102008045600c0d000002d040351010002540d400d01d008043c100d1030b003000c2241c02d40301c0d44103580034403060140c00626803900c86180c500703030300a80c0e0103040e070307480c0100030380702e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 738831564 1250 738830314 738830321
    0x4020409060b1302130b090904060209040b06041e090b060f071e050615030a120c170310050a050616021003021201031406100e0109090f02090f0f0a02040e0703 70
    0x1250600e6440c10b909401c0c1e200c91884103c0340980c030740010380c0e80302038400c1d01d80044904e60110030400c20401040c01903480b20031500c0d400035405840580c45140240016000c0c140c0007030300640000010034002010320b80701d181a0307424400540c000381d0f000e031100c80c00001d907145400190f8100c039042040c00000300c1005c00404541e0700580320000348240551600140b55220f040c01e4070b56900a800f03001014003107841441d003642c412002059004900e5964000d0012416051300510040c1102e071024482d403103070440400c00d41d205000350361340b40994281e21564424018140100311580001c10603050040c100c940807491183c00143c1d10b001603003044800b800040600b820140c01f030080c00011a9520340e81e901840c86222202801642d502c0c0a030303d0480c0090455a4016031380400f00709061412082d82d05540158002240c2007040d4103103c1c110074400780009402c540702c5001c218100842500650080492071b54070211340d12205070020580c040c0c0d004070582c4880007004a07410b64001c1c1e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 738832814 1250 738831564 738831581
    0x403060c03050c160606052806021b2101140a110906040909080706052703030f0f180303090309010306060f050d0f0b0301090b060913052d030f0a080a14040204 70
    0x1400421603e07118008103c06c03002d48038200188c8000300070500da01e400c0b0a281c41e40030700f003a840103000d58201f504201e142c02c2d041c086030724050143c01c01c1e0b06034078100c810001003604000100a1002514048002084000071103c485441d45020302ca481007170708403003c031015103200030309045c141402c2c101e050b0000d000d8114100d8110500b00714407000107481e030040380c3c400e0100a8003000384800b0314520956902c00c40002c030038103800410030400441c20b804c00054020380c000000301256664030841010790040c5203030044403484003008000800c0c10000041c00203040030ba030b090180766940d0006642061a042070074000c03400034048400750403881d03031004030b080c1c21004000ca00354450074040780c00c440325000c00703590742a080c4041052a0400700303261500484d0700001da250311455a21900e4403008820384406044e401d140b04400f055000c4034034402c03041102ca00396941c8040038250000e155100e02002404541410005411807025125001800c400d145141d842d0740d440d0760800008001c0d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 738834064 1250 738832814 738832823
    0x3090904060c1e080601020c040b0d03120b04020d0e0709020a0504060e0f0d0807170301081504051c0801150e0f1c170918060616060b0d06020403060c03050c16 70
    0x40001c0071401d20400f4446002e1080d40d26081003604101c0d000a080495645a0320b01a60805440c1d805a413181e4400c902142d0b090702e80740c183d0310307075a88502d401f4101e1601c07041c5d4001c0c00400c41100c40c2140740d2040140907090701c00c0b030320001d85e10052141070b801550b0031500481c1c001d010070003480e0b01601c1000c11807400144034001c42a6024005145110744c28000d0701e2100c1e010441d0010402c2642d0360307107410b000180c08503055601d0300415540c0c4038a0050551241301025000c5420400300704400d6071903007400b011040075442e00c002c00a141110900c84c80c8681d0802c0050341c03c44078000e040520842d800508005500d0820354288400d181c0858104803d0107918001000410920480202080c484e003400c0d0303a465103007108104106070802c5e181016400410203004140e924882202c0001c4508003018040d80b841c0d0403e0308c024504282c0c16a00038402207850302c02c00c040d6900030400c1d05e10604080020030181c400480031540100c1d424551048100141d403283c00c02c840140448034481c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 738835314 1250 738834064 738834077
    0xe07090f05040203072115060602010506010903150c140a05030702060f06030c010c0203210c010b040e0607080c070503040e1006020105100e0c16082d090d0204180f0201090803090904060c 82
    0x35031f0f1841c2001c4105452001026690f0300180005907080c011a0f4114009103410480e15055486034000e0b00040c0310b400300015030f10b22002464601602c4800c05040c80000100d88514884c1c00240c0b10f580116070310f400601074800001c0880d140b8521144c06690080d000b804051030b150015990301000a13020f990505c0b80d588070100901c44c0615421707020340c1c1004c4c40703900c0b44802c001041c2925481d00327006204a00304013590031207600004405d544080c0e1031424805c1602c03000c41d64042ca20909a014100f03000010b00410b00089902c880ca01440340e00001c40c000300d55405e4101c2c00c8510942c0d00e03a0307101c00c005034108500c610b040692900020101440b901d04003021140242003240341d001216003031008503180b541c1141c00c20071030020551189100440c203a5424540703401e4410510401e11924110b1404400e5480300d5110b10040001c000400b003c40c4124104558110004070381203002422100c80880c4a94022069401c18034025090750055152a51080b01529181c800c5108220a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 738836564 1250 738835314 738835379
    0x4080313051e0108182b050406020c04051806040c0608010f120f023d05090a030f0303180605060a09020f0a030f2a020106080102040323010f0e07090f0504020307 71
    0x3840400060b02c0a9003444289aa03c46d221180708084c0b50b0380f040900c2801c4c04200303c4180c001c00c0380d04240004942c0040c150740c84100c800d48940404000300e820340301b44410002000244440c0c0c1303054480607200c0004507030741c40c031100125410340d00520501e0210141c0e5000024008150700186920082c070202d03080740c2d00300d440e440b2000e00035005401da83c0810710000451380b40c1030003181d1031451490b14602d0420b0402c041b0782030024034800100b440c2c00c2042000e06240c86684103445680001c003810f0080c00702820310001408043ea03000b48208059480001d0781d07000c51080310b4448000341089418926003c0b000da000340350a4500301c8080380c0b525103109107030740c000241d69030303040d061510a406400c941c0b40090844140d40c1080f0303103030b82c4100400d001040300011a81e40c151029956100f001c42c1c09400c140c094542401c012190a00307059001100d00320205a0034150b50142804100d450300910000d07083d2201680e0284d0543c20003842408013004d50003600b0f021300882410b4080040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 738837814 1250 738836564 738836611
    0xe0613061805190509091605090c0f0a0903150b2107050d061512151112090319030506090a02070206270a0803130e0709080304080313051e0108 63
    0x30700f41844035610102201440300c0d1401600c0360b50006c40086c000e02c0340c2000381290002801090082d681310301c506500103075082c17404e03600b11000000e003032079646c0e198020300c40d01510150040c0003c442103020b1003580500800a03116081000740c00420320240c06100c0d01d1034010f0309034003d410010502a041020410380c48000a00381f0040c400c14001440d42d040000c0321326444482d030042e6882489040700c68010545948243c80044024440055982d100c0e142d48290340c410030072002c9020f04404100000100040301400c603008411200102c0085070341e0b0704404640c400c8414030b5000c03a0100104105114a81c040c29001d03101500c118a0207502c42003084001c0386003194101a00701d1304165072900e081540c00800181601384c01907003054000180640d47d101d190040d047c080c8400000281d030b4034803d0400702c006040140c29680d403940c55510058a9a00c2400343c041c00740108540021541000705002051a00d186603510040f103980004451100c006092404407421114202c01000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 738839064 1250 738837814 738837829
    0x10c0b1807380703021209130e0a0b090c0102061b04180209040c0c0206070f051221010501020304060210050a02070c08010c08280b060c060103030801060e0613061805 73
    0x26401800902000d048040006105030300900091640b1100b4032640700000c2e0005a440215616504107a46035004400459980c100c4462400145c40c10b040d00c880034500085076030905070f406070070386e03400c2c603911002c4d459681d444c003c4895006a0100b0000b41c18840e12402042d00031030800b040a1501d07039180801c2d4410305122013020799455000503041c42d24501485070003c80c04880c10030015000301c13a0005045030103030041c00740070120283c9255041190070310840d1100540040703030546540c0080303008201d10046441c4201020f42c07c00c00030a00d50f0002082c0ca007150015030044c00585500540c41001c1d040140003018829024440b0f8000202100c20320006443e0200c000a440701441030700070044034018103c01c05508158849808220000390340e0181c41000c03031804124420b0880102d442481a0100d07020f041c003c00c40040101a0710800182c1251000e60f1400c0461841390200304144c410300342c0f421580322640030108480c03802603ea000c0e01d508900040d481c029070b0754000c10241c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 738840314 1250 738839064 738839099
    0x50903030711070e15150a0c02042708071109161e1d03120f0912030c07030b07032c3c1c0914010c0b1807 47
    0x1a000402000381080e80031459004541101004007203151500c0102943d41601806000c1e58040c84200c0e00400e40358581d28031411004200030641d10107041d5401454a581c0d40c03801c07403296043c604800038085100d00440c52044020200d90b1031820181c1d40c0006950095008a070b01c04038410001e0b85540d6881c42c00c511a034032291081c0341a141c15030000341721320381041e50340a8250301079000d000507a60110f80d980102c055000314096210301c030000a0300d0103103407010040c40c1c02c41c0001d40415800215010b02400801981c0080c4801100d054194a034022950100c4280e030042500304041441c00e00c820383c120f82c00f402c1c009020401800306003040300000381c2c403090220301d00617a44806402000507111500c2c9018210010010b000100303c202d60480c5840c40005054407e031540e04141440460219000e201151040585616010306000311520901c1034180e00040c5007031841d40202e40240e41300341e10260b055070640d191600b175440001080c000b6007452091081c08158140040341c121039 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 738841564 1250 738840314 738840331
    0xb1206040c0611010510031b120821040b0c0304170a09030b150609132d0b120a0f03020705040c0503090f07030302300d0c020d0221090a0905 62
    0xc01402c046000e05054124016095168544001c100219032922103910a90394040d440703904a41c0321204030840c17411190440054001c5010041c0104100a00181242d840201c00711140310410602249541411180030700413140d580d0000b400d4580040085a103d44034820781c0b868000c2143c4081e6254000480c60b6000c69030298090092100e560807641d80310f000866141da0070887c040100b40c0c54025640302c14010701c10590410600a406d820a4041c0064189061440b000c001c00f102a9801c0b2107030b012254905d8501071141d1400d04a81e80a80e0740c005600400f9074070680c0d9161016980f801e0710540031805403040129040e51203019203000540c4541cac4aa8890400038107003030034400e440e07400b180d20768005041000000d801043c0c0801c901d10340c24505000c12443c0054410141c1044a12240c54200185444440e16980d1103100400a1682243d042d135555070003e0769a10340140d00001244605807000060002c0350004100080c0003405003500d855803034100ca02910030070f450214 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 738842814 1250 738841564 738841583
    0x10b0c03210943050303070c0e01140114090a08010e2503031e030204050409080a02010b040908180103020702030f01140906070f03052211040f05100501030b120604 72
    0x3401c00410400c2842282c09209011581e2000c5450000000c024503040c0c41e003540c5032214040c440ca140c040f403a00400c0b000d0141c1e030391210280341080100141d07014a4003110071a00000c1143d050001d542041c622068440041748202d0368103241041c0c00c0300801645c04502c1103404100b0510a005800240c042c402c0140b941c0c0c68100768100680005a02425250308880000c00209611582c200045011059059100841c1520850103031040e81c03c5160821b080c192003004200070a401021500c200782c1c000c00c0f1038026403003003005651000c1c0703010301740c01814400880700f4500c4010301042490141030044c0342400310b901082c11305682001441c0740380d640d0444203c80074410041503074040000000392505144ca6030002e08051030300f440b15070400d503560000500da01d901d00545100c10150828486080b0054a4a1142003000510480c00b85003040c001080b0b81d048e07402050f0080501e42000b0401604000c011001440c502418580c40803174141c511280003030038002640540d01a900c0d03007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 738844064 1250 738842814 738842821
    0x311070c060503270a030e0307120b0708060d05070506031f0f031a04080d1a060d05071412010e041a0403030b0102011a010c110a0b040e0114030606010206010b0c0321 73
    0x803da040d02e940a4481311045804001e1803910100b0120a1140d00d42050803d01d9141c3d000b007842c0801d03507084101c41441c0903014005101c0b0092410307128901a07039070083d9950350f40080c48005c504a4000908680c0501c10a01031072400710065980601035060f0a50103202c2003280701c08031100d6a00c0640000b1200c4002e00600c000a8030300008255441d00c20413260425945620003445854032070130110b540d0321588044c40e00c4500d0301c65808080140901c1d02e4900004a66009040c140c90765404030310080040c2c01038080344e809031040032614031488091a840c002a0380040c150040c41151090b180e240c141c0d41050071441102e0040d4029600002c00511610019017143c07000f50f4105445203d40e003148285070b03401040d485801d40d101649092005001021800700c2290f46c0080c83d802c0c0300480e000c95801d400d412400e0486000345408203001041d8001d03d03442e20790588050740180c00c5030005006000c0c1d550018440b0030000340440f8506039680c0480070307451003441c00f84070f81c2c07004003c00c4c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 738845314 1250 738844064 738844081
    0x4031814040e1501030f08070215120f070c060b0402131811190509031609150e0417031b12040201030b0406080c150408010e060103051b030604030311070c060503 71
    0x1806403101e902d0340205071010303d60b4101d41948070140f10040c40c0f500c403d0411001c101c4c1c0c035410385500c07550180202c0c3c25401016401700080d0000c85517130b42c2040039980001d0303480318030800881c0901324949030303006542e0032a110b181c05049046589138106400304a503031008840c00c0300706002419648000781142440244400c11b95258000c5081408400e02891003030b1355002004040c030016509260b9601c24140d0086030802e0600d4000d0301140f9420f40b000240400150402d000c01c10602c00b091110136100c50445604103809d07a006880c0211311440c004088400320029038018501482e010880c41c1003c0fa000c8183c1c0c0801d194000d00d998003c1030001f1560503029501d181ca40449092040134108100b295403550403010380e074450409104901080010182120b000c2d00911009003d020401803201d40e030342d00d003840112000e02c101c24901e820407186010709010f801d00140980706035290f60b2012400391418a505410000301002407070001501d200c4a18003c0c00325844454036440d00b403a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 738846564 1250 738845314 738845321
    0x50f0f15010e060d0b03191b0b0f0c1e030405031207051902130509010b04060503011e0c030f112503020714060c0f0a02100905090415020f030a0b0a17030703080403181404 75
    0x40340d040d1450340c101c02d1042c0c0410078290b440b4954807045c03454032000c521030742c14079081422a03240c0b1a108cca8000100040c2d0100c0244151642a0102ca032074841104070204684100b0401409503003100300828680d98000c0b0f40070760014002406c000c015485050900103c44c402d40380b8480903913540302581d1545c141401f504005260490080110040d1380030486401203009084a00c0b407580c0c3d590308209180a9489100c80c1080c0f40400c100402035880d1001d413540c40710036105000310035030380c40c102001c20f0314002043c11603256000c1c3c00705030f142c003007000040e0960003810340d8050f01c103114051204004008203d8050402070043c50400e441e4010f200c04106420400f80801c50b4034081401aa201d181e940c0d0741065006400820300d00e1b4298802c0001d0084148820708648000b040c010f100780b580e000508020b0003200d05000896842401c2ca0b500d07403c01c080c1030940d400520002c07010a0040507459400307402030030940c0e080c4281c07a032088200c1c48150400381c10500494081e800c00c1c1464030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 738847814 1250 738846564 738846593
    0x507030c0e061c150f0e06061321151515140d060306020a05031e160806030a05070620011503020607060f050f0f15010e060d0b0319 58
    0x41207940d40c004100800d03480d00c100f001d07003040a84085080a1030410a0b40060703010903502508452540c1c450751602040401c503c542022244094007058103803529804840005c00000307c0c0d4400c551070455030010a283e415100900b0302c070409521000b00301c135a1450740c12110150800140d183c00150703007010408882e0000c842604040c005620070a8211941f41c24000780c1c2c04845446031080200344003e0f0640c0c2e08000d007c50300100314403075015000009940521b02e04282c0451081035481040c01e8004200d80d041d0450b003140c1c607140d02960040443c260005000360a965100c4d84c240c507000e190003101d40c02a40010000501800030a1595064100319040c1e41c00074030420180741458154a050303030101030720035800050103d080204581c8101401811005d00780000d01c0c00400782135004c2d10450355500c10031001030018000c03071400214000f1000050b1100244900140c09006107a00001108041a9598652030100c0c0d5020000c009036802e45484200b0040090b10309071105250350b9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 738848920 1106 738847814 738847817
    0x1a130902191e09020a0525050a0311121602210609010902011b030c060f020c06090a050c031b01030c05041212090503160521060a0507030c 61
    0x5000038420200200b0baa150540da040080203a2140c044000c0c0043c504114007c544070014014981c0840e15038410900144c030766407060715140440c0d0065020840190440c1c04c00003040012904d02c1c940d109106083c40c1c8a078048400700c0b440701c0702c006d205074807540d0741c440c03411403000050101c2d101050494165007401089039009200c182030a070700041d22040700d00d00850711001103001540c3e241d51103800c0c0300c0050f03d49800400007502d0328801d0507001c010141c40288100541400b42000d10060a00c481300b40c0341c29490912000845402508151303d03000c40d03810741281072801d40e4001e013000b00e10814108021102031180c2c0e008030840c0d503034141c80b10b014082d0311146004d030000c098440040e05a00d6400301130b90342440741e2441f8441c1c40d0084d010710160815142c50428100d002a0441400c111162040e0070309a0481e030416840c2d80d550104050300b41e060103814a49440c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 738669064 738848920 := by
  have h0 := BRFrame.cov_init 738669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 738669064 ≤ n) (h2 : n < 738848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
